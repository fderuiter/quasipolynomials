use crate::math_utils::SigmaCache;
use crate::schema_generated::{Prefix, SerializedPrefix};
use crate::types::{Int, PrimePower, Uint};
use crate::types::UintExt;
use serde::{Deserialize, Serialize};
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct RangeWorkUnit {
    pub start_bound: Vec<u64>,
    pub end_bound: Vec<u64>,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum Message {
    RequestWork,
    WorkUnit(Option<RangeWorkUnit>),
    Event(crate::events::SearchEvent),
    Heartbeat,
}

pub fn generate_work_units(
    components: &[PrimePower],
    target_bound: &Uint,
    depth_limit: usize,
) -> Vec<RangeWorkUnit> {
    let lazy_cache: std::sync::Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>> =
        std::sync::Arc::new(
            std::iter::repeat_with(std::sync::OnceLock::new)
                .take(components.len())
                .collect(),
        );
    let backbone = crate::backbone::SearchBackbone::new(components, &lazy_cache);

    let mut units = Vec::new();
    for i in 0..components.len() {
        let comp = &components[i];
        let mut curr = Prefix {
            n_l: comp.val,
            s_l: comp.sigma,
            last_idx: i + 1,
            factors: vec![comp.p],
            sigma_factors_u64: {
                let mut su = Vec::new();
                for sf in &comp.sigma_factors {
                    if *sf <= Uint::from_u128((u64::MAX) as u128) {
                        su.push(sf.as_u64());
                    }
                }
                su
            },
            sigma_factors: comp.sigma_factors.clone(),
            active_mask: backbone.compatibility_matrix[i].clone(),
        };
        expand_work_units(
            &mut curr,
            components,
            target_bound,
            depth_limit,
            0,
            &mut units,
            &backbone,
        );
    }

    let mut paths: Vec<Vec<u64>> = units.into_iter().map(|u| u.factors).collect();
    // Sort paths lexicographically just in case
    paths.sort();

    let mut ranges = Vec::new();
    if paths.is_empty() {
        ranges.push(RangeWorkUnit {
            start_bound: vec![],
            end_bound: vec![],
        });
    } else {
        ranges.push(RangeWorkUnit {
            start_bound: vec![],
            end_bound: paths[0].clone(),
        });
        for i in 0..paths.len() - 1 {
            ranges.push(RangeWorkUnit {
                start_bound: paths[i].clone(),
                end_bound: paths[i + 1].clone(),
            });
        }
        ranges.push(RangeWorkUnit {
            start_bound: paths.last().unwrap().clone(),
            end_bound: vec![],
        });
    }
    ranges
}

fn expand_work_units(
    curr: &mut Prefix,
    components: &[PrimePower],
    target_bound: &Uint,
    depth_limit: usize,
    depth: usize,
    units: &mut Vec<Prefix>,
    backbone: &crate::backbone::SearchBackbone,
) {
    if curr.n_l > *target_bound {
        return;
    }
    if depth >= depth_limit {
        units.push(curr.clone());
        return;
    }

    let saved_state = curr.capture_state();

    for i in saved_state.last_idx..components.len() {
        let comp = &components[i];
        if !curr.factors.contains(&comp.p) {
            if let (Some(next_n_l), Some(next_s_l)) = (
                saved_state.n_l.checked_mul(comp.val),
                saved_state.s_l.checked_mul(comp.sigma),
            ) {
                if next_n_l <= *target_bound {
                    curr.n_l = next_n_l;
                    curr.s_l = next_s_l;
                    curr.last_idx = i + 1;
                    curr.factors.push(comp.p);
                    curr.sigma_factors.extend_from_slice(&comp.sigma_factors);
                    for sf in &comp.sigma_factors {
                        if *sf <= Uint::from_u128(u64::MAX as u128) {
                            curr.sigma_factors_u64.push(sf.as_u64());
                        }
                    }

                    let row = &backbone.compatibility_matrix[i];
                    for k in 0..curr.active_mask.len() {
                        curr.active_mask[k] &= row[k];
                    }
                    expand_work_units(
                        curr,
                        components,
                        target_bound,
                        depth_limit,
                        depth + 1,
                        units,
                        backbone,
                    );
                    curr.restore_state(&saved_state);
                }
            }
        }
    }
}

use std::sync::atomic::{AtomicUsize, Ordering};

use std::collections::HashMap;
use std::time::{Duration, Instant};

struct ActiveWorkerState {
    active_task: RangeWorkUnit,
    last_heartbeat: Instant,
}

pub fn run_controller(addr: &str, units: Vec<RangeWorkUnit>) {
    let listener = TcpListener::bind(addr).unwrap();

    let heartbeat_timeout = std::env::var("UALBF_HEARTBEAT_TIMEOUT_SEC")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(15);

    let active_workers: Arc<Mutex<HashMap<usize, ActiveWorkerState>>> =
        Arc::new(Mutex::new(HashMap::new()));
    let worker_id_counter = Arc::new(AtomicUsize::new(1));

    println!("Controller listening on {}", addr);

    // Load from checkpoint if exists
    let initial_units = if let Ok(content) = std::fs::read_to_string("checkpoint.json") {
        println!("Resuming from checkpoint.json");
        serde_json::from_str::<Vec<RangeWorkUnit>>(&content).unwrap_or_else(|_| units)
    } else {
        units
    };

    let work_queue = Arc::new(Mutex::new(initial_units));
    let total_units = work_queue.lock().unwrap().len();
    println!(
        "Partitioned search space into {} discrete pending work units.",
        total_units
    );

    let completed = Arc::new(AtomicUsize::new(0));

    let active_workers_monitor = Arc::clone(&active_workers);
    let work_queue_monitor = Arc::clone(&work_queue);
    std::thread::spawn(move || {
        let timeout = Duration::from_secs(heartbeat_timeout);
        loop {
            std::thread::sleep(Duration::from_secs(1));
            let now = Instant::now();
            let mut to_remove = Vec::new();
            {
                let workers = active_workers_monitor.lock().unwrap();
                for (&id, state) in workers.iter() {
                    if now.duration_since(state.last_heartbeat) > timeout {
                        to_remove.push(id);
                    }
                }
            }
            if !to_remove.is_empty() {
                let mut queue = work_queue_monitor.lock().unwrap();
                let mut workers = active_workers_monitor.lock().unwrap();
                let mut changed = false;
                for id in &to_remove {
                    if let Some(state) = workers.remove(id) {
                        println!("Worker {} timed out. Recovering task.", id);
                        queue.push(state.active_task);
                        changed = true;
                    }
                }
                if changed {
                    if let Ok(json) = serde_json::to_string(&*queue) {
                        let _ = std::fs::write("checkpoint.json", json);
                    }
                }
            }
        }
    });

    for stream in listener.incoming() {
        if let Ok(mut stream) = stream {
            let work_queue = Arc::clone(&work_queue);
            let completed = Arc::clone(&completed);
            let active_workers = Arc::clone(&active_workers);
            let worker_id = worker_id_counter.fetch_add(1, Ordering::Relaxed);

            thread::spawn(move || {
                let mut buf = vec![0; 1024 * 1024];
                loop {
                    match stream.read(&mut buf) {
                        Ok(0) => break, // Connection closed
                        Ok(n) => {
                            let msg: Result<Message, _> = serde_json::from_slice(&buf[..n]);
                            if let Ok(msg) = msg {
                                match msg {
                                    Message::RequestWork => {
                                        let mut queue = work_queue.lock().unwrap();
                                        let work = queue.pop();
                                        if let Some(ref w) = work {
                                            let mut workers = active_workers.lock().unwrap();
                                            workers.insert(
                                                worker_id,
                                                ActiveWorkerState {
                                                    active_task: w.clone(),
                                                    last_heartbeat: Instant::now(),
                                                },
                                            );
                                        }
                                        // Save checkpoint
                                        if let Ok(json) = serde_json::to_string(&*queue) {
                                            let _ = std::fs::write("checkpoint.json", json);
                                        }
                                        let reply = Message::WorkUnit(work);
                                        let reply_bytes = serde_json::to_vec(&reply).unwrap();
                                        if stream.write_all(&reply_bytes).is_err() {
                                            break;
                                        }
                                    }
                                    Message::Heartbeat => {
                                        let mut workers = active_workers.lock().unwrap();
                                        if let Some(state) = workers.get_mut(&worker_id) {
                                            state.last_heartbeat = Instant::now();
                                        }
                                    }
                                    Message::WorkUnit(_) => {}
                                    Message::Event(event) => {
                                        println!("{}", serde_json::to_string(&event).unwrap());
                                        if let crate::events::SearchEvent::DFSComplete { .. } =
                                            event
                                        {
                                            let _queue = work_queue.lock().unwrap();
                                            let mut workers = active_workers.lock().unwrap();
                                            if workers.remove(&worker_id).is_some() {
                                                let c =
                                                    completed.fetch_add(1, Ordering::Relaxed) + 1;
                                                if c >= total_units {
                                                    println!(
                                                        "{}",
                                                        serde_json::to_string(
                                                            &crate::events::SearchEvent::Phase {
                                                                phase: 4,
                                                                name: "All work units completed"
                                                                    .to_string()
                                                            }
                                                        )
                                                        .unwrap()
                                                    );
                                                    std::process::exit(0);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        Err(_) => break,
                    }
                }

                // Connection closed unexpectedly
                let mut queue = work_queue.lock().unwrap();
                let mut workers = active_workers.lock().unwrap();
                if let Some(state) = workers.remove(&worker_id) {
                    println!(
                        "Worker {} disconnected unexpectedly. Recovering task.",
                        worker_id
                    );
                    queue.push(state.active_task);
                    if let Ok(json) = serde_json::to_string(&*queue) {
                        let _ = std::fs::write("checkpoint.json", json);
                    }
                }
            });
        }
    }
}

pub fn run_worker(
    addr: &str,
    components: &[PrimePower],
    stop_threshold: &Uint,
    target_min: &Uint,
    target_bound: &Uint,
    illegal_valuations: &[(Int, Int)],
    suffix_abundance: &[u128],
    total_weight_scaled: usize,
    sigma_cache: &SigmaCache,
    max_idx_3: usize,
    max_idx_5: usize,
) -> (crate::dfs_tree::DfsTelemetry, Vec<RangeWorkUnit>) {
    use std::sync::atomic::AtomicU64;

    let active_primes: Arc<[AtomicU64]> = std::iter::repeat_with(|| AtomicU64::new(0))
        .take(crate::profile::get_profile().active_prime_slots)
        .collect();
    let lazy_cache: Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>> = Arc::new(
        std::iter::repeat_with(std::sync::OnceLock::new)
            .take(components.len())
            .collect(),
    );
    let backbone = Arc::new(crate::backbone::SearchBackbone::new(
        components,
        &lazy_cache,
    ));
    let mut stream = TcpStream::connect(addr).expect("Failed to connect to controller");
    println!("Connected to controller at {}", addr);
    let mut total_branches = 0;
    let mut total_abundance_pruned = 0;
    let mut total_raycast_pruned = 0;
    let mut total_math_interruptions = 0;
    let mut explored_ranges = Vec::new();

    loop {
        // Request work
        let req = Message::RequestWork;
        let req_bytes = serde_json::to_vec(&req).unwrap();
        stream.write_all(&req_bytes).unwrap();

        let mut buf = vec![0; 1024 * 1024]; // 1MB buffer
        let n = stream.read(&mut buf).unwrap();
        if n == 0 {
            break;
        }

        let msg: Message = serde_json::from_slice(&buf[..n]).unwrap();
        match msg {
            Message::WorkUnit(Some(range_bound)) => {
                let mask_len = if !components.is_empty() {
                    backbone.compatibility_matrix[0].len()
                } else {
                    1
                };
                let mut prefix = Prefix {
                    n_l: Uint::from_u32(1),
                    s_l: Uint::from_u32(1),
                    last_idx: 0,
                    factors: vec![],
                    sigma_factors: vec![],
                    sigma_factors_u64: vec![],
                    active_mask: vec![u64::MAX; mask_len],
                };

                let count = AtomicUsize::new(0);
                let pruned_count = AtomicUsize::new(0);
                let abundance_pruned = AtomicUsize::new(0);
                let completed_weight_scaled = AtomicUsize::new(0);
                let math_interruptions = AtomicUsize::new(0);

                let (tx, rx) = crossbeam_channel::unbounded();
                let mut stream_clone = stream.try_clone().unwrap();
                let reporter_thread = std::thread::spawn(move || {
                    while let Ok(msg) = rx.recv() {
                        let rep = Message::Event(msg);
                        let rep_bytes = serde_json::to_vec(&rep).unwrap();
                        let _ = stream_clone.write_all(&rep_bytes);
                    }
                });

                let heartbeat_interval = std::env::var("UALBF_HEARTBEAT_INTERVAL_SEC")
                    .ok()
                    .and_then(|v| v.parse().ok())
                    .unwrap_or(5);

                let (hb_tx, hb_rx) = crossbeam_channel::unbounded::<()>();
                let mut hb_stream = stream.try_clone().unwrap();
                let hb_thread = std::thread::spawn(move || {
                    let interval = std::time::Duration::from_secs(heartbeat_interval);
                    loop {
                        match hb_rx.recv_timeout(interval) {
                            Ok(_) | Err(crossbeam_channel::RecvTimeoutError::Disconnected) => break,
                            Err(crossbeam_channel::RecvTimeoutError::Timeout) => {
                                let rep = Message::Heartbeat;
                                if let Ok(rep_bytes) = serde_json::to_vec(&rep) {
                                    if hb_stream.write_all(&rep_bytes).is_err() {
                                        break;
                                    }
                                }
                            }
                        }
                    }
                });

                let start_bound = if range_bound.start_bound.is_empty() {
                    None
                } else {
                    Some(range_bound.start_bound.as_slice())
                };
                let end_bound = if range_bound.end_bound.is_empty() {
                    None
                } else {
                    Some(range_bound.end_bound.as_slice())
                };

                crate::dfs_tree::explore_prefix(
                    start_bound,
                    end_bound,
                    &mut prefix,
                    components,
                    stop_threshold,
                    target_min,
                    target_bound,
                    illegal_valuations,
                    suffix_abundance,
                    &count,
                    &pruned_count,
                    &abundance_pruned,
                    &completed_weight_scaled,
                    &math_interruptions,
                    total_weight_scaled,
                    &active_primes,
                    0,
                    sigma_cache,
                    Some(&tx),
                    max_idx_3,
                    max_idx_5,
                    &lazy_cache,
                    &backbone,
                    None,
                );
                drop(tx);
                let _ = reporter_thread.join();

                drop(hb_tx);
                let _ = hb_thread.join();

                // Report back
                total_branches += count.load(Ordering::Relaxed);
                total_abundance_pruned += abundance_pruned.load(Ordering::Relaxed);
                total_raycast_pruned += pruned_count.load(Ordering::Relaxed);
                total_math_interruptions += math_interruptions.load(Ordering::Relaxed);
                explored_ranges.push(range_bound.clone());
                let rep = Message::Event(crate::events::SearchEvent::DFSComplete {
                    total_branches: count.into_inner(),
                    ap: abundance_pruned.into_inner(),
                    rp: pruned_count.into_inner(),
                });
                let rep_bytes = serde_json::to_vec(&rep).unwrap();
                stream.write_all(&rep_bytes).unwrap();
            }
            Message::WorkUnit(None) => {
                println!("No more work. Worker exiting.");
                break;
            }
            _ => {}
        }
    }
    (
        crate::dfs_tree::DfsTelemetry {
            total_branches,
            abundance_pruned: total_abundance_pruned,
            raycast_pruned: total_raycast_pruned,
            search_space_density: 0.0,
            math_interruptions: total_math_interruptions,
        },
        explored_ranges,
    )
}
