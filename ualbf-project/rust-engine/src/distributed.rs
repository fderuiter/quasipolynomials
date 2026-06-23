use crate::schema_generated::{Prefix, SerializedPrefix};
use crate::types::{UintExt, IntExt};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;
use std::io::{Read, Write};
use crate::types::{Uint, Int, PrimePower};
use crate::math_utils::SigmaCache;
use serde::{Serialize, Deserialize};



#[derive(Serialize, Deserialize, Debug)]
pub enum Message {
    RequestWork,
    WorkUnit(Option<SerializedPrefix>), // None means no more work
    ReportResult { branches: usize, pruned: usize, abundance_pruned: usize },
    ReportCandidate(String),
}

pub fn generate_work_units(
    components: &[PrimePower],
    target_bound: &Uint,
    depth_limit: usize,
) -> Vec<Prefix> {
    let lazy_cache: std::sync::Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>> = std::sync::Arc::new(std::iter::repeat_with(std::sync::OnceLock::new).take(components.len()).collect());
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
        expand_work_units(&mut curr, components, target_bound, depth_limit, 0, &mut units, &backbone);
    }
    units
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

    let saved_last_idx = curr.last_idx;
    let saved_n_l = curr.n_l;
    let saved_s_l = curr.s_l;

    for i in saved_last_idx..components.len() {
        let comp = &components[i];
        if !curr.factors.contains(&comp.p) {
            if let (Some(next_n_l), Some(next_s_l)) = (
                saved_n_l.checked_mul(comp.val),
                saved_s_l.checked_mul(comp.sigma),
            ) {
                if next_n_l <= *target_bound {
                    let sigma_start_len = curr.sigma_factors.len();

                    curr.n_l = next_n_l;
                    curr.s_l = next_s_l;
                    curr.last_idx = i + 1;
                    curr.factors.push(comp.p);
                    curr.sigma_factors.extend_from_slice(&comp.sigma_factors);
                                        
                    let saved_active_mask = curr.active_mask.clone();
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
                    curr.active_mask = saved_active_mask;

                    curr.n_l = saved_n_l;
                    curr.s_l = saved_s_l;
                    curr.last_idx = saved_last_idx;
                    curr.factors.pop();
                    curr.sigma_factors.truncate(sigma_start_len);
                                    }
            }
        }
    }
}

use std::sync::atomic::{AtomicUsize, Ordering};

pub fn run_controller(addr: &str, units: Vec<Prefix>, total_weight_scaled: usize) -> crate::dfs_tree::DfsTelemetry {
    let listener = TcpListener::bind(addr).unwrap();
    println!("Controller listening on {}", addr);
    
    // Load from checkpoint if exists
    let initial_units = if let Ok(content) = std::fs::read_to_string("checkpoint.json") {
        println!("Resuming from checkpoint.json");
        serde_json::from_str::<Vec<SerializedPrefix>>(&content).unwrap_or_else(|_| {
            units.into_iter().map(|p| SerializedPrefix::from_prefix(&p)).collect()
        })
    } else {
        units.into_iter().map(|p| SerializedPrefix::from_prefix(&p)).collect::<Vec<_>>()
    };

    let work_queue = Arc::new(Mutex::new(initial_units));
    let total_units = work_queue.lock().unwrap().len();
    println!("Partitioned search space into {} discrete pending work units.", total_units);

    let completed = Arc::new(AtomicUsize::new(0));
    let total_branches = Arc::new(AtomicUsize::new(0));
    let total_abundance_pruned = Arc::new(AtomicUsize::new(0));

    // Create a channel to signal completion
    let (tx, rx) = std::sync::mpsc::channel();
    
    // Check if we start already completed (e.g. from checkpoint)
    if total_units == 0 {
        return crate::dfs_tree::DfsTelemetry {
            total_branches: 0,
            abundance_pruned: 0,
            search_space_density: 0.0,
        };
    }

    listener.set_nonblocking(true).unwrap();

    let mut threads = Vec::new();

    loop {
        if completed.load(Ordering::Relaxed) >= total_units {
            break;
        }

        match listener.accept() {
            Ok((mut stream, _)) => {
                let work_queue = Arc::clone(&work_queue);
                let completed = Arc::clone(&completed);
                let total_branches = Arc::clone(&total_branches);
                let total_abundance_pruned = Arc::clone(&total_abundance_pruned);
                let tx = tx.clone();
                
                let t = thread::spawn(move || {
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
                                            // Save checkpoint
                                            if let Ok(json) = serde_json::to_string(&*queue) {
                                                let _ = std::fs::write("checkpoint.json", json);
                                            }
                                            let reply = Message::WorkUnit(work);
                                            let reply_bytes = serde_json::to_vec(&reply).unwrap();
                                            if stream.write_all(&reply_bytes).is_err() { break; }
                                        }
                                        Message::ReportResult { branches, pruned, abundance_pruned } => {
                                            total_branches.fetch_add(branches, Ordering::Relaxed);
                                            total_abundance_pruned.fetch_add(abundance_pruned, Ordering::Relaxed);
                                            let c = completed.fetch_add(1, Ordering::Relaxed) + 1;
                                            println!("Worker completed unit {}/{}. Branches: {}, Pruned: {}, Abundance pruned: {}", c, total_units, branches, pruned, abundance_pruned);
                                            if c >= total_units {
                                                println!("All work units completed.");
                                                let _ = tx.send(());
                                            }
                                        }
                                        Message::ReportCandidate(c) => {
                                            println!(">>> CANDIDATE REPORTED BY WORKER: {} <<<", c);
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                                std::thread::sleep(std::time::Duration::from_millis(10));
                            }
                            Err(_) => break,
                        }
                    }
                });
                threads.push(t);
            }
            Err(ref e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                // Check if workers finished
                if rx.try_recv().is_ok() {
                    break;
                }
                std::thread::sleep(std::time::Duration::from_millis(100));
            }
            Err(e) => {
                eprintln!("Listener accept error: {}", e);
                break;
            }
        }
    }

    let final_branches = total_branches.load(Ordering::Relaxed);
    let final_abundance_pruned = total_abundance_pruned.load(Ordering::Relaxed);
    let density = (final_branches as f64) / (total_weight_scaled as f64 + 1.0);

    crate::dfs_tree::DfsTelemetry {
        total_branches: final_branches,
        abundance_pruned: final_abundance_pruned,
        search_space_density: density,
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
) {
    use std::sync::atomic::AtomicU64;
    
    let active_primes: Arc<[AtomicU64; crate::dfs_tree::ACTIVE_PRIME_SLOTS]> = Arc::new(std::array::from_fn(|_| AtomicU64::new(0)));
    let lazy_cache: Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>> = Arc::new(std::iter::repeat_with(std::sync::OnceLock::new).take(components.len()).collect());
    let backbone = Arc::new(crate::backbone::SearchBackbone::new(components, &lazy_cache));
    let mut stream = TcpStream::connect(addr).expect("Failed to connect to controller");
    println!("Connected to controller at {}", addr);

    loop {
        // Request work
        let req = Message::RequestWork;
        let req_bytes = serde_json::to_vec(&req).unwrap();
        stream.write_all(&req_bytes).unwrap();

        let mut buf = vec![0; 1024 * 1024]; // 1MB buffer
        let n = stream.read(&mut buf).unwrap();
        if n == 0 { break; }

        let msg: Message = serde_json::from_slice(&buf[..n]).unwrap();
        match msg {
            Message::WorkUnit(Some(serialized_prefix)) => {
                let mut prefix = serialized_prefix.to_prefix();
                let count = AtomicUsize::new(0);
                let pruned_count = AtomicUsize::new(0);
                let abundance_pruned = AtomicUsize::new(0);
                let completed_weight_scaled = AtomicUsize::new(0);

                let (tx, rx) = crossbeam_channel::unbounded();
                let mut stream_clone = stream.try_clone().unwrap();
                let reporter_thread = std::thread::spawn(move || {
                    while let Ok(msg) = rx.recv() {
                        let rep = Message::ReportCandidate(msg);
                        let rep_bytes = serde_json::to_vec(&rep).unwrap();
                        let _ = stream_clone.write_all(&rep_bytes);
                    }
                });

                crate::dfs_tree::explore_prefix(
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
                    total_weight_scaled,
                    &active_primes,
                    0,
                    sigma_cache,
                    Some(&tx),
                    max_idx_3,
                    max_idx_5,
                    &lazy_cache,
                    &backbone,
                );
                drop(tx);
                let _ = reporter_thread.join();

                // Report back
                let rep = Message::ReportResult {
                    branches: count.into_inner(),
                    pruned: pruned_count.into_inner(),
                    abundance_pruned: abundance_pruned.into_inner(),
                };
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
}
