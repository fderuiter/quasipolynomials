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
    WorkUnit(Option<SerializedPrefix>),
    Event(crate::events::SearchEvent),
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

pub fn run_controller(addr: &str, units: Vec<Prefix>) {
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

    for stream in listener.incoming() {
        if let Ok(mut stream) = stream {
            let work_queue = Arc::clone(&work_queue);
            let completed = Arc::clone(&completed);
            
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
                                        // Save checkpoint
                                        if let Ok(json) = serde_json::to_string(&*queue) {
                                            let _ = std::fs::write("checkpoint.json", json);
                                        }
                                        let reply = Message::WorkUnit(work);
                                        let reply_bytes = serde_json::to_vec(&reply).unwrap();
                                        if stream.write_all(&reply_bytes).is_err() { break; }
                                    }
                                    Message::Event(event) => {
                                        println!("{}", serde_json::to_string(&event).unwrap());
                                        if let crate::events::SearchEvent::DFSComplete { .. } = event {
                                            let c = completed.fetch_add(1, Ordering::Relaxed) + 1;
                                            if c >= total_units {
                                                println!("{}", serde_json::to_string(&crate::events::SearchEvent::Phase { phase: 4, name: "All work units completed".to_string() }).unwrap());
                                                std::process::exit(0);
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                        Err(_) => break,
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
                        let rep = Message::Event(msg);
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
                    None,
                );
                drop(tx);
                let _ = reporter_thread.join();

                // Report back
                let rep = Message::Event(crate::events::SearchEvent::DFSComplete { total_branches: count.into_inner(), ap: abundance_pruned.into_inner(), rp: pruned_count.into_inner() });
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
