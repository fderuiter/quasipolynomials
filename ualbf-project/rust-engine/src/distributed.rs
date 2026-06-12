use crate::types::{UintExt, IntExt};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;
use std::io::{Read, Write};
use crate::types::{Prefix, Uint, Int, PrimePower};
use crate::math_utils::SigmaCache;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct SerializedPrefix {
    pub n_l_hex: String,
    pub s_l_hex: String,
    pub last_idx: usize,
    pub factors: Vec<u64>,
    pub sigma_factors: Vec<String>,
    pub active_mask: Vec<u64>,
}

impl SerializedPrefix {
    pub fn from_prefix(p: &Prefix) -> Self {
        Self {
            n_l_hex: format!("{:x}", p.n_l),
            s_l_hex: format!("{:x}", p.s_l),
            last_idx: p.last_idx,
            factors: p.factors.clone(),
            sigma_factors: p.sigma_factors.iter().map(|sf| format!("{:x}", sf)).collect(),
            active_mask: p.active_mask.clone(),
        }
    }

    pub fn to_prefix(&self) -> Prefix {
        let n_l = Uint::from_str_radix(&self.n_l_hex, 16).unwrap_or_else(|_| Uint::zero());
        let s_l = Uint::from_str_radix(&self.s_l_hex, 16).unwrap_or_else(|_| Uint::zero());
        
        let sigma_factors: Vec<Uint> = self.sigma_factors.iter().map(|s| {
            Uint::from_str_radix(s, 16).unwrap_or_else(|_| Uint::zero())
        }).collect();
        let mut sigma_factors_u64 = Vec::new();
        for sf in &sigma_factors {
            if *sf <= Uint::from_u128((u64::MAX) as u128) {
                sigma_factors_u64.push(sf.as_u64());
            }
        }
        Prefix {
            n_l,
            s_l,
            last_idx: self.last_idx,
            factors: self.factors.clone(),
            sigma_factors,
            sigma_factors_u64,
            active_mask: self.active_mask.clone(),
        }
    }
}

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
                                    Message::ReportResult { branches, pruned, abundance_pruned } => {
                                        let c = completed.fetch_add(1, Ordering::Relaxed) + 1;
                                        println!("Worker completed unit {}/{}. Branches: {}, Pruned: {}, Abundance pruned: {}", c, total_units, branches, pruned, abundance_pruned);
                                        if c >= total_units {
                                            println!("All work units completed.");
                                            std::process::exit(0);
                                        }
                                    }
                                    Message::ReportCandidate(c) => {
                                        println!(">>> CANDIDATE REPORTED BY WORKER: {} <<<", c);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Prefix, Uint, UintExt};
    use serde_json;

    #[test]
    fn test_variable_length_serialization_roundtrip() {
        // Create a prefix with > 256-bit values to verify it doesn't truncate.
        // U512 max value is 2^512 - 1. We'll set something very large.
        let large_hex = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"; // 128 hex chars = 512 bits
        let val = Uint::from_str_radix(large_hex, 16).unwrap();
        
        let p = Prefix {
            n_l: val,
            s_l: val,
            last_idx: 5,
            factors: vec![2, 3, 5],
            sigma_factors: vec![val],
            sigma_factors_u64: vec![],
            active_mask: vec![0, 1, 2],
        };

        let serialized = SerializedPrefix::from_prefix(&p);
        let json = serde_json::to_string(&serialized).unwrap();
        
        // Ensure hex encoding is used in JSON
        assert!(json.contains("ffffffffffffffffffffffffffffffff"));

        // Deserialize back
        let deserialized: SerializedPrefix = serde_json::from_str(&json).unwrap();
        let restored = deserialized.to_prefix();

        assert_eq!(p.n_l, restored.n_l);
        assert_eq!(p.s_l, restored.s_l);
        assert_eq!(p.last_idx, restored.last_idx);
        assert_eq!(p.factors, restored.factors);
        assert_eq!(p.sigma_factors, restored.sigma_factors);
    }
}

#[cfg(test)]
mod integration_tests {
    use super::*;
    use crate::types::{Prefix, Uint, UintExt};
    use std::thread;
    use std::time::Duration;
    use std::net::TcpStream;
    use std::io::{Write, Read};

    #[test]
    fn test_mock_search_checkpoint_resume() {
        let _ = std::fs::remove_file("checkpoint.json");

        let val = Uint::from_u64(999);
        let p = Prefix {
            n_l: val,
            s_l: val,
            last_idx: 5,
            factors: vec![2, 3, 5],
            sigma_factors: vec![val],
            sigma_factors_u64: vec![],
            active_mask: vec![0, 1, 2],
        };
        
        let p2 = Prefix {
            n_l: Uint::from_u64(1000),
            s_l: Uint::from_u64(1000),
            last_idx: 5,
            factors: vec![7],
            sigma_factors: vec![],
            sigma_factors_u64: vec![],
            active_mask: vec![],
        };
        
        // Spawn controller with 2 units so it doesn't exit(0) immediately
        let units = vec![p.clone(), p2.clone()];
        thread::spawn(move || {
            run_controller("127.0.0.1:8282", units);
        });

        thread::sleep(Duration::from_millis(100));

        // Worker connects and requests work
        let mut stream = TcpStream::connect("127.0.0.1:8282").expect("Failed to connect");
        let req = Message::RequestWork;
        stream.write_all(&serde_json::to_vec(&req).unwrap()).unwrap();
        
        let mut buf = vec![0; 1024];
        let n = stream.read(&mut buf).unwrap();
        let msg: Message = serde_json::from_slice(&buf[..n]).unwrap();
        if let Message::WorkUnit(Some(work)) = msg {
            // Because queue.pop() takes the last element, it will return p2
            assert_eq!(work.n_l_hex, "3e8"); // 1000 in hex
        } else {
            panic!("Expected WorkUnit");
        }

        // Wait to make sure checkpoint was saved
        thread::sleep(Duration::from_millis(100));
        let content = std::fs::read_to_string("checkpoint.json").expect("checkpoint.json not found");
        let checkpoint: Vec<SerializedPrefix> = serde_json::from_str(&content).unwrap();
        // Since we had 2 elements and popped 1, there should be 1 left (p)
        assert_eq!(checkpoint.len(), 1);
        assert_eq!(checkpoint[0].n_l_hex, "3e7");

        // Spawn another controller on a different port to test resume from checkpoint.json
        thread::spawn(move || {
            run_controller("127.0.0.1:8283", vec![]); // Pass empty units, it should load from checkpoint
        });

        thread::sleep(Duration::from_millis(100));
        let mut stream2 = TcpStream::connect("127.0.0.1:8283").expect("Failed to connect");
        stream2.write_all(&serde_json::to_vec(&Message::RequestWork).unwrap()).unwrap();
        let n = stream2.read(&mut buf).unwrap();
        let msg2: Message = serde_json::from_slice(&buf[..n]).unwrap();
        if let Message::WorkUnit(Some(work)) = msg2 {
            assert_eq!(work.n_l_hex, "3e7"); // resumed successfully from checkpoint.json!
        } else {
            panic!("Expected WorkUnit from resume");
        }
        
        let _ = std::fs::remove_file("checkpoint.json");
    }
}
