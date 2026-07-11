use crate::schema_generated::{Prefix, SerializedPrefix};
use crate::types::{UintExt, IntExt};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex};
use std::thread;
use std::io::{Read, Write};
use crate::types::{Uint, Int, PrimePower};
use crate::math_utils::SigmaCache;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct RangeWorkUnit {
    pub start_bound: Vec<u64>,
    pub end_bound: Vec<u64>,
}

#[derive(Serialize, Deserialize, Debug)]
pub enum Message {
    RequestWork(String),
    WorkUnit(Option<RangeWorkUnit>),
    Event(crate::events::SearchEvent),
    Heartbeat,
    GetPeers,
    Peers(Vec<String>),
    RegisterStolenTask(RangeWorkUnit),
}

pub struct StealState {
    pub steal_requested: std::sync::atomic::AtomicBool,
    pub response: std::sync::Mutex<Option<Vec<u8>>>,
    pub cv: std::sync::Condvar,
}

#[derive(Debug)]
pub struct StolenTask {
    pub start_bound: Vec<u64>,
    pub end_bound: Vec<u64>,
    pub prefix: crate::schema_generated::Prefix,
}

impl StolenTask {
    pub fn serialize_bin(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(1024);
        
        buf.extend_from_slice(&(self.start_bound.len() as u32).to_le_bytes());
        for &x in &self.start_bound { buf.extend_from_slice(&x.to_le_bytes()); }
        
        buf.extend_from_slice(&(self.end_bound.len() as u32).to_le_bytes());
        for &x in &self.end_bound { buf.extend_from_slice(&x.to_le_bytes()); }
        
        buf.extend_from_slice(&self.prefix.n_l.to_le_bytes());
        buf.extend_from_slice(&self.prefix.s_l.to_le_bytes());
        buf.extend_from_slice(&(self.prefix.last_idx as u32).to_le_bytes());
        
        buf.extend_from_slice(&(self.prefix.factors.len() as u32).to_le_bytes());
        for &x in &self.prefix.factors { buf.extend_from_slice(&x.to_le_bytes()); }
        
        buf.extend_from_slice(&(self.prefix.sigma_factors.len() as u32).to_le_bytes());
        for x in &self.prefix.sigma_factors { buf.extend_from_slice(&x.to_le_bytes()); }
        
        buf.extend_from_slice(&(self.prefix.sigma_factors_u64.len() as u32).to_le_bytes());
        for &x in &self.prefix.sigma_factors_u64 { buf.extend_from_slice(&x.to_le_bytes()); }
        
        buf.extend_from_slice(&(self.prefix.active_mask.len() as u32).to_le_bytes());
        for &x in &self.prefix.active_mask { buf.extend_from_slice(&x.to_le_bytes()); }
        
        buf
    }

    pub fn deserialize_bin(buf: &[u8]) -> Option<Self> {
        let mut idx = 0;
        let read_u32 = |idx: &mut usize| -> Option<u32> {
            if *idx + 4 > buf.len() { return None; }
            let v = u32::from_le_bytes(buf[*idx..*idx+4].try_into().ok()?);
            *idx += 4;
            Some(v)
        };
        let read_u64 = |idx: &mut usize| -> Option<u64> {
            if *idx + 8 > buf.len() { return None; }
            let v = u64::from_le_bytes(buf[*idx..*idx+8].try_into().ok()?);
            *idx += 8;
            Some(v)
        };
        let read_uint = |idx: &mut usize| -> Option<Uint> {
            if *idx + 64 > buf.len() { return None; }
            let v = Uint::from_le_bytes(buf[*idx..*idx+64].try_into().ok()?);
            *idx += 64;
            Some(v)
        };

        let start_len = read_u32(&mut idx)?;
        let mut start_bound = Vec::with_capacity(start_len as usize);
        for _ in 0..start_len { start_bound.push(read_u64(&mut idx)?); }

        let end_len = read_u32(&mut idx)?;
        let mut end_bound = Vec::with_capacity(end_len as usize);
        for _ in 0..end_len { end_bound.push(read_u64(&mut idx)?); }

        let n_l = read_uint(&mut idx)?;
        let s_l = read_uint(&mut idx)?;
        let last_idx = read_u32(&mut idx)? as usize;

        let factors_len = read_u32(&mut idx)?;
        let mut factors = Vec::with_capacity(factors_len as usize);
        for _ in 0..factors_len { factors.push(read_u64(&mut idx)?); }

        let sf_len = read_u32(&mut idx)?;
        let mut sigma_factors = Vec::with_capacity(sf_len as usize);
        for _ in 0..sf_len { sigma_factors.push(read_uint(&mut idx)?); }

        let sfu_len = read_u32(&mut idx)?;
        let mut sigma_factors_u64 = Vec::with_capacity(sfu_len as usize);
        for _ in 0..sfu_len { sigma_factors_u64.push(read_u64(&mut idx)?); }

        let mask_len = read_u32(&mut idx)?;
        let mut active_mask = Vec::with_capacity(mask_len as usize);
        for _ in 0..mask_len { active_mask.push(read_u64(&mut idx)?); }

        Some(Self {
            start_bound,
            end_bound,
            prefix: crate::schema_generated::Prefix {
                n_l, s_l, last_idx, factors, sigma_factors, sigma_factors_u64, active_mask
            }
        })
    }
}

pub fn generate_work_units(
    components: &[PrimePower],
    target_bound: &Uint,
    depth_limit: usize,
) -> Vec<RangeWorkUnit> {
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
    
    let mut paths: Vec<Vec<u64>> = units.into_iter().map(|u| u.factors).collect();
    // Sort paths lexicographically just in case
    paths.sort();
    
    let mut ranges = Vec::new();
    if paths.is_empty() {
        ranges.push(RangeWorkUnit { start_bound: vec![], end_bound: vec![] });
    } else {
        ranges.push(RangeWorkUnit { start_bound: vec![], end_bound: paths[0].clone() });
        for i in 0..paths.len() - 1 {
            ranges.push(RangeWorkUnit { start_bound: paths[i].clone(), end_bound: paths[i+1].clone() });
        }
        ranges.push(RangeWorkUnit { start_bound: paths.last().unwrap().clone(), end_bound: vec![] });
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
use std::time::{Instant, Duration};

struct ActiveWorkerState {
    active_task: RangeWorkUnit,
    last_heartbeat: Instant,
    p2p_addr: String,
}

pub fn run_controller(addr: &str, units: Vec<RangeWorkUnit>) {
    let listener = TcpListener::bind(addr).unwrap();
    
    let heartbeat_timeout = std::env::var("UALBF_HEARTBEAT_TIMEOUT_SEC")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(15);
    
    let active_workers: Arc<Mutex<HashMap<usize, ActiveWorkerState>>> = Arc::new(Mutex::new(HashMap::new()));
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
    let total_units = Arc::new(AtomicUsize::new(work_queue.lock().unwrap().len()));
    println!("Partitioned search space into {} discrete pending work units.", total_units.load(Ordering::Relaxed));

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
            let total_units_ref = Arc::clone(&total_units);
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
                                    Message::RequestWork(p2p_addr) => {
                                        let mut queue = work_queue.lock().unwrap();
                                        let work = queue.pop();
                                        if let Some(ref w) = work {
                                            let mut workers = active_workers.lock().unwrap();
                                            workers.insert(worker_id, ActiveWorkerState {
                                                active_task: w.clone(),
                                                last_heartbeat: Instant::now(),
                                                p2p_addr,
                                            });
                                        }
                                        // Save checkpoint
                                        if let Ok(json) = serde_json::to_string(&*queue) {
                                            let _ = std::fs::write("checkpoint.json", json);
                                        }
                                        let reply = Message::WorkUnit(work);
                                        let reply_bytes = serde_json::to_vec(&reply).unwrap();
                                        if stream.write_all(&reply_bytes).is_err() { break; }
                                    }
                                    Message::Heartbeat => {
                                        let mut workers = active_workers.lock().unwrap();
                                        if let Some(state) = workers.get_mut(&worker_id) {
                                            state.last_heartbeat = Instant::now();
                                        }
                                    }
                                    Message::GetPeers => {
                                        let workers = active_workers.lock().unwrap();
                                        let peers: Vec<String> = workers.iter().filter(|(&id, _)| id != worker_id).map(|(_, state)| state.p2p_addr.clone()).collect();
                                        let reply = Message::Peers(peers);
                                        let reply_bytes = serde_json::to_vec(&reply).unwrap();
                                        if stream.write_all(&reply_bytes).is_err() { break; }
                                    }
                                    Message::Peers(_) => {},
                                    Message::RegisterStolenTask(w) => {
                                        total_units_ref.fetch_add(1, Ordering::Relaxed);
                                        let mut workers = active_workers.lock().unwrap();
                                        // p2p_addr isn't strictly necessary here since it's just for peer discovery and this worker is active.
                                        workers.insert(worker_id, ActiveWorkerState {
                                            active_task: w,
                                            last_heartbeat: Instant::now(),
                                            p2p_addr: String::new(),
                                        });
                                    }
                                    Message::WorkUnit(_) => {},
                                    Message::Event(event) => {
                                        println!("{}", serde_json::to_string(&event).unwrap());
                                        if let crate::events::SearchEvent::DFSComplete { .. } = event {
                                            let mut queue = work_queue.lock().unwrap();
                                            let mut workers = active_workers.lock().unwrap();
                                            if workers.remove(&worker_id).is_some() {
                                                let c = completed.fetch_add(1, Ordering::Relaxed) + 1;
                                                if c >= total_units_ref.load(Ordering::Relaxed) {
                                                    println!("{}", serde_json::to_string(&crate::events::SearchEvent::Phase { phase: 4, name: "All work units completed".to_string() }).unwrap());
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
                    println!("Worker {} disconnected unexpectedly. Recovering task.", worker_id);
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
    use std::sync::atomic::{AtomicU64, AtomicBool};
    
    let active_primes: Arc<[AtomicU64]> = std::iter::repeat_with(|| AtomicU64::new(0)).take(crate::profile::get_profile().active_prime_slots).collect();
    let lazy_cache: Arc<Vec<std::sync::OnceLock<Result<Vec<Uint>, ()>>>> = Arc::new(std::iter::repeat_with(std::sync::OnceLock::new).take(components.len()).collect());
    let backbone = Arc::new(crate::backbone::SearchBackbone::new(components, &lazy_cache));
    let mut stream = TcpStream::connect(addr).expect("Failed to connect to controller");
    println!("Connected to controller at {}", addr);
    
    let p2p_listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    p2p_listener.set_nonblocking(true).unwrap();
    let p2p_port = p2p_listener.local_addr().unwrap().port();
    let p2p_addr_str = format!("127.0.0.1:{}", p2p_port);
    
    let steal_state = Arc::new(StealState {
        steal_requested: AtomicBool::new(false),
        response: std::sync::Mutex::new(None),
        cv: std::sync::Condvar::new(),
    });
    
    let steal_state_p2p = Arc::clone(&steal_state);
    let (p2p_shutdown_tx, p2p_shutdown_rx) = crossbeam_channel::unbounded();
    std::thread::spawn(move || {
        loop {
            if p2p_shutdown_rx.try_recv().is_ok() { break; }
            if let Ok((mut stream, _)) = p2p_listener.accept() {
                let mut buf = [0; 5];
                if stream.read_exact(&mut buf).is_ok() && &buf == b"STEAL" {
                    let mut resp_lock = steal_state_p2p.response.lock().unwrap();
                    *resp_lock = None;
                    steal_state_p2p.steal_requested.store(true, Ordering::SeqCst);
                    
                    let (new_lock, res) = steal_state_p2p.cv.wait_timeout(resp_lock, Duration::from_millis(50)).unwrap();
                    resp_lock = new_lock;
                    
                    if let Some(data) = resp_lock.take() {
                        let _ = stream.write_all(&data);
                    }
                    steal_state_p2p.steal_requested.store(false, Ordering::SeqCst);
                }
            } else {
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    });

    let mut total_branches = 0;
    let mut total_abundance_pruned = 0;
    let mut total_raycast_pruned = 0;
    let mut total_math_interruptions = 0;
    let mut explored_ranges = Vec::new();

    loop {
        // Request work
        let req = Message::RequestWork(p2p_addr_str.clone());
        let req_bytes = serde_json::to_vec(&req).unwrap();
        stream.write_all(&req_bytes).unwrap();

        let mut buf = vec![0; 1024 * 1024]; // 1MB buffer
        let n = stream.read(&mut buf).unwrap();
        if n == 0 { break; }

        let msg: Message = serde_json::from_slice(&buf[..n]).unwrap();
        let range_bound = match msg {
            Message::WorkUnit(Some(rb)) => Some(rb),
            Message::WorkUnit(None) => {
                // Request peers
                let req = Message::GetPeers;
                let req_bytes = serde_json::to_vec(&req).unwrap();
                stream.write_all(&req_bytes).unwrap();
                
                let n = stream.read(&mut buf).unwrap();
                if n == 0 { break; }
                if let Ok(Message::Peers(peers)) = serde_json::from_slice(&buf[..n]) {
                    let mut stolen = None;
                    for peer in peers {
                        if let Ok(mut peer_stream) = TcpStream::connect(&peer) {
                            if peer_stream.write_all(b"STEAL").is_ok() {
                                let mut peer_buf = Vec::new();
                                peer_stream.set_read_timeout(Some(Duration::from_millis(100))).unwrap();
                                if peer_stream.read_to_end(&mut peer_buf).is_ok() && !peer_buf.is_empty() {
                                    if let Some(task) = StolenTask::deserialize_bin(&peer_buf) {
                                        let stolen_task = RangeWorkUnit { start_bound: task.start_bound, end_bound: task.end_bound };
                                        
                                        // Register stolen task with controller
                                        let req = Message::RegisterStolenTask(stolen_task.clone());
                                        let req_bytes = serde_json::to_vec(&req).unwrap();
                                        stream.write_all(&req_bytes).unwrap();
                                        
                                        stolen = Some(stolen_task);
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    stolen
                } else {
                    None
                }
            }
            _ => None,
        };

        if let Some(range_bound) = range_bound {
            let mask_len = if !components.is_empty() { backbone.compatibility_matrix[0].len() } else { 1 };
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

            let start_bound = if range_bound.start_bound.is_empty() { None } else { Some(range_bound.start_bound.clone()) };
            let end_bound = if range_bound.end_bound.is_empty() { None } else { Some(range_bound.end_bound.clone()) };

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
                Some(&steal_state),
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
            let rep = Message::Event(crate::events::SearchEvent::DFSComplete { total_branches: count.into_inner(), ap: abundance_pruned.into_inner(), rp: pruned_count.into_inner() });
            let rep_bytes = serde_json::to_vec(&rep).unwrap();
            stream.write_all(&rep_bytes).unwrap();
        } else {
            println!("No more work globally. Worker exiting.");
            break;
        }
    }
    let _ = p2p_shutdown_tx.send(());
    (crate::dfs_tree::DfsTelemetry { total_branches, abundance_pruned: total_abundance_pruned, raycast_pruned: total_raycast_pruned, search_space_density: 0.0, math_interruptions: total_math_interruptions }, explored_ranges)
}
