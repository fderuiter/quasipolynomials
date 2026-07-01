use serde::{Deserialize, Serialize};
use std::fs;
use std::sync::OnceLock;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct PerformanceProfile {
    pub pollard_rho_batch_size: u32,
    pub active_prime_slots: usize,
    pub engine_telemetry_interval_ms: u64,
    pub dashboard_telemetry_interval_ms: u64,
}

impl Default for PerformanceProfile {
    fn default() -> Self {
        Self {
            pollard_rho_batch_size: 128,
            active_prime_slots: 64,
            engine_telemetry_interval_ms: 1000,
            dashboard_telemetry_interval_ms: 250,
        }
    }
}

pub fn load_profile() -> PerformanceProfile {
    match fs::read_to_string("profile.json") {
        Ok(content) => match serde_json::from_str(&content) {
            Ok(profile) => profile,
            Err(_) => PerformanceProfile::default(),
        },
        Err(_) => PerformanceProfile::default(),
    }
}

pub fn get_profile() -> &'static PerformanceProfile {
    static PROFILE: OnceLock<PerformanceProfile> = OnceLock::new();
    PROFILE.get_or_init(|| load_profile())
}
