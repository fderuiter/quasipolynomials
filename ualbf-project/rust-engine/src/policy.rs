use crate::manifest_constants::*;
use std::env;

#[derive(Debug, Clone)]
pub struct EngineConfig {
    pub target_min_log10: u32,
    pub target_max_log10: u32,
    pub sieve_limit: usize,
    pub max_exponent: u32,
    pub prefix_stop: u64,
}

pub fn get_safe_config() -> EngineConfig {
    let target_min_log10 = match env::var("UALBF_TARGET_MIN_LOG10") {
        Ok(v) => v.parse().expect("FATAL: UALBF_TARGET_MIN_LOG10 must be a valid u32"),
        Err(_) => TARGET_MIN_LOG10,
    };
    
    let target_max_log10 = match env::var("UALBF_TARGET_MAX_LOG10") {
        Ok(v) => v.parse().expect("FATAL: UALBF_TARGET_MAX_LOG10 must be a valid u32"),
        Err(_) => TARGET_MAX_LOG10,
    };

    let sieve_limit = match env::var("UALBF_SIEVE_LIMIT") {
        Ok(v) => v.parse().expect("FATAL: UALBF_SIEVE_LIMIT must be a valid usize"),
        Err(_) => SIEVE_LIMIT,
    };

    let max_exponent = match env::var("UALBF_MAX_EXPONENT") {
        Ok(v) => v.parse().expect("FATAL: UALBF_MAX_EXPONENT must be a valid u32"),
        Err(_) => MAX_EXPONENT,
    };

    let prefix_stop = match env::var("UALBF_PREFIX_STOP_THRESHOLD") {
        Ok(v) => v.parse().expect("FATAL: UALBF_PREFIX_STOP_THRESHOLD must be a valid u64"),
        Err(_) => PREFIX_STOP_THRESHOLD,
    };

    let mut config = EngineConfig {
        target_min_log10,
        target_max_log10,
        sieve_limit,
        max_exponent,
        prefix_stop,
    };

    if config.target_min_log10 > TARGET_MIN_LOG10 {
        panic!("FATAL: Runtime value for UALBF_TARGET_MIN_LOG10 ({}) exceeds proven manifest maximum ({}). The requested bound requires a formal proof in the manifest first.", config.target_min_log10, TARGET_MIN_LOG10);
    }

    if config.target_max_log10 > TARGET_MAX_LOG10 {
        panic!("FATAL: Runtime value for UALBF_TARGET_MAX_LOG10 ({}) exceeds proven manifest maximum ({}). The requested bound requires a formal proof in the manifest first.", config.target_max_log10, TARGET_MAX_LOG10);
    }

    if config.sieve_limit > SIEVE_LIMIT {
        panic!("FATAL: Runtime value for UALBF_SIEVE_LIMIT ({}) exceeds proven manifest maximum ({}). The requested bound requires a formal proof in the manifest first.", config.sieve_limit, SIEVE_LIMIT);
    }

    if config.max_exponent > MAX_EXPONENT {
        panic!("FATAL: Runtime value for UALBF_MAX_EXPONENT ({}) exceeds proven manifest maximum ({}). The requested bound requires a formal proof in the manifest first.", config.max_exponent, MAX_EXPONENT);
    }

    if config.prefix_stop > PREFIX_STOP_THRESHOLD {
        panic!("FATAL: Runtime value for UALBF_PREFIX_STOP_THRESHOLD ({}) exceeds proven manifest maximum ({}). The requested bound requires a formal proof in the manifest first.", config.prefix_stop, PREFIX_STOP_THRESHOLD);
    }

    config
}
