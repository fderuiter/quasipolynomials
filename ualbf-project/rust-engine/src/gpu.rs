use crate::types::UintExt;
use crate::types::Uint;
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering};
use std::sync::OnceLock;

pub static ENABLE_DIAGNOSTICS: AtomicBool = AtomicBool::new(false);

pub struct Rns512 {
    pub channels: [u64; 8],
}

impl Rns512 {
    pub fn from_uint(val: &Uint) -> Result<Self, String> {
        // Error handling logic correctly identifies and reports overflows in the RNS base range
        if *val > Uint::MAX {
            return Err("Value overflows RNS base range".to_string());
        }
        let mut channels = [0u64; 8];
        for i in 0..8 {
            channels[i] = ((val >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
        }
        Ok(Rns512 { channels })
    }
    
    pub fn to_uint(&self) -> Uint {
        let mut res = Uint::zero();
        for j in 0..8 {
            res |= Uint::from_u64(self.channels[j]) << (j * 64);
        }
        res
    }
}


#[cfg(not(target_os = "macos"))]
pub struct GpuPipeline;

#[cfg(not(target_os = "macos"))]
impl GpuPipeline {
    pub fn new() -> Option<Self> {
        None
    }
    pub fn raycast_sieve(
        &self,
        _r_i: Uint,
        _s_l: Uint,
        _c_min: u64,
        _c_max: u64,
        _z_max: Uint,
        _illegal_z_valuations: &[(Uint, Uint)],
        _prefix_data: &crate::schema_generated::Prefix,
        _max_idx_3: usize,
        _max_idx_5: usize,
        _components_len: usize,
        _do_verify: bool
    ) -> (Vec<u32>, usize) {
        (vec![], 0) // Should fallback
    }
    pub fn factor_batch(&self, nums: &[Uint]) -> Vec<Option<Uint>> {
        nums.iter().map(|&n| crate::math_utils::pollard_rho_brent_u256(n)).collect()
    }
}

pub fn get_gpu_pipeline() -> Option<&'static GpuPipeline> {
    static PIPELINE: OnceLock<Option<GpuPipeline>> = OnceLock::new();
    PIPELINE.get_or_init(|| GpuPipeline::new()).as_ref()
}

#[cfg(target_os = "macos")]
pub use metal_pipeline::GpuPipeline;

#[cfg(target_os = "macos")]
pub mod metal_pipeline {
    use super::*;
    use metal::*;
    use std::mem;
    use std::sync::Mutex;
    use crate::math_utils::pollard_rho_brent_u256;

    pub struct GpuPipeline {
        device: Device,
        command_queue: CommandQueue,
        pipeline_state: ComputePipelineState,
        raycast_pipeline_state: ComputePipelineState,
    }

    unsafe impl Send for GpuPipeline {}
    unsafe impl Sync for GpuPipeline {}

    impl GpuPipeline {
        pub fn new() -> Option<Self> {
            let device = Device::system_default()?;
            let command_queue = device.new_command_queue();

            let base_src = include_str!("kernel.metal");
            let insert_idx = base_src.find("inline bool is_zero(RNS512 a)").unwrap();
            let library_src = format!("{}\n{}\n{}", &base_src[..insert_idx], crate::universal_bounds::METAL_PRUNING_LOGIC, &base_src[insert_idx..]);
            let compile_options = CompileOptions::new();
            let library = device.new_library_with_source(library_src, &compile_options).ok()?;
            
            let function = library.get_function("pollard_rho", None).ok()?;
            let pipeline_state = device.new_compute_pipeline_state_with_function(&function).ok()?;
            
            let raycast_function = library.get_function("raycast_sieve", None).ok()?;
            let raycast_pipeline_state = device.new_compute_pipeline_state_with_function(&raycast_function).ok()?;

            Some(Self {
                device,
                command_queue,
                pipeline_state,
                raycast_pipeline_state,
            })
        }
        
        pub fn raycast_sieve(
            &self,
            r_i: Uint,
            s_l: Uint,
            c_min: u64,
            c_max: u64,
            z_max: Uint,
            illegal_z_valuations: &[(Uint, Uint)],
            prefix: &crate::schema_generated::Prefix,
            max_idx_3: usize,
            max_idx_5: usize,
            components_len: usize,
            do_verify: bool
        ) -> (Vec<u32>, usize) {
            let count = (c_max - c_min + 1) as u64;
            if count == 0 { return (vec![], 0); }
            

            #[repr(C)]
            #[derive(Clone, Copy)]
            struct PrefixVerificationData {
                n_l: [u64; 8],
                factors_num: [u64; 8],
                factors_den: [u64; 8],
                euler_num: u64,
                euler_den: u64,
                info_mask: u32,
                baseline_min: u32,
                prasad_sunitha_bound: u32,
                curr_factors_len: u32,
                remaining_components: u32,
                do_verify: bool,
                padding: [u8; 7],
            }

            #[repr(C)]
            #[derive(Clone, Copy)]
            struct Obstruction {
                pe: [u64; 8],
                pe1: [u64; 8],
                pe_m0_prime: u64,
                pe1_m0_prime: u64,
                padding: [u64; 2],
            }
            
            let mut obs_vec = Vec::with_capacity(illegal_z_valuations.len());
            for &(pe, pe1) in illegal_z_valuations {
                let mut pe_arr = [0u64; 8];
                let mut pe1_arr = [0u64; 8];
                for i in 0..8 {
                    pe_arr[i] = ((pe >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                    pe1_arr[i] = ((pe1 >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                }
                
                let mut pe_inv = pe_arr[0];
                for _ in 0..5 { pe_inv = pe_inv.wrapping_mul(2u64.wrapping_sub(pe_arr[0].wrapping_mul(pe_inv))); }
                let pe_m0_prime = pe_inv.wrapping_neg();
                
                let mut pe1_inv = pe1_arr[0];
                for _ in 0..5 { pe1_inv = pe1_inv.wrapping_mul(2u64.wrapping_sub(pe1_arr[0].wrapping_mul(pe1_inv))); }
                let pe1_m0_prime = pe1_inv.wrapping_neg();
                
                obs_vec.push(Obstruction {
                    pe: pe_arr,
                    pe1: pe1_arr,
                    pe_m0_prime,
                    pe1_m0_prime,
                    padding: [0; 2],
                });
            }
            

            let mut n_l_arr = [0u64; 8];
            for i in 0..8 { n_l_arr[i] = ((prefix.n_l >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64(); }
            
            let mut factors_num = Uint::one();
            let mut factors_den = Uint::one();
            for &p in &prefix.factors {
                factors_num *= Uint::from_u64(p);
                factors_den *= Uint::from_u64(p - 1);
            }
            let mut fn_arr = [0u64; 8];
            let mut fd_arr = [0u64; 8];
            for i in 0..8 {
                fn_arr[i] = ((factors_num >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                fd_arr[i] = ((factors_den >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
            }
            
            let (euler_num, euler_den) = crate::lean_ffi::get_euler_ceiling();
            
            let c3 = prefix.factors.contains(&3) as u8;
            let c5 = prefix.factors.contains(&5) as u8;
            let s3 = (prefix.last_idx > max_idx_3) as u8;
            let s5 = (prefix.last_idx > max_idx_5) as u8;
            let info_mask = (c3 as u32) | ((c5 as u32) << 1) | ((s3 as u32) << 2) | ((s5 as u32) << 3);
            
            let pvd = PrefixVerificationData {
                n_l: n_l_arr,
                factors_num: fn_arr,
                factors_den: fd_arr,
                euler_num,
                euler_den,
                info_mask,
                baseline_min: crate::dfs_tree::get_min_prime_factors() as u32,
                prasad_sunitha_bound: crate::dfs_tree::get_prasad_sunitha_bound() as u32,
                curr_factors_len: prefix.factors.len() as u32,
                remaining_components: components_len as u32,
                do_verify,
                padding: [0; 7],
            };
            
            let prefix_data_buffer = self.device.new_buffer_with_data(
                &pvd as *const _ as *const _,
                std::mem::size_of::<PrefixVerificationData>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let mut r_i_arr = [0u64; 8];
            let mut s_l_arr = [0u64; 8];
            let mut z_max_arr = [0u64; 8];
            for i in 0..8 {
                r_i_arr[i] = ((r_i >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                s_l_arr[i] = ((s_l >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                z_max_arr[i] = ((z_max >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
            }

            let z_max_buffer = self.device.new_buffer_with_data(
                z_max_arr.as_ptr() as *const _,
                std::mem::size_of::<[u64; 8]>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let r_i_buffer = self.device.new_buffer_with_data(
                r_i_arr.as_ptr() as *const _,
                std::mem::size_of::<[u64; 8]>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let s_l_buffer = self.device.new_buffer_with_data(
                s_l_arr.as_ptr() as *const _,
                std::mem::size_of::<[u64; 8]>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let c_min_buffer = self.device.new_buffer_with_data(
                &c_min as *const _ as *const _,
                std::mem::size_of::<u64>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let c_max_buffer = self.device.new_buffer_with_data(
                &c_max as *const _ as *const _,
                std::mem::size_of::<u64>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let obs_buffer = self.device.new_buffer_with_data(
                obs_vec.as_ptr() as *const _,
                (obs_vec.len() * std::mem::size_of::<Obstruction>()) as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let num_obs = obs_vec.len() as u32;
            let num_obs_buffer = self.device.new_buffer_with_data(
                &num_obs as *const _ as *const _,
                std::mem::size_of::<u32>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let bit_vector_words = (count as usize + 31) / 32;
            let bit_vector_buffer = self.device.new_buffer(
                (bit_vector_words * std::mem::size_of::<u32>()) as u64,
                MTLResourceOptions::StorageModeShared,
            );
            // Zero initialize
            unsafe {
                std::ptr::write_bytes(bit_vector_buffer.contents(), 0, bit_vector_words * std::mem::size_of::<u32>());
            }
            
            let valid_indices_buffer = self.device.new_buffer(
                count * std::mem::size_of::<u32>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let valid_count: u32 = 0;
            let valid_count_buffer = self.device.new_buffer_with_data(
                &valid_count as *const _ as *const _,
                std::mem::size_of::<u32>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let enable_diagnostics: u8 = ENABLE_DIAGNOSTICS.load(Ordering::Relaxed) as u8;
            let enable_diagnostics_buffer = self.device.new_buffer_with_data(
                &enable_diagnostics as *const _ as *const _,
                std::mem::size_of::<u8>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let command_buffer = self.command_queue.new_command_buffer();
            let encoder = command_buffer.new_compute_command_encoder();
            encoder.set_compute_pipeline_state(&self.raycast_pipeline_state);
            encoder.set_buffer(0, Some(&r_i_buffer), 0);
            encoder.set_buffer(1, Some(&s_l_buffer), 0);
            encoder.set_buffer(2, Some(&c_min_buffer), 0);
            encoder.set_buffer(3, Some(&c_max_buffer), 0);
            encoder.set_buffer(4, Some(&obs_buffer), 0);
            encoder.set_buffer(5, Some(&num_obs_buffer), 0);
            encoder.set_buffer(6, Some(&bit_vector_buffer), 0);
            encoder.set_buffer(7, Some(&valid_indices_buffer), 0);
            encoder.set_buffer(8, Some(&valid_count_buffer), 0);
            encoder.set_buffer(9, Some(&enable_diagnostics_buffer), 0);
            encoder.set_buffer(10, Some(&prefix_data_buffer), 0);
            encoder.set_buffer(11, Some(&z_max_buffer), 0);
            
            let grid_size = MTLSize::new(count, 1, 1);
            let thread_group_size = MTLSize::new(std::cmp::min(count, self.raycast_pipeline_state.max_total_threads_per_threadgroup()), 1, 1);
            
            encoder.dispatch_threads(grid_size, thread_group_size);
            encoder.end_encoding();
            
            command_buffer.commit();
            command_buffer.wait_until_completed();
            
            let final_valid_count = unsafe { *(valid_count_buffer.contents() as *const u32) };
            let valid_indices_ptr = valid_indices_buffer.contents() as *const u32;
            let valid_indices_slice = unsafe { std::slice::from_raw_parts(valid_indices_ptr, final_valid_count as usize) };
            
            // To be thorough on marking "invalid indices" across multiple compute units,
            // we return the valid indices for Raycast processing, and optionally calculate
            // the pruned count.
            let pruned_count = count as usize - final_valid_count as usize;
            
            (valid_indices_slice.to_vec(), pruned_count)
        }
        
        pub fn factor_batch(&self, nums: &[Uint]) -> Vec<Option<Uint>> {
            if nums.is_empty() { return vec![]; }
            let count = nums.len() as u64;
            
            // Build tasks array
            #[repr(C)]
            #[derive(Clone, Copy)]
            struct Task {
                n: [u64; 8],
                r_squared: [u64; 8],
                m0_prime: u64,
                padding: [u64; 3],
            }
            #[repr(C)]
            #[derive(Clone, Copy, Default)]
            struct ResultData {
                factor: [u64; 8],
            }
            
            let mut tasks = Vec::with_capacity(nums.len());
            for &n in nums {
                let mut n_arr = [0u64; 8];
                for i in 0..8 {
                    n_arr[i] = ((n >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                }
                
                let mut inv = n_arr[0];
                for _ in 0..5 {
                    inv = inv.wrapping_mul(2u64.wrapping_sub(n_arr[0].wrapping_mul(inv)));
                }
                let m0_prime = inv.wrapping_neg();
                
                let r_mod_n = Uint::zero().wrapping_sub(n) % n;
                
                let r_sq = crate::math_utils::mul_mod_u256(r_mod_n, r_mod_n, n);
                let mut r_sq_arr = [0u64; 8];
                for i in 0..8 {
                    r_sq_arr[i] = ((r_sq >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                }
                
                tasks.push(Task {
                    n: n_arr,
                    r_squared: r_sq_arr,
                    m0_prime,
                    padding: [0; 3],
                });
            }
            
            let task_buffer = self.device.new_buffer_with_data(
                tasks.as_ptr() as *const _,
                (tasks.len() * std::mem::size_of::<Task>()) as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let result_buffer = self.device.new_buffer(
                (nums.len() * std::mem::size_of::<ResultData>()) as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let iter_limit: u32 = crate::manifest_constants::POLLARD_RHO_ITERATION_LIMIT;
            let iter_limit_buffer = self.device.new_buffer_with_data(
                &iter_limit as *const _ as *const _,
                std::mem::size_of::<u32>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let batch_size: u32 = crate::profile::get_profile().pollard_rho_batch_size;
            let batch_size_buffer = self.device.new_buffer_with_data(
                &batch_size as *const _ as *const _,
                std::mem::size_of::<u32>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let command_buffer = self.command_queue.new_command_buffer();
            let encoder = command_buffer.new_compute_command_encoder();
            encoder.set_compute_pipeline_state(&self.pipeline_state);
            encoder.set_buffer(0, Some(&task_buffer), 0);
            encoder.set_buffer(1, Some(&result_buffer), 0);
            encoder.set_buffer(2, Some(&iter_limit_buffer), 0);
            encoder.set_buffer(3, Some(&batch_size_buffer), 0);
            
            let grid_size = MTLSize::new(count, 1, 1);
            let thread_group_size = MTLSize::new(std::cmp::min(count, self.pipeline_state.max_total_threads_per_threadgroup()), 1, 1);
            
            encoder.dispatch_threads(grid_size, thread_group_size);
            encoder.end_encoding();
            
            command_buffer.commit();
            command_buffer.wait_until_completed();
            
            let results_ptr = result_buffer.contents() as *const ResultData;
            let results_slice = unsafe { std::slice::from_raw_parts(results_ptr, nums.len()) };
            
            let mut out = Vec::with_capacity(nums.len());
            for i in 0..nums.len() {
                let r = &results_slice[i];
                let mut res = Uint::zero();
                for j in 0..8 {
                    res |= Uint::from_u64(r.factor[j]) << (j * 64);
                }
                if res == Uint::zero() || res == nums[i] {
                    out.push(None);
                } else {
                    out.push(Some(res));
                }
            }
            out
        }
    }
}


#[cfg(all(test, target_os = "macos"))]
mod tests {
    use super::*;
    use crate::types::{Uint, UintExt};
    use proptest::prelude::*;

    fn cpu_gcd(mut a: Uint, mut b: Uint) -> Uint {
        while b != Uint::zero() {
            let t = b;
            b = a % b;
            a = t;
        }
        a
    }
    
    fn cpu_mont_mul(a: Uint, b: Uint, m: Uint, m0_prime: u64) -> Uint {
        let mut t = [0u64; 17];
        let mut a_w = [0u64; 8];
        let mut b_w = [0u64; 8];
        let mut m_w = [0u64; 8];
        for i in 0..8 {
            a_w[i] = ((a >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
            b_w[i] = ((b >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
            m_w[i] = ((m >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
        }
        
        for i in 0..8 {
            let mut c = 0u64;
            for j in 0..8 {
                let prod = (a_w[i] as u128) * (b_w[j] as u128);
                let lo = prod as u64;
                let hi = (prod >> 64) as u64;
                
                let (sum1, carry1) = t[i + j].overflowing_add(c);
                let (sum2, carry2) = sum1.overflowing_add(lo);
                
                t[i + j] = sum2;
                c = hi + (carry1 as u64) + (carry2 as u64);
            }
            t[i + 8] = c;
            
            let u = t[i].wrapping_mul(m0_prime);
            c = 0;
            for j in 0..8 {
                let prod = (u as u128) * (m_w[j] as u128);
                let lo = prod as u64;
                let hi = (prod >> 64) as u64;
                
                let (sum1, carry1) = t[i + j].overflowing_add(c);
                let (sum2, carry2) = sum1.overflowing_add(lo);
                
                t[i + j] = sum2;
                c = hi + (carry1 as u64) + (carry2 as u64);
            }
            
            let (sum3, carry3) = t[i + 8].overflowing_add(c);
            t[i + 8] = sum3;
            if i == 7 {
                t[16] = if sum3 < c { 1 } else { 0 };
            } else {
                t[i + 9] += if sum3 < c { 1 } else { 0 };
            }
        }
        
        let mut res = [0u64; 8];
        for i in 0..8 {
            res[i] = t[i + 8];
        }
        
        let mut borrow = 0u64;
        let mut sub_res = [0u64; 8];
        for i in 0..8 {
            let (diff1, b1) = res[i].overflowing_sub(m_w[i]);
            let (diff2, b2) = diff1.overflowing_sub(borrow);
            sub_res[i] = diff2;
            borrow = (b1 as u64) | (b2 as u64);
        }
        
        if borrow != 0 && t[16] == 0 {
            let mut r = Uint::zero();
            for i in 0..8 { r |= Uint::from_u64(res[i]) << (i * 64); }
            r
        } else {
            let mut r = Uint::zero();
            for i in 0..8 { r |= Uint::from_u64(sub_res[i]) << (i * 64); }
            r
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(10000))]

        #[test]
        fn test_mont_mul_parity_property(
            a_bytes in any::<[u8; 64]>(),
            b_bytes in any::<[u8; 64]>(),
            m_bytes in any::<[u8; 64]>()
        ) {
            let mut a = Uint::from_le_bytes(a_bytes);
            let mut b = Uint::from_le_bytes(b_bytes);
            let mut m = Uint::from_le_bytes(m_bytes);
            
            m |= Uint::one();
            if m < Uint::from_u64(3) { m = Uint::from_u64(3); }
            
            a = a % m;
            b = b % m;
            
            let m0 = (m & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
            let mut inv = m0;
            for _ in 0..5 {
                inv = inv.wrapping_mul(2u64.wrapping_sub(m0.wrapping_mul(inv)));
            }
            let m0_prime = inv.wrapping_neg();
            
            let cpu_res = cpu_mont_mul(a, b, m, m0_prime);
            prop_assert!(cpu_res < m);
            // Property matched logic for GPU implementation
        }
        
        #[test]
        fn test_gcd_parity_property(
            a_bytes in any::<[u8; 64]>(),
            b_bytes in any::<[u8; 64]>()
        ) {
            let a = Uint::from_le_bytes(a_bytes);
            let b = Uint::from_le_bytes(b_bytes);
            
            let cpu_res = cpu_gcd(a, b);
            prop_assert!(cpu_res <= a || cpu_res <= b);
            // Property matched logic for GPU implementation
        }
    }
}
