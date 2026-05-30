use crate::types::Uint;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::OnceLock;

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
        _illegal_z_valuations: &[(Uint, Uint)]
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

            let library_src = include_str!("kernel.metal");
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
            illegal_z_valuations: &[(Uint, Uint)]
        ) -> (Vec<u32>, usize) {
            let count = (c_max - c_min + 1) as u64;
            if count == 0 { return (vec![], 0); }
            
            #[repr(C)]
            #[derive(Clone, Copy)]
            struct Obstruction {
                pe: [u32; 8],
                pe1: [u32; 8],
                pe_m0_prime: u32,
                pe1_m0_prime: u32,
                padding: [u32; 2],
            }
            
            let mut obs_vec = Vec::with_capacity(illegal_z_valuations.len());
            for &(pe, pe1) in illegal_z_valuations {
                let mut pe_arr = [0u32; 8];
                let mut pe1_arr = [0u32; 8];
                for i in 0..8 {
                    pe_arr[i] = ((pe >> (i * 32)) & Uint::from(0xFFFFFFFFu32)).as_u32();
                    pe1_arr[i] = ((pe1 >> (i * 32)) & Uint::from(0xFFFFFFFFu32)).as_u32();
                }
                
                let mut pe_inv = pe_arr[0];
                for _ in 0..4 { pe_inv = pe_inv.wrapping_mul(2u32.wrapping_sub(pe_arr[0].wrapping_mul(pe_inv))); }
                let pe_m0_prime = pe_inv.wrapping_neg();
                
                let mut pe1_inv = pe1_arr[0];
                for _ in 0..4 { pe1_inv = pe1_inv.wrapping_mul(2u32.wrapping_sub(pe1_arr[0].wrapping_mul(pe1_inv))); }
                let pe1_m0_prime = pe1_inv.wrapping_neg();
                
                obs_vec.push(Obstruction {
                    pe: pe_arr,
                    pe1: pe1_arr,
                    pe_m0_prime,
                    pe1_m0_prime,
                    padding: [0; 2],
                });
            }
            
            let mut r_i_arr = [0u32; 8];
            let mut s_l_arr = [0u32; 8];
            for i in 0..8 {
                r_i_arr[i] = ((r_i >> (i * 32)) & Uint::from(0xFFFFFFFFu32)).as_u32();
                s_l_arr[i] = ((s_l >> (i * 32)) & Uint::from(0xFFFFFFFFu32)).as_u32();
            }
            
            let r_i_buffer = self.device.new_buffer_with_data(
                r_i_arr.as_ptr() as *const _,
                std::mem::size_of::<[u32; 8]>() as u64,
                MTLResourceOptions::StorageModeShared,
            );
            
            let s_l_buffer = self.device.new_buffer_with_data(
                s_l_arr.as_ptr() as *const _,
                std::mem::size_of::<[u32; 8]>() as u64,
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
                n: [u32; 8],
                r_squared: [u32; 8],
                m0_prime: u32,
                padding: [u32; 3],
            }
            #[repr(C)]
            #[derive(Clone, Copy, Default)]
            struct ResultData {
                factor: [u32; 8],
            }
            
            let mut tasks = Vec::with_capacity(nums.len());
            for &n in nums {
                let mut n_arr = [0u32; 8];
                for i in 0..8 {
                    n_arr[i] = ((n >> (i * 32)) & Uint::from(0xFFFFFFFFu32)).as_u32();
                }
                
                let mut inv = n_arr[0];
                for _ in 0..4 {
                    inv = inv.wrapping_mul(2u32.wrapping_sub(n_arr[0].wrapping_mul(inv)));
                }
                let m0_prime = inv.wrapping_neg();
                
                let r_mod_n = Uint::ZERO.wrapping_sub(n) % n;
                
                let r_sq = crate::math_utils::mul_mod_u256(r_mod_n, r_mod_n, n);
                let mut r_sq_arr = [0u32; 8];
                for i in 0..8 {
                    r_sq_arr[i] = ((r_sq >> (i * 32)) & Uint::from(0xFFFFFFFFu32)).as_u32();
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
            
            let command_buffer = self.command_queue.new_command_buffer();
            let encoder = command_buffer.new_compute_command_encoder();
            encoder.set_compute_pipeline_state(&self.pipeline_state);
            encoder.set_buffer(0, Some(&task_buffer), 0);
            encoder.set_buffer(1, Some(&result_buffer), 0);
            
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
                let mut res = Uint::ZERO;
                for j in 0..8 {
                    res |= Uint::from(r.factor[j]) << (j * 32);
                }
                if res == Uint::ZERO || res == nums[i] {
                    out.push(None);
                } else {
                    out.push(Some(res));
                }
            }
            out
        }
    }
}
