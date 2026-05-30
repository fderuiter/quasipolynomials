use crate::types::Uint;
use std::sync::atomic::{AtomicUsize, Ordering};

#[cfg(not(target_os = "macos"))]
pub struct GpuPipeline;

#[cfg(not(target_os = "macos"))]
impl GpuPipeline {
    pub fn new() -> Option<Self> {
        None
    }
    pub fn factor_batch(&self, nums: &[Uint]) -> Vec<Option<Uint>> {
        nums.iter().map(|n| crate::math_utils::pollard_rho_brent_u256(n.clone())).collect()
    }
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

            Some(Self {
                device,
                command_queue,
                pipeline_state,
            })
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
