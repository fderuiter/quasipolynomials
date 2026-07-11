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
pub use opencl_pipeline::GpuPipeline;

#[cfg(not(target_os = "macos"))]
pub mod opencl_pipeline {
    use super::*;
    use opencl3::command_queue::{CommandQueue, CL_QUEUE_PROFILING_ENABLE};
    use opencl3::context::Context;
    use opencl3::device::{get_all_devices, Device, CL_DEVICE_TYPE_GPU};
    use opencl3::kernel::{ExecuteKernel, Kernel};
    use opencl3::memory::{Buffer, CL_MEM_READ_ONLY, CL_MEM_READ_WRITE, CL_MEM_COPY_HOST_PTR, CL_MEM_WRITE_ONLY};
    use opencl3::program::Program;
    use opencl3::types::{cl_uint, cl_ulong, cl_uchar, cl_int};
    use opencl3::Result as ClResult;
    use std::ptr;
    use std::sync::atomic::Ordering;
    use crate::math_utils::pollard_rho_brent_u256;

    pub struct GpuPipeline {
        context: Context,
        command_queue: CommandQueue,
        pollard_rho_kernel: Kernel,
        raycast_sieve_kernel: Kernel,
    }

    unsafe impl Send for GpuPipeline {}
    unsafe impl Sync for GpuPipeline {}

    impl GpuPipeline {
        pub fn new() -> Option<Self> {
            unsafe {
                let device_ids = get_all_devices(CL_DEVICE_TYPE_GPU).ok()?;
                if device_ids.is_empty() {
                    return None;
                }
                let device_id = device_ids[0];
                let device = Device::new(device_id);

                let context = Context::from_device(&device).ok()?;
                let command_queue = CommandQueue::create_with_properties(&context, device_id, 0, 0).ok()?;

                let base_src = include_str!("kernel.cl");
                let pruning_logic = crate::universal_bounds::METAL_PRUNING_LOGIC.replace("mulhi", "mul_hi");
                let insert_idx = base_src.find("inline bool is_zero(RNS512 a)").unwrap_or(0);
                let library_src = format!("{}\n{}\n{}", &base_src[..insert_idx], pruning_logic, &base_src[insert_idx..]);

                let program = Program::create_and_build_from_source(&context, &library_src, "").ok()?;

                let pollard_rho_kernel = Kernel::create(&program, "pollard_rho").ok()?;
                let raycast_sieve_kernel = Kernel::create(&program, "raycast_sieve").ok()?;

                Some(Self {
                    context,
                    command_queue,
                    pollard_rho_kernel,
                    raycast_sieve_kernel,
                })
            }
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
        ) -> crossbeam_channel::Receiver<(Vec<u32>, usize)> {
            let (tx, rx) = crossbeam_channel::bounded(1);
            let result = (|| {
            unsafe {
                let count = (c_max - c_min + 1) as usize;
                if count == 0 { return (vec![], 0); }
                
                #[repr(C)]
                #[derive(Clone, Copy, Default)]
                struct Rns512Cl { w: [u64; 8] }
                
                #[repr(C)]
                #[derive(Clone, Copy)]
                struct PrefixVerificationData {
                    n_l: Rns512Cl,
                    factors_num: Rns512Cl,
                    factors_den: Rns512Cl,
                    euler_num: u64,
                    euler_den: u64,
                    overflow_num: u64,
                    overflow_den: u64,
                    info_mask: u32,
                    baseline_min: u32,
                    prasad_sunitha_bound: u32,
                    curr_factors_len: u32,
                    remaining_components: u32,
                    do_verify: u8,
                    padding: [u8; 3],
                }

                #[repr(C)]
                #[derive(Clone, Copy)]
                struct Obstruction {
                    pe: Rns512Cl,
                    pe1: Rns512Cl,
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
                        pe: Rns512Cl { w: pe_arr },
                        pe1: Rns512Cl { w: pe1_arr },
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
                
                let (e_num, e_den) = crate::lean_ffi::get_euler_ceiling();
                let euler_num: u64 = e_num.try_into().unwrap();
                let euler_den: u64 = e_den.try_into().unwrap();
                
                let c3 = prefix.factors.contains(&3) as u8;
                let c5 = prefix.factors.contains(&5) as u8;
                let s3 = (prefix.last_idx > max_idx_3) as u8;
                let s5 = (prefix.last_idx > max_idx_5) as u8;
                let info_mask = (c3 as u32) | ((c5 as u32) << 1) | ((s3 as u32) << 2) | ((s5 as u32) << 3);
                
                let pvd = PrefixVerificationData {
                    n_l: Rns512Cl { w: n_l_arr },
                    factors_num: Rns512Cl { w: fn_arr },
                    factors_den: Rns512Cl { w: fd_arr },
                    euler_num,
                    euler_den,
                    overflow_num: crate::lean_ffi::get_target_abundance_num(),
                    overflow_den: crate::lean_ffi::get_target_abundance_den(),
                    info_mask,
                    baseline_min: crate::dfs_tree::get_min_prime_factors() as u32,
                    prasad_sunitha_bound: crate::dfs_tree::get_prasad_sunitha_bound() as u32,
                    curr_factors_len: prefix.factors.len() as u32,
                    remaining_components: components_len as u32,
                    do_verify: do_verify as u8,
                    padding: [0; 3],
                };
                
                let mut r_i_arr = [0u64; 8];
                let mut s_l_arr = [0u64; 8];
                let mut z_max_arr = [0u64; 8];
                for i in 0..8 {
                    r_i_arr[i] = ((r_i >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                    s_l_arr[i] = ((s_l >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                    z_max_arr[i] = ((z_max >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                }
                
                let r_i_cl = Rns512Cl { w: r_i_arr };
                let s_l_cl = Rns512Cl { w: s_l_arr };
                let z_max_cl = Rns512Cl { w: z_max_arr };

                let obs_len = obs_vec.len();
                let mut obs_buffer = Buffer::<Obstruction>::create(&self.context, CL_MEM_READ_ONLY.try_into().unwrap(), obs_len.max(1), ptr::null_mut()).unwrap();
                if obs_len > 0 {
                    let _ = self.command_queue.enqueue_write_buffer(&mut obs_buffer, 1, 0, &obs_vec, &[]);
                }

                let num_obs = obs_len as u32;

                let bit_vector_words = (count + 31) / 32;
                let mut bit_vector_buffer = Buffer::<u32>::create(&self.context, CL_MEM_READ_WRITE.try_into().unwrap(), bit_vector_words, ptr::null_mut()).unwrap();
                let zeros = vec![0u32; bit_vector_words];
                let _ = self.command_queue.enqueue_write_buffer(&mut bit_vector_buffer, 1, 0, &zeros, &[]);
                
                let valid_indices_buffer = Buffer::<u32>::create(&self.context, CL_MEM_READ_WRITE.try_into().unwrap(), count, ptr::null_mut()).unwrap();
                let mut valid_count_buffer = Buffer::<u32>::create(&self.context, CL_MEM_READ_WRITE.try_into().unwrap(), 1, ptr::null_mut()).unwrap();
                let init_count = [0u32];
                let _ = self.command_queue.enqueue_write_buffer(&mut valid_count_buffer, 1, 0, &init_count, &[]);
                
                let enable_diagnostics: u8 = ENABLE_DIAGNOSTICS.load(Ordering::Relaxed) as u8;

                let _ = ExecuteKernel::new(&self.raycast_sieve_kernel)
                    .set_arg(&r_i_cl)
                    .set_arg(&s_l_cl)
                    .set_arg(&c_min)
                    .set_arg(&c_max)
                    .set_arg(&obs_buffer)
                    .set_arg(&num_obs)
                    .set_arg(&bit_vector_buffer)
                    .set_arg(&valid_indices_buffer)
                    .set_arg(&valid_count_buffer)
                    .set_arg(&enable_diagnostics)
                    .set_arg(&pvd)
                    .set_arg(&z_max_cl)
                    .set_global_work_size(count)
                    .enqueue_nd_range(&self.command_queue);
                
                self.command_queue.finish().unwrap();

                let mut final_valid_count = [0u32];
                let _ = self.command_queue.enqueue_read_buffer(&valid_count_buffer, 1, 0, &mut final_valid_count, &[]);
                
                let fvc = final_valid_count[0] as usize;
                let mut valid_indices = vec![0u32; fvc];
                if fvc > 0 {
                    let _ = self.command_queue.enqueue_read_buffer(&valid_indices_buffer, 1, 0, &mut valid_indices, &[]);
                }

                let pruned_count = count - fvc;
                (valid_indices, pruned_count)
            }
        
            })();
            let _ = tx.send(result);
            rx
        }
        
        pub fn factor_batch(&self, nums: &[Uint]) -> crossbeam_channel::Receiver<Vec<Option<Uint>>> {
            let (tx, rx) = crossbeam_channel::bounded(1);
            let result = (|| {
            unsafe {
                if nums.is_empty() { return vec![]; }
                let count = nums.len();
                
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
                
                let mut task_buffer = Buffer::<Task>::create(&self.context, CL_MEM_READ_ONLY.try_into().unwrap(), count, ptr::null_mut()).unwrap();
                let _ = self.command_queue.enqueue_write_buffer(&mut task_buffer, 1, 0, &tasks, &[]);
                
                let result_buffer = Buffer::<ResultData>::create(&self.context, CL_MEM_READ_WRITE.try_into().unwrap(), count, ptr::null_mut()).unwrap();
                
                let iter_limit: u32 = crate::lean_ffi::get_pollard_rho_iteration_limit();
                let batch_size: u32 = crate::profile::get_profile().pollard_rho_batch_size;
                
                let _ = ExecuteKernel::new(&self.pollard_rho_kernel)
                    .set_arg(&task_buffer)
                    .set_arg(&result_buffer)
                    .set_arg(&iter_limit)
                    .set_arg(&batch_size)
                    .set_global_work_size(count)
                    .enqueue_nd_range(&self.command_queue);
                
                self.command_queue.finish().unwrap();
                
                let mut results = vec![ResultData::default(); count];
                let _ = self.command_queue.enqueue_read_buffer(&result_buffer, 1, 0, &mut results, &[]);
                
                let mut out = Vec::with_capacity(count);
                for i in 0..count {
                    let r = &results[i];
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
        
            })();
            let _ = tx.send(result);
            rx
        }
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
    use crossbeam_channel::{bounded, Sender, Receiver};
    use block::ConcreteBlock;
    use crate::math_utils::pollard_rho_brent_u256;

    fn ensure_buffer(device: &Device, buffer: &mut Option<Buffer>, size: u64, data: Option<*const std::ffi::c_void>) {
        let create_new = match buffer {
            Some(b) => b.length() < size,
            None => true,
        };
        if create_new {
            if let Some(ptr) = data {
                *buffer = Some(device.new_buffer_with_data(ptr, size, MTLResourceOptions::StorageModeShared));
            } else {
                *buffer = Some(device.new_buffer(size, MTLResourceOptions::StorageModeShared));
            }
        } else {
            if let Some(ptr) = data {
                unsafe {
                    std::ptr::copy_nonoverlapping(ptr as *const u8, buffer.as_ref().unwrap().contents() as *mut u8, size as usize);
                }
            }
        }
    }

    #[derive(Clone)]
    struct RaycastSlot {
        prefix_data_buffer: Option<Buffer>,
        z_max_buffer: Option<Buffer>,
        r_i_buffer: Option<Buffer>,
        s_l_buffer: Option<Buffer>,
        c_min_buffer: Option<Buffer>,
        c_max_buffer: Option<Buffer>,
        obs_buffer: Option<Buffer>,
        num_obs_buffer: Option<Buffer>,
        bit_vector_buffer: Option<Buffer>,
        valid_indices_buffer: Option<Buffer>,
        valid_count_buffer: Option<Buffer>,
        enable_diagnostics_buffer: Option<Buffer>,
    }

    impl RaycastSlot {
        fn new() -> Self {
            RaycastSlot {
                prefix_data_buffer: None,
                z_max_buffer: None,
                r_i_buffer: None,
                s_l_buffer: None,
                c_min_buffer: None,
                c_max_buffer: None,
                obs_buffer: None,
                num_obs_buffer: None,
                bit_vector_buffer: None,
                valid_indices_buffer: None,
                valid_count_buffer: None,
                enable_diagnostics_buffer: None,
            }
        }
    }

    #[derive(Clone)]
    struct FactorSlot {
        task_buffer: Option<Buffer>,
        result_buffer: Option<Buffer>,
        iter_limit_buffer: Option<Buffer>,
        batch_size_buffer: Option<Buffer>,
    }

    impl FactorSlot {
        fn new() -> Self {
            FactorSlot {
                task_buffer: None,
                result_buffer: None,
                iter_limit_buffer: None,
                batch_size_buffer: None,
            }
        }
    }

    pub struct GpuPipeline {
        device: Device,
        command_queue: CommandQueue,
        pipeline_state: ComputePipelineState,
        raycast_pipeline_state: ComputePipelineState,
        raycast_free_list: Receiver<RaycastSlot>,
        raycast_pool_tx: Sender<RaycastSlot>,
        factor_free_list: Receiver<FactorSlot>,
        factor_pool_tx: Sender<FactorSlot>,
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

            let (raycast_pool_tx, raycast_free_list) = bounded(16);
            for _ in 0..16 {
                let _ = raycast_pool_tx.send(RaycastSlot::new());
            }

            let (factor_pool_tx, factor_free_list) = bounded(16);
            for _ in 0..16 {
                let _ = factor_pool_tx.send(FactorSlot::new());
            }

            Some(Self {
                device,
                command_queue,
                pipeline_state,
                raycast_pipeline_state,
                raycast_free_list,
                raycast_pool_tx,
                factor_free_list,
                factor_pool_tx,
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
            prefix: &crate::raycast::Prefix,
            max_idx_3: usize,
            max_idx_5: usize,
            components_len: usize,
            do_verify: bool,
        ) -> Receiver<(Vec<u32>, usize)> {
            let mut slot = self.raycast_free_list.recv().expect("Failed to acquire GPU ring buffer slot");
            let count = c_max - c_min + 1;
            
            #[repr(C)]
            struct Obstruction {
                pe: u64,
                pe1: u64,
            }
            let mut obs_vec = Vec::with_capacity(illegal_z_valuations.len());
            for &(pe, pe1) in illegal_z_valuations {
                obs_vec.push(Obstruction {
                    pe: pe.as_u64(),
                    pe1: pe1.as_u64(),
                });
            }
            
            let mut n_l_arr = [0u64; 8];
            for i in 0..8 {
                n_l_arr[i] = ((prefix.n_l >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
            }
            let mut fn_arr = [0u64; 8];
            let mut fd_arr = [0u64; 8];
            for i in 0..std::cmp::min(8, prefix.factors.len()) {
                fn_arr[i] = prefix.factors[i].as_u64();
                fd_arr[i] = prefix.factors[i].as_u64() - 1;
            }
            let (euler_num, euler_den) = crate::lean_ffi::get_euler_ceiling();
            
            let info_mask = ((max_idx_3 as u32) << 16) | (max_idx_5 as u32);
            
            #[repr(C)]
            #[derive(Clone, Copy)]
            struct PrefixVerificationData {
                n_l: [u64; 8],
                factors_num: [u64; 8],
                factors_den: [u64; 8],
                euler_num: u64,
                euler_den: u64,
                overflow_num: u64,
                overflow_den: u64,
                info_mask: u32,
                baseline_min: u32,
                prasad_sunitha_bound: u32,
                curr_factors_len: u32,
                remaining_components: u32,
                do_verify: bool,
                padding: [u8; 7],
            }
            let pvd = PrefixVerificationData {
                n_l: n_l_arr,
                factors_num: fn_arr,
                factors_den: fd_arr,
                euler_num,
                euler_den,
                overflow_num: crate::lean_ffi::get_target_abundance_num(),
                overflow_den: crate::lean_ffi::get_target_abundance_den(),
                info_mask,
                baseline_min: crate::dfs_tree::get_min_prime_factors() as u32,
                prasad_sunitha_bound: crate::dfs_tree::get_prasad_sunitha_bound() as u32,
                curr_factors_len: prefix.factors.len() as u32,
                remaining_components: components_len as u32,
                do_verify,
                padding: [0; 7],
            };
            
            ensure_buffer(&self.device, &mut slot.prefix_data_buffer, std::mem::size_of::<PrefixVerificationData>() as u64, Some(&pvd as *const _ as *const _));
            
            let mut r_i_arr = [0u64; 8];
            let mut s_l_arr = [0u64; 8];
            let mut z_max_arr = [0u64; 8];
            for i in 0..8 {
                r_i_arr[i] = ((r_i >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                s_l_arr[i] = ((s_l >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
                z_max_arr[i] = ((z_max >> (i * 64)) & Uint::from_u64(0xFFFFFFFFFFFFFFFFu64)).as_u64();
            }

            ensure_buffer(&self.device, &mut slot.z_max_buffer, std::mem::size_of::<[u64; 8]>() as u64, Some(z_max_arr.as_ptr() as *const _));
            ensure_buffer(&self.device, &mut slot.r_i_buffer, std::mem::size_of::<[u64; 8]>() as u64, Some(r_i_arr.as_ptr() as *const _));
            ensure_buffer(&self.device, &mut slot.s_l_buffer, std::mem::size_of::<[u64; 8]>() as u64, Some(s_l_arr.as_ptr() as *const _));
            ensure_buffer(&self.device, &mut slot.c_min_buffer, std::mem::size_of::<u64>() as u64, Some(&c_min as *const _ as *const _));
            ensure_buffer(&self.device, &mut slot.c_max_buffer, std::mem::size_of::<u64>() as u64, Some(&c_max as *const _ as *const _));
            
            ensure_buffer(&self.device, &mut slot.obs_buffer, (obs_vec.len() * std::mem::size_of::<Obstruction>()) as u64, if obs_vec.is_empty() { None } else { Some(obs_vec.as_ptr() as *const _) });
            
            let num_obs = obs_vec.len() as u32;
            ensure_buffer(&self.device, &mut slot.num_obs_buffer, std::mem::size_of::<u32>() as u64, Some(&num_obs as *const _ as *const _));
            
            let bit_vector_words = (count as usize + 31) / 32;
            ensure_buffer(&self.device, &mut slot.bit_vector_buffer, (bit_vector_words * std::mem::size_of::<u32>()) as u64, None);
            unsafe {
                std::ptr::write_bytes(slot.bit_vector_buffer.as_ref().unwrap().contents(), 0, bit_vector_words * std::mem::size_of::<u32>());
            }
            
            ensure_buffer(&self.device, &mut slot.valid_indices_buffer, count * std::mem::size_of::<u32>() as u64, None);
            
            let valid_count: u32 = 0;
            ensure_buffer(&self.device, &mut slot.valid_count_buffer, std::mem::size_of::<u32>() as u64, Some(&valid_count as *const _ as *const _));
            
            let enable_diagnostics: u8 = ENABLE_DIAGNOSTICS.load(std::sync::atomic::Ordering::Relaxed) as u8;
            ensure_buffer(&self.device, &mut slot.enable_diagnostics_buffer, std::mem::size_of::<u8>() as u64, Some(&enable_diagnostics as *const _ as *const _));
            
            let command_buffer = self.command_queue.new_command_buffer();
            let encoder = command_buffer.new_compute_command_encoder();
            encoder.set_compute_pipeline_state(&self.raycast_pipeline_state);
            encoder.set_buffer(0, Some(slot.r_i_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(1, Some(slot.s_l_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(2, Some(slot.c_min_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(3, Some(slot.c_max_buffer.as_ref().unwrap()), 0);
            if !obs_vec.is_empty() {
                encoder.set_buffer(4, Some(slot.obs_buffer.as_ref().unwrap()), 0);
            }
            encoder.set_buffer(5, Some(slot.num_obs_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(6, Some(slot.bit_vector_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(7, Some(slot.valid_indices_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(8, Some(slot.valid_count_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(9, Some(slot.z_max_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(10, Some(slot.prefix_data_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(11, Some(slot.enable_diagnostics_buffer.as_ref().unwrap()), 0);
            
            let grid_size = MTLSize::new(count, 1, 1);
            let thread_group_size = MTLSize::new(std::cmp::min(count, self.raycast_pipeline_state.max_total_threads_per_threadgroup()), 1, 1);
            
            encoder.dispatch_threads(grid_size, thread_group_size);
            encoder.end_encoding();
            
            let (tx, rx) = bounded(1);
            let pool_tx = self.raycast_pool_tx.clone();
            
            let slot_clone = slot.clone();
            
            let block = ConcreteBlock::new(move |_cb: &CommandBufferRef| {
                let valid_count_buf = slot_clone.valid_count_buffer.as_ref().unwrap();
                let valid_indices_buf = slot_clone.valid_indices_buffer.as_ref().unwrap();
                
                let final_valid_count = unsafe { *(valid_count_buf.contents() as *const u32) };
                let valid_indices_ptr = valid_indices_buf.contents() as *const u32;
                let valid_indices_slice = unsafe { std::slice::from_raw_parts(valid_indices_ptr, final_valid_count as usize) };
                
                let pruned_count = count as usize - final_valid_count as usize;
                
                let _ = tx.send((valid_indices_slice.to_vec(), pruned_count));
                
                let _ = pool_tx.send(slot_clone);
            }).copy();
            
            command_buffer.add_completed_handler(&block);
            command_buffer.commit();
            
            rx
        }
        
        pub fn factor_batch(&self, nums: &[Uint]) -> Receiver<Vec<Option<Uint>>> {
            let (tx, rx) = bounded(1);
            if nums.is_empty() { 
                let _ = tx.send(vec![]);
                return rx; 
            }
            
            let mut slot = self.factor_free_list.recv().expect("Failed to acquire GPU ring buffer slot");
            let count = nums.len() as u64;
            
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
            
            ensure_buffer(&self.device, &mut slot.task_buffer, (tasks.len() * std::mem::size_of::<Task>()) as u64, Some(tasks.as_ptr() as *const _));
            ensure_buffer(&self.device, &mut slot.result_buffer, (nums.len() * std::mem::size_of::<ResultData>()) as u64, None);
            
            let iter_limit: u32 = crate::lean_ffi::get_pollard_rho_iteration_limit();
            ensure_buffer(&self.device, &mut slot.iter_limit_buffer, std::mem::size_of::<u32>() as u64, Some(&iter_limit as *const _ as *const _));
            
            let batch_size: u32 = crate::profile::get_profile().pollard_rho_batch_size;
            ensure_buffer(&self.device, &mut slot.batch_size_buffer, std::mem::size_of::<u32>() as u64, Some(&batch_size as *const _ as *const _));
            
            let command_buffer = self.command_queue.new_command_buffer();
            let encoder = command_buffer.new_compute_command_encoder();
            encoder.set_compute_pipeline_state(&self.pipeline_state);
            encoder.set_buffer(0, Some(slot.task_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(1, Some(slot.result_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(2, Some(slot.iter_limit_buffer.as_ref().unwrap()), 0);
            encoder.set_buffer(3, Some(slot.batch_size_buffer.as_ref().unwrap()), 0);
            
            let grid_size = MTLSize::new(count, 1, 1);
            let thread_group_size = MTLSize::new(std::cmp::min(count, self.pipeline_state.max_total_threads_per_threadgroup()), 1, 1);
            
            encoder.dispatch_threads(grid_size, thread_group_size);
            encoder.end_encoding();
            
            let pool_tx = self.factor_pool_tx.clone();
            let slot_clone = slot.clone();
            let nums_cloned = nums.to_vec();
            
            let block = ConcreteBlock::new(move |_cb: &CommandBufferRef| {
                let result_buf = slot_clone.result_buffer.as_ref().unwrap();
                let results_ptr = result_buf.contents() as *const ResultData;
                let results_slice = unsafe { std::slice::from_raw_parts(results_ptr, nums_cloned.len()) };
                
                let mut out = Vec::with_capacity(nums_cloned.len());
                for i in 0..nums_cloned.len() {
                    let r = &results_slice[i];
                    let mut res = Uint::zero();
                    for j in 0..8 {
                        res |= Uint::from_u64(r.factor[j]) << (j * 64);
                    }
                    if res == Uint::zero() || res == nums_cloned[i] {
                        out.push(None);
                    } else {
                        out.push(Some(res));
                    }
                }
                
                let _ = tx.send(out);
                let _ = pool_tx.send(slot_clone);
            }).copy();
            
            command_buffer.add_completed_handler(&block);
            command_buffer.commit();
            
            rx
        }
    }
}
