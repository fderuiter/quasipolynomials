#[cfg(feature = "gpu")]
pub trait MetalLayout {
    fn get_layout() -> String;
}

#[cfg(feature = "gpu")]
pub trait MetalPipeline {
    fn get_signature(kernel_name: &str) -> String;
    #[cfg(target_os = "macos")]
    fn bind(&self, encoder: &metal::ComputeCommandEncoderRef);
}

#[cfg(target_os = "macos")]
pub struct DeviceConstRef<T>(pub metal::Buffer, std::marker::PhantomData<T>);
#[cfg(target_os = "macos")]
pub struct DeviceConstPtr<T>(pub metal::Buffer, std::marker::PhantomData<T>);
#[cfg(target_os = "macos")]
pub struct DevicePtr<T>(pub metal::Buffer, std::marker::PhantomData<T>);
#[cfg(target_os = "macos")]
pub struct DeviceAtomicPtr<T>(pub metal::Buffer, std::marker::PhantomData<T>);
#[cfg(target_os = "macos")]
pub struct ConstantRef<T>(pub metal::Buffer, std::marker::PhantomData<T>);

#[cfg(target_os = "macos")]
impl<T> DeviceConstRef<T> {
    pub fn new(b: metal::Buffer) -> Self {
        Self(b, std::marker::PhantomData)
    }
}
#[cfg(target_os = "macos")]
impl<T> DeviceConstPtr<T> {
    pub fn new(b: metal::Buffer) -> Self {
        Self(b, std::marker::PhantomData)
    }
}
#[cfg(target_os = "macos")]
impl<T> DevicePtr<T> {
    pub fn new(b: metal::Buffer) -> Self {
        Self(b, std::marker::PhantomData)
    }
}
#[cfg(target_os = "macos")]
impl<T> DeviceAtomicPtr<T> {
    pub fn new(b: metal::Buffer) -> Self {
        Self(b, std::marker::PhantomData)
    }
}
#[cfg(target_os = "macos")]
impl<T> ConstantRef<T> {
    pub fn new(b: metal::Buffer) -> Self {
        Self(b, std::marker::PhantomData)
    }
}
