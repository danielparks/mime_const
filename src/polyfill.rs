//! Polyfill to support old versions of Rust

#[macro_export]
macro_rules! panic {
    ($e:expr) => {
        {
            #[allow(unconditional_panic, clippy::out_of_bounds_indexing)]
            let _: usize = [/* $e */][0];
            #[allow(clippy::empty_loop)]
            loop {}
        }
    };
    () => {
        panic!("panic")
    }
}

pub use panic;
