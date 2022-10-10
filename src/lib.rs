#![deny(missing_docs)]
//! block_stm implementation
use executor::Executor;
use mvmemory::MVMemory;
use once_cell::sync::Lazy;
use scheduler::Scheduler;
use std::marker::PhantomData;
use traits::{Storage, Transaction, VM};

mod executor;
mod log;
mod mvmemory;
mod scheduler;
mod sync;
/// test utils used by benches and tests
pub mod test_utils;
/// public abstract traits
pub mod traits;
mod types;

static RAYON_EXEC_POOL: Lazy<rayon::ThreadPool> = Lazy::new(|| {
    rayon::ThreadPoolBuilder::new()
        .num_threads(num_cpus::get())
        .thread_name(|index| format!("rayon_exec_pool_{}", index))
        .build()
        .unwrap()
});
/// parallel executor
pub struct ParallelExecutor<T, S, V>
where
    T: Transaction,
    S: Storage<T = T>,
    V: VM<T = T, S = S>,
{
    concurrency_level: usize,
    phantom: PhantomData<(T, S, V)>,
}
impl<T, S, V> ParallelExecutor<T, S, V>
where
    T: Transaction,
    S: Storage<T = T>,
    V: VM<T = T, S = S>,
{
    fn thread_task(
        txns: &[T],
        view: &S,
        mvmemory: &MVMemory<T::Key, T::Value>,
        scheduler: &Scheduler,
    ) {
        let vm = V::new();
        let task = Executor::new(vm, txns, view, mvmemory, scheduler);
        task.run();
        rayon_debug!("task finished");
    }
}
impl<T, S, V> ParallelExecutor<T, S, V>
where
    T: Transaction,
    S: Storage<T = T>,
    V: VM<T = T, S = S>,
{
    /// create a parallel executor
    pub fn new(concurrency_level: usize) -> Self {
        assert!(
            concurrency_level > 0 && concurrency_level <= num_cpus::get(),
            "concurrency level {} should be between 1 and number of CPUs",
            concurrency_level
        );
        Self {
            concurrency_level,
            phantom: PhantomData,
        }
    }
    /// parallel execute a batch of txns
    pub fn execute_transactions(&self, txns: &Vec<T>, view: &S) -> Vec<(T::Key, T::Value)> {
        let txns_num = txns.len();
        let mvmemory = MVMemory::new(txns_num);
        let scheduler = Scheduler::new(txns_num);
        RAYON_EXEC_POOL.scope(|s| {
            for _ in 0..self.concurrency_level {
                s.spawn(|_| {
                    ParallelExecutor::<T, S, V>::thread_task(txns, view, &mvmemory, &scheduler);
                });
            }
        });
        mvmemory.snapshot()
    }
}
