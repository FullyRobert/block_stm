use block_stm::{reorder::transaction_reorder, test_utils::simulated::*};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use pprof::criterion::{Output, PProfProfiler};
const TXNS_NUM: usize = 1_000;

fn reorder_block_size(c: &mut Criterion) {
    let mut group = c.benchmark_group("reorder_block_size");
    group.throughput(Throughput::Elements(TXNS_NUM as u64));
    for accounts_num in [2, 10, 100, 1000] {
        let (txns, _ledger) = generate_txns_and_ledger(accounts_num, 1_000_000, TXNS_NUM, 1, 1000);
        group.bench_with_input(
            BenchmarkId::new("txn reordering", accounts_num),
            &accounts_num,
            |b, _| b.iter(|| transaction_reorder(&txns)),
        );
    }
    group.finish();
}

criterion_group!(
    name = benches;
    config=Criterion::default().with_profiler(PProfProfiler::new(100,Output::Flamegraph(None))).sample_size(10);
    targets= reorder_block_size);
criterion_main!(benches);
