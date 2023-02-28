use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, Criterion, SamplingMode};
use lib::verify;

pub fn criterion_benchmark(c: &mut Criterion) {
    let k = 40;
    let mut group = c.benchmark_group("experiment1");
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);
    group.bench_function("One Node", |b| b.iter(|| verify("./benchmark_programs/experiment1/1Node.oox", "Main", "test2", k, true)));
    group.bench_function("Two Nodes", |b| b.iter(|| verify("./benchmark_programs/experiment1/2Node.oox", "Main", "test2", k, true)));
    group.bench_function("Three Nodes", |b| b.iter(|| verify("./benchmark_programs/experiment1/3Node.oox", "Main", "test2", k, true)));
    group.bench_function("Four Nodes", |b| b.iter(|| verify("./benchmark_programs/experiment1/4Node.oox", "Main", "test2", k, false)));
    // group.bench_function("Five Nodes", |b| b.iter(|| verify("./benchmark_programs/experiment1/5Node.oox", "Main", "test2", k)));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);