use criterion::{criterion_group, criterion_main, Criterion, SamplingMode};
use lib::{verify, Options};

pub fn criterion_benchmark(c: &mut Criterion) {
    let k = 40;
    let mut group = c.benchmark_group("experiment1");
    let options = Options {
        k,
        quiet: true,
        with_exceptional_clauses: true,
        heuristic: lib::Heuristic::DepthFirstSearch,
        visualize_heuristic: false,
        visualize_coverage: false,
    };
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);
    group.bench_function("One Node", |b| {
        b.iter(|| {
            verify(
                &["./benchmark_programs/experiment1/1Node.oox"],
                "Main",
                "test2",
                options,
            )
        })
    });
    group.bench_function("Two Nodes", |b| {
        b.iter(|| {
            verify(
                &["./benchmark_programs/experiment1/2Node.oox"],
                "Main",
                "test2",
                options,
            )
        })
    });
    group.bench_function("Three Nodes", |b| {
        b.iter(|| {
            verify(
                &["./benchmark_programs/experiment1/3Node.oox"],
                "Main",
                "test2",
                options,
            )
        })
    });
    group.bench_function("Four Nodes", |b| {
        b.iter(|| {
            verify(
                &["./benchmark_programs/experiment1/4Node.oox"],
                "Main",
                "test2",
                options,
            )
        })
    });
    // group.bench_function("Five Nodes", |b| b.iter(|| verify("./benchmark_programs/experiment1/5Node.oox", "Main", "test2", k)));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
