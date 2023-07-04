use criterion::{criterion_group, criterion_main, Criterion, SamplingMode, BenchmarkGroup, measurement::{Measurement}};
use lib::{verify, Options};

fn options() -> Options<'static> {
    Options {
        k: 60,
        quiet: true,
        with_exceptional_clauses: true,
        heuristic: lib::Heuristic::DepthFirstSearch,
        visualize_heuristic: false,
        visualize_coverage: false,
        symbolic_array_size: 3,
        time_budget: 900,
        log_path: "./logs/log.txt",
        discard_logs: true,
        prune_path_z3: false,
        local_solving_threshold: Some(1000),
    }
}

fn experiment1<'a, M: Measurement>(c: &'a mut Criterion<M>) -> BenchmarkGroup<'a, M>{
    let options = options();
    let mut group = c.benchmark_group("experiment1");
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
    group
}


criterion_group!(benches, experiment1);
criterion_main!(benches);
