use criterion::{criterion_group, criterion_main, Criterion, SamplingMode, BenchmarkGroup, measurement::{Measurement, WallTime}};
use lib::{verify, Options};

fn options() -> Options<'static> {
    Options {
        k: 120,
        quiet: true,
        with_exceptional_clauses: true,
        heuristic: lib::Heuristic::DepthFirstSearch,
        visualize_heuristic: false,
        visualize_coverage: false,
        symbolic_array_size: 5,
        time_budget: 900,
        log_path: "./logs/log.txt",
        discard_logs: true,
        prune_path_z3: false,
        local_solving_threshold: Some(1000),
    }
}

fn experiment2<'a, M: Measurement>(c: &'a mut Criterion<M>) -> BenchmarkGroup<'a, M>{
    let options = options();
    let mut group = c.benchmark_group("experiment1");
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);
    group.bench_function("Array sorting functions", |b| {
        b.iter(|| {
            verify(
                &["./benchmark_programs/experiment2/array-sorting/sorting.oox"],
                "Main",
                "test",
                options,
            )
        })
    });
    group
}


criterion_group!(benches, experiment2);
criterion_main!(benches);
