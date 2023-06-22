use criterion::{criterion_group, criterion_main, Criterion, SamplingMode, BenchmarkGroup, measurement::{Measurement, WallTime}};
use lib::{verify, Options, Heuristic};

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



fn experiment4<'a, M: Measurement>(c: &'a mut Criterion<M>) -> BenchmarkGroup<'a, M>{
    let path = "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/ArchiveOutputStream.oox ./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/ArchiveEntry.oox ./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Zip/* ./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/**/*.oox ./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/*.oox";
    let path: Vec<&str> = path.split(' ').collect();
    let mut options = options();
    let mut group = c.benchmark_group("experiment2.4");
    group.sample_size(1000);
    group.sampling_mode(SamplingMode::Flat);
    group.bench_function("Compress 3 --heuristic Depth First Search", |b| {
        b.iter(|| {
            verify(
                &path,
                "Main",
                "test_symbolic",
                options,
            )
        })
    });
    options.heuristic = Heuristic::MinDist2Uncovered;
    group.bench_function("Compress 3 --heuristic Min Dist 2 Uncovered", |b| {
        b.iter(|| {
            verify(
                &path,
                "Main",
                "test_symbolic",
                options,
            )
        })
    });
    options.heuristic = Heuristic::RandomPath;
    group.bench_function("Compress 3 --heuristic Random Path", |b| {
        b.iter(|| {
            verify(
                &path,
                "Main",
                "test_symbolic",
                options,
            )
        })
    });

    options.heuristic = Heuristic::RoundRobinMD2URandomPath;
    group.bench_function("Compress 3 --heuristic Round Robin MD2U & Random Path", |b| {
        b.iter(|| {
            verify(
                &path,
                "Main",
                "test_symbolic",
                options,
            )
        })
    });
    group
}

criterion_group!(benches, experiment4);
criterion_main!(benches);
