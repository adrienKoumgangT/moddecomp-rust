use std::hint::black_box;
use criterion::{criterion_group, criterion_main, Criterion};
use std::fs::File;
use std::io;
use std::io::{Read, Write};

use moddecomp::two_structure::{digraph_ex1, TwoStructure};
use moddecomp::moddecomp::moddecomp::modular_decomposition;


fn read_dot_file(filename: &str) -> io::Result<String> {
    let mut file = File::open(filename)?;
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    Ok(content)
}


fn criterion_benchmark(c: &mut Criterion) {
    let filename = "files/two_structure_undirected_nodes_1000_edges_100206.dot";
    let result_dot_content = read_dot_file(filename);
    let dot_content = result_dot_content.unwrap();

    let mut ts = TwoStructure::from_dot(&dot_content);

    c.bench_function("modular decomposition graph 1000 100206", |b| b.iter(|| modular_decomposition(black_box(&mut ts), black_box(None))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
