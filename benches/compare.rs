use std::io::{BufReader, BufRead};

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use split_read::Piece;

const DATA: [(&str, &[u8]);3] = [
    ("tiny", include_bytes!("sample/tiny.txt")),
    ("medium", include_bytes!("sample/alice29.txt")),
    ("medium-large", include_bytes!("sample/pci.ids")),
];

#[no_mangle]
#[inline(never)]
pub fn bench_std_iter(input: &[u8]) -> usize {
    input.split(|&b| b == b'\n').map(|l| l.len()).sum::<usize>()
}

#[no_mangle]
#[inline(never)]
pub fn bench_std_lines(input: &[u8]) -> usize {
    BufReader::new(input).lines().map(|l| l.unwrap().as_bytes().len()).sum::<usize>()
}

#[no_mangle]
#[inline(never)]
fn bench_entry(c: &mut Criterion) {
    let mut g = c.benchmark_group("Compare");
    for (input_name, input) in DATA {
        g.bench_with_input(BenchmarkId::new("slice::split", input_name), input, |b, input| b.iter(|| {
            bench_std_iter(input)
        }));
        g.bench_with_input(BenchmarkId::new("std::io::Lines", input_name), input, |b, input| b.iter(|| {
            bench_std_lines(input)
        }));
        g.bench_with_input(BenchmarkId::new("split_read", input_name), input, |b, input| b.iter(|| {
            let mut r = split_read::Split::<512,_>::read_lines(input);
            let mut n = 0usize;
            while let Piece::Terminal(bs) |  Piece::Partial(bs) = r.next_piece().unwrap() { n += bs.len() } 
            n
        }));
    }
}

criterion_group!(benches, bench_entry);
criterion_main!(benches);

