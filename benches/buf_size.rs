use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use split_read::Piece;

const DATA: [(&str, &[u8]);3] = [
    ("tiny", include_bytes!("sample/tiny.txt")),
    ("medium", include_bytes!("sample/alice29.txt")),
    ("medium-large", include_bytes!("sample/pci.ids")),
];

fn run<const N: usize>(input: &[u8]) -> usize {
    let mut r = split_read::Split::<N,_>::bytes_lines(&input);
    let mut n = 0usize;
    while let Piece::Terminal(bs) |  Piece::Partial(bs) = r.next_piece().unwrap() { n = n.wrapping_add(bs.len()) } 
    n
}

#[no_mangle]
#[inline(never)]
fn bench_entry(c: &mut Criterion) {
    for (input_name, input) in DATA {
        let mut g = c.benchmark_group("Buffer");
        {
            macro_rules! bench { ($($n:expr),+ $(,)?) => { $(g.bench_function(BenchmarkId::new(input_name, stringify!($n)), |b| b.iter(|| run::<$n>(input)));)+ }; }
            bench!(
                //2, 4, 8,
                16, 32,
                64, 128,
                256, 512, 1024, 2048,
                // 4096, 8192,
                //16384, 32768
                );
        };
    }
}

criterion_group!(benches, bench_entry);
criterion_main!(benches);

