use std::fs::File;

use criterion::{criterion_group, criterion_main, Criterion, black_box};
use split_read::{Piece, Split};

#[no_mangle]
#[inline(never)]
fn bench_entry(c: &mut Criterion) {
    let path = "benches/sample/pci.ids";
    c.bench_function("pci.id", |b| b.iter(|| {
        let mut split = Split::<512,_>::read_lines(File::open(path).unwrap());
        loop { if let Piece::End = black_box(split.next_piece().unwrap()) { break } }
    }));
}

criterion_group!(benches, bench_entry);
criterion_main!(benches);

