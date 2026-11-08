//! P0' 速度比較。入力長ごとに ns/hash、GB/s、TSC cycles/byte を測る。
//!
//! 使い方: `cargo run --release -p leanhash-bench -- [--quick] [--csv out.csv]`
//! CLHASH も比べるときは `CLHASH_DIR=~/.local/src/clhash` を付けてビルドする。
//!
//! 計測法: 1 MiB のランダムバッファ上で開始位置をずらしながら同じ長さの入力をハッシュし、
//! 結果を XOR で畳み込んで最適化を防ぐ（スループット計測。直前の結果に依存しない）。
//! 1 回あたり約 `TARGET_MS` ミリ秒の計測を `RUNS` 回行い、中央値を取る。

use std::hash::{BuildHasher, Hasher};
use std::hint::black_box;
use std::time::Instant;

const BUF: usize = 1 << 21;
const SIZES: &[usize] = &[
    0, 3, 8, 16, 24, 32, 64, 100, 128, 256, 512, 1024, 4096, 16384, 65536, 1 << 20,
];

#[cfg(have_clhash)]
mod clhash_ffi {
    use std::ffi::{c_char, c_void};
    extern "C" {
        pub fn get_random_key_for_clhash(seed1: u64, seed2: u64) -> *mut c_void;
        pub fn clhash(random: *const c_void, s: *const c_char, len: usize) -> u64;
    }
}

type HashFn = Box<dyn Fn(&[u8]) -> u64>;

fn hashers(seed: u64) -> Vec<(&'static str, HashFn)> {
    let k = leanhash::Keys::from_seed(seed);
    let k2 = k.clone();
    let kv2 = leanhash::v2::Keys::from_seed(seed);
    let kv2b = kv2.clone();
    let kv2c = kv2.clone();
    let rs = rapidhash::v3::RapidSecrets::seed(seed);
    let fold = foldhash::fast::FixedState::with_seed(seed);
    let foldq = foldhash::quality::FixedState::with_seed(seed);
    let ah = ahash::RandomState::with_seeds(seed, 1, 2, 3);
    let poly = polymur_hash::PolymurHash::from_u64_seed(seed);
    #[allow(unused_mut)]
    let mut v: Vec<(&'static str, HashFn)> = vec![
        ("leanhash-v2", Box::new(move |d| leanhash::v2::hash(&kv2, d))),
        ("leanhash-v2b", Box::new(move |d| leanhash::v2::hash_b(&kv2b, d))),
        ("leanhash-v2c", Box::new(move |d| leanhash::v2::hash_c(&kv2c, d))),
        ("leanhash-nh64", Box::new(move |d| leanhash::hash_nh64(&k, d))),
        ("leanhash-nh32", Box::new(move |d| leanhash::hash_nh32(&k2, d))),
        ("xxh3-64", Box::new(move |d| xxhash_rust::xxh3::xxh3_64_with_seed(d, seed))),
        ("rapidhash-v3", Box::new(move |d| rapidhash::v3::rapidhash_v3_seeded(d, &rs))),
        ("foldhash-fast", Box::new(move |d| {
            let mut h = fold.build_hasher();
            h.write(d);
            h.finish()
        })),
        ("foldhash-quality", Box::new(move |d| {
            let mut h = foldq.build_hasher();
            h.write(d);
            h.finish()
        })),
        ("polymurhash", Box::new(move |d| poly.hash(d))),
        ("ahash", Box::new(move |d| {
            let mut h = ah.build_hasher();
            h.write(d);
            h.finish()
        })),
    ];
    #[cfg(have_clhash)]
    {
        let key = unsafe { clhash_ffi::get_random_key_for_clhash(seed, !seed) } as usize;
        v.push(("clhash", Box::new(move |d| unsafe {
            clhash_ffi::clhash(key as *const _, d.as_ptr() as *const _, d.len())
        })));
    }
    v
}

#[cfg(target_arch = "x86_64")]
fn tsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}
#[cfg(not(target_arch = "x86_64"))]
fn tsc() -> u64 {
    0
}

struct Sample {
    ns_per_hash: f64,
    cyc_per_hash: f64,
}

fn run_once(f: &HashFn, buf: &[u8], n: usize, iters: usize) -> (f64, f64) {
    let span = buf.len() - n;
    let step = 64usize.max(n.next_power_of_two().min(4096)) + 8; // 開始位置を毎回ずらす
    let t = Instant::now();
    let c0 = tsc();
    let mut acc = 0u64;
    let mut off = 0usize;
    for _ in 0..iters {
        acc ^= f(black_box(&buf[off..off + n]));
        off += step;
        if off > span {
            off -= span;
        }
    }
    black_box(acc);
    let c1 = tsc();
    (t.elapsed().as_secs_f64() * 1e9 / iters as f64, (c1 - c0) as f64 / iters as f64)
}

/// 同じ入力長について全ハッシュを交互に測る（VM の速度の揺れが特定のハッシュに偏らないように）。
fn measure_all(hs: &[(&'static str, HashFn)], buf: &[u8], n: usize, target_ms: f64, runs: usize) -> Vec<Sample> {
    let iters: Vec<usize> = hs
        .iter()
        .map(|(_, f)| {
            let mut it = 1usize;
            loop {
                let (ns, _) = run_once(f, buf, n, it);
                let ms = ns * it as f64 / 1e6;
                if ms > target_ms / 4.0 {
                    break ((it as f64) * target_ms / ms).max(1.0) as usize;
                }
                it *= 4;
            }
        })
        .collect();
    let mut ns = vec![Vec::new(); hs.len()];
    let mut cyc = vec![Vec::new(); hs.len()];
    for _ in 0..runs {
        for (i, (_, f)) in hs.iter().enumerate() {
            let (a, c) = run_once(f, buf, n, iters[i]);
            ns[i].push(a);
            cyc[i].push(c);
        }
    }
    let med = |mut v: Vec<f64>| {
        v.sort_by(|a, b| a.partial_cmp(b).unwrap());
        v[v.len() / 2]
    };
    ns.into_iter()
        .zip(cyc)
        .map(|(a, c)| Sample { ns_per_hash: med(a), cyc_per_hash: med(c) })
        .collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let quick = args.iter().any(|a| a == "--quick");
    let csv = args.iter().position(|a| a == "--csv").map(|i| args[i + 1].clone());
    let (target_ms, runs) = if quick { (10.0, 5) } else { (40.0, 15) };

    let mut s = 0x1234_5678u64;
    let buf: Vec<u8> = (0..BUF)
        .map(|_| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s as u8
        })
        .collect();

    let hs = hashers(0xdead_beef);
    let mut rows = Vec::new();
    println!("| size | {} |", hs.iter().map(|h| h.0).collect::<Vec<_>>().join(" | "));
    println!("|---:|{}", "---:|".repeat(hs.len()));
    for &n in SIZES {
        let mut cells = Vec::new();
        let samples = measure_all(&hs, &buf, n, target_ms, runs);
        for ((name, _), r) in hs.iter().zip(samples) {
            let gbs = if n == 0 { 0.0 } else { n as f64 / r.ns_per_hash };
            let cpb = if n == 0 { 0.0 } else { r.cyc_per_hash / n as f64 };
            rows.push(format!("{name},{n},{:.3},{:.3},{:.4}", r.ns_per_hash, gbs, cpb));
            cells.push(if n >= 1024 {
                format!("{gbs:.2} GB/s")
            } else {
                format!("{:.2} ns", r.ns_per_hash)
            });
        }
        println!("| {n} | {} |", cells.join(" | "));
    }
    if let Some(path) = csv {
        let mut out = String::from("hash,size,ns_per_hash,gb_per_s,tsc_cycles_per_byte\n");
        for r in rows {
            out.push_str(&r);
            out.push('\n');
        }
        std::fs::write(&path, out).unwrap();
        eprintln!("wrote {path}");
    }
}
