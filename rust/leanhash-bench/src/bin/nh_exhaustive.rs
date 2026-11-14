//! P2 のゲート：NH の ε-AU 定理（`LeanHash/Props/NH.lean` の `nh_eau`）を縮小版の全数検査で照合する。
//!
//! 定理: M ≠ M' なら、衝突する鍵の数 ≤ W^(2n−1)（確率 ≤ 1/W）。
//! 1 組の補題（証明の中で使う形）: 任意の c について、差 ≡ c となる鍵 (k1,k2) の数 ≤ W。
//!
//! 鍵をずらしても差は変わらない（u = m + k と置き換えると m' + k = u + δ、δ = m' − m）ので、
//! 衝突の数は差 δ だけで決まる。`pair` / `nh2` はこれを使って m = 0 に固定する。
//! `pair-full` は置き換えを使わずに全メッセージ対を数え、置き換えが正しいことも確かめる。
//!
//! 使い方: `cargo run --release -p leanhash-bench --bin nh_exhaustive -- <mode> <w> [...]`
//!   pair <w>              1 組、全 δ ≠ 0、全鍵、全 c（w ≤ 8）
//!   pair-full <w>         1 組、全 (m, m')、全鍵、全 c（w ≤ 4）
//!   nh2 <w>               2 組、全 δ ≠ 0、全鍵、c = 0（w ≤ 4）
//!   sample <w> <count> <seed>  1 組、無作為な δ、全鍵、c = 0（w = 16 用）
use std::thread;

fn threads() -> usize {
    thread::available_parallelism().map(|n| n.get()).unwrap_or(1)
}

/// 1 組の差 f(m + k) − f(m' + k) mod W²（f(a, b) = a·b、加算は mod W）。
#[inline(always)]
fn pd(w_mask: u64, w2_mask: u64, m: (u64, u64), mp: (u64, u64), k: (u64, u64)) -> u64 {
    let a = (m.0 + k.0) & w_mask;
    let x = (m.1 + k.1) & w_mask;
    let ap = (mp.0 + k.0) & w_mask;
    let xp = (mp.1 + k.1) & w_mask;
    (a * x).wrapping_sub(ap * xp) & w2_mask
}

/// δ ごとに全鍵の差のヒストグラムを作り、最大の山の高さを返す。
fn pair_max_for_delta(w: u32, d: (u64, u64), hist: &mut [u32]) -> (u32, bool) {
    let wm = (1u64 << w) - 1;
    let w2m = (1u64 << (2 * w)) - 1;
    hist.iter_mut().for_each(|h| *h = 0);
    let mut per_k1_ok = true;
    for k1 in 0..=wm {
        let mut seen: Vec<u64> = Vec::new();
        for k2 in 0..=wm {
            let c = pd(wm, w2m, (0, 0), d, (k1, k2));
            hist[c as usize] += 1;
            if d.0 != 0 {
                seen.push(c);
            }
        }
        if d.0 != 0 {
            // 1 語目が違えば、k1 を固定したとき各 c の解 k2 は高々 1 個（Lean の pd_inj2）
            seen.sort_unstable();
            if seen.windows(2).any(|p| p[0] == p[1]) {
                per_k1_ok = false;
            }
        }
    }
    (*hist.iter().max().unwrap(), per_k1_ok)
}

fn mode_pair(w: u32) {
    let big_w = 1u64 << w;
    let deltas: Vec<(u64, u64)> =
        (0..big_w).flat_map(|a| (0..big_w).map(move |b| (a, b))).filter(|&d| d != (0, 0)).collect();
    let t = threads();
    let chunk = deltas.len().div_ceil(t);
    let res: Vec<(u32, u64, bool)> = thread::scope(|s| {
        let hs: Vec<_> = deltas
            .chunks(chunk)
            .map(|ds| {
                s.spawn(move || {
                    let mut hist = vec![0u32; 1 << (2 * w)];
                    let (mut mx, mut at_max, mut ok) = (0u32, 0u64, true);
                    for &d in ds {
                        let (m, o) = pair_max_for_delta(w, d, &mut hist);
                        ok &= o;
                        if m > mx {
                            mx = m;
                            at_max = 0;
                        }
                        if m == mx {
                            at_max += 1;
                        }
                    }
                    (mx, at_max, ok)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mx = res.iter().map(|r| r.0).max().unwrap();
    let at_max: u64 = res.iter().filter(|r| r.0 == mx).map(|r| r.1).sum();
    let ok = res.iter().all(|r| r.2);
    println!(
        "pair w={w}: deltas={} max collisions over all c = {mx} (bound W = {big_w}) -> {}; deltas attaining max = {at_max}; per-k1 injectivity (pd_inj2) = {ok}",
        deltas.len(),
        if mx as u64 <= big_w { "OK" } else { "VIOLATED" }
    );
    assert!(mx as u64 <= big_w && ok);
}

fn mode_pair_full(w: u32) {
    let wm = (1u64 << w) - 1;
    let w2m = (1u64 << (2 * w)) - 1;
    let mut hist = vec![0u32; 1 << (2 * w)];
    let mut mx = 0u32;
    let mut mismatch = 0u64;
    for m0 in 0..=wm {
        for m1 in 0..=wm {
            for n0 in 0..=wm {
                for n1 in 0..=wm {
                    if (m0, m1) == (n0, n1) {
                        continue;
                    }
                    hist.iter_mut().for_each(|h| *h = 0);
                    for k1 in 0..=wm {
                        for k2 in 0..=wm {
                            hist[pd(wm, w2m, (m0, m1), (n0, n1), (k1, k2)) as usize] += 1;
                        }
                    }
                    let m = *hist.iter().max().unwrap();
                    mx = mx.max(m);
                    // 置き換え（m = 0、δ = m' − m）と同じ値になるか
                    let d = ((n0.wrapping_sub(m0)) & wm, (n1.wrapping_sub(m1)) & wm);
                    let mut h2 = vec![0u32; 1 << (2 * w)];
                    let (m_red, _) = pair_max_for_delta(w, d, &mut h2);
                    if m_red != m {
                        mismatch += 1;
                    }
                }
            }
        }
    }
    println!(
        "pair-full w={w}: max collisions over all (m,m',c) = {mx} (bound W = {}) -> {}; reduction mismatches = {mismatch}",
        1u64 << w,
        if mx as u64 <= 1u64 << w { "OK" } else { "VIOLATED" }
    );
    assert!(mx as u64 <= 1u64 << w && mismatch == 0);
}

fn mode_nh2(w: u32) {
    let wm = (1u64 << w) - 1;
    let w2m = (1u64 << (2 * w)) - 1;
    let big_w = 1u64 << w;
    let n_words = 1u64 << (4 * w); // δ と鍵はどちらも W^4 通り
    let word = |v: u64, i: u32| (v >> (w * i)) & wm;
    let t = threads() as u64;
    let res: Vec<(u64, u64)> = thread::scope(|s| {
        let hs: Vec<_> = (0..t)
            .map(|tid| {
                s.spawn(move || {
                    let (mut mx, mut at_max) = (0u64, 0u64);
                    let mut d = 1 + tid;
                    while d < n_words {
                        let d1 = (word(d, 0), word(d, 1));
                        let d2 = (word(d, 2), word(d, 3));
                        let mut cnt = 0u64;
                        for k in 0..n_words {
                            let k1 = (word(k, 0), word(k, 1));
                            let k2 = (word(k, 2), word(k, 3));
                            let s = pd(wm, w2m, (0, 0), d1, k1) + pd(wm, w2m, (0, 0), d2, k2);
                            if s & w2m == 0 {
                                cnt += 1;
                            }
                        }
                        if cnt > mx {
                            mx = cnt;
                            at_max = 0;
                        }
                        if cnt == mx {
                            at_max += 1;
                        }
                        d += t;
                    }
                    (mx, at_max)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mx = res.iter().map(|r| r.0).max().unwrap();
    let at_max: u64 = res.iter().filter(|r| r.0 == mx).map(|r| r.1).sum();
    let bound = big_w.pow(3);
    println!(
        "nh2 w={w}: keys={n_words} max collisions = {mx} (bound W^3 = {bound}) -> {}; deltas attaining max = {at_max}",
        if mx <= bound { "OK" } else { "VIOLATED" }
    );
    assert!(mx <= bound);
}

fn splitmix64(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn mode_sample(w: u32, count: usize, seed: u64) {
    let wm = (1u64 << w) - 1;
    let w2m = (1u64 << (2 * w)) - 1;
    let mut s = seed;
    let mut deltas = Vec::new();
    // 端の値（1 語目だけ違う・2 語目だけ違う・最大）も入れる
    deltas.extend([(1, 0), (0, 1), (wm, wm), (1 << (w - 1), 0), (1, 1)]);
    while deltas.len() < count {
        let d = (splitmix64(&mut s) & wm, splitmix64(&mut s) & wm);
        if d != (0, 0) {
            deltas.push(d);
        }
    }
    let t = threads() as u64;
    let mut mx = 0u64;
    for d in deltas {
        let cnt: u64 = thread::scope(|sc| {
            let hs: Vec<_> = (0..t)
                .map(|tid| {
                    sc.spawn(move || {
                        let mut c = 0u64;
                        let mut k1 = tid;
                        while k1 <= wm {
                            for k2 in 0..=wm {
                                if pd(wm, w2m, (0, 0), d, (k1, k2)) == 0 {
                                    c += 1;
                                }
                            }
                            k1 += t;
                        }
                        c
                    })
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).sum()
        });
        println!("  delta=({:#x},{:#x}) collisions={cnt}", d.0, d.1);
        mx = mx.max(cnt);
    }
    println!(
        "sample w={w}: max collisions (c=0) = {mx} (bound W = {}) -> {}",
        1u64 << w,
        if mx <= 1u64 << w { "OK" } else { "VIOLATED" }
    );
    assert!(mx <= 1u64 << w);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let arg = |i: usize| args[i].parse::<u64>().unwrap();
    match args.get(1).map(String::as_str) {
        Some("pair") => mode_pair(arg(2) as u32),
        Some("pair-full") => mode_pair_full(arg(2) as u32),
        Some("nh2") => mode_nh2(arg(2) as u32),
        Some("sample") => mode_sample(arg(2) as u32, arg(3) as usize, arg(4)),
        _ => eprintln!("usage: nh_exhaustive pair|pair-full|nh2 <w> | sample <w> <count> <seed>"),
    }
}
