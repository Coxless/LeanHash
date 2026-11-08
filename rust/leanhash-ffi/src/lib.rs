//! SMHasher3 に試作をリンクするための C ABI。鍵は呼び出し側（C++ の thread_local）に置く。

use leanhash::{v2, Keys};

/// `out` に v2 の鍵を書き込む。`out` は `leanhash_v2_keys_size()` バイト以上、8 バイト境界。
///
/// # Safety
/// `out` は書き込み可能で十分な大きさがあること。
#[no_mangle]
pub unsafe extern "C" fn leanhash_v2_keys_init(seed: u64, out: *mut v2::Keys) {
    out.write(v2::Keys::from_seed(seed));
}

#[no_mangle]
pub extern "C" fn leanhash_v2_keys_size() -> usize {
    core::mem::size_of::<v2::Keys>()
}

/// # Safety
/// `keys` は `leanhash_v2_keys_init` で初期化済み、`data` は `len` バイト読めること。
#[no_mangle]
pub unsafe extern "C" fn leanhash_v2c(keys: *const v2::Keys, data: *const u8, len: usize) -> u64 {
    v2::hash_c(&*keys, core::slice::from_raw_parts(data, len))
}

/// 素朴版（試作1）。比較用。
///
/// # Safety
/// `out` は書き込み可能で十分な大きさがあること。
#[no_mangle]
pub unsafe extern "C" fn leanhash_v1_keys_init(seed: u64, out: *mut Keys) {
    out.write(Keys::from_seed(seed));
}

#[no_mangle]
pub extern "C" fn leanhash_v1_keys_size() -> usize {
    core::mem::size_of::<Keys>()
}

/// # Safety
/// `keys` は初期化済み、`data` は `len` バイト読めること。
#[no_mangle]
pub unsafe extern "C" fn leanhash_v1_nh64(keys: *const Keys, data: *const u8, len: usize) -> u64 {
    leanhash::hash_nh64(&*keys, core::slice::from_raw_parts(data, len))
}
