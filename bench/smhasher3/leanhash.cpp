/*
 * LeanHash P0' prototypes, linked from the Rust staticlib (rust/leanhash-ffi).
 * Built by bench/smhasher3/build.sh; not part of upstream SMHasher3.
 */
#include "Platform.h"
#include "Hashlib.h"

#include <cassert>

extern "C" {
size_t   leanhash_v2_keys_size( void );
void     leanhash_v2_keys_init( uint64_t seed, void * out );
uint64_t leanhash_v2c( const void * keys, const uint8_t * data, size_t len );
size_t   leanhash_v1_keys_size( void );
void     leanhash_v1_keys_init( uint64_t seed, void * out );
uint64_t leanhash_v1_nh64( const void * keys, const uint8_t * data, size_t len );
}

// SMHasher3 は seedfn の戻り値をそのまま seed_t として各ハッシュ呼び出しに渡す
alignas(64) static thread_local uint8_t v2_keys[2048];
alignas(64) static thread_local uint8_t v1_keys[512];

static uintptr_t v2_seed( const seed_t seed ) {
    assert(leanhash_v2_keys_size() <= sizeof(v2_keys));
    leanhash_v2_keys_init((uint64_t)seed, v2_keys);
    return (uintptr_t)(void *)v2_keys;
}

static uintptr_t v1_seed( const seed_t seed ) {
    assert(leanhash_v1_keys_size() <= sizeof(v1_keys));
    leanhash_v1_keys_init((uint64_t)seed, v1_keys);
    return (uintptr_t)(void *)v1_keys;
}

template <bool bswap>
static void LeanHash_v2c( const void * in, const size_t len, const seed_t seed, void * out ) {
    uint64_t h = leanhash_v2c((const void *)(uintptr_t)seed, (const uint8_t *)in, len);
    PUT_U64<bswap>(h, (uint8_t *)out, 0);
}

template <bool bswap>
static void LeanHash_v1( const void * in, const size_t len, const seed_t seed, void * out ) {
    uint64_t h = leanhash_v1_nh64((const void *)(uintptr_t)seed, (const uint8_t *)in, len);
    PUT_U64<bswap>(h, (uint8_t *)out, 0);
}

REGISTER_FAMILY(LeanHash,
   $.src_url    = "https://github.com/coxless/leanhash",
   $.src_status = HashFamilyInfo::SRC_ACTIVE
 );

REGISTER_HASH(LeanHash_v2c,
   $.desc            = "LeanHash P0' v2c (NH64 short / NH32x2 AVX2 + multiply-shift / poly mod 2^61-1, fmix64)",
   $.hash_flags      =
         FLAG_HASH_XL_SEED,
   $.impl_flags      =
         FLAG_IMPL_MULTIPLY_64_128 |
         FLAG_IMPL_LICENSE_MIT,
   $.bits            = 64,
   $.verification_LE = 0x0,
   $.verification_BE = 0x0,
   $.hashfn_native   = LeanHash_v2c<false>,
   $.hashfn_bswap    = LeanHash_v2c<true>,
   $.seedfn          = v2_seed
 );

REGISTER_HASH(LeanHash_v1,
   $.desc            = "LeanHash P0' v1 naive (NH64 128B blocks + poly mod 2^61-1, fmix64)",
   $.hash_flags      =
         FLAG_HASH_XL_SEED,
   $.impl_flags      =
         FLAG_IMPL_MULTIPLY_64_128 |
         FLAG_IMPL_LICENSE_MIT,
   $.bits            = 64,
   $.verification_LE = 0x0,
   $.verification_BE = 0x0,
   $.hashfn_native   = LeanHash_v1<false>,
   $.hashfn_bswap    = LeanHash_v1<true>,
   $.seedfn          = v1_seed
 );
