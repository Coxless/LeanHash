#!/bin/bash
# SMHasher3 に LeanHash の試作（Rust staticlib）を組み込んだ版をビルドする。
# 上流のソース（bench SDK が ~/.local/src/smhasher3 に置いたもの）は汚さず、別ディレクトリに複製して改変する。
#   bench/smhasher3/build.sh            → ~/.local/opt/bin/SMHasher3-leanhash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
SRC="${SMHASHER3_SRC:-$HOME/.local/src/smhasher3}"
WORK="${SMHASHER3_WORK:-$HOME/.local/src/smhasher3-leanhash}"
OUT="${LEANHASH_TOOLS:-$HOME/.local/opt}/bin"

(cd "$ROOT/rust" && RUSTFLAGS="-C target-cpu=native" cargo build --release -q -p leanhash-ffi)
LIB="$ROOT/rust/target/release/libleanhash_ffi.a"

# build/ だけ残して作り直す（毎回まっさらな上流ソースに改変を当てる）
mkdir -p "$WORK"
find "$WORK" -mindepth 1 -maxdepth 1 ! -name build -exec rm -rf {} +
tar -C "$SRC" --exclude=./build --exclude=./.git -cf - . | tar -C "$WORK" -xf -
cp "$ROOT/bench/smhasher3/leanhash.cpp" "$WORK/hashes/leanhash.cpp"
sed -i 's|^  hashes/rust-rapidhash.cpp$|&\n  hashes/leanhash.cpp|' "$WORK/hashes/Hashsrc.cmake"
grep -q 'hashes/leanhash.cpp' "$WORK/hashes/Hashsrc.cmake"
cat >> "$WORK/CMakeLists.txt" <<CMAKE
target_link_libraries(SMHasher3Hashlib PUBLIC $LIB gcc_s util rt pthread m dl)
CMAKE
cmake -S "$WORK" -B "$WORK/build" -G Ninja -DCMAKE_BUILD_TYPE=Release >/dev/null
cmake --build "$WORK/build" -j"$(nproc)"
mkdir -p "$OUT"
cp "$WORK/build/SMHasher3" "$OUT/SMHasher3-leanhash"
echo "built $OUT/SMHasher3-leanhash"
