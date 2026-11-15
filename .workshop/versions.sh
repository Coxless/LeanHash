# ツールのバージョン固定（変更はこのファイルだけで行う）。
# Lean 本体は /project/lean-toolchain、Rust は /project/rust-toolchain.toml が正。
ELAN_VERSION=v4.2.4
SMHASHER3_REPO=https://gitlab.com/fwojcik/smhasher3.git
SMHASHER3_REV=3b619371047761408406991685da1c2b3f751899
CLHASH_REPO=https://github.com/lemire/clhash.git
CLHASH_REV=c35030af08df1503e7b880435a804431f7ac73ca
AENEAS_REPO=https://github.com/AeneasVerif/aeneas.git
# lakefile.toml の aeneas の rev と同じにする。GitHub Releases の nightly-2026.11.09-5a392f4 にビルド済みバイナリがある
AENEAS_REV=5a392f4b80a4d0d05abc240eb2a7fa70622a9a35
OCAML_VERSION=5.3.0
