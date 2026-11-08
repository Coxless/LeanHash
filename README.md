# LeanHash

衝突確率の上界が Lean 4 で証明された、実用速度の 64bit 鍵付きハッシュ関数。
目的・設計・ロードマップは [CONCEPT.md](CONCEPT.md) を参照。

## 開発環境（Ubuntu Workshop）

[Canonical Workshop](https://ubuntu.com/workshop/docs/) の定義を `.workshop/` に置いている。
SDK はすべてリポジトリ内（in-project SDK）で、ストアの SDK には依存しない。

| ワークショップ | 用途 | SDK |
| :--- | :--- | :--- |
| `dev` | 通常開発（P0'〜P4） | `lean`, `rust`, `bench` |
| `verify` | Rust → Lean 抽出（P3.5） | `dev` の全部 ＋ `aeneas` |

| SDK | 入るもの | 版の固定場所 |
| :--- | :--- | :--- |
| `lean` | elan, Lean 4, Lake, Mathlib キャッシュ | `lean-toolchain`, `lakefile.toml` |
| `rust` | rustup, rustc/cargo, rustfmt, clippy | `rust-toolchain.toml` |
| `bench` | SMHasher3（XXH3・rapidhash・CLhash 等を内蔵）, CLHASH 単体, libxxhash, hyperfine | `.workshop/versions.sh` |
| `aeneas` | OCaml (opam), Charon, Aeneas | `.workshop/versions.sh` |

```bash
workshop launch dev
```

```bash
workshop run dev -- versions
```

```bash
workshop run dev -- lean-build
```

```bash
workshop shell dev
```

主な actions（`workshop actions dev` で一覧）:

- `versions` … 各ツールの版を表示
- `lean-build` / `lean-cache` … `lake build` / Mathlib キャッシュ取得
- `rust-test` / `rust-lint` … `rust/` の crate のテストと fmt・clippy
- `smhasher` … `SMHasher3` に引数を渡して実行（例: `smhasher --list`）
- `check` … Lean ビルドと Rust の lint・テストをまとめて実行
- `extract <crate>`（verify のみ）… Charon＋Aeneas で `LeanHash/Extracted/` に抽出

### 注意

- 初回 `launch` は Mathlib キャッシュ（数GB）と SMHasher3 のビルドで時間がかかる。`verify` は Aeneas のビルドでさらに 30 分以上かかる。
- Aeneas の Lean ライブラリ（固定コミット）は Lean v4.35.0 / Mathlib v4.35.0 を要求するため、本体の `lean-toolchain` も同じ版に揃えている。版を上げるときは `.workshop/versions.sh` の `AENEAS_REV` と一緒に動かす。
- `.workshop.lock` は launch 時に生成され、git 管理外。
- 試行錯誤の記録は `docs/journal/`（ルールは `CLAUDE.md`）。
