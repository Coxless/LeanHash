# LeanHash

衝突確率の上界を Lean 4 で証明した、実用速度の 64bit 鍵付きハッシュ（Rust の `BuildHasher`）。
目的・設計・保証範囲・ロードマップは `CONCEPT.md` が正。

## 構成

- `LeanHash/` … Lean の仕様・証明（Lake、Mathlib）。`rust/` … crate とベンチ
- `.workshop/` … Ubuntu Workshop 定義（`dev` / `verify`）。ツールの版は `.workshop/versions.sh`、`lean-toolchain`、`rust-toolchain.toml` だけで固定する
- `docs/journal/` … 試行錯誤の記録（下記）

## 試行錯誤の記録（必須）

作業ごとに `docs/journal/YYYY-MM-DD-<topic>.md` を作り、作業しながら追記する（終わってからまとめない）。

- 書くこと: 目的 / 試したこと（再現できるコマンド）/ 結果（数値・エラーは原文の要点）/ 失敗・行き止まりとその理由 / 決めたこと / 次にやること
- 失敗や捨てた案ほど残す。成功した手順だけにしない
- 計測値には環境（CPU、コア数、ツールの版）を添える
- `CONCEPT.md` に影響する決定（目標値、未解決の問い）は `CONCEPT.md` も更新し、根拠の journal へリンクする

## 守ること

- main に `sorry` を入れない。証明できない性質（暗号学的衝突耐性、鍵漏洩時の安全性、下位ビットだけの衝突確率）は主張しない
- 64bit 乗算を `bv_decide` に投げない（代数的補題で処理し、SAT はシフト/XOR に限定）
- 計算の核は HashIR から生成する方針。手書きの Rust 実装は試作・差分テスト用と明記する

## クラウドセッションでの注意

- LXD がないため `workshop` は動かない。フックを `bash -eo pipefail .workshop/<sdk>/hooks/setup-project` で直接実行して代用する（`/project` → リポジトリのシンボリックリンクが必要）
- release.lean-lang.org はネットワーク方針で遮断されている。Lean は GitHub Releases（`leanprover/lean4`）から直接取得する
