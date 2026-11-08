# 2026-11-08 開発環境（Ubuntu Workshop）の準備

## 目的

CONCEPT の P0'〜P4 に必要なツール（Lean 4 / Mathlib、Rust、SMHasher3、CLHASH、Charon + Aeneas）を
Ubuntu Workshop の定義ファイルで再現可能に用意する。

## 試したこと・結果

### Workshop の仕様調査

- Workshop は 2026-05 公開の新しいツール。定義は `workshop.yaml` か `.workshop/<NAME>.yaml`。トップレベルキーは `name` / `base` / `runtime` / `sdks` / `connections` / `actions` のみ（apt パッケージや環境変数のキーはない）
- インストール処理は SDK のフック（`hooks/setup-base` は root、`hooks/setup-project` は workshop ユーザー）に書く
- ストアに Rust / Lean の SDK があるか確認できなかった → **すべて in-project SDK（`.workshop/<name>/`）にした**
- ドキュメント内の食い違い: in-project の `sdk.yaml` で必須の項目が、表では `name` だけ、JSON Schema では `version` や `summary` なども必須。安全側に `name` / `version` / `summary` / `description` を書いた。**実機で未確認**

### 版の固定

- Mathlib の安定タグの最新は `v4.35.0`（master は `v4.36.0-rc2`）
- Aeneas の固定コミット `698a336` の `backends/lean/lean-toolchain` が `v4.35.0`、Mathlib も `v4.35.0` → 本体も v4.35.0 に揃えた（P3.5 で同じ Lake プロジェクトに Aeneas を依存として足せる）
- Rust はコンテナの既存版 1.97.0 に固定

### このコンテナでのフック実行（LXD がないため直接実行）

| フック | 結果 |
| :--- | :--- |
| rust/setup-project | 成功。新しい rustup は `rustup show` で自動インストールしないため、`rustup toolchain install`（引数なしで rust-toolchain.toml を読む）に変更 |
| bench/setup-project | 初回失敗: `ln: failed to create symbolic link '~/.local/bin/SMHasher3'`（ディレクトリ未作成）→ `mkdir -p "$HOME/.local/bin"` を追加して成功。2回目はビルドをスキップ |
| lean/setup-project | 失敗: elan-init が release.lean-lang.org から取得しようとし、クラウド環境のプロキシに遮断された（`connect_rejected`）。実機では問題にならない想定 |
| aeneas/setup-project | 未実行（ビルドに 30 分以上） |

- Lean は GitHub Releases の `lean-4.35.0-linux.tar.zst` を直接取得して確認。展開に `zstd` が必要だった（lean SDK の setup-base には入れてある）
- `lean LeanHash/Spec/Mix.lean` で `xs_involutive` が `bv_decide` により約 0.9 秒で通った
- SMHasher3（`20260827-main-3b619371`）は XXH3、rapidhash（v3、micro/nano/protected 含む）、CLhash（素の版と `.bitmix` 版）を内蔵していた → 比較対象の多くはここで揃う

## 決めたこと

- ワークショップは `dev`（lean, rust, bench）と `verify`（+ aeneas）の2つに分ける。Aeneas のビルド失敗が通常開発を止めないため
- ツールの版は `.workshop/versions.sh` / `lean-toolchain` / `rust-toolchain.toml` の3か所だけで管理する

## 未確認・次

- 実機で `workshop launch dev` / `verify` を通す（sdk.yaml の必須項目、actions の PATH、check-health の挙動）
- `lake exe cache get` で Mathlib キャッシュが取れるか（クラウドでは未実行）
