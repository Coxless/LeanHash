# 2026-11-10 経路ごとに独立な fin（v2c の変更）と、1KB 以下全体の ε の定理

ブランチ `ccr-ee5848fc-6dhgaa`。前の作業: [P2 残り](2026-11-09-p2-rest.md)。

## 目的

- P2 で見つけた穴「経路をまたぐ 2 入力（≤ 32B の NH64 経路と 33B〜1KB の NH32×2 経路）の衝突確率が証明できない」を、
  経路ごとに独立な fin を使う形で塞ぐ（2026-11-10 ユーザー承認）
- Rust 試作を変え、SMHasher3 を再実行する
- Lean で「1KB 以下の違う 2 入力なら、どの組み合わせでも ε ≤ 2⁻⁶²」を 1 本の定理にする

## 環境

- クラウドセッション、Intel Xeon @ 2.30GHz、4 コア、メモリ 15GB
- Lean 4.35.0、Mathlib v4.35.0、rustc 1.97.0、SMHasher3 `3b619371`、cmake / ninja は apt

## 試したこと

### Rust 試作（`rust/leanhash/src/v2.rs`）

- `Keys` に `fin_mid`（33〜1024 の NH32×2 経路）と `fin_long`（1KB より長い経路）を足した。`fin` は 1KB 以下の NH64 経路（v2c では 32B 以下）のまま
- `from_seed` では追加の鍵を最後に引くので、既存の鍵（nh、m、r、fin）の値は変わらない。32B 以下の出力は前と同じ
- `lean_spec_matches_hash_c`（Lean の仕様を写したテスト）も経路ごとの fin に合わせた
- `cargo test -p leanhash`: 17 passed（既定のビルドと `RUSTFLAGS="-C target-cpu=native"` の両方）
- 速度は測り直していない。変わったのは XOR する定数の読み込み先だけ

### SMHasher3

```sh
apt-get install -y cmake ninja-build
git clone https://gitlab.com/fwojcik/smhasher3.git ~/.local/src/smhasher3 && git -C ~/.local/src/smhasher3 checkout 3b619371
LEANHASH_TOOLS=$HOME/.local/opt bash bench/smhasher3/build.sh      # 56 秒
~/.local/opt/bin/SMHasher3-leanhash --ncpu=4 LeanHash-v2c > bench/results/2026-11-10-smhasher3-quality-v2c-per-path-fin.txt
```

- **188 / 188 PASS**（637 秒）。`!!!!!` は 0 件、-log2(p) の最大は 11（前回 run2 は 10。目安の 25 よりずっと下）
- 検証値 LE: `0xD8FD2032` → `0xA4C9FC72`
- 訂正: [P2 残りの journal](2026-11-09-p2-rest.md) で「検証値（0xAEF37E4F）が変わる」と書いたが、0xAEF37E4F は SeedZeroes 修正前（run1）の値。修正後の値は 0xD8FD2032 だった

### Lean（`LeanHash/Props/Le1K.lean`）

- 鍵は Rust と同じ「u64 × 130 語」（`Words`）で持ち、経路 A は語 2i, 2i+1 を組 i（`eA`）、経路 B は語 i の下位・上位 32bit をレーン i（`eB`）として読む。どちらも全単射（`Equiv`）なので、一様性がそのまま移る
- `hash1K`：L ≤ 32 なら経路 A と fin、それ以外は経路 B と fin_mid
- `le1K_eps`：1024 バイト以下の違う 2 入力について、鍵 (w, m, fin, fin_mid) が一様なら Pr[衝突] ≤ 2⁻⁶²
  - 同じ経路: fin は衝突に関係しないので約分し、鍵の読み方を全単射で移して `pathA_eps` / `pathB_eps`（2⁻⁶⁴ + 2⁻⁶³）
  - 経路が違う: (w, m) をどう固定しても衝突する (fin, fin_mid) はちょうど 2⁶⁴ 組（`card_out_collide`）→ 2⁻⁶⁴
- `#print axioms le1K_eps` → `[propext, Classical.choice, Quot.sound, xsr33_involutive._native.bv_decide.ax_1_5]`（最後は P1 の xorshift の `bv_decide`）

#### 行き止まり

- **メモリ不足で 2 回 kill された。** 原因は `push_cast` と `exact_mod_cast` が `Fintype.card Words` を `(2^64)^130` に展開し、さらにその数を計算しようとしたこと。`#exit` を途中に入れて切り分けた
  - → 鍵の数は `simp` 系に触らせない。`Nat.cast_pos.mpr Fintype.card_pos` と `rw [Nat.cast_mul, …]` だけで扱い、約分は抽象的な補題（`ratio_cancel`、`ratio_cross`、変数 W, O で証明）に出した
  - 1 回目の kill は SMHasher3（4 スレッド）と Lean が同時に走っていたときだった。SMHasher3 の結果には影響がなかった（188/188、正常終了）
- `rw [card_prod_const _ _ …]` は `P p.1 p.2` の形の高階の単一化に失敗し、`refine cross _ …` は `maximum recursion depth`。P を明示的に渡したら通った
- `Fin.ext (by simp only [Fin.val_mk]; omega)` は「`Fin.val_mk` は使われていない」と警告が出るが、外すと omega が `↑⟨2 * (j / 2), _⟩` を原子として扱って失敗する。`dsimp only` で射影を簡約してから omega にした
- `card_equiv_keys` で linter（`constructorNameAsVariable`）自体が recursion depth で落ちたので、その定理だけ linter を切った

## 決めたこと

- v2c の仕上げの XOR 定数は経路ごとに独立（`fin` / `fin_mid` / `fin_long`）。速度への影響なし
- 1KB 以下の ε の主張は `le1K_eps`（≤ 2⁻⁶²、全組み合わせ）

## 次にやること

- P2.5: 長い入力（> 1KB）。多項式 mod 2⁶¹−1 の段と NH32×2 のブロック出力の合成。1KB 以下の経路とのまたぎは `fin_long` で同じ議論（`card_out_collide`）が使える
