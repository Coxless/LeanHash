# LeanHash CONCEPT

> 「CLHASH の系譜を、HACL* のやり方で、Lean 4 上に作る」
>
> 衝突確率の上界が **証明された**、実用速度の 64bit 鍵付きハッシュ関数（Rust の `BuildHasher`）。

策定日: 2026-11-08（検討結果 第5章より抽出）
詳細な検討経緯: [Lean 4で目指す次世代ハッシュ関数：歴史から導く設計方針とロードマップ](https://claude.ai/artifact/V31Po15xo27JgmtyHTr3PA)

---

## 1. 背景と位置づけ

ハッシュ関数の系譜は次の4つに分けられる。LeanHash は「理論」の系譜の関数を、「検証」の手法で作る。

| 系譜 | 目指すもの | 品質の根拠 | 代表例 |
| :--- | :--- | :--- | :--- |
| 非暗号 | 速く偏りなく散らす | 実験（SMHasher） | FNV、Murmur、xxHash、rapidhash |
| 理論 | 鍵を乱択すれば任意入力で衝突確率 ≤ ε | 数学的証明 | Carter–Wegman、multiply-shift、UMAC/NH、CLHASH |
| 暗号 | 攻撃者でも衝突・原像を見つけられない | 長年の暗号解析（計算量的仮定） | SHA-2/3、BLAKE3、SipHash、Poseidon |
| 検証 | 既存関数の実装が仕様どおりであることを保証 | 定理証明支援系 | HACL*、LNSym、bv_decide、Clean |

「検証」だけは設計思想ではなく手法の系譜で、軸が異なる。

### 1.1 採用したアプローチ

| 案 | 評価 | 扱い |
| :--- | :--- | :--- |
| ① 仕様 ⇔ 最適化実装の等価証明 | ◎ `BitVec` / `bv_decide`、LNSym・sha2-fv の前例あり | **採用**（実装の正しさ） |
| ② 一様分布性の検証 | 鍵なしでは原理的に不可能（鳩の巣原理）。ε-AU に問いを立て直せば証明可能 | **採用**（ε-AU として） |
| ③ ZK ハッシュ | 安全性は定理化困難、回路等価性は可能 | 対象外 |

### 1.2 空白地帯（＝本プロジェクトの新規性）

最も近い先行例は **PolymurHash**（多項式 mod 2⁶¹−1、n バイトで衝突確率 ≤ n·2⁻⁶⁰·²、証明は手書き）。P0' で見つけた（[journal](docs/journal/2026-11-08-p0prime-prototype.md)）。LeanHash との差は「機械検証」と「NH 段による長さに強い上界」。

先行研究調査で見つからなかったもの:

- 非暗号ハッシュ（xxHash、rapidhash 等）の実装検証
- Lean 4 でのユニバーサルハッシュ（NH 等）の ε-AU 証明
- 「証明付き衝突上界」と「実用速度」を両立する非暗号ハッシュ設計
- folded multiply の非単射性の形式化

---

## 2. 設計原則（歴史からの教訓）

1. **鍵なしの品質保証は破られる。** Murmur/CityHash は SMHasher 通過後にシード非依存の多重衝突を構成された（2012）。
2. **シードは各ブロックの演算に構造的に効かせる。**
3. **証明付きでも速くできる。** CLHASH は CityHash より高速と報告（2015）。
4. **脅威モデルを定理の仮定として明示する。** 確率保証は「鍵が入力と独立」が前提で、鍵漏洩（タイミング等）は保証外。
5. **速度の工夫（SIMD・展開・分岐）がバグの温床。** そこを等価性証明で守る。
6. **証明できない性質は主張しない。** 暗号学的衝突耐性はうたわない。

---

## 3. 構造

```
入力 ─▶ 分割（64bit ブロック＋長さ符号化）
     ─▶ NH 圧縮（鍵 K、固定長ブロック）              … ε-AU
     ─▶ 多項式ハッシュ mod 2⁶¹−1 で連結（任意長対応） … ε ≤ ℓ/p
     ─▶ 全単射ミキサー（fmix64 型）                  … 衝突確率を変えない
     ─▶ 64bit 出力
```

設計判断:

- 圧縮段は **NH** を第一候補。CLHASH 型の繰り上がりなし乗算（GF(2)[x] の形式化が必要）は第二段階。
- folded multiply は使わないか、反例と対策を Lean で示した上で使う。
- 実装は小さな DSL（**HashIR**）の意味論で仕様との等価性を証明し、そこからコードを出力する。FFI 経由では呼ばない。
- **主な出力先は Rust**、C は同じ HashIR から副次的に出力。

---

## 4. 保証の範囲

### 4.1 証明する性質（Lean 4、`sorry` なし）

| 性質 | 述べ方 |
| :--- | :--- |
| 圧縮段（NH）の ε-AU | `Fintype.card` による数え上げ |
| 多項式段の ε-AU | 根の個数 ≤ 次数（`Polynomial.card_roots'` 等）、ε ≤ ℓ/p |
| ミキサーの全単射性 | 逆関数を構成し左右逆を示す |
| 合成則 | Pr[g(f_K(x)) = g(f_K(y))] = Pr[f_K(x) = f_K(y)] ≤ ε |
| 実装の正しさ | HashIR から出力した実装と仕様の等価性（`eval fast = spec`） |
| ストリーミングの分割非依存性 | `Hasher::write` の呼び出し方に結果が依存しない |

### 4.2 実験で確かめる性質

- SMHasher3 全通過
- 下位ビットの偏りのなさ
- 速度（2026-11-08 承認、同じ VM で交互計測した比、[journal](docs/journal/2026-11-08-p0prime-prototype.md)）: ≤32B で rapidhash の 0.6 倍以上、64B〜1KB で rapidhash の 0.8 倍以上、≥4KB で XXH3 の 0.5 倍以上、8B 以上の全区間で PolymurHash の 1.0 倍以上

### 4.3 狙わないもの

- 暗号学的衝突耐性
- 鍵漏洩時の安全性
- 鍵なしでの一様性

### 4.4 証明範囲の注意

- 合成則が保証するのは **64bit 出力全体** の衝突確率 ≤ ε まで。ハッシュ表のように下位 b ビットだけ使う場合は定理の範囲外。主張は「全体衝突 ≤ ε（証明）」「下位ビットの偏りのなさ（実験）」の2段で書く。
- ε は乗算の幅で決まる。32bit 語の NH（32×32→64）なら ε = 2⁻³²。2⁻⁶⁴ 寄りにするには 64×64→128 の乗算か NH の2本並列が必要。→ 2⁻⁶⁴ 寄りに決定（2026-11-08）。NH の定理は一般の語幅 W で証明済み

---

## 5. 実装言語の方針：Rust

- **ルートA（Lean → Rust）:** 計算の核（NH 内側ループ、多項式段、fmix64、SIMD）は HashIR から Rust を出力。
  - `wrapping_*` が BitVec の mod 2ⁿ 意味論と1対1で対応、`u128` が標準で使え、safe 部分に未定義動作がない。
  - `std::simd` は nightly 専用のため、SIMD は `std::arch` の組み込み関数を `unsafe` ブロックで出力し、「組み込み関数 ↔ HashIR 命令」の対応表だけを信頼する。
- **ルートB（Rust → Lean）:** 外側処理（`Hasher` 実装、バッファリング）は手書きの safe Rust を Charon＋Aeneas で Lean に抽出して検証（hax 0.4 の Lean バックエンドも同系統）。発展途上のツールで、抽出が失敗しうる。
- **位置づけ:** Rust の `BuildHasher`（HashMap ごとにランダムな鍵）は ε-AU 定理の仮定「鍵が入力と独立」とそのまま一致する。foldhash / ahash と並ぶ「衝突上界が証明された BuildHasher」として提供する。

---

## 6. モジュール構成（予定）

```
LeanHash/
├─ Spec/{Mix,NH,Poly}.lean                   -- BitVec / ZMod 上の純粋な仕様
├─ Props/{Bijective,Universal,Compose}.lean  -- 全単射、ε-AU、合成則
├─ IR/{Syntax,Semantics,EmitRust,EmitC}.lean -- 直線型 DSL とコード出力
├─ Impl/{Fast,Equiv}.lean                    -- 最適化版と eval fast = spec
├─ Streaming/                                -- Aeneas 抽出物と分割非依存性の証明
└─ Test/Vectors.lean
rust/leanhash/                               -- crate（kernel は生成コード、外側は手書き safe Rust。P0' の手書き試作もここ）
bench/                                       -- SMHasher3 への組み込み、計測結果
```

証明戦略:

- 64bit 乗算は `bv_decide` に投げず代数的補題（結合則・逆元）で処理し、SAT はシフト/XOR 部に限定。
- 定数の探索・逆元計算は外部で行い、Lean は検証のみ。
- ループはブロック単位の等価性から `List.foldl` の帰納法で持ち上げる。

---

## 7. ロードマップ

各段階は「`sorry` のない定理」または「再現可能な実験」でゲートする。

| 段階 | 内容 | ゲート |
| :--- | :--- | :--- |
| **P0' 試作（約2週間）** | Rust で NH＋fmix64 の素朴版。SMHasher3 と速度を foldhash / ahash / XXH3 / rapidhash / CLHASH と比較。CLHASH の論文値も再現 | **速度目標と ε 目標を数値で決定**（進むか判断）→ 試作 v2c で SMHasher3 全 PASS、目標を承認（2026-11-08）✅（[journal](docs/journal/2026-11-08-p0prime-prototype.md)） |
| P0 Lean 準備（並行） | Lean 4 / Mathlib 環境、BitVec と bv_decide | xorshift 自己逆の定理 ✅ `LeanHash/Spec/Mix.lean` |
| P1 仕上げ段 | fmix64 の仕様・逆関数・左右逆 | fmix64 全単射の定理 ✅ `LeanHash/Spec/Fmix.lean`（[journal](docs/journal/2026-11-08-p1-fmix64.md)） |
| P2 圧縮段（中心） | 固定長 NH の ε-AU を数え上げで証明、8〜16bit 版で全数照合 | ε-AU 定理と実測が一致 → 教科書どおりの NH の (1/W)-AU を証明 ✅ `LeanHash/Props/NH.lean`、全数照合は 1 組 9bit・2 組 4bit・16bit は抜き取りで一致（上界は tight）。1/W がちょうどの値であること（下限）も証明 ✅ `LeanHash/Props/NHLower.lean`（[journal](docs/journal/2026-11-09-p2-nh-lower.md)）。v2c の 1KB 以下の 2 経路（NH64 / NH32 の Toeplitz 2 本、端数の重ね読み、長さの組、multiply-shift、仕上げ）について、同じ経路の違う 2 入力で ε ≤ 2⁻⁶⁴ + 2⁻⁶³ ≤ 2⁻⁶² を証明 ✅ `LeanHash/Props/ShortPath.lean`（[journal](docs/journal/2026-11-09-p2-rest.md)）。経路ごとに独立な fin にして、1KB 以下の違う 2 入力すべてで ε ≤ 2⁻⁶² を 1 本の定理に ✅ `LeanHash/Props/Le1K.lean`（[journal](docs/journal/2026-11-10-per-path-fin.md)） |
| P2.5 多項式段 | mod 2⁶¹−1 の多項式ハッシュの ε-AU（ε ≤ ℓ/p）と2段の合成 | 定理 → Horner mod p の ε-AU（違う係数列で衝突する r は次数以下）を証明 ✅ `LeanHash/Props/Poly.lean`（p = 2⁶¹−1 の素数性は Lucas–Lehmer）。v2c の 1KB より長い経路（NH32×2 → 60bit limb → 多項式 → multiply-shift）で ε ≤ 2⁻⁶⁴ + 3N/p + 2⁻⁶³ ≤ 2⁻⁶³ + (3N+1)/p（N = ⌊L/1024⌋+1）✅ `LeanHash/Props/Long.lean`。全長（L < p）の違う 2 入力すべてで ε ≤ 2⁻⁶³ + (3N+1)/p を 1 本の定理に ✅ `LeanHash/Props/All.lean` の `v2c_eps`。Lean の仕様と Rust の一致はテスト（`lean_spec_matches_hash_long`）（[journal](docs/journal/2026-11-10-p25-poly.md)） |
| P3 結合と Rust 出力 | 合成則、HashIR と EmitRust（`wrapping_*`、`u128`、`std::arch`）、eval fast = spec | 差分テストで全一致 |
| P3.5 外側処理の検証 | `Hasher::write` のバッファリング・端数・長さ符号化を safe Rust で書き、Aeneas で抽出して分割非依存性を証明 | 定理（詰まれば差分テスト・ファジングで代替） |
| P4 評価と改良 | SMHasher3、速度比較、攻撃試行、SIMD 最適化、CLHASH 型・folded multiply 検討、C 出力 | SMHasher3 全通過＋速度目標 |

---

## 8. 未解決の問い

- [x] 速度目標 → ≤32B: rapidhash の 0.6 倍、64B〜1KB: 0.8 倍、≥4KB: XXH3 の 0.5 倍、PolymurHash 以上（2026-11-08 承認、[journal](docs/journal/2026-11-08-p0prime-prototype.md)）
- [x] ε の目標 → 「2⁻⁶⁴ 寄り」: ≤1KB で 2⁻⁶²、長い入力で 2⁻⁶³ + (3n+1)/p（2026-11-08 承認、[journal](docs/journal/2026-11-08-p0prime-prototype.md)）。≤1KB は全組み合わせで ≤ 2⁻⁶² を証明（同じ経路 2⁻⁶⁴ + 2⁻⁶³、経路またぎ 2⁻⁶⁴。[journal](docs/journal/2026-11-10-per-path-fin.md)）。長い入力も 2⁻⁶³ + (3N+1)/p（N = ⌊L/1024⌋+1、L < p）を証明し、全長で 1 本の定理 `v2c_eps` に（[journal](docs/journal/2026-11-10-p25-poly.md)）
- [ ] Hasher に約 1KB の鍵をどう渡すか（P3.5 の設計に直結）
- [ ] 通常乗算（NH）か繰り上がりなし乗算（CLHASH）か
- [x] 任意長入力 → NH（固定長）＋多項式 mod 2⁶¹−1 の二段構成（UMAC/VHASH 型）を採用候補
- [x] 経路をまたぐ 2 入力（≤32B の NH64 経路と 33B〜1KB の NH32×2 経路、長い経路）の衝突確率 → **経路ごとに独立な fin を使う**（2026-11-10 決定）。1KB 以下はどの組み合わせでも ε ≤ 2⁻⁶² を証明（`le1K_eps`）。SMHasher3 は 188/188 PASS のまま（[journal](docs/journal/2026-11-10-per-path-fin.md)）
- [ ] 下位 b ビットまで証明すべきか（するなら multiply-shift 系の構成が必要）
- [ ] Aeneas が外側処理（スライス操作、ループ）をどこまで抽出できるか → P3.5 の最初に小さな例で確認
- [ ] NH より ε の小さい圧縮段の構成 → NH 1 本の ε = 1/W はちょうどの値で、これ以上は縮められない（1 語だけ違う組で等号。Lean で証明済み: `nh_eps_exact`、[journal](docs/journal/2026-11-09-p2-nh-lower.md)。出力 W² 通りに対する下限は約 1/W² なので、出力の半分ぶんの強さを捨てている）。**当面は v2c の構成（NH32×2 など）のまま進め、別の構成は今後の改善として検討する**（2026-11-09 決定、[journal](docs/journal/2026-11-08-p2-nh-eau.md)）

---

## 9. 参考

- [Rust-to-Lean Verification Pipeline (arXiv 2605.30106)](https://arxiv.org/html/2605.30106)
- [hax blog](https://hax.cryspen.com/blog/)
- [std::simd](https://doc.rust-lang.org/std/simd)
