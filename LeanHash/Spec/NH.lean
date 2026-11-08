/-
P2 圧縮段：NH（UMAC）の仕様。

語は Fin W（W = 2ʷ が実用、証明は一般の W で行う）。鍵とメッセージは「語の組」の n 個の並び。
NH_K(M) = Σᵢ ((m₂ᵢ₋₁ + k₂ᵢ₋₁) mod W) · ((m₂ᵢ + k₂ᵢ) mod W)   mod W²

Fin W の加算はそのまま mod W の加算なので、`m.1 + k.1` がそのまま (m + k) mod W になる。
-/
import Mathlib

namespace LeanHash.Spec

variable {W n : ℕ}

/-- 1 組の積（自然数として。mod W² はまだ取らない）。 -/
def pairVal (m k : Fin W × Fin W) : ℕ :=
  ((m.1 + k.1 : Fin W) : ℕ) * ((m.2 + k.2 : Fin W) : ℕ)

/-- NH。値は ZMod (W²)（= mod W² の剰余）。 -/
def nh (K M : Fin n → Fin W × Fin W) : ZMod (W ^ 2) :=
  ∑ i, (pairVal (M i) (K i) : ZMod (W ^ 2))

end LeanHash.Spec
