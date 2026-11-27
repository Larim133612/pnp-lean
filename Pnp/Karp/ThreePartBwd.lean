import Pnp.Karp.ThreePartArith

/-!
# 3-PARTITION: a partition gives an exact cover (backward direction)
-/

namespace Pnp.Karp.ThreePart

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM

theorem cov_of_tp (q : ℕ) (hq : 2 ≤ q) (ts : List (ℕ × ℕ × ℕ))
    (hts : ∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (h : TPLang (TPW q ts)) :
    ∃ y : List Bool, ∀ p < 3 * q, covT q ts y p = 1 := by
  sorry

end Pnp.Karp.ThreePart
