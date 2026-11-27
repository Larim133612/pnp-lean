import Pnp.Karp.ThreePartArith

/-!
# 3-PARTITION: an exact cover gives a partition (forward direction)
-/

namespace Pnp.Karp.ThreePart

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM

theorem tp_of_cov (q : ℕ) (hq : 2 ≤ q) (ts : List (ℕ × ℕ × ℕ))
    (hts : ∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (y : List Bool)
    (hy : ∀ p < 3 * q, covT q ts y p = 1) : TPLang (TPW q ts) := by
  sorry

end Pnp.Karp.ThreePart
