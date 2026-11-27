import Pnp.Karp.ThreePart

/-!
# 3-PARTITION: arithmetic of the items (no carries) and the rigidity of the groups
-/

namespace Pnp.Karp.ThreePart

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM

/-- The parameters of an item are in range. -/
def OkEl (q M : ℕ) : El → Prop
  | .cp c e _ => c < 3 ∧ e < q
  | .al c t _ => c < 3 ∧ t < M
  | .be c t e => c < 3 ∧ t < M ∧ e < q

/-- The intended groups: `{cp c e s, al c t s, be c t e}` and `{al 0 t s, al 1 t s, al 2 t s}`
(in any order). -/
def IsPat (g : List El) : Prop :=
  (∃ c e t s, g.Perm [.cp c e s, .al c t s, .be c t e]) ∨
    ∃ t s, g.Perm [.al 0 t s, .al 1 t s, .al 2 t s]

/-- Every item is strictly between a quarter and a half of the bound. -/
theorem tp_el_bounds (q M : ℕ) (x : El) :
    bv (bRow q M) < 4 * bv (elRow q M x) ∧ 2 * bv (elRow q M x) < bv (bRow q M) := by
  sorry

/-- **Rigidity**: a list of items (in range, `q ≥ 2`) sums to the bound iff it is an intended
group. -/
theorem tp_sum_iff (q M : ℕ) (hq : 2 ≤ q) (g : List El) (hg : ∀ x ∈ g, OkEl q M x) :
    (g.map fun x => bv (elRow q M x)).sum = bv (bRow q M) ↔ IsPat g := by
  sorry

/-- `binSum` as a sum over the indices of the group. -/
theorem tp_binSum_eq (rs : List (List SatSym)) (f : ℕ → ℕ) (b : ℕ) :
    binSum rs f b = (((List.range rs.length).filter fun i => f i = b).map
      fun i => bv (rs.getD i [])).sum := by
  sorry

end Pnp.Karp.ThreePart
