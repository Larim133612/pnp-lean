import Pnp.Karp.ThreePartFwd
import Pnp.Karp.ThreePartBwd
import Pnp.Karp.ThreeDMComb
import Pnp.Karp.ThreeDMRed

/-!
# 3-PARTITION: correctness of the reduction instance

`sat_iff_tp`: a formula `w` is satisfiable iff `TPI w ∈ TPLang`, from `sat_iff_covT` (M46) and
`tp_of_cov`, `cov_of_tp` (`q = 2 N m ≥ 2` when there is a clause; with no clause there are no
triples and no items).
-/

namespace Pnp.Karp.ThreePart

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM

theorem tp_empty (q : ℕ) (hq : q = 0) : TPLang (TPW q []) := by
  subst hq
  refine ⟨[], bRow 0 (mT 0 []), ?_, rfl, by simp, fun _ => 0, by simp, by simp⟩
  have : els 0 [] = [] := by simp [els]
  simp only [TPW, this, List.map_nil, List.nil_append]
  rw [clauses_flatMap]
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  simp [bRow]

theorem sat_iff_tp (w : List SatSym) : SATLang w ↔ TPLang (TPI w) := by
  rw [sat_iff_covT]
  by_cases hm : mC w = 0
  · have hq : qB w = 0 := by simp [qB, hm]
    have ht : tris w = [] := by simp [tris, hm, hq]
    unfold TPI
    rw [ht]
    simp only [hq, Nat.mul_zero, Nat.not_lt_zero, false_imp_iff,
      implies_true, exists_const, true_iff]
    exact tp_empty 0 rfl
  · have hN : 1 ≤ NV w := by unfold NV; omega
    have hq : 2 ≤ qB w := by
      unfold qB
      rw [Nat.mul_assoc]
      have : 1 ≤ NV w * mC w := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hm)
      omega
    exact ⟨fun ⟨y, hy⟩ => tp_of_cov _ hq _ (dr_tris_lt w) y hy,
      fun h => cov_of_tp _ hq _ (dr_tris_lt w) h⟩

end Pnp.Karp.ThreePart
