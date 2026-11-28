import Pnp.Karp.ThreePartURed

/-!
# Unary 3-PARTITION: the shape of the reduction instances `TPUI w`

`tpui_wf`: the rows of `TPUI w` are `items ++ [Bv]` with `3 ∣ |items|` and every size strictly
between `B / 4` and `B / 2` (shared by the strong NP-completeness proofs of unary BIN PACKING and
unary 4-PARTITION, M65).
-/

namespace Pnp.Karp.ThreePartU

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

theorem tpu_clauses (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) :
    clauses (TPUW q ts) = (els q ts).map (fun x => uRow (uval q (mT q ts) x)) ++
      [uRow (uB (mT q ts))] := by
  unfold TPUW
  apply clauses_flatMap
  intro r hr
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨x, -, hx⟩ | hx
  · rw [← hx]; exact tpu_sep_nmem _
  · rw [hx]; exact tpu_sep_nmem _

theorem tpu_qB_cases (w : List SatSym) : (qB w = 0 ∧ tris w = []) ∨ 2 ≤ qB w := by
  by_cases hm : mC w = 0
  · left
    have hq : qB w = 0 := by simp [qB, hm]
    exact ⟨hq, by simp [tris, hm, hq]⟩
  · right
    have hN : 1 ≤ NV w := by unfold NV; omega
    unfold qB
    rw [Nat.mul_assoc]
    have : 1 ≤ NV w * mC w := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hm)
    omega

theorem tpui_wf (w : List SatSym) :
    clauses (TPUI w) = (els (qB w) (tris w)).map
        (fun x => uRow (uval (qB w) (mT (qB w) (tris w)) x)) ++
      [uRow (uB (mT (qB w) (tris w)))] ∧
    (els (qB w) (tris w)).length % 3 = 0 ∧
    ∀ x ∈ els (qB w) (tris w), uB (mT (qB w) (tris w)) < 4 * uval (qB w) (mT (qB w) (tris w)) x ∧
      2 * uval (qB w) (mT (qB w) (tris w)) x < uB (mT (qB w) (tris w)) := by
  refine ⟨tpu_clauses _ _, by rw [tpf_len_els]; omega, ?_⟩
  rcases tpu_qB_cases w with ⟨hq, ht⟩ | hq
  · intro x hx
    rw [ht, hq] at hx
    simp [els] at hx
  · intro x hx
    have hqM : qB w ≤ mT (qB w) (tris w) := by unfold mT; omega
    exact tpu_el_bounds _ _ hqM x (tpf_ok _ hq _ (dr_tris_lt w) x hx)

end Pnp.Karp.ThreePartU
