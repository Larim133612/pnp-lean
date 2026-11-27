import Pnp.Karp.SetPacking
import Pnp.Karp.SetCoverRed

/-!
# SET PACKING: the instance `SPI w` is a yes-instance iff the X3C instance `X3I w` is

`SPI w = SCI w`: header `zero^(3q)`, target `zero^q`, the triple rows of `X3I w`, each a
3-element subset of `[0, 3q)`.  A point is covered at least twice by a selection iff two
distinct selected rows contain it (`spk_covC_two`).  Hence an exact cover is a packing, of
`q` rows by double counting (`sr_sum_covC`); conversely a packing of at least `q` rows covers
every point at most once while the coverage counts sum to at least `3q`, so every point is
covered exactly once.
-/

namespace Pnp.Karp.SetPacking

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM
  Pnp.Karp.SetCover

/-- `p` is covered at least twice by `y` iff two distinct selected rows contain it. -/
theorem spk_covC_two : ∀ (rs : List (List SatSym)) (y : List Bool) (p : ℕ),
    2 ≤ covC rs y p ↔
      ∃ i j, i < j ∧ j < rs.length ∧ y.getD i false = true ∧ (rs.getD i []).getD p zero = pos ∧
        y.getD j false = true ∧ (rs.getD j []).getD p zero = pos
  | [], y, p => by simp [covC]
  | r :: rs, y, p => by
    simp only [covC]
    constructor
    · intro h
      by_cases h1 : (y.headD false && decide (r.getD p zero = pos)) = true
      · rw [if_pos h1] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨j, hj, h2, h3⟩ := (sr_covC_pos rs y.tail p).1 (by omega)
        exact ⟨0, j + 1, by omega, by simp; omega, by rw [← sr_headD]; exact h1.1,
          by simpa using h1.2, by rw [sr_getD_succ]; exact h2, by simpa using h3⟩
      · rw [if_neg h1] at h
        obtain ⟨i, j, hij, hj, h2, h3, h4, h5⟩ := (spk_covC_two rs y.tail p).1 (by omega)
        exact ⟨i + 1, j + 1, by omega, by simp; omega, by rw [sr_getD_succ]; exact h2,
          by simpa using h3, by rw [sr_getD_succ]; exact h4, by simpa using h5⟩
    · rintro ⟨i, j, hij, hj, h2, h3, h4, h5⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [sr_getD_succ] at h4
      cases i with
      | zero =>
        rw [← sr_headD] at h2
        have : (y.headD false && decide (r.getD p zero = pos)) = true := by
          simp only [h2, Bool.true_and, decide_eq_true_eq]; simpa using h3
        rw [if_pos this]
        have := (sr_covC_pos rs y.tail p).2 ⟨j, by simp at hj; omega, h4, by simpa using h5⟩
        omega
      | succ i =>
        rw [sr_getD_succ] at h2
        have := (spk_covC_two rs y.tail p).2
          ⟨i, j, by omega, by simp at hj; omega, h2, by simpa using h3, h4, by simpa using h5⟩
        omega

/-- **X3C ≤ SET PACKING** on the reduction instances: `X3I w` has an exact cover iff `SPI w`
has a packing of at least `q` pairwise disjoint sets. -/
theorem x3c_iff_spk (w : List SatSym) : ThreeDM.X3CLang (ThreeDM.X3I w) ↔ SPLang (SPI w) := by
  constructor
  · rintro ⟨u, rs, hc, -, y, hy⟩
    rw [X3I, dr_clauses] at hc
    obtain ⟨rfl, rfl⟩ := List.cons.inj hc
    simp only [List.length_replicate] at hy
    refine ⟨_, _, _, sr_clauses w,
      (Finset.range (triRows w).length).filter (fun i => y.getD i false = true), ?_, ?_, ?_⟩
    · have hs := sr_sum_covC _ _ (sr_rows w) y
      rw [Finset.sum_congr rfl (fun p hp => hy p (Finset.mem_range.1 hp))] at hs
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hs
      rw [Finset.card_filter, List.length_replicate, ← sr_sel]
      omega
    · intro i hi; exact Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    · intro i hi j hj hij p hp ⟨h1, h2⟩
      rw [List.length_replicate] at hp
      obtain ⟨hil, hi⟩ := Finset.mem_filter.1 hi
      obtain ⟨hjl, hj⟩ := Finset.mem_filter.1 hj
      rw [Finset.mem_range] at hil hjl
      have h2le : 2 ≤ covC (triRows w) y p := by
        rcases Nat.lt_or_gt_of_ne hij with h | h
        · exact (spk_covC_two _ y p).2 ⟨i, j, h, hjl, hi, h1, hj, h2⟩
        · exact (spk_covC_two _ y p).2 ⟨j, i, h, hil, hj, h2, hi, h1⟩
      have := hy p hp
      omega
  · rintro ⟨u, kr, rs, hc, S, hS, hSl, hdis⟩
    rw [SPI, sr_clauses] at hc
    obtain ⟨rfl, hc'⟩ := List.cons.inj hc
    obtain ⟨rfl, rfl⟩ := List.cons.inj hc'
    simp only [List.length_replicate] at hS hdis
    let y : List Bool := (List.range (triRows w).length).map (fun i => decide (i ∈ S))
    have hy : ∀ i < (triRows w).length, y.getD i false = decide (i ∈ S) := by
      intro i hi
      simp [y, List.getD_eq_getElem?_getD, hi]
    refine ⟨_, _, by rw [X3I, dr_clauses], ?_, y, ?_⟩
    · intro r hr
      rw [List.length_replicate]; exact sr_rows w r hr
    rw [List.length_replicate]
    have hle : ∀ p ∈ Finset.range (3 * qB w), covC (triRows w) y p ≤ 1 := by
      intro p hp
      by_contra hcon
      obtain ⟨i, j, hij, hj, h2, h3, h4, h5⟩ := (spk_covC_two (triRows w) y p).1 (by omega)
      rw [hy i (by omega)] at h2
      rw [hy j hj] at h4
      exact hdis i (by simpa using h2) j (by simpa using h4) (by omega) p
        (Finset.mem_range.1 hp) ⟨h3, h5⟩
    have hsel : S.card = sr_sel y (triRows w).length := by
      rw [sr_sel, ← Finset.card_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h; exact ⟨hSl i h, by rw [hy i (hSl i h)]; simpa using h⟩
      · rintro ⟨hi, h⟩; rw [hy i hi] at h; simpa using h
    have hs := sr_sum_covC _ _ (sr_rows w) y
    have hsum := Finset.sum_le_sum hle
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hsum
    have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]; omega)
    intro p hp
    exact heq p (Finset.mem_range.2 hp)

end Pnp.Karp.SetPacking
