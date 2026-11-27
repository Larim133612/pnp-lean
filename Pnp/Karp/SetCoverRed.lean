import Pnp.Karp.SetCover
import Pnp.Karp.ThreeDMRed

/-!
# SET COVER: the instance `SCI w` is a yes-instance iff the X3C instance `X3I w` is

Every triple row is a 3-element subset of `[0, 3q)`.  By double counting
(`sr_sum_covC`), for any selection `y` the coverage counts `covC rs y p` over `p < 3q` sum to
`3 · (number of selected rows)`.  Hence an exact cover selects exactly `q` rows, and a cover
by at most `q` rows covers every point exactly once.
-/

namespace Pnp.Karp.SetCover

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM

/-- The number of rows (among the first `n`) selected by `y`. -/
def sr_sel (y : List Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if y.getD i false = true then 1 else 0

theorem sr_getD_succ (y : List Bool) (i : ℕ) : y.getD (i + 1) false = y.tail.getD i false := by
  cases y <;> simp

theorem sr_headD (y : List Bool) : y.headD false = y.getD 0 false := by
  cases y <;> simp

theorem sr_sel_succ (y : List Bool) (k : ℕ) :
    sr_sel y (k + 1) = (if y.headD false = true then 1 else 0) + sr_sel y.tail k := by
  unfold sr_sel
  rw [Finset.sum_range_succ', add_comm, sr_headD]
  simp only [sr_getD_succ]

/-- A row of length `n` has `Σ_{p<n} [r_p = pos] = count pos r`. -/
theorem sr_sum_row : ∀ (r : List SatSym),
    (∑ p ∈ Finset.range r.length, if r.getD p zero = pos then 1 else 0) = r.count pos
  | [] => by simp
  | a :: r => by
    rw [List.length_cons, Finset.sum_range_succ', List.count_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [sr_sum_row r]
    cases a <;> simp

/-- Double counting: the coverage counts sum to three times the number of selected rows. -/
theorem sr_sum_covC (n : ℕ) : ∀ (rs : List (List SatSym)),
    (∀ r ∈ rs, r.length = n ∧ r.count pos = 3) → ∀ y : List Bool,
      (∑ p ∈ Finset.range n, covC rs y p) = 3 * sr_sel y rs.length
  | [], _, y => by simp [covC, sr_sel]
  | r :: rs, h, y => by
    obtain ⟨hl, hc⟩ := h r (by simp)
    simp only [covC, Finset.sum_add_distrib]
    rw [sr_sum_covC n rs (fun r hr => h r (by simp [hr])) y.tail, List.length_cons,
      sr_sel_succ]
    cases y.headD false
    · simp
    · simp only [Bool.true_and, decide_eq_true_eq, if_true]
      rw [← hl, sr_sum_row, hc]; ring

/-- `p` is covered by `y` iff some selected row contains it. -/
theorem sr_covC_pos : ∀ (rs : List (List SatSym)) (y : List Bool) (p : ℕ),
    1 ≤ covC rs y p ↔
      ∃ i < rs.length, y.getD i false = true ∧ (rs.getD i []).getD p zero = pos
  | [], y, p => by simp [covC]
  | r :: rs, y, p => by
    simp only [covC]
    constructor
    · intro h
      by_cases h1 : (y.headD false && decide (r.getD p zero = pos)) = true
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        exact ⟨0, by simp, by rw [← sr_headD]; exact h1.1, by simpa using h1.2⟩
      · rw [if_neg h1] at h
        obtain ⟨i, hi, h2, h3⟩ := (sr_covC_pos rs y.tail p).1 (by omega)
        exact ⟨i + 1, by simp; omega, by rw [sr_getD_succ]; exact h2, by simpa using h3⟩
    · rintro ⟨i, hi, h2, h3⟩
      cases i with
      | zero =>
        rw [← sr_headD] at h2
        have : (y.headD false && decide (r.getD p zero = pos)) = true := by
          simp only [h2, Bool.true_and, decide_eq_true_eq]; simpa using h3
        rw [if_pos this]; omega
      | succ i =>
        rw [sr_getD_succ] at h2
        have := (sr_covC_pos rs y.tail p).2 ⟨i, by simp at hi; omega, h2, by simpa using h3⟩
        omega

theorem sr_sep_free (w : List SatSym) :
    ∀ c ∈ List.replicate (3 * qB w) zero :: List.replicate (qB w) zero :: triRows w, sep ∉ c := by
  intro c hc
  simp only [List.mem_cons, triRows, List.mem_map] at hc
  rcases hc with rfl | rfl | ⟨t, _, rfl⟩
  · simp [List.mem_replicate]
  · simp [List.mem_replicate]
  · exact dr_sep_triRow _ _

theorem sr_clauses (w : List SatSym) :
    clauses (SCI w) =
      List.replicate (3 * qB w) zero :: List.replicate (qB w) zero :: triRows w :=
  clauses_flatMap _ (sr_sep_free w)

theorem sr_rows (w : List SatSym) :
    ∀ r ∈ triRows w, r.length = 3 * qB w ∧ r.count pos = 3 := by
  intro r hr
  simp only [triRows, List.mem_map] at hr
  obtain ⟨t, ht, rfl⟩ := hr
  obtain ⟨h1, h2, h3⟩ := dr_tris_lt w t ht
  exact ⟨dr_triRow_len _ _, dr_triRow_count _ _ h1 h2 h3⟩

/-- **X3C ≤ SET COVER** on the reduction instances: `X3I w` has an exact cover iff `SCI w`
has a cover by at most `q` sets. -/
theorem x3c_iff_sc (w : List SatSym) : X3CLang (X3I w) ↔ SCLang (SCI w) := by
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
    · intro p hp
      rw [List.length_replicate] at hp
      obtain ⟨i, hi, h2, h3⟩ := (sr_covC_pos _ y p).1 (by rw [hy p hp])
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, h2⟩, h3⟩
  · rintro ⟨u, kr, rs, hc, S, hS, hSl, hcov⟩
    rw [sr_clauses] at hc
    obtain ⟨rfl, hc'⟩ := List.cons.inj hc
    obtain ⟨rfl, rfl⟩ := List.cons.inj hc'
    simp only [List.length_replicate] at hS hcov
    let y : List Bool := (List.range (triRows w).length).map (fun i => decide (i ∈ S))
    have hy : ∀ i < (triRows w).length, y.getD i false = decide (i ∈ S) := by
      intro i hi
      simp [y, List.getD_eq_getElem?_getD, hi]
    refine ⟨_, _, by rw [X3I, dr_clauses], ?_, y, ?_⟩
    · intro r hr
      rw [List.length_replicate]; exact sr_rows w r hr
    rw [List.length_replicate]
    have hge : ∀ p ∈ Finset.range (3 * qB w), 1 ≤ covC (triRows w) y p := by
      intro p hp
      obtain ⟨i, hiS, hi⟩ := hcov p (Finset.mem_range.1 hp)
      have hil := hSl i hiS
      exact (sr_covC_pos _ y p).2 ⟨i, hil, by rw [hy i hil]; simpa using hiS, hi⟩
    have hsel : sr_sel y (triRows w).length ≤ qB w := by
      have : sr_sel y (triRows w).length = S.card := by
        rw [sr_sel, ← Finset.card_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hi, h⟩; rw [hy i hi] at h; simpa using h
        · intro h; exact ⟨hSl i h, by rw [hy i (hSl i h)]; simpa using h⟩
      omega
    have hs := sr_sum_covC _ _ (sr_rows w) y
    have hle := Finset.sum_le_sum hge
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hle
    have heq := (Finset.sum_eq_sum_iff_of_le hge).1 (by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]; omega)
    intro p hp
    exact (heq p (Finset.mem_range.2 hp)).symm

end Pnp.Karp.SetCover
