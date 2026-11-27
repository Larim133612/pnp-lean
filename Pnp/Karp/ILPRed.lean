import Pnp.Karp.ILP
import Pnp.Karp.HittingSetRed

/-!
# 0-1 INTEGER PROGRAMMING: correctness of the reduction from SAT

`sat_iff_ilp`: a formula `w` is satisfiable iff the constraint system `ILPI w` has a `0-1`
solution.  Let `N = NV w`; variable `2j` is `x_j`, variable `2j + 1` is `¬x_j`.

* Closed forms: for a `pos`/`zero` pattern `r`, with `cnt r x = Σ_{r_k = pos} x_k`
  (`selSum (r.map ilr_phi) x`), `rowOK (posR r) (true :: x) ↔ 1 ≤ cnt r x`
  (`ilr_rowOK_posR`) and `rowOK (negR r) (true :: x) ↔ cnt r x ≤ 1` (`ilr_rowOK_negR`).
  `1 ≤ cnt r x` iff some `k` has `r_k = pos` and `x_k = 1` (`ilr_cnt_pos`); two such `k`
  give `2 ≤ cnt r x` (`ilr_cnt_two`), and at most one gives `cnt r x ≤ 1` (`ilr_cnt_le`).
* (→) the assignment `a` gives `x_{2j} = a j`, `x_{2j+1} = ¬a j` (`j < N`);
* (←) a solution `x` gives `a j := x_{2j}`; the `negR` pair constraint forbids
  `x_{2j} = x_{2j+1} = 1`, so a true variable `2j + 1` of a clause row means `a j = false`.
-/

namespace Pnp.Karp.ILP

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.HittingSet
  Pnp.Karp.Knapsack

/-- The chunk of a pattern symbol: `[pos]` (the number `1`) for `pos`, else `[]` (`0`). -/
def ilr_phi (s : SatSym) : List SatSym := if s = pos then [pos] else []

theorem ilr_ichunks_pos (r : List SatSym) :
    pairs (ichunks (r.flatMap fun s => if s = pos then [pos, neg, neg] else [neg, neg])) =
      r.map (fun s => (ilr_phi s, [])) ++ [([], [])] := by
  induction r with
  | nil => rfl
  | cons s r ih =>
    by_cases h : s = pos
    · subst h; simp [ichunks, pairs, ih, ilr_phi]
    · simp [ichunks, pairs, ih, ilr_phi, h]

theorem ilr_ichunks_neg (r : List SatSym) :
    pairs (ichunks (r.flatMap fun s => if s = pos then [neg, pos, neg] else [neg, neg])) =
      r.map (fun s => ([], ilr_phi s)) ++ [([], [])] := by
  induction r with
  | nil => rfl
  | cons s r ih =>
    by_cases h : s = pos
    · subst h; simp [ichunks, pairs, ih, ilr_phi]
    · simp [ichunks, pairs, ih, ilr_phi, h]

theorem ilr_selSum_app : ∀ (L : List (List SatSym)) (y : List Bool),
    selSum (L ++ [[]]) y = selSum L y
  | [], y => by simp [selSum, bv]
  | c :: L, y => by simp [selSum, ilr_selSum_app L]

theorem ilr_selSum_nil : ∀ (n : ℕ) (y : List Bool),
    selSum (List.replicate n ([] : List SatSym)) y = 0
  | 0, y => rfl
  | n + 1, y => by rw [List.replicate_succ, selSum, ilr_selSum_nil n]; simp [bv]

theorem ilr_rowOK_posR (r : List SatSym) (x : List Bool) :
    rowOK (posR r) (true :: x) ↔ 1 ≤ selSum (r.map ilr_phi) x := by
  unfold rowOK posR
  simp only [List.cons_append, List.nil_append, ichunks]
  simp [ilr_ichunks_pos, pairs, selSum, bv, Function.comp_def, ilr_selSum_app, ilr_selSum_nil]

theorem ilr_rowOK_negR (r : List SatSym) (x : List Bool) :
    rowOK (negR r) (true :: x) ↔ selSum (r.map ilr_phi) x ≤ 1 := by
  unfold rowOK negR
  simp only [List.cons_append, List.nil_append, ichunks]
  simp [ilr_ichunks_neg, pairs, selSum, bv, Function.comp_def, ilr_selSum_app, ilr_selSum_nil]

theorem ilr_sel_cons (s : SatSym) (r : List SatSym) (x : List Bool) :
    selSum ((s :: r).map ilr_phi) x =
      (if s = pos ∧ x.getD 0 false = true then 1 else 0) + selSum (r.map ilr_phi) x.tail := by
  cases x <;> by_cases h : s = pos <;> simp [selSum, ilr_phi, h, bv]

theorem ilr_getD_tail (x : List Bool) (k : ℕ) : x.tail.getD k false = x.getD (k + 1) false := by
  cases x <;> simp

/-- `1 ≤ Σ_{r_k = pos} x_k` iff some `k` has `r_k = pos` and `x_k = 1`. -/
theorem ilr_cnt_pos : ∀ (r : List SatSym) (x : List Bool),
    1 ≤ selSum (r.map ilr_phi) x ↔ ∃ k, r.getD k zero = pos ∧ x.getD k false = true
  | [], x => by simp [selSum]
  | s :: r, x => by
    rw [ilr_sel_cons]
    constructor
    · intro h
      by_cases h0 : s = pos ∧ x.getD 0 false = true
      · exact ⟨0, by simpa using h0⟩
      · rw [if_neg h0] at h
        obtain ⟨k, hk⟩ := (ilr_cnt_pos r x.tail).1 (by omega)
        exact ⟨k + 1, by simpa [ilr_getD_tail] using hk⟩
    · rintro ⟨k, hk⟩
      cases k with
      | zero => rw [if_pos (by simpa using hk)]; omega
      | succ k =>
        have := (ilr_cnt_pos r x.tail).2 ⟨k, by simpa [ilr_getD_tail] using hk⟩
        omega

/-- Two distinct `k < k'` with `r_k = r_{k'} = pos` and `x_k = x_{k'} = 1` give `2 ≤ cnt`. -/
theorem ilr_cnt_two : ∀ (r : List SatSym) (x : List Bool) (k k' : ℕ), k < k' →
    r.getD k zero = pos → x.getD k false = true → r.getD k' zero = pos →
    x.getD k' false = true → 2 ≤ selSum (r.map ilr_phi) x
  | [], _, _, _, _, h, _, _, _ => by simp at h
  | s :: r, x, k, k', hlt, h1, h2, h3, h4 => by
    rw [ilr_sel_cons]
    cases k with
    | zero =>
      obtain ⟨k', rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by omega⟩
      rw [if_pos (by simpa using And.intro h1 h2)]
      have := (ilr_cnt_pos r x.tail).2 ⟨k', by simpa [ilr_getD_tail] using And.intro h3 h4⟩
      omega
    | succ k =>
      obtain ⟨k', rfl⟩ : ∃ m, k' = m + 1 := ⟨k' - 1, by omega⟩
      have := ilr_cnt_two r x.tail k k' (by omega) (by simpa using h1)
        (by simpa [ilr_getD_tail] using h2) (by simpa using h3)
        (by simpa [ilr_getD_tail] using h4)
      omega

/-- At most one `k` with `r_k = pos` and `x_k = 1` gives `cnt ≤ 1`. -/
theorem ilr_cnt_le : ∀ (r : List SatSym) (x : List Bool),
    (∀ k k', r.getD k zero = pos → x.getD k false = true → r.getD k' zero = pos →
      x.getD k' false = true → k = k') → selSum (r.map ilr_phi) x ≤ 1
  | [], _, _ => by simp [selSum]
  | s :: r, x, h => by
    rw [ilr_sel_cons]
    by_cases h0 : s = pos ∧ x.getD 0 false = true
    · rw [if_pos h0]
      have : ¬ 1 ≤ selSum (r.map ilr_phi) x.tail := by
        rw [ilr_cnt_pos]
        rintro ⟨k, hk1, hk2⟩
        have := h 0 (k + 1) (by simpa using h0.1) h0.2 (by simpa using hk1)
          (by simpa [ilr_getD_tail] using hk2)
        omega
      omega
    · rw [if_neg h0]
      have := ilr_cnt_le r x.tail fun k k' h1 h2 h3 h4 => by
        have := h (k + 1) (k' + 1) (by simpa using h1) (by simpa [ilr_getD_tail] using h2)
          (by simpa using h3) (by simpa [ilr_getD_tail] using h4)
        omega
      omega

theorem ilr_sep_posR (r : List SatSym) : sep ∉ posR r := by
  simp only [posR, List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil,
    reduceCtorEq, or_false, false_or, not_exists, not_and]
  intro s _; split <;> simp

theorem ilr_sep_negR (r : List SatSym) : sep ∉ negR r := by
  simp only [negR, List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil,
    reduceCtorEq, or_false, false_or, not_exists, not_and]
  intro s _; split <;> simp

/-- The rows of the instance. -/
theorem ilr_clauses (w : List SatSym) : clauses (ILPI w) = ilpRows w := by
  refine clauses_flatMap _ fun c hc => ?_
  simp only [ilpRows, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with ⟨_, _, rfl | rfl⟩ | ⟨c, _, rfl⟩
  · exact ilr_sep_posR _
  · exact ilr_sep_negR _
  · exact ilr_sep_posR _

/-- **SAT ≤ 0-1 INTEGER PROGRAMMING**: correctness of the instance `ILPI w`. -/
theorem sat_iff_ilp (w : List SatSym) : SATLang w ↔ ILPLang (ILPI w) := by
  rw [clauses_sat_iff]
  unfold ILPLang
  rw [ilr_clauses]
  constructor
  · rintro ⟨a, ha⟩
    set x := (List.range (2 * NV w)).map
      (fun p => if p % 2 = 0 then a (p / 2) else !a (p / 2)) with hxdef
    have hx : ∀ p, x.getD p false = true ↔
        p < 2 * NV w ∧ (p % 2 = 0 ∧ a (p / 2) = true ∨ p % 2 = 1 ∧ a (p / 2) = false) := by
      intro p
      by_cases hp : p < 2 * NV w
      · rw [List.getD_eq_getElem _ _ (by simpa [hxdef] using hp)]
        simp only [hxdef, List.getElem_map, List.getElem_range]
        split <;> cases a (p / 2) <;> simp <;> omega
      · rw [List.getD_eq_default _ _ (by simp [hxdef]; omega)]; simp [hp]
    refine ⟨x, fun r hr => ?_⟩
    simp only [ilpRows, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ⟨_, ⟨i, hi, rfl⟩, rfl | rfl⟩ | ⟨c, hc, rfl⟩
    · rw [ilr_rowOK_posR, ilr_cnt_pos]
      refine ⟨2 * i + if a i then 0 else 1, ?_, ?_⟩
      · rw [hsr_pair_getD]; split <;> omega
      · rw [hx]; cases h : a i <;> simp
        · exact ⟨by omega, by rwa [show (2 * i + 1) / 2 = i by omega]⟩
        · exact ⟨hi, h⟩
    · rw [ilr_rowOK_negR]
      refine ilr_cnt_le _ _ fun k k' h1 h2 h3 h4 => ?_
      rw [hsr_pair_getD] at h1 h3
      rw [hx] at h2 h4
      obtain ⟨-, rfl⟩ := h1
      rw [h3.2] at h4
      revert h2 h4; cases a (k / 2) <;> simp <;> omega
    · rw [ilr_rowOK_posR, ilr_cnt_pos]
      obtain ⟨j, hj, hl⟩ := ha c hc
      have hjN : j < NV w := lt_trans hj (hsr_len_lt w hc)
      cases h : c.getD j zero <;> rw [h] at hl <;> simp only [litTrue] at hl
      · refine ⟨2 * j, ?_, ?_⟩
        · rw [hsr_dbl_getD]; left; refine ⟨by omega, ?_⟩
          rw [show 2 * j / 2 = j by omega, h]
        · rw [hx]; refine ⟨by omega, Or.inl ⟨by omega, ?_⟩⟩
          rwa [show 2 * j / 2 = j by omega]
      · refine ⟨2 * j + 1, ?_, ?_⟩
        · rw [hsr_dbl_getD]; right; refine ⟨by omega, ?_⟩
          rw [show (2 * j + 1) / 2 = j by omega, h]
        · rw [hx]; refine ⟨by omega, Or.inr ⟨by omega, ?_⟩⟩
          rwa [show (2 * j + 1) / 2 = j by omega]
  · rintro ⟨x, hx⟩
    have hneg : ∀ i < NV w, x.getD (2 * i) false = true → x.getD (2 * i + 1) false = true →
        False := by
      intro i hi h0 h1
      have hr := (ilr_rowOK_negR (pairRow (NV w) i) x).1 (hx _ (List.mem_append_left _ (List.mem_flatMap.2
        ⟨pairRow (NV w) i, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, by simp⟩)))
      have := ilr_cnt_two (pairRow (NV w) i) x (2 * i) (2 * i + 1) (by omega)
        ((hsr_pair_getD _ _ _).2 ⟨by omega, by omega⟩) h0
        ((hsr_pair_getD _ _ _).2 ⟨by omega, by omega⟩) h1
      omega
    refine ⟨fun j => x.getD (2 * j) false, fun c hc => ?_⟩
    obtain ⟨p, hg, hp⟩ := (ilr_cnt_pos _ _).1 ((ilr_rowOK_posR _ _).1
      (hx _ (List.mem_append_right _ (List.mem_map.2 ⟨c, hc, rfl⟩))))
    have hjl : ∀ s, s ≠ zero → c.getD (p / 2) zero = s → p / 2 < c.length := by
      intro s hs h
      by_contra hn
      rw [List.getD_eq_default _ _ (by omega)] at h
      exact hs h.symm
    rw [hsr_dbl_getD] at hg
    rcases hg with ⟨h2, h⟩ | ⟨h2, h⟩
    · refine ⟨p / 2, hjl pos (by decide) h, ?_⟩
      rw [h]; simp only [litTrue]
      rwa [show 2 * (p / 2) = p by omega]
    · have hj := hjl neg (by decide) h
      refine ⟨p / 2, hj, ?_⟩
      rw [h]; simp only [litTrue]
      cases h0 : x.getD (2 * (p / 2)) false
      · rfl
      · exact (hneg _ (hj.trans (hsr_len_lt w hc)) h0
          (by rwa [show 2 * (p / 2) + 1 = p by omega])).elim

end Pnp.Karp.ILP
