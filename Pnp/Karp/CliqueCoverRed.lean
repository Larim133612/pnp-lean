import Pnp.Karp.CliqueCover
import Pnp.Karp.ColorRed
import Pnp.Karp.DHamRed

/-!
# CLIQUE COVER: correctness of the reduction from 3-COLORING (and SAT)

`col_iff_cc : ColLang (G w) ↔ CCLang (CCI w)`: the rows of `CCI w` are the target row
`pos^3` followed by the complement of the symmetrized matrix of `G w`, so two different
vertices may share a class iff they are not adjacent in `G w`.  The graph `G w` has no loops
and no edge leaves the vertex range `[0, n)` (`ccr_struct`), so a class map into `3` classes is
a proper 3-coloring and conversely.

`sat_iff_cc : SATLang w ↔ CCLang (CCI w)`, composed with `Color.sat_iff_col`.
-/

namespace Pnp.Karp.CliqueCover

open Pnp.CookLevin SatSym Pnp.Karp.Color

/-! ## Structure of `G w`: no loops, no edges leaving the vertex range -/

theorem ccr_length_gadAll (L : ℕ) : ∀ (p : ℕ) (A : List (SatSym × ℕ × ℕ)),
    (gadAll L p A).length = 3 * A.length
  | _, [] => rfl
  | p, a :: A => by
    simp [gadAll, gadRows, ccr_length_gadAll L (p + 1) A]; ring

theorem ccr_length_gRows (w : List SatSym) :
    (gRows w).length = base (Clique.annW w).length (Clique.annW w).length := by
  rw [gRows_eq, List.length_append, length_pre, ccr_length_gadAll]; simp [base]

theorem ccr_litCol_lt (s : SatSym) (j L : ℕ) (hj : j < L) : litCol s j < base L 0 := by
  cases s <;> simp [litCol, base] <;> omega

theorem ccr_gad (w : List SatSym) :
    ∀ (r : List SatSym) (t j p : ℕ) (P : List (List SatSym)),
    gRows w = P ++ gadAll (Clique.annW w).length p (Clique.ann r t j) → P.length = base (Clique.annW w).length p →
    j ≤ p → p + r.length = (Clique.annW w).length →
    ∀ i k, base (Clique.annW w).length p ≤ i → ((gRows w).getD i []).getD k zero = pos →
      k < base (Clique.annW w).length (Clique.annW w).length ∧ i ≠ k
  | [], _, _, _, P, hrows, hP, _, _, i, k, hi, hk => by
    rw [hrows, List.getD_append_right _ _ _ _ (by omega)] at hk
    simp [gadAll, Clique.ann] at hk
  | s :: r, t, j, p, P, hrows, hP, hjp, hlen, i, k, hi, hk => by
    have hjL : j < (Clique.annW w).length := by simp at hlen; omega
    have hpL : p < (Clique.annW w).length := by simp at hlen; omega
    rw [ann_cons] at hrows
    obtain ⟨hx, hy, ho, hrows', hP'⟩ := gad_rows hrows hP
    have hlen' : p + 1 + r.length = (Clique.annW w).length := by simp at hlen; omega
    have hb : 3 ≤ base (Clique.annW w).length p := by unfold base; omega
    have hbL : base (Clique.annW w).length p + 3 ≤ base (Clique.annW w).length (Clique.annW w).length := by
      unfold base; omega
    have hb0 : base (Clique.annW w).length 0 ≤ base (Clique.annW w).length p := by unfold base; omega
    by_cases hib : i < base (Clique.annW w).length p + 3
    · have : i = base (Clique.annW w).length p ∨ i = base (Clique.annW w).length p + 1 ∨
          i = base (Clique.annW w).length p + 2 := by omega
      rcases this with rfl | rfl | rfl
      · rw [hx, xRow_pos _ _ _ (by omega)] at hk
        rcases hk with hk | rfl | rfl
        · split_ifs at hk <;> omega
        · omega
        · omega
      · rw [hy, yRow_pos] at hk; simp only at hk
        have := ccr_litCol_lt s j _ hjL
        omega
      · rw [ho, oRow_pos _ _ _ (by omega)] at hk
        rcases hk with rfl | ⟨rfl, rfl⟩ | rfl <;> omega
    · exact ccr_gad w r _ _ (p + 1) _ hrows' hP' (by split_ifs <;> omega) hlen' i k
        (by unfold base at *; omega) hk

theorem ccr_pre (w : List SatSym) (i k : ℕ) (hi : i < base (Clique.annW w).length 0)
    (hk : ((gRows w).getD i []).getD k zero = pos) :
    k < base (Clique.annW w).length 0 ∧ i ≠ k := by
  rw [pre_rows w i hi] at hk
  by_cases h3 : i < 3
  · rw [tri_rows _ _ h3] at hk
    have hb : 3 ≤ base (Clique.annW w).length 0 := by simp [base]
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simp only [triRows, List.getD_cons_zero, getD_cons_pos_iff, getD_nil_pos] at hk
      simp at hk; omega
    · simp only [triRows, List.getD_cons_zero, List.getD_cons_succ, getD_cons_pos_iff,
        getD_nil_pos] at hk
      simp at hk; omega
    · simp [triRows] at hk
  · have hm : i - 3 < 2 * (Clique.annW w).length := by simp [base] at hi; omega
    have e := lit_rows (Clique.annW w).length (i - 3) hm
    rw [show 3 + (i - 3) = i by omega] at e
    rw [e] at hk
    simp only [base] at hi ⊢
    split_ifs at hk with hpar
    · rw [vpRow_pos] at hk; omega
    · rw [vnRow_pos] at hk; omega

/-- Every `pos` entry `(i, k)` of `G w` lies inside the vertex range and off the diagonal. -/
theorem ccr_struct (w : List SatSym) (i k : ℕ)
    (hk : ((gRows w).getD i []).getD k zero = pos) :
    i < (gRows w).length ∧ k < (gRows w).length ∧ i ≠ k := by
  have hi : i < (gRows w).length := by
    by_contra hc
    rw [List.getD_eq_default (gRows w) [] (by omega)] at hk
    simp at hk
  rw [ccr_length_gRows] at hi ⊢
  refine ⟨hi, ?_⟩
  by_cases h0 : i < base (Clique.annW w).length 0
  · have := ccr_pre w i k h0 hk
    have : base (Clique.annW w).length 0 ≤ base (Clique.annW w).length (Clique.annW w).length := by
      unfold base; omega
    omega
  · exact ccr_gad w (Clique.trunc w) 0 0 0 _ (gRows_eq w) (length_pre _) le_rfl
      (by rw [length_annW]; simp) i k (by omega) hk

/-! ## Rows of `CCI w` -/

theorem ccr_clauses_hdr (X : List SatSym) :
    clauses (ccHdr ++ X) = [zero, zero, zero] :: clauses X := by
  have := Clique.clausesAux_app [zero, zero, zero] X [] (by simp)
  simpa [clauses, ccHdr] using this

/-- The complemented symmetrized rows. -/
def ccRows (w : List SatSym) : List (List SatSym) :=
  ((List.range (gRows w).length).map (Ham.symRow (G w))).map (List.map IndSet.cs)

theorem ccr_clauses_CCI (w : List SatSym) :
    clauses (CCI w) = [pos, pos, pos] :: ccRows w := by
  unfold CCI ccRows
  rw [IndSet.clauses_cmap, ccr_clauses_hdr, Ham.dr_clauses_symG, clauses_G]
  simp [IndSet.cs]

theorem ccr_length_ccRows (w : List SatSym) : (ccRows w).length = (gRows w).length := by
  simp [ccRows]

theorem ccr_entry (w : List SatSym) (i j : ℕ) (hi : i < (gRows w).length)
    (hj : j < (gRows w).length) :
    ((ccRows w).getD i []).getD j zero = pos ↔ ¬ Ham.adjU (G w) i j := by
  have e : (ccRows w).getD i [] = (Ham.symRow (G w) i).map IndSet.cs := by
    unfold ccRows
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
  have hj' : j < (Ham.symRow (G w) i).length := by simpa [Ham.symRow, clauses_G] using hj
  have e2 : (Ham.symRow (G w) i).getD j zero =
      if Ham.ent (G w) i j = pos ∨ Ham.ent (G w) j i = pos then pos else zero := by
    unfold Ham.symRow
    rw [List.getD_eq_getElem _ _ (by simpa [clauses_G] using hj)]; simp
  rw [e, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
    ← List.getD_eq_getElem _ zero hj', e2]
  unfold Ham.adjU
  split_ifs with h <;> simp [h, IndSet.cs]

theorem ccr_ent (w : List SatSym) (i j : ℕ) :
    Ham.ent (G w) i j = ((gRows w).getD i []).getD j zero := by
  unfold Ham.ent; rw [clauses_G]

/-! ## Correctness -/

/-- **3-COLORING of `G w` ↔ CLIQUE COVER of `CCI w`.** -/
theorem col_iff_cc (w : List SatSym) : Color.ColLang (Color.G w) ↔ CCLang (CCI w) := by
  unfold Color.ColLang CCLang
  rw [ccr_clauses_CCI, clauses_G]
  simp only [List.length_cons, List.length_nil, ccr_length_ccRows]
  constructor
  · rintro ⟨col, hcol⟩
    refine ⟨fun i => (col i).val, fun i _ => (col i).isLt, fun i hi j hj hij hc => ?_⟩
    rw [ccr_entry w i j hi hj]
    rintro (h | h) <;> rw [ccr_ent] at h
    · exact hcol i j h (Fin.ext hc)
    · exact hcol j i h (Fin.ext hc.symm)
  · rintro ⟨c, hc3, hc⟩
    refine ⟨fun i => if h : i < (gRows w).length then ⟨c i, hc3 i h⟩ else 0,
      fun i j hij => ?_⟩
    obtain ⟨hi, hj, hne⟩ := ccr_struct w i j hij
    simp only [hi, hj, dite_true]
    intro heq
    have h1 := hc i hi j hj hne (Fin.mk.inj heq)
    rw [ccr_entry w i j hi hj] at h1
    exact h1 (Or.inl (by rw [ccr_ent]; exact hij))

/-- **Correctness of the reduction SAT ≤ CLIQUE COVER.** -/
theorem sat_iff_cc (w : List SatSym) : SATLang w ↔ CCLang (CCI w) :=
  (Color.sat_iff_col w).trans (col_iff_cc w)

end Pnp.Karp.CliqueCover
