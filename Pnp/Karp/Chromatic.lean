import Pnp.Karp.CliqueCoverRed
import Pnp.Karp.CliqueCoverProg

/-!
# CHROMATIC NUMBER (k-COLORING with `k` in the input): the language and the reduction

## Encoding of instances

The rows `clauses w = kr :: rows`: the number of colors is `k = |kr|` (unary), and `rows` is an
adjacency matrix on the vertices `[0, n)`, `n = |rows|`, with an edge between `i` and `j` iff
the entry `(i, j)` is `pos` (a `pos` on the diagonal is a loop; entries in columns `≥ n` are
ignored).

`KColLang w` holds iff there is a coloring `c` of `[0, n)` with colors `< k` such that the two
ends of every edge get different colors.

## The reduction (from SAT, through the 3-COLORING graph of M36)

`KCI w = ccHdr ++ symG (G w)`: the target row `zero^3`, followed by the symmetrized
`n × n` matrix of the 3-COLORING graph `Color.G w`.  Every edge of `G w` joins two different
vertices `< n` (`CliqueCover.ccr_struct`), so `G w` is 3-colorable iff `KCI w` is.
-/

namespace Pnp.Karp.Chromatic

open Pnp.CookLevin SatSym Pnp.Karp.Color Pnp.Karp.CliqueCover

/-- **CHROMATIC NUMBER** (`k`-COLORING) over `SatSym` (see the module docstring). -/
def KColLang : Millennium.Language (List SatSym) := fun w =>
  match clauses w with
  | [] => False
  | kr :: rows => ∃ c : ℕ → ℕ, (∀ i < rows.length, c i < kr.length) ∧
      ∀ i < rows.length, ∀ j < rows.length, (rows.getD i []).getD j zero = pos → c i ≠ c j

/-- The **CHROMATIC NUMBER** instance of the formula `w` (three colors). -/
def KCI (w : List SatSym) : List SatSym := ccHdr ++ Ham.symG (G w)

theorem kc_clauses (w : List SatSym) :
    clauses (KCI w) = [zero, zero, zero] ::
      (List.range (gRows w).length).map (Ham.symRow (G w)) := by
  rw [KCI, ccr_clauses_hdr, Ham.dr_clauses_symG, clauses_G]

theorem kc_entry (w : List SatSym) {i j : ℕ} (hi : i < (gRows w).length)
    (hj : j < (gRows w).length) :
    (((List.range (gRows w).length).map (Ham.symRow (G w))).getD i []).getD j zero = pos ↔
      Ham.adjU (G w) i j := by
  have h := Ham.dr_ent (G w) (u := i) (v := j) (by rwa [clauses_G]) (by rwa [clauses_G])
  unfold Ham.adjD Ham.ent at h
  rwa [Ham.dr_clauses_symG, clauses_G] at h

/-- **3-COLORING of `G w` ↔ 3-COLORING of `KCI w`.** -/
theorem col_iff_kcol (w : List SatSym) : ColLang (G w) ↔ KColLang (KCI w) := by
  unfold ColLang KColLang
  rw [kc_clauses, clauses_G]
  simp only [List.length_cons, List.length_nil, List.length_map, List.length_range]
  constructor
  · rintro ⟨col, hcol⟩
    refine ⟨fun i => (col i).val, fun i _ => (col i).isLt, fun i hi j hj hij hc => ?_⟩
    rcases (kc_entry w hi hj).1 hij with h | h <;> rw [ccr_ent] at h
    · exact hcol i j h (Fin.ext hc)
    · exact hcol j i h (Fin.ext hc.symm)
  · rintro ⟨c, hc3, hc⟩
    refine ⟨fun i => if h : i < (gRows w).length then ⟨c i, hc3 i h⟩ else 0,
      fun i j hij => ?_⟩
    obtain ⟨hi, hj, -⟩ := ccr_struct w i j hij
    simp only [hi, hj, dite_true]
    intro heq
    exact hc i hi j hj ((kc_entry w hi hj).2 (Or.inl (by rw [ccr_ent]; exact hij)))
      (Fin.mk.inj heq)

/-- **Correctness of the reduction SAT ≤ CHROMATIC NUMBER.** -/
theorem sat_iff_kcol (w : List SatSym) : SATLang w ↔ KColLang (KCI w) :=
  (sat_iff_col w).trans (col_iff_kcol w)

/-- **SAT ≤ₚ CHROMATIC NUMBER** (official polynomial-time many-one reducibility). -/
theorem sat_le_kcol :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang KColLang := by
  obtain ⟨hG⟩ := ccp_G_computable
  obtain ⟨hS⟩ := ccp_hdrSym_computable
  exact ⟨(fun x => ccHdr ++ Ham.symG x) ∘ G, Pnp.TM2Comp.comp hG hS, sat_iff_kcol⟩

end Pnp.Karp.Chromatic
