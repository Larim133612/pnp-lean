import Pnp.Karp.FeedbackVS

/-!
# The reduction SAT ≤ FEEDBACK VERTEX SET (correctness)

The matrix of `FVSI w = cmap (GV w)` is symmetric (`fvr_entry_symm`): the CLIQUE adjacency `adjB`
is symmetric and `cmap` acts entrywise on the full-length rows.  Hence a set of vertices is a
feedback vertex set iff it is a vertex cover (`vc_iff_fvs`), and with `sat_iff_vc` this gives
`sat_iff_fvs : SATLang w ↔ FVSLang (FVSI w)`.
-/

namespace Pnp.Karp.FeedbackVS

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.IndSet

theorem fvr_adjB_comm (a b : SatSym × ℕ × ℕ) : adjB a b = adjB b a := by
  rcases a with ⟨s, t, j⟩
  rcases b with ⟨s', t', j'⟩
  simp only [adjB]
  have h1 : (j == j') = (j' == j) := by rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact eq_comm
  rw [@bne_comm _ _ _ t t', h1, @bne_comm _ _ _ s s', Bool.and_comm (isLit s)]

theorem fvr_E_symm (A : List (SatSym × ℕ × ℕ)) (i j : ℕ) : E A i j ↔ E A j i := by
  rcases i with _ | p <;> rcases j with _ | q
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · simp only [E]
    constructor
    · rintro ⟨a, b, ha, hb, h⟩; exact ⟨b, a, hb, ha, by rw [fvr_adjB_comm]; exact h⟩
    · rintro ⟨a, b, ha, hb, h⟩; exact ⟨b, a, hb, ha, by rw [fvr_adjB_comm]; exact h⟩

theorem fvr_gRows_symm (w : List SatSym) (i j : ℕ) :
    ((gRows w).getD i []).getD j zero = pos ↔ ((gRows w).getD j []).getD i zero = pos := by
  simp only [gRows, entry_iff]; exact fvr_E_symm _ _ _

theorem fvr_cs_pos {x : SatSym} (hx : x ≠ sep) : cs x = pos ↔ x ≠ pos := by
  cases x <;> simp_all [cs]

theorem fvr_entry_ne_sep (rows : List (List SatSym)) (hsep : ∀ r ∈ rows, sep ∉ r) (i j : ℕ) :
    (rows.getD i []).getD j zero ≠ sep := by
  intro e
  by_cases hi : i < rows.length
  · have hr : rows.getD i [] ∈ rows := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    by_cases hj : j < (rows.getD i []).length
    · rw [List.getD_eq_getElem _ _ hj] at e
      exact hsep _ hr (e ▸ List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)] at e; cases e
  · rw [List.getD_eq_default rows [] (by omega)] at e; simp at e

/-- **Symmetry** of the matrix of `FVSI w`. -/
theorem fvr_entry_symm (w : List SatSym) (i j : ℕ) (hi : i < (gRows w).length)
    (hj : j < (gRows w).length) :
    (((gRows w).map (List.map cs)).getD i []).getD j zero = pos ↔
      (((gRows w).map (List.map cs)).getD j []).getD i zero = pos := by
  have hrow : ∀ k < (gRows w).length, (gRows w).getD k [] ∈ gRows w := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  rw [entry_cmap _ i j hi (lt_of_lt_of_le hj (length_row_G w _ (hrow i hi))),
    entry_cmap _ j i hj (lt_of_lt_of_le hi (length_row_G w _ (hrow j hj))),
    fvr_cs_pos (fvr_entry_ne_sep _ (sep_not_mem_gRows w) _ _),
    fvr_cs_pos (fvr_entry_ne_sep _ (sep_not_mem_gRows w) _ _), ne_eq, ne_eq,
    fvr_gRows_symm w i j]

theorem vc_iff_fvs (w : List SatSym) : VertexCover.VCLang (FVSI w) ↔ FVSLang (FVSI w) := by
  unfold VertexCover.VCLang FVSLang FVSI
  rw [clauses_cmap, VertexCover.clauses_GV]
  simp only [List.map_cons]
  constructor
  · rintro ⟨C, hk, hC, hcov⟩
    have hno : ∀ a b, ¬ arcOut ((gRows w).map (List.map cs)) C a b := by
      rintro a b ⟨ha, hb, haC, hbC, hab, he⟩
      rcases hcov a ha b hb hab he with h | h
      · exact haC h
      · exact hbC h
    refine ⟨C, hk, hC, fun u h => ?_⟩
    cases h with
    | single h => exact hno _ _ h
    | tail _ h => exact hno _ _ h
  · rintro ⟨F, hk, hF, hacyc⟩
    refine ⟨F, hk, hF, fun i hi j hj hij he => ?_⟩
    by_contra hc
    push Not at hc
    have hi' : i < (gRows w).length := by simpa using hi
    have hj' : j < (gRows w).length := by simpa using hj
    exact hacyc i (Relation.TransGen.head ⟨hi, hj, hc.1, hc.2, hij, he⟩
      (Relation.TransGen.single ⟨hj, hi, hc.2, hc.1, Ne.symm hij,
        (fvr_entry_symm w i j hi' hj').1 he⟩))

/-- **Correctness of the reduction SAT ≤ FEEDBACK VERTEX SET.** -/
theorem sat_iff_fvs (w : List SatSym) : SATLang w ↔ FVSLang (FVSI w) :=
  (VertexCover.sat_iff_vc w).trans (vc_iff_fvs w)

end Pnp.Karp.FeedbackVS
