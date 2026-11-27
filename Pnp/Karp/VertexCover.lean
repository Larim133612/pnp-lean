import Pnp.Karp.IndSetNP

/-!
# VERTEX COVER: the language, VERTEX COVER ∈ NP, and its relation to INDEPENDENT SET

## Encoding

Instances use the encoding of `Pnp.Karp.Clique.CliqueLang` (`Pnp/Karp/Clique.lean`): the rows
`clauses w`; the length of the first row is the bound `k`; the remaining rows `r₀, …, r_{n-1}`
are an adjacency matrix on the vertices `0, …, n-1` with entries
`(rows.getD i []).getD j zero`, the entry `pos` meaning "edge".

`VCLang w` holds iff there is a set `C` of at most `k` vertices such that every entry `(i, j) = pos`
with `i ≠ j < n` has `i ∈ C` or `j ∈ C` (a vertex cover of the undirected graph with an edge
`{i, j}` iff one of the two entries is `pos`).  A word without any row is not in the language.

## Contents

* `vcLang_iff`, `vc_in_np`: VERTEX COVER ∈ NP, with the verifier of `Pnp/Karp/IndSetVer.lean` in
  mode `vc = true` (the certificate is the indicator list of the complement `S` of the cover);
* `isBody_iff_vcBody`: for `k ≤ n`, the graph has an independent set of size `≥ k` iff it has a
  vertex cover of size `≤ n - k` (complements in `{0, …, n-1}`).
-/

namespace Pnp.Karp.VertexCover

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.IndSet

/-! ## The language -/

/-- **VERTEX COVER** over `SatSym` (see the module docstring for the encoding). -/
def VCLang : Millennium.Language (List SatSym) := fun w =>
  match clauses w with
  | [] => False
  | kr :: rows => ∃ C : Finset ℕ, C.card ≤ kr.length ∧ (∀ i ∈ C, i < rows.length) ∧
      ∀ i < rows.length, ∀ j < rows.length, i ≠ j →
        (rows.getD i []).getD j zero = pos → i ∈ C ∨ j ∈ C

/-! ## Independent sets and vertex covers -/

/-- **Complementation**: for `k ≤ n`, an independent set of size `≥ k` exists iff a vertex cover
of size `≤ n - k` exists. -/
theorem isBody_iff_vcBody (K K' : ℕ) (rows : List (List SatSym)) (hK : K ≤ rows.length)
    (hK' : K' = rows.length - K) :
    (∃ S : Finset ℕ, K ≤ S.card ∧ (∀ i ∈ S, i < rows.length) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (rows.getD i []).getD j zero ≠ pos) ↔
    (∃ C : Finset ℕ, C.card ≤ K' ∧ (∀ i ∈ C, i < rows.length) ∧
      ∀ i < rows.length, ∀ j < rows.length, i ≠ j →
        (rows.getD i []).getD j zero = pos → i ∈ C ∨ j ∈ C) := by
  subst hK'
  set n := rows.length
  constructor
  · rintro ⟨S, hk, hS, hadj⟩
    have hsub : S ⊆ Finset.range n := fun i hi => Finset.mem_range.2 (hS i hi)
    refine ⟨Finset.range n \ S, ?_, fun i hi => by simpa using (Finset.mem_sdiff.1 hi).1,
      fun i hi j hj hij he => ?_⟩
    · rw [Finset.card_sdiff_of_subset hsub, Finset.card_range]; omega
    · by_contra hc
      simp only [Finset.mem_sdiff, Finset.mem_range, not_or, not_and, not_not] at hc
      exact hadj i (hc.1 hi) j (hc.2 hj) hij he
  · rintro ⟨C, hk, hC, hcov⟩
    have hsub : C ⊆ Finset.range n := fun i hi => Finset.mem_range.2 (hC i hi)
    refine ⟨Finset.range n \ C, ?_, fun i hi => by simpa using (Finset.mem_sdiff.1 hi).1,
      fun i hi j hj hij he => ?_⟩
    · rw [Finset.card_sdiff_of_subset hsub, Finset.card_range]; omega
    · simp only [Finset.mem_sdiff, Finset.mem_range] at hi hj
      rcases hcov i hi.1 j hj.1 hij he with h | h
      · exact hi.2 h
      · exact hj.2 h

/-! ## VERTEX COVER ∈ NP -/

theorem vcLang_iff (w : List SatSym) :
    VCLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ vresI true w y = true := by
  classical
  have hcl := length_clauses_le w
  unfold VCLang
  simp only [vresI_iff]
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · simp
  · rw [hcw] at hcl
    simp only [List.length_cons] at hcl
    simp only [IndSet.Good, Nat.zero_add, Nat.sub_zero, Nat.zero_le, true_implies, finB, if_true,
      decide_eq_true_eq, ← card_filter_eq_cntB]
    constructor
    · rintro ⟨C, hk, hC, hcov⟩
      let y : Str := (List.range rows.length).map fun i => decide (i ∉ C)
      have hy : ∀ i, y.getD i false = true ↔ i < rows.length ∧ i ∉ C := by
        intro i
        by_cases hi : i < rows.length
        · simp [y, List.getD_eq_getElem?_getD, hi]
        · rw [List.getD_eq_default _ _ (by simp [y]; omega)]; simp [hi]
      refine ⟨y, by simp [y]; omega, fun j hj => ((hy j).1 hj).1, ?_,
        fun i _ hyi j hji hyj he => ?_⟩
      · refine le_trans (Finset.card_le_card fun i hi => ?_) hk
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        by_contra hc
        have : y.getD i false = true := (hy i).2 ⟨hi.1, hc⟩
        rw [this] at hi; simp at hi
      · rw [hy] at hyi hyj
        rcases hcov i hyi.1 j hyj.1 (Ne.symm hji) he with h | h
        · exact hyi.2 h
        · exact hyj.2 h
    · rintro ⟨y, -, h1, h2, h3⟩
      refine ⟨_, h2, fun i hi => by simpa using (Finset.mem_filter.1 hi).1,
        fun i hi j hj hij he => ?_⟩
      by_contra hc
      simp only [Finset.mem_filter, Finset.mem_range, not_or, not_and] at hc
      have hyi : y.getD i false = true := by simpa using hc.1 hi
      have hyj : y.getD j false = true := by simpa using hc.2 hj
      exact h3 i hi hyi j (Ne.symm hij) hyj he

/-- **VERTEX COVER ∈ NP** for the official class `NP`. -/
theorem vc_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      VCLang :=
  inNP_of_vresI true VCLang vcLang_iff

end Pnp.Karp.VertexCover
