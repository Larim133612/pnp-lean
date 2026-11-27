import Pnp.Karp.CliqueProg

/-!
# INDEPENDENT SET: the language and the reduction SAT ≤ₚ INDEPENDENT SET

## Encoding

Instances use the encoding of `Pnp.Karp.Clique.CliqueLang` (`Pnp/Karp/Clique.lean`): the rows
`clauses w` of a word `w` over `SatSym`; the length of the first row is the bound `k`; the
remaining rows `r₀, …, r_{n-1}` are an adjacency matrix on the vertices `0, …, n-1`, whose entry
`(i, j)` is `(rows.getD i []).getD j zero`, and the entry `pos` means "edge".

`ISLang w` holds iff there is a set `S` of at least `k` vertices such that no entry `(i, j)` with
`i ≠ j ∈ S` is `pos` (both orders are required, so a non-symmetric matrix is read as the
undirected graph with an edge `{i, j}` iff one of the two entries is `pos`).  A word without any
row is not in the language.

## The reduction

The complement map `cmap` (symbol-wise: `pos ↦ zero`, `zero, neg ↦ pos`, `sep ↦ sep`) sends a
CLIQUE instance whose adjacency rows all have length `≥ n` to an INDEPENDENT SET instance of the
complement graph (`isBody_cmap_iff`).  The rows of the CLIQUE instance `G w` of a formula `w`
(`Pnp/Karp/CliqueRed.lean`) all have full length (`length_row_G`), so
`sat_iff_is : SATLang w ↔ ISLang (cmap (G w))`.  `cmap` is computed by a symbol-wise
homomorphism followed by the decoder `FunBridge.computableB`; composed (`Pnp.TM2Comp.comp`) with
the CLIQUE reduction program this gives `sat_le_is : SATLang ≤ₚ ISLang`.
-/

namespace Pnp.Karp.IndSet

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## The language -/

/-- **INDEPENDENT SET** over `SatSym` (see the module docstring for the encoding). -/
def ISLang : Millennium.Language (List SatSym) := fun w =>
  match clauses w with
  | [] => False
  | kr :: rows => ∃ S : Finset ℕ, kr.length ≤ S.card ∧ (∀ i ∈ S, i < rows.length) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (rows.getD i []).getD j zero ≠ pos

/-! ## The complement map -/

/-- Complement of one symbol. -/
def cs : SatSym → SatSym
  | pos => zero
  | zero => pos
  | neg => pos
  | sep => sep

/-- Symbol-wise complement of a word. -/
def cmap (w : List SatSym) : List SatSym := w.map cs

theorem cs_eq_sep {s : SatSym} : cs s = sep ↔ s = sep := by cases s <;> simp [cs]

theorem clausesAux_map : ∀ (w cur : List SatSym),
    clausesAux (w.map cs) (cur.map cs) = (clausesAux w cur).map (List.map cs)
  | [], cur => by simp [clausesAux]
  | sep :: w, cur => by
    have := clausesAux_map w []
    simp only [List.map_nil] at this
    simp [clausesAux, cs, this, List.map_reverse]
  | pos :: w, cur => by
    have := clausesAux_map w (pos :: cur); simpa [clausesAux, cs] using this
  | zero :: w, cur => by
    have := clausesAux_map w (zero :: cur); simpa [clausesAux, cs] using this
  | neg :: w, cur => by
    have := clausesAux_map w (neg :: cur); simpa [clausesAux, cs] using this

theorem clauses_cmap (w : List SatSym) : clauses (cmap w) = (clauses w).map (List.map cs) := by
  have := clausesAux_map w []; simpa [clauses, cmap] using this

theorem cs_ne_pos_iff {s : SatSym} (hs : s ≠ sep) : cs s ≠ pos ↔ s = pos := by
  cases s <;> simp_all [cs]

/-- Entries of the complemented matrix (inside the full part of the rows). -/
theorem entry_cmap (rows : List (List SatSym)) (i j : ℕ) (hi : i < rows.length)
    (hj : j < (rows.getD i []).length) :
    ((rows.map (List.map cs)).getD i []).getD j zero = cs ((rows.getD i []).getD j zero) := by
  have e : (rows.map (List.map cs)).getD i [] = (rows.getD i []).map cs := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]; simp
  rw [e, List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]; simp

/-- **Complementation**: on matrices with full rows, an independent set of the complement is a
clique and conversely. -/
theorem isBody_cmap_iff (kr : List SatSym) (rows : List (List SatSym))
    (hsep : ∀ r ∈ rows, sep ∉ r) (hfull : ∀ r ∈ rows, rows.length ≤ r.length) :
    (∃ S : Finset ℕ, (kr.map cs).length ≤ S.card ∧
      (∀ i ∈ S, i < (rows.map (List.map cs)).length) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((rows.map (List.map cs)).getD i []).getD j zero ≠ pos) ↔
    (∃ S : Finset ℕ, kr.length ≤ S.card ∧ (∀ i ∈ S, i < rows.length) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (rows.getD i []).getD j zero = pos) := by
  simp only [List.length_map]
  have key : ∀ i j, i < rows.length → j < rows.length →
      (((rows.map (List.map cs)).getD i []).getD j zero ≠ pos ↔
        (rows.getD i []).getD j zero = pos) := by
    intro i j hi hj
    have hr : rows.getD i [] ∈ rows := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    have hj' : j < (rows.getD i []).length := lt_of_lt_of_le hj (hfull _ hr)
    rw [entry_cmap rows i j hi hj']
    refine cs_ne_pos_iff fun e => hsep _ hr ?_
    rw [← e, List.getD_eq_getElem _ _ hj']; exact List.getElem_mem hj'
  constructor
  · rintro ⟨S, h1, h2, h3⟩
    exact ⟨S, h1, h2, fun i hi j hj hij => (key i j (h2 i hi) (h2 j hj)).1 (h3 i hi j hj hij)⟩
  · rintro ⟨S, h1, h2, h3⟩
    exact ⟨S, h1, h2, fun i hi j hj hij => (key i j (h2 i hi) (h2 j hj)).2 (h3 i hi j hj hij)⟩

/-! ## Correctness of the reduction -/

theorem length_row_G (w : List SatSym) : ∀ r ∈ gRows w, (gRows w).length ≤ r.length := by
  intro r hr
  simp only [gRows, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨a, _, rfl⟩ <;> simp [gRows, litRow, vRow]

theorem sep_not_mem_gRows (w : List SatSym) : ∀ r ∈ gRows w, sep ∉ r := by
  intro r hr
  have := sep_not_mem_clauses (G w) r (by rw [clauses_G]; exact List.mem_cons_of_mem _ hr)
  exact this

/-- On instances with full rows, CLIQUE of `w` is INDEPENDENT SET of `cmap w`. -/
theorem clique_iff_is_cmap (w : List SatSym)
    (hfull : ∀ kr rows, clauses w = kr :: rows → ∀ r ∈ rows, rows.length ≤ r.length) :
    CliqueLang w ↔ ISLang (cmap w) := by
  unfold CliqueLang ISLang
  rw [clauses_cmap]
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · simp
  · simp only [List.map_cons]
    have hsep : ∀ r ∈ rows, sep ∉ r := fun r hr =>
      sep_not_mem_clauses w r (by rw [hcw]; exact List.mem_cons_of_mem _ hr)
    exact (isBody_cmap_iff kr rows hsep (hfull kr rows hcw)).symm

/-- **Correctness of the reduction SAT ≤ INDEPENDENT SET.** -/
theorem sat_iff_is (w : List SatSym) : SATLang w ↔ ISLang (cmap (G w)) := by
  rw [sat_iff_clique]
  refine clique_iff_is_cmap (G w) fun kr rows h => ?_
  rw [clauses_G] at h
  cases h
  exact length_row_G w

/-! ## Polynomial-time computability -/

/-- The complement map is polynomial-time computable. -/
theorem cmap_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    cmap) := by
  have e : FunBridge.dec2 ∘ (fun t => ((Millennium.fin_encoding_string SatSym).encode t).flatMap
      fun s => ic (cs s)) = cmap := by
    funext t
    simp only [comp_apply, Millennium.fin_encoding_string_encode, cmap]
    rw [← FunBridge.dec2_flatMap_ic (t.map cs), List.flatMap_map]
  rw [← e]
  exact ⟨Pnp.TM2Comp.comp (Pnp.TM2Hom.homComp _ _) FunBridge.computableB⟩

/-- The CLIQUE graph `G` is polynomial-time computable (`Pnp/Karp/CliqueProg.lean`). -/
theorem G_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    G) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    redCmd 1 10 (fun x => G (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := exec_redCmd x
      exact ⟨σ', h1.mono (Tred_le _), h2⟩)
    G (fun t => (congrArg G (FunBridge.dec2_flatMap_ic t)).symm)

/-- **SAT ≤ₚ INDEPENDENT SET** (official polynomial-time many-one reducibility). -/
theorem sat_le_is :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang ISLang := by
  obtain ⟨hG⟩ := G_computable
  obtain ⟨hc⟩ := cmap_computable
  exact ⟨cmap ∘ G, Pnp.TM2Comp.comp hG hc, sat_iff_is⟩

end Pnp.Karp.IndSet
