import Pnp.Karp.Basic

/-!
# CLIQUE: the language and shared tools

## Encoding of CLIQUE instances

An instance is a word `w` over the four-letter alphabet `SatSym = {pos, neg, zero, sep}` (the
alphabet of `SATLang`; it is also the fixed output alphabet of
`Pnp.CookLevin.FunBridge.computable_of_cmd_code`).  The word is read as its *rows*
`clauses w` (`Pnp.CookLevin.clauses`): the maximal `sep`-terminated blocks, ignoring the symbols
after the last `sep`.

* the length of the first row is the clique size bound `k` (unary; its symbols are arbitrary
  non-`sep` symbols);
* the remaining rows `r₀, …, r_{n-1}` form the adjacency matrix of a graph on the vertices
  `0, …, n-1`: the entry `(i, j)` is `(rows.getD i []).getD j zero` (missing entries count as
  `zero`), and only the entry `pos` means "present".

`CliqueLang w` holds iff there is a set `S` of at least `k` vertices such that the `(i, j)` entry
is `pos` for all distinct `i, j ∈ S`, i.e. the graph has a clique of size `≥ k`.  Since both
orders `(i, j)` and `(j, i)` are required, a non-symmetric matrix is implicitly read as the
undirected graph with an edge `{i, j}` iff both entries are `pos`; diagonal entries are
irrelevant.  A word without any row is not in the language.

## Shared tools (this file)

* `trunc w`: the finished rows of `w` followed by their separators; `w = trunc w ++ tl w` with
  `tl w` free of `sep` (`trunc_append_tl`), and all rows are `sep`-free (`sep_not_mem_clauses`);
* `trimC k`: a stack command that, given the reversed internal code of `w` on stack `k`,
  strips the unfinished tail (`exec_trimC`), leaving the reversed code of `trunc w`.
-/

namespace Pnp.Karp.Clique

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

/-! ## The language -/

/-- **CLIQUE** over `SatSym` (see the module docstring for the encoding). -/
def CliqueLang : Millennium.Language (List SatSym) := fun w =>
  match clauses w with
  | [] => False
  | kr :: rows => ∃ S : Finset ℕ, kr.length ≤ S.card ∧ (∀ i ∈ S, i < rows.length) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (rows.getD i []).getD j zero = pos

/-! ## Rows of a word -/

/-- The unfinished tail of a word (after the last `sep`). -/
def tlAux : List SatSym → List SatSym → List SatSym
  | [], cur => cur.reverse
  | sep :: w, _ => tlAux w []
  | s :: w, cur => tlAux w (s :: cur)

/-- The unfinished tail of `w`. -/
def tl (w : List SatSym) : List SatSym := tlAux w []

/-- The finished rows of `w`, each followed by `sep`. -/
def trunc (w : List SatSym) : List SatSym := (clauses w).flatMap (· ++ [sep])

theorem clausesAux_decomp : ∀ (w cur : List SatSym),
    cur.reverse ++ w = (clausesAux w cur).flatMap (· ++ [sep]) ++ tlAux w cur
  | [], cur => by simp [clausesAux, tlAux]
  | sep :: w, cur => by
    have := clausesAux_decomp w []
    simp only [List.reverse_nil, List.nil_append] at this
    simp [clausesAux, tlAux, ← this]
  | zero :: w, cur => by
    have := clausesAux_decomp w (zero :: cur)
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
    simp only [clausesAux, tlAux, ← this]
  | pos :: w, cur => by
    have := clausesAux_decomp w (pos :: cur)
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
    simp only [clausesAux, tlAux, ← this]
  | neg :: w, cur => by
    have := clausesAux_decomp w (neg :: cur)
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at this
    simp only [clausesAux, tlAux, ← this]

theorem trunc_append_tl (w : List SatSym) : trunc w ++ tl w = w := by
  have := clausesAux_decomp w []
  simpa [trunc, tl, clauses] using this.symm

theorem sep_not_mem_aux : ∀ (w cur : List SatSym), sep ∉ cur →
    (∀ c ∈ clausesAux w cur, sep ∉ c) ∧ sep ∉ tlAux w cur
  | [], cur, h => by simp [clausesAux, tlAux, h]
  | sep :: w, cur, h => by
    have := sep_not_mem_aux w [] (by simp)
    simp only [clausesAux, tlAux, List.mem_cons, forall_eq_or_imp, List.mem_reverse]
    exact ⟨⟨h, this.1⟩, this.2⟩
  | zero :: w, cur, h => by
    simpa [clausesAux, tlAux] using sep_not_mem_aux w (zero :: cur) (by simp [h])
  | pos :: w, cur, h => by
    simpa [clausesAux, tlAux] using sep_not_mem_aux w (pos :: cur) (by simp [h])
  | neg :: w, cur, h => by
    simpa [clausesAux, tlAux] using sep_not_mem_aux w (neg :: cur) (by simp [h])

theorem sep_not_mem_clauses (w : List SatSym) : ∀ c ∈ clauses w, sep ∉ c :=
  (sep_not_mem_aux w [] (by simp)).1

theorem sep_not_mem_tl (w : List SatSym) : sep ∉ tl w := (sep_not_mem_aux w [] (by simp)).2

theorem length_trunc_le (w : List SatSym) : (trunc w).length ≤ w.length := by
  conv_rhs => rw [← trunc_append_tl w]
  simp

theorem length_clauses_le (w : List SatSym) : (clauses w).length ≤ w.length := by
  refine le_trans ?_ (length_trunc_le w)
  unfold trunc
  induction clauses w with
  | nil => simp
  | cons c cs ih => simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega

theorem ic_ne_sep {s : SatSym} (h : s ≠ sep) : ∃ a b, ic s = [a, b] ∧ (a = true ∨ b = true) := by
  cases s <;> simp_all [ic]

/-! ## Stripping the unfinished tail -/

/-- Loop body of `trimC`: pop one (reversed) symbol code; at a `sep` push it back and stop. -/
def trimB (k : ℕ) : Cmd :=
  .pop k .brk (.pop k .brk (.seq (.push k false) (.seq (.push k false) .brk)) .skip)
    (.pop k .brk .skip .skip)

/-- Strip the topmost symbols of stack `k` (a reversed internal code) down to the first `sep`. -/
def trimC (k : ℕ) : Cmd := .loop (trimB k)

/-- Reversed code of a list of symbols read in reverse. -/
def rc (l : List SatSym) : Str := l.flatMap fun s => (ic s).reverse

theorem rc_eq (l : List SatSym) : rc l.reverse = (l.flatMap ic).reverse := by
  induction l with
  | nil => rfl
  | cons s l ih => simp [rc, List.flatMap_append] at ih ⊢; rw [ih]

theorem exec_trimC (k : ℕ) (u : List SatSym) (hu : u = [] ∨ ∃ u', u = u' ++ [sep]) :
    ∀ (t : List SatSym) (σ : ℕ → Str), sep ∉ t → σ k = rc t ++ (u.flatMap ic).reverse →
    ExecLe (trimC k) σ (.norm (update σ k ((u.flatMap ic).reverse))) (4 * t.length + 6)
  | [], σ, _, h => by
    rcases hu with rfl | ⟨u', rfl⟩
    · refine (ExecLe.loop_brk (ExecLe.pop_nil (by simpa [rc] using h) (ExecLe.brk _))).cast ?_
        (by simp)
      congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [rc]
    · have h' : σ k = false :: false :: (u'.flatMap ic).reverse := by
        simpa [rc, List.flatMap_append, ic] using h
      refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := false)
        (s := (u'.flatMap ic).reverse)
        (by simp) ((ExecLe.push k false _).seq_norm ((ExecLe.push k false _).seq_norm
          (ExecLe.brk _)))))).cast ?_ (by simp)
      congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [List.flatMap_append, ic]
  | s :: t, σ, hs, h => by
    have hs' : s ≠ sep := fun e => hs (e ▸ List.mem_cons_self ..)
    have ht : sep ∉ t := fun e => hs (List.mem_cons_of_mem _ e)
    set rest := rc t ++ (u.flatMap ic).reverse
    have ih := exec_trimC k u hu t (update σ k rest) ht (by simp [rest])
    have hb : ExecLe (trimB k) σ (.norm (update σ k rest)) 3 := by
      cases s with
      | sep => exact absurd rfl hs'
      | zero =>
        have h' : σ k = true :: false :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := false) (s := rest) (by simp)
          (ExecLe.skip _))).cast
          (by simp) le_rfl
      | neg =>
        have h' : σ k = true :: true :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := true) (s := rest) (by simp)
          (ExecLe.skip _))).cast
          (by simp) le_rfl
      | pos =>
        have h' : σ k = false :: true :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := true) (s := rest) (by simp)
          (ExecLe.skip _))).cast
          (by simp) le_rfl
    refine (ExecLe.loop_norm hb ih).cast (by simp) (by simp; omega)

/-- `trimC` on the reversed code of a word leaves the reversed code of `trunc w`. -/
theorem exec_trimC_word (k : ℕ) (w : List SatSym) (σ : ℕ → Str) (h : σ k = (w.flatMap ic).reverse) :
    ExecLe (trimC k) σ (.norm (update σ k (((trunc w).flatMap ic).reverse)))
      (4 * w.length + 6) := by
  have hu : trunc w = [] ∨ ∃ u', trunc w = u' ++ [sep] := by
    unfold trunc
    rcases (clauses w).eq_nil_or_concat with h | ⟨L, c, h⟩
    · left; rw [h]; rfl
    · right; exact ⟨L.flatMap (· ++ [sep]) ++ c, by rw [h]; simp⟩
  have e : σ k = rc (tl w).reverse ++ ((trunc w).flatMap ic).reverse := by
    rw [h, rc_eq, ← List.reverse_append, ← List.flatMap_append, trunc_append_tl]
  refine (exec_trimC k (trunc w) hu (tl w).reverse σ (by simpa using sep_not_mem_tl w) e).mono ?_
  have := congrArg List.length (trunc_append_tl w)
  simp only [List.length_append] at this
  simp; omega

end Pnp.Karp.Clique
