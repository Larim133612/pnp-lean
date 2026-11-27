import Pnp.Karp.Color

/-!
# MAX CUT (simple undirected graphs): the language and the reduction graph

## Encoding of MAX CUT instances

An instance is a word `w` over `SatSym`, read as its rows `clauses w = kr :: rows`.  The bound is
`K = |kr|` (unary).  The rows `rows` describe a simple undirected graph on the vertices `[0, n)`,
`n = |rows|`, by its **lower triangle**: for `j < i < n` there is an edge `{i, j}` iff the entry
`(i, j) = ((rows.getD i []).getD j zero)` is `pos`.  Entries with `j ≥ i` are ignored (so every
edge is written exactly once and there are no loops or multiple edges).

For a side assignment `s : ℕ → Bool` the cut value `cutVal rows s` is the number of edges
`{i, j}` with `s i ≠ s j`.  `MCLang w` holds iff some `s` has `K ≤ cutVal rows s`.

## The reduction graph (from a dense CNF formula `w`)

Let `A = annW w` (the annotated positions of `trunc w`, `Pnp/Karp/CliqueRed.lean`) and
`L = |A|`.  Vertices (truth value of a vertex `v` := "`v` is not on the side of `Z`"):

* `Z = 0` ("false") and `T = 1` ("true"), with the edge `Z—T`;
* `X j = 2 + 2j` and `X' j = 3 + 2j` for `j < L` (the literals `xⱼ`, `¬xⱼ`), with the edge
  `X j — X' j`;
* for the position `p` of `A` with annotation `(s, t, j)` (`j` = index inside the clause), base
  `b = base L p = 2 + 2L + 3p`: the vertices `Lₚ = b` (copy of the literal), `Cₚ = b + 1`,
  `Bₚ = b + 2` (the running OR of the clause), with edges
  * the triangle `acc — Lₚ — Cₚ — acc`, where `acc = accV L p j` is `Z` at the start of a clause
    (`j = 0`) and `B_{p-1} = b - 1` otherwise;
  * `Lₚ — nlCol s j`, where `nlCol` is `X' j` (`s = pos`), `X j` (`s = neg`) or `T` (otherwise),
    so that `Lₚ` copies the literal value (false for `zero`/`sep`);
  * `Bₚ — Cₚ` if `s ≠ sep`; and `Cₚ — T` if `s = sep` (forcing `Cₚ` false, hence the clause
    true).

There are `1 + L + 2L` "forced" edges and `L` triangles; a triangle has at most `2` cut edges,
exactly `2` iff its three vertices are not all on the same side.  The bound is
`K = 1 + L + 2L + 2L = 5L + 1`, so a cut of size `≥ K` must cut every forced edge and two edges
of every triangle (not-all-equal).  Then `Bₚ` true ⇒ `acc` true or the literal true, and at every
`sep` the accumulator is true: the formula is satisfied.  Conversely, a satisfying assignment
gives such a cut (`Bₚ` := running OR, `Cₚ := ¬Bₚ`).  This is `sat_iff_mc`
(`Pnp/Karp/MaxCutRed.lean`).

The rows below only have `pos` entries strictly below the diagonal.
-/

namespace Pnp.Karp.MaxCut

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## The language -/

/-- The number of cut edges `{i, j}`, `j < i`, of row `i`. -/
def rowCut (rows : List (List SatSym)) (s : ℕ → Bool) (i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => (rows.getD i []).getD j zero = pos ∧ s i ≠ s j).card

/-- The cut value of the side assignment `s`. -/
def cutVal (rows : List (List SatSym)) (s : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range rows.length, rowCut rows s i

/-- **MAX CUT** over `SatSym` (see the module docstring for the encoding). -/
def MCLang : Millennium.Language (List SatSym) := fun w =>
  match clauses w with
  | [] => False
  | kr :: rows => ∃ s : ℕ → Bool, kr.length ≤ cutVal rows s

/-! ## The reduction graph -/

/-- The row with `pos` exactly at the columns `a < c`. -/
def tw (a c : ℕ) : List SatSym :=
  List.replicate a zero ++ pos :: List.replicate (c - a - 1) zero ++ [pos]

/-- Rows of `Z = 0` and `T = 1` (edge `Z—T`). -/
def preRows : List (List SatSym) := [[], [pos]]

/-- Row of `X' j` (vertex `3 + 2j`): edge to `X j = 2 + 2j`. -/
def xpRow (j : ℕ) : List SatSym := List.replicate (2 + 2 * j) zero ++ [pos]

/-- The literal rows for the variables `j < L`. -/
def litRows (L : ℕ) : List (List SatSym) :=
  (List.range L).flatMap fun j => [[], xpRow j]

/-- The column of the vertex whose side is opposite to the literal copy `Lₚ`. -/
def nlCol : SatSym → ℕ → ℕ
  | pos, j => 3 + 2 * j
  | neg, j => 2 + 2 * j
  | _, _ => 1

/-- The base vertex of the gadget of position `p`. -/
def base (L p : ℕ) : ℕ := 2 + 2 * L + 3 * p

/-- The accumulator input of the gadget of position `p` (index `j` inside the clause). -/
def accV (L p j : ℕ) : ℕ := if j = 0 then 0 else base L p - 1

/-- Row of `Lₚ` (vertex `b`): edges to `acc` and `nlCol s j`. -/
def lRow (s : SatSym) (b j : ℕ) : List SatSym :=
  if j = 0 then tw 0 (nlCol s j) else tw (nlCol s j) (b - 1)

/-- Row of `Cₚ` (vertex `b + 1`): edges to `acc`, `Lₚ = b`, and to `T` at a `sep` position. -/
def cRow (s : SatSym) (b j : ℕ) : List SatSym :=
  if j = 0 then
    (if s = sep then [pos, pos] ++ List.replicate (b - 2) zero ++ [pos] else tw 0 b)
  else
    (if s = sep then [zero, pos] ++ List.replicate (b - 3) zero ++ [pos, pos]
     else List.replicate (b - 1) zero ++ [pos, pos])

/-- Row of `Bₚ` (vertex `b + 2`): edge to `Cₚ = b + 1` unless `s = sep`. -/
def bRow (s : SatSym) (b : ℕ) : List SatSym :=
  if s = sep then [] else List.replicate (b + 1) zero ++ [pos]

/-- The three gadget rows of the annotated position `a` at position `p`. -/
def gadRows (L p : ℕ) (a : SatSym × ℕ × ℕ) : List (List SatSym) :=
  [lRow a.1 (base L p) a.2.2, cRow a.1 (base L p) a.2.2, bRow a.1 (base L p)]

/-- The gadget rows of the positions `p, p + 1, …` (annotated by the list). -/
def gadAll (L : ℕ) : ℕ → List (SatSym × ℕ × ℕ) → List (List SatSym)
  | _, [] => []
  | p, a :: A => gadRows L p a ++ gadAll L (p + 1) A

/-- The graph rows. -/
def gRows (w : List SatSym) : List (List SatSym) :=
  preRows ++ litRows (annW w).length ++ gadAll (annW w).length 0 (annW w)

/-- The bound row: `K = 5L + 1`. -/
def kRow (w : List SatSym) : List SatSym := List.replicate (5 * (annW w).length + 1) zero

/-- The **MAX CUT** instance of the formula `w`. -/
def MCI (w : List SatSym) : List SatSym := (kRow w :: gRows w).flatMap (· ++ [sep])

/-! ## Rows of `MCI w` -/

theorem sep_not_mem_tw (a c : ℕ) : sep ∉ tw a c := by
  simp [tw, List.mem_replicate]

theorem sep_not_mem_gadRows (L p : ℕ) (a : SatSym × ℕ × ℕ) : ∀ c ∈ gadRows L p a, sep ∉ c := by
  intro c hc
  simp only [gadRows, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · unfold lRow; split_ifs <;> exact sep_not_mem_tw _ _
  · unfold cRow; split_ifs <;> simp [List.mem_replicate, sep_not_mem_tw]
  · unfold bRow; split_ifs <;> simp [List.mem_replicate]

theorem sep_not_mem_gadAll (L : ℕ) : ∀ (p : ℕ) (A : List (SatSym × ℕ × ℕ)),
    ∀ c ∈ gadAll L p A, sep ∉ c
  | _, [] => by simp [gadAll]
  | p, a :: A => by
    intro c hc
    simp only [gadAll, List.mem_append] at hc
    rcases hc with h | h
    · exact sep_not_mem_gadRows L p a c h
    · exact sep_not_mem_gadAll L (p + 1) A c h

theorem sep_not_mem_gRows (w : List SatSym) : ∀ c ∈ gRows w, sep ∉ c := by
  intro c hc
  simp only [gRows, List.mem_append, preRows, litRows, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl) | ⟨j, _, rfl | rfl⟩) | h
  · simp
  · simp
  · simp
  · simp [xpRow, List.mem_replicate]
  · exact sep_not_mem_gadAll _ _ _ c h

theorem clauses_MCI (w : List SatSym) : clauses (MCI w) = kRow w :: gRows w := by
  refine clauses_flatMap _ ?_
  intro c hc
  simp only [List.mem_cons] at hc
  rcases hc with rfl | h
  · simp [kRow, List.mem_replicate]
  · exact sep_not_mem_gRows w c h

end Pnp.Karp.MaxCut
