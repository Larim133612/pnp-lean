import Pnp.Karp.VertexCoverProg

/-!
# FEEDBACK VERTEX SET (directed; Karp's FEEDBACK NODE SET): the language and the instance

## Encoding of instances

As for VERTEX COVER (`Pnp/Karp/VertexCover.lean`): the rows `clauses w = kr :: rows`, the budget
is `k = |kr|` (unary), and `rows` is an adjacency matrix on the vertices `[0, n)`,
`n = |rows|`.  There is an **arc** `i → j` iff `i ≠ j` and the entry `(i, j)` is `pos`
(diagonal entries are ignored).

`FVSLang w` holds iff some set `F` of at most `k` vertices meets every directed cycle, i.e. the
digraph with the vertices of `F` removed is acyclic: no vertex reaches itself
(`Relation.TransGen`) along arcs between vertices outside `F`.

## The reduction (from SAT, through the VERTEX COVER instance of M35)

The instance is the VERTEX COVER instance itself, `FVSI w = cmap (GV w)`
(`Pnp/Karp/VertexCoverProg.lean`).  Its matrix is symmetric, so every edge `{i, j}` is a
directed 2-cycle `i → j → i`: a feedback vertex set must cover every edge, and conversely after
removing a vertex cover no arc is left at all.
-/

namespace Pnp.Karp.FeedbackVS

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-- The arcs among the vertices `[0, n)` outside `F`. -/
def arcOut (rows : List (List SatSym)) (F : Finset ℕ) (a b : ℕ) : Prop :=
  a < rows.length ∧ b < rows.length ∧ a ∉ F ∧ b ∉ F ∧ a ≠ b ∧ (rows.getD a []).getD b zero = pos

/-- **FEEDBACK VERTEX SET** (directed) over `SatSym` (see the module docstring). -/
def FVSLang : Millennium.Language (List SatSym) := fun w =>
  match clauses w with
  | [] => False
  | kr :: rows => ∃ F : Finset ℕ, F.card ≤ kr.length ∧ (∀ i ∈ F, i < rows.length) ∧
      ∀ u, ¬ Relation.TransGen (arcOut rows F) u u

/-- The **FEEDBACK VERTEX SET** instance of the formula `w`: the VERTEX COVER instance. -/
def FVSI (w : List SatSym) : List SatSym := IndSet.cmap (VertexCover.GV w)

end Pnp.Karp.FeedbackVS
