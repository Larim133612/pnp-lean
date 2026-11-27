import Pnp.Karp.FeedbackVS

/-!
# FEEDBACK ARC SET (directed): the language and the instance

## Encoding of instances

As for FEEDBACK VERTEX SET (`Pnp/Karp/FeedbackVS.lean`): the rows `clauses w = kr :: rows`, the
budget is `k = |kr|` (unary), and `rows` is an adjacency matrix on the vertices `[0, n)`,
`n = |rows|`; there is an **arc** `a → b` iff `a, b < n`, `a ≠ b` and the entry `(a, b)` is `pos`.

`FASLang w` holds iff some set `F` of at most `k` pairs meets every directed cycle, i.e. the
digraph with the arcs of `F` removed is acyclic (no vertex reaches itself, `Relation.TransGen`).

## The reduction (from FEEDBACK VERTEX SET, vertex splitting)

`splitW x` replaces every vertex `v` of the digraph of `x` by `v_in = 2v` and `v_out = 2v + 1`
with the arc `v_in → v_out`, and every arc `u → v` (`u ≠ v`) by the arc `u_out → v_in`:

* row `2v` (`inRow v`): `pos` at column `2v + 1`;
* row `2v + 1` (`outRow r v`, `r` = row `v`): the entries of `r` with the diagonal entry cleared,
  each followed by `zero` (so the entry at column `j` lands at column `2j`).

The budget row is kept.  A feedback vertex set `F` gives the feedback arc set
`{(2v, 2v+1) | v ∈ F}`; a feedback arc set `F` gives the feedback vertex set
`{p.2 / 2 | p ∈ F}` (restricted to `[0, n)`).  This is `fvs_iff_fas`
(`Pnp/Karp/FeedbackArcRed.lean`).
-/

namespace Pnp.Karp.FeedbackArc

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-- The arcs among the vertices `[0, n)` that are not in `F`. -/
def arcF (rows : List (List SatSym)) (F : Finset (ℕ × ℕ)) (a b : ℕ) : Prop :=
  a < rows.length ∧ b < rows.length ∧ a ≠ b ∧ (rows.getD a []).getD b zero = pos ∧ (a, b) ∉ F

/-- **FEEDBACK ARC SET** (directed) over `SatSym` (see the module docstring). -/
def FASLang : Millennium.Language (List SatSym) := fun w =>
  match clauses w with
  | [] => False
  | kr :: rows => ∃ F : Finset (ℕ × ℕ), F.card ≤ kr.length ∧
      ∀ u, ¬ Relation.TransGen (arcF rows F) u u

/-- Row of `v_in = 2v`: the arc to `v_out = 2v + 1`. -/
def inRow (v : ℕ) : List SatSym := List.replicate (2 * v + 1) zero ++ [pos]

/-- Row of `v_out = 2v + 1`: the arcs of row `r` (diagonal cleared) to the `in` vertices. -/
def outRow (r : List SatSym) (v : ℕ) : List SatSym := (r.set v zero).flatMap fun e => [e, zero]

/-- The rows of the split digraph. -/
def splitRows (rows : List (List SatSym)) : List (List SatSym) :=
  (List.range rows.length).flatMap fun v => [inRow v, outRow (rows.getD v []) v]

/-- The **FEEDBACK ARC SET** instance of the word `x` (an FVS instance). -/
def splitW (x : List SatSym) : List SatSym :=
  match clauses x with
  | [] => []
  | kr :: rows => (kr :: splitRows rows).flatMap (· ++ [sep])

/-- The **FEEDBACK ARC SET** instance of the formula `w`. -/
def FASI (w : List SatSym) : List SatSym := splitW (FeedbackVS.FVSI w)

end Pnp.Karp.FeedbackArc
