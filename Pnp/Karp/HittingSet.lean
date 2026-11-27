import Pnp.Karp.SetCover

/-!
# HITTING SET: the language and the reduction instance

## Encoding of instances

As for SET COVER (`Pnp/Karp/SetCover.lean`): the rows `clauses w = u :: kr :: rs`, a row `r`
stands for the set of positions `p` with `r.getD p zero = pos`, the ground set is `[0, |u|)`
and the budget is `k = |kr|`.

`HSLang w` holds iff some set `H ⊆ [0, |u|)` of at most `k` elements meets every row of `rs`.

## The reduction (from SAT)

Let `N = NV w = |trunc w| + 1` (variables `j < N`; every clause has length `< N`).  The ground
set is `[0, 2N)`: element `2j` is the literal `x_j`, element `2j + 1` is `¬x_j`.  The budget is
`N`.  The sets are

* `pairRow N i` for `i < N`: the pair `{2i, 2i + 1}`;
* for every clause `c`, the row `c.flatMap dbl` (`pos ↦ [pos, zero]` puts `2j` for a positive
  literal at position `j`, `neg ↦ [zero, pos]` puts `2j + 1`, `zero ↦ [zero, zero]`).

A hitting set of size `≤ N` must take exactly one element of every pair, i.e. it is an
assignment; it meets the row of a clause iff the assignment satisfies the clause.
-/

namespace Pnp.Karp.HittingSet

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum

/-- **HITTING SET** over `SatSym` (see the module docstring for the encoding). -/
def HSLang : Millennium.Language (List SatSym) := fun w =>
  ∃ u kr rs, clauses w = u :: kr :: rs ∧
    ∃ H : Finset ℕ, H.card ≤ kr.length ∧ (∀ p ∈ H, p < u.length) ∧
      ∀ r ∈ rs, ∃ p ∈ H, r.getD p zero = pos

/-- A literal symbol as two symbols (`x_j` at `2j`, `¬x_j` at `2j + 1`). -/
def dbl : SatSym → List SatSym
  | pos => [pos, zero]
  | neg => [zero, pos]
  | _ => [zero, zero]

/-- The pair `{2i, 2i + 1}` as a row of length `2N`. -/
def pairRow (N i : ℕ) : List SatSym :=
  (List.range (2 * N)).map fun p => if p / 2 = i then pos else zero

/-- The set rows of the instance. -/
def hsRows (w : List SatSym) : List (List SatSym) :=
  (List.range (NV w)).map (pairRow (NV w)) ++ (clauses w).map fun c => c.flatMap dbl

/-- The **HITTING SET** instance of the formula `w`: header `zero^(2N)`, budget `zero^N`. -/
def HSI (w : List SatSym) : List SatSym :=
  (List.replicate (2 * NV w) zero :: List.replicate (NV w) zero :: hsRows w).flatMap (· ++ [sep])

end Pnp.Karp.HittingSet
