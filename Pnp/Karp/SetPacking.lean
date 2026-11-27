import Pnp.Karp.SetCover

/-!
# SET PACKING: the language and the reduction instance

## Encoding of instances

As for SET COVER (`Pnp/Karp/SetCover.lean`): the rows `clauses w = u :: kr :: rs`, a row `r`
stands for the set of positions `p` with `r.getD p zero = pos`, the ground set is `[0, |u|)`
and the target is `k = |kr|` (unary).

`SPLang w` holds iff some set `S` of at least `k` row indices consists of pairwise disjoint
sets: no point `p < |u|` lies in two different selected rows.

## The reduction (from SAT, through the EXACT COVER BY 3-SETS instance of M46)

The instance is the SET COVER instance itself: `SPI w = SCI w` (header `zero^(3q)`, budget
`zero^q`, the triple rows of `X3I w`).  Every triple row is a 3-element subset of `[0, 3q)`, so
`q` pairwise disjoint triples cover `3q` points, i.e. they form an exact cover (double counting).
-/

namespace Pnp.Karp.SetPacking

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM
  Pnp.Karp.SetCover

/-- **SET PACKING** over `SatSym` (see the module docstring for the encoding). -/
def SPLang : Millennium.Language (List SatSym) := fun w =>
  ∃ u kr rs, clauses w = u :: kr :: rs ∧
    ∃ S : Finset ℕ, kr.length ≤ S.card ∧ (∀ i ∈ S, i < rs.length) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ p < u.length,
        ¬((rs.getD i []).getD p zero = pos ∧ (rs.getD j []).getD p zero = pos)

/-- The **SET PACKING** instance of the formula `w`: the SET COVER instance `SCI w`
(header `zero^(3q)`, target `zero^q`, the triple rows of the X3C instance). -/
def SPI (w : List SatSym) : List SatSym := SCI w

end Pnp.Karp.SetPacking
