import Pnp.Karp.ThreeDM

/-!
# SET COVER: the language and the reduction instance

## Encoding of instances

A word `w` over `SatSym` is read as its rows `clauses w`.  A row `r` stands for the set of
positions `p` with `r.getD p zero = pos`.  The first row `u` is a header giving the size of the
ground set `[0, |u|)` by its length; the second row `kr` gives the budget `k = |kr|` (unary);
the other rows `rs` are the sets.

`SCLang w` holds iff some set `S` of at most `k` row indices covers the ground set: every
`p < |u|` lies in some row `rs[i]` with `i ∈ S`.

## The reduction (from SAT, through the EXACT COVER BY 3-SETS instance of M46)

`SCI w` is the X3C instance `X3I w` (`Pnp/Karp/ThreeDM.lean`: header `zero^(3q)`, the triple
rows `triRows w`) with the budget row `zero^q` inserted after the header.  Every triple row is a
3-element subset of `[0, 3q)`, so a cover of `[0, 3q)` by at most `q` of them is exactly an
exact cover (double counting).
-/

namespace Pnp.Karp.SetCover

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM

/-- **SET COVER** over `SatSym` (see the module docstring for the encoding). -/
def SCLang : Millennium.Language (List SatSym) := fun w =>
  ∃ u kr rs, clauses w = u :: kr :: rs ∧
    ∃ S : Finset ℕ, S.card ≤ kr.length ∧ (∀ i ∈ S, i < rs.length) ∧
      ∀ p < u.length, ∃ i ∈ S, (rs.getD i []).getD p zero = pos

/-- The **SET COVER** instance of the formula `w`: header `zero^(3q)`, budget `zero^q`, and
the triple rows of the X3C instance. -/
def SCI (w : List SatSym) : List SatSym :=
  (List.replicate (3 * qB w) zero :: List.replicate (qB w) zero :: triRows w).flatMap (· ++ [sep])

end Pnp.Karp.SetCover
