import Pnp.Karp.ThreeDM

/-!
# EXACT COVER: the language and the reduction instance

## Encoding of instances

As for X3C (`Pnp/Karp/ThreeDM.lean`): the rows `clauses w = u :: rs`, the ground set is
`[0, n)` with `n = |u|`, and every row of `rs` is the characteristic vector (length `n`) of a
subset of `[0, n)` (any number of `pos` entries).

`ECLang w` holds iff some selection `y` of rows covers every point `p < n` exactly once.

## The reduction (from SAT, through the X3C instance of M46)

X3C is the special case where every set has three elements, so the X3C instance `X3I w` itself
is the EXACT COVER instance.
-/

namespace Pnp.Karp.ExactCover

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.ThreeDM

/-- **EXACT COVER** over `SatSym` (see the module docstring for the encoding). -/
def ECLang : Millennium.Language (List SatSym) := fun w =>
  ∃ u rs, clauses w = u :: rs ∧ (∀ r ∈ rs, r.length = u.length) ∧
    ∃ y : List Bool, ∀ p < u.length, covC rs y p = 1

/-- X3C is a special case of EXACT COVER. -/
theorem x3c_imp_ec {w : List SatSym} (h : X3CLang w) : ECLang w := by
  obtain ⟨u, rs, hc, hr, y, hy⟩ := h
  exact ⟨u, rs, hc, fun r hr' => (hr r hr').1, y, hy⟩

end Pnp.Karp.ExactCover
