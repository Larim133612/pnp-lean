import Pnp.Karp.DHam
import Pnp.Karp.HPath

/-!
# DIRECTED HAMILTONIAN PATH: the language

## Encoding

As for `DHamLang` (`Pnp/Karp/DHam.lean`): the rows `clauses w` of the word are an adjacency
matrix on `n = |clauses w|` vertices, and there is an **arc** `u → v` iff the entry `(u, v)` is
`pos` (`adjD`).  `DHPathLang w` holds iff some ordering `σ` of the vertices visits them along a
directed path: there is an arc `σᵢ → σᵢ₊₁` for every `i + 1 < n` (no wrap-around).

## The reduction from (undirected) HAMILTONIAN PATH

Every edge becomes two arcs (`symG`, `Pnp/Karp/DHam.lean`).
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-- **DIRECTED HAMILTONIAN PATH** over `SatSym` (see the module docstring). -/
def DHPathLang : Millennium.Language (List SatSym) := fun w =>
  ∃ σ : List ℕ, IsHamPath (clauses w).length (adjD w) σ

end Pnp.Karp.Ham
