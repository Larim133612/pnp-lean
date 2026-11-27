import Pnp.Karp.Ham

/-!
# DIRECTED HAMILTONIAN CYCLE: the language and the reduction from the undirected version

## Encoding

As for `UHamLang` (`Pnp/Karp/Ham.lean`): the rows `clauses w` of the word are an adjacency
matrix on `n = |clauses w|` vertices, with entry `(u, v)` = `ent w u v` (missing entries count
as `zero`).  Here there is an **arc** `u → v` iff the entry `(u, v)` is `pos`.
`DHamLang w` holds iff `n ≥ 3` (as for `UHamLang`) and some ordering `σ` of the vertices visits
them along a directed cycle: there is an arc `σᵢ → σᵢ₊₁` for every `i`, cyclically.

## The reduction from (undirected) HAMILTONIAN CYCLE

Every edge becomes two arcs: `symG w` is the `n × n` matrix whose entry `(u, v)` is `pos` iff
`u` and `v` are adjacent in `w` (`adjU w u v`), and `zero` otherwise.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-- Directed adjacency: the entry `(u, v)` is `pos`. -/
def adjD (w : List SatSym) (u v : ℕ) : Prop := ent w u v = pos

/-- **DIRECTED HAMILTONIAN CYCLE** over `SatSym` (see the module docstring). -/
def DHamLang : Millennium.Language (List SatSym) := fun w =>
  3 ≤ (clauses w).length ∧ ∃ σ : List ℕ, IsHamCycle (clauses w).length (adjD w) σ

/-- Row `u` of the symmetrized matrix. -/
def symRow (w : List SatSym) (u : ℕ) : List SatSym :=
  (List.range (clauses w).length).map fun v =>
    if ent w u v = pos ∨ ent w v u = pos then pos else zero

/-- The symmetrized matrix: every undirected edge becomes two arcs. -/
def symG (w : List SatSym) : List SatSym :=
  ((List.range (clauses w).length).map (symRow w)).flatMap (· ++ [sep])

end Pnp.Karp.Ham
