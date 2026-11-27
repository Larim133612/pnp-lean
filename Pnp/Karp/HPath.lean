import Pnp.Karp.Ham

/-!
# HAMILTONIAN PATH: the language and the reduction instance

## Encoding

As for `UHamLang` (`Pnp/Karp/Ham.lean`): the rows `clauses w` are an adjacency matrix on
`n = |clauses w|` vertices, `u` and `v` adjacent iff the entry `(u, v)` or `(v, u)` is `pos`
(`adjU`).  `UHPathLang w` holds iff some ordering `σ` of the vertices visits them along a path:
consecutive vertices `σᵢ`, `σᵢ₊₁` are adjacent (no wrap-around).

## The reduction from (undirected) HAMILTONIAN CYCLE

For a graph `w` on `n ≥ 3` vertices, `hpI w` is the graph on `n + 3` vertices: the vertices
`u < n` of `w` with their edges; a copy `n` of the vertex `0` (adjacent to the neighbours
`v ≥ 1` of `0`); a pendant `n + 1` attached to `0` and a pendant `n + 2` attached to `n`.
A Hamiltonian path must run from `n + 1` to `n + 2`, i.e. `n + 1, 0, a₁, …, aₙ₋₁, n, n + 2`,
which is the same as a Hamiltonian cycle `0, a₁, …, aₙ₋₁` of `w`.  For `n < 3` (no
Hamiltonian cycle) `hpI w` is the edgeless graph on `2` vertices (no Hamiltonian path).
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-- `σ` is a Hamiltonian path for the adjacency relation `adj` on `n` vertices. -/
def IsHamPath (n : ℕ) (adj : ℕ → ℕ → Prop) (σ : List ℕ) : Prop :=
  σ.Perm (List.range n) ∧ ∀ i, i + 1 < σ.length → adj (σ.getD i 0) (σ.getD (i + 1) 0)

/-- **(Undirected) HAMILTONIAN PATH** over `SatSym` (see the module docstring). -/
def UHPathLang : Millennium.Language (List SatSym) := fun w =>
  ∃ σ : List ℕ, IsHamPath (clauses w).length (adjU w) σ

/-- The adjacency matrix of `hpI w` (for `n = |clauses w|`, entries `(u, v)`, `u, v < n + 3`). -/
def hpE (w : List SatSym) (u v : ℕ) : Bool :=
  let n := (clauses w).length
  if u < n ∧ v < n then decide (ent w u v = pos ∨ ent w v u = pos)
  else if u = n ∧ v < n then decide (1 ≤ v ∧ (ent w 0 v = pos ∨ ent w v 0 = pos))
  else if u = n + 1 then decide (v = 0)
  else if u = n + 2 then decide (v = n)
  else false

/-- Row `u` of `hpI w`. -/
def hpRow (w : List SatSym) (u : ℕ) : List SatSym :=
  (List.range ((clauses w).length + 3)).map fun v => if hpE w u v then pos else zero

/-- The HAMILTONIAN PATH instance of the graph `w` (see the module docstring). -/
def hpI (w : List SatSym) : List SatSym :=
  if (clauses w).length < 3 then [sep, sep]
  else ((List.range ((clauses w).length + 3)).map (hpRow w)).flatMap (· ++ [sep])

end Pnp.Karp.Ham
