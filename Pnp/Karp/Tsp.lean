import Pnp.Karp.Ham
import Pnp.Karp.SubsetSum

/-!
# TRAVELING SALESMAN (decision version): the language and the reduction instance

## Encoding of TSP instances (weights in binary)

An instance is a word `w` over `SatSym`, read as its rows `clauses w`.  The first row `Bd` is the
budget, a number in binary (`bv`, least significant bit first, `pos` = 1, `zero`/`neg` = 0, as
for SUBSET SUM).  The other rows `M` are the rows of the weight matrix on `n = |M|` cities: row
`u` is the list of its entries separated by `neg`, so the weight `wt M u v` of the step `u → v`
is the value `bv` of the `v`-th `neg`-separated chunk (`wchunk`) of row `u` (missing rows and
chunks are weight `0`).  The matrix need not be symmetric.

`TSPLang w` holds iff there are at least `3` cities and some tour `σ` (an ordering of the cities)
whose cost `tourCost M σ` (the sum of the weights of the steps `σᵢ → σᵢ₊₁`, cyclically) is at
most the budget.

## The reduction from (undirected) HAMILTONIAN CYCLE

For a graph `w` (`Pnp/Karp/Ham.lean`) on `n` vertices, `tspI w` has budget `0` (the empty row)
and the `n × n` matrix with weight `0` (the empty chunk) on the edges (`adjU w u v`) and
weight `1` (the chunk `pos`) elsewhere.  A tour of cost `0` is exactly a Hamiltonian cycle.
-/

namespace Pnp.Karp.Tsp

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.Ham Pnp.Karp.SubsetSum

/-! ## The language -/

/-- The `v`-th `neg`-separated chunk of a row. -/
def wchunk : List SatSym → ℕ → List SatSym
  | [], _ => []
  | s :: r, 0 => if s = neg then [] else s :: wchunk r 0
  | s :: r, v + 1 => if s = neg then wchunk r v else wchunk r (v + 1)

/-- The weight of the step `u → v` in the matrix `M` (rows of `neg`-separated binary numbers). -/
def wt (M : List (List SatSym)) (u v : ℕ) : ℕ := bv (wchunk (M.getD u []) v)

/-- The cost of the tour `σ` (cyclically). -/
def tourCost (M : List (List SatSym)) (σ : List ℕ) : ℕ :=
  ((List.range σ.length).map fun i => wt M (σ.getD i 0) (σ.getD ((i + 1) % σ.length) 0)).sum

/-- **TRAVELING SALESMAN** (decision version) over `SatSym` (see the module docstring). -/
def TSPLang : Millennium.Language (List SatSym) := fun w =>
  ∃ Bd M, clauses w = Bd :: M ∧ 3 ≤ M.length ∧
    ∃ σ : List ℕ, σ.Perm (List.range M.length) ∧ tourCost M σ ≤ bv Bd

/-! ## The reduction instance -/

/-- The chunk of the entry `(u, v)`: weight `0` on an edge, weight `1` otherwise. -/
def tEnt (w : List SatSym) (u v : ℕ) : List SatSym :=
  if ent w u v = pos ∨ ent w v u = pos then [] else [pos]

/-- Row `u` of the weight matrix. -/
def tRow (w : List SatSym) (u : ℕ) : List SatSym :=
  (List.range (clauses w).length).flatMap fun v => tEnt w u v ++ [neg]

/-- The TSP instance of the graph `w`: budget `0`, weights `0` on edges and `1` elsewhere. -/
def tspI (w : List SatSym) : List SatSym :=
  ([] :: (List.range (clauses w).length).map (tRow w)).flatMap (· ++ [sep])

end Pnp.Karp.Tsp
