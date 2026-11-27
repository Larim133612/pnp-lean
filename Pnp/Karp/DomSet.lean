import Pnp.Karp.HittingSet

/-!
# DOMINATING SET: the language and the reduction instance

## Encoding of instances

As for VERTEX COVER (`Pnp/Karp/VertexCover.lean`): the rows `clauses w = kr :: rows`; the length
of `kr` is the budget `k`, and `rows` is the adjacency matrix of a graph on `n = |rows|`
vertices, entry `(u, v)` = `(rows.getD u []).getD v zero` (missing entries count as `zero`).
The graph is undirected: `u` and `v` are adjacent iff the entry `(u, v)` or `(v, u)` is `pos`
(`dAdj`).

`DSLang w` holds iff some set `D` of at most `k` vertices dominates the graph: every vertex is
in `D` or adjacent to a vertex of `D`.

## The reduction (from SAT)

Let `N = NV w` (variables `j < N`) and let the clauses be `c₀, …, c_{m-1}`.  The graph has the
vertices `3j` (the literal `x_j`), `3j + 1` (`¬x_j`), `3j + 2` (a private vertex of `j`) for
`j < N`, forming a triangle for every `j` (`triRow`), and a vertex `3N + i` for every clause
`cᵢ`, adjacent to its literals (`cᵢ.flatMap trp`).  The budget is `N`.

A dominating set of size `≤ N` must meet every triangle (to dominate `3j + 2`), hence it takes
exactly one vertex of every triangle and nothing else; a clause vertex is dominated iff the
assignment `x_j := (3j ∈ D)` satisfies the clause.
-/

namespace Pnp.Karp.DomSet

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum

/-- Adjacency in the graph `rows` (undirected: either entry). -/
def dAdj (rows : List (List SatSym)) (u v : ℕ) : Prop :=
  (rows.getD u []).getD v zero = pos ∨ (rows.getD v []).getD u zero = pos

/-- **DOMINATING SET** over `SatSym` (see the module docstring for the encoding). -/
def DSLang : Millennium.Language (List SatSym) := fun w =>
  ∃ kr rows, clauses w = kr :: rows ∧
    ∃ D : Finset ℕ, D.card ≤ kr.length ∧ (∀ u ∈ D, u < rows.length) ∧
      ∀ v < rows.length, v ∈ D ∨ ∃ u ∈ D, dAdj rows u v

/-- A literal symbol as three symbols (`x_j` at `3j`, `¬x_j` at `3j + 1`). -/
def trp : SatSym → List SatSym
  | pos => [pos, zero, zero]
  | neg => [zero, pos, zero]
  | _ => [zero, zero, zero]

/-- Row `u` of the triangles: `pos` at the vertices of the triangle of `u` (`v / 3 = u / 3`). -/
def triRow (N u : ℕ) : List SatSym :=
  (List.range (3 * N)).map fun v => if v / 3 = u / 3 then pos else zero

/-- The adjacency rows of the instance. -/
def dsRows (w : List SatSym) : List (List SatSym) :=
  (List.range (3 * NV w)).map (triRow (NV w)) ++ (clauses w).map fun c => c.flatMap trp

/-- The **DOMINATING SET** instance of the formula `w`: budget `zero^N`. -/
def DSI (w : List SatSym) : List SatSym :=
  (List.replicate (NV w) zero :: dsRows w).flatMap (· ++ [sep])

end Pnp.Karp.DomSet
