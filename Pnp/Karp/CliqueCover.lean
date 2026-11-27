import Pnp.Karp.Color
import Pnp.Karp.DHam
import Pnp.Karp.IndSet

/-!
# CLIQUE COVER: the language and the reduction instance

## Encoding of instances

A word `w` over `SatSym` is read as its rows `clauses w = kr :: rows`.  The first row gives the
number of cliques `k = |kr|` (unary); the other rows are an adjacency matrix on the
`n = |rows|` vertices `[0, n)`, with entry `(i, j)` = `(rows.getD i []).getD j zero`
(as for CLIQUE, `Pnp/Karp/Clique.lean`: two vertices of a clique need the entry `pos` in both
orientations).

`CCLang w` holds iff the vertices can be partitioned into at most `k` cliques: there is a
class map `c` with `c i < k` for every vertex `i < n` such that any two different vertices of
the same class are adjacent.

## The reduction (from SAT, through the 3-COLORING graph of M36)

Two vertices may share a class iff they are adjacent in the complement graph, so a partition of
the complement of a graph `H` into `k` cliques is exactly a proper `k`-coloring of `H`.  For a
formula `w`, the 3-COLORING graph `Color.G w` is symmetrized to the full `n × n` matrix
`Ham.symG (G w)`, the target row `zero^3` is put in front, and every symbol is complemented
(`IndSet.cmap`: `pos ↦ zero`, `zero ↦ pos`):

`CCI w = cmap (ccHdr ++ symG (G w))`, `ccHdr = [zero, zero, zero, sep]`.
-/

namespace Pnp.Karp.CliqueCover

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-- **CLIQUE COVER** over `SatSym` (see the module docstring for the encoding). -/
def CCLang : Millennium.Language (List SatSym) := fun w =>
  match clauses w with
  | [] => False
  | kr :: rows => ∃ c : ℕ → ℕ, (∀ i < rows.length, c i < kr.length) ∧
      ∀ i < rows.length, ∀ j < rows.length, i ≠ j → c i = c j →
        (rows.getD i []).getD j zero = pos

/-- The target row `zero^3` (three cliques), as a finished row. -/
def ccHdr : List SatSym := [zero, zero, zero, sep]

/-- The **CLIQUE COVER** instance of the formula `w`: the complement of the symmetrized
3-COLORING graph, with target `3`. -/
def CCI (w : List SatSym) : List SatSym :=
  IndSet.cmap (ccHdr ++ Ham.symG (Color.G w))

end Pnp.Karp.CliqueCover
