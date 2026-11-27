import Pnp.Karp.ThreeDM

/-!
# STEINER TREE in graphs: the language and the reduction instance

## Encoding of instances

A word `w` over `SatSym` is read as its rows `clauses w = kr :: tr :: rows`:

* the budget `K = |kr|` (unary);
* `rows` is an adjacency matrix on the vertices `[0, n)`, `n = |rows|`: the graph has the
  (undirected) edge `{a, b}` iff `a ≠ b`, `a, b < n` and the entry `(a, b)` or `(b, a)` is `pos`
  (rows may be shorter than `n`; missing entries are `zero`);
* the **terminals** are the vertices `t < n` with `tr.getD t zero = pos`.

`STLang w` holds iff some set `F` of at most `K` edges (each given as an ordered pair `(a, b)`
with entry `(a, b) = pos`) connects all terminals: any two terminals are joined by a path of
edges of `F`.  A minimal such `F` is a tree (a *Steiner tree*), so this is the problem
STEINER TREE IN GRAPHS (Karp 1972; Garey–Johnson ND12): is there a subtree of the graph with at
most `K` edges containing all terminals?

## The reduction (from SAT, through the X3C instance of M46; Karp's construction)

For the X3C instance `X3I w` (ground set `[0, 3q)`, triple rows `triRows w`) the graph has

* the element vertices `0, …, 3q - 1` and the root `3q` (all terminals, empty rows);
* one vertex `3q + 1 + i` for every triple row `r_i`, with row `r_i ++ [pos]`: edges to the
  three elements of the triple and to the root;

and the budget `K = 4q`.  An exact cover (`q` triples) gives the tree with the `q` root edges and
the `3q` element edges.  Conversely, the component of the root in a connecting edge set `F`
contains the `3q + 1` terminals and `t` triple vertices, so `|F| ≥ 3q + t`; hence `t ≤ q`, and
since every element is joined to a triple vertex containing it, the `t ≤ q` triples cover all
`3q` elements: they form an exact cover.
-/

namespace Pnp.Karp.Steiner

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.ThreeDM

/-- The entry `(a, b)` of the matrix `rows`. -/
def ent (rows : List (List SatSym)) (a b : ℕ) : SatSym := (rows.getD a []).getD b zero

/-- `(a, b)` is an edge of the graph of `rows`, given in the direction of its `pos` entry. -/
def IsEdge (rows : List (List SatSym)) (e : ℕ × ℕ) : Prop :=
  e.1 < rows.length ∧ e.2 < rows.length ∧ e.1 ≠ e.2 ∧ ent rows e.1 e.2 = pos

/-- `t` is a terminal. -/
def IsTerm (tr : List SatSym) (rows : List (List SatSym)) (t : ℕ) : Prop :=
  t < rows.length ∧ tr.getD t zero = pos

/-- Adjacency along the edges of `F` (both directions). -/
def adjF (F : Finset (ℕ × ℕ)) (a b : ℕ) : Prop := (a, b) ∈ F ∨ (b, a) ∈ F

/-- **STEINER TREE** (in graphs) over `SatSym` (see the module docstring). -/
def STLang : Millennium.Language (List SatSym) := fun w =>
  ∃ kr tr rows, clauses w = kr :: tr :: rows ∧
    ∃ F : Finset (ℕ × ℕ), F.card ≤ kr.length ∧ (∀ e ∈ F, IsEdge rows e) ∧
      ∀ a b, IsTerm tr rows a → IsTerm tr rows b → Relation.ReflTransGen (adjF F) a b

/-- The matrix rows of the instance: `3q + 1` empty rows (elements and root), then the triple
rows, each followed by the root column `pos`. -/
def stRows (q : ℕ) (rs : List (List SatSym)) : List (List SatSym) :=
  List.replicate (3 * q + 1) [] ++ rs.map (· ++ [pos])

/-- The **STEINER TREE** instance of the X3C data `(q, rs)`: budget `zero^(4q)`, terminal row
`pos^(3q+1)`. -/
def STW (q : ℕ) (rs : List (List SatSym)) : List SatSym :=
  (List.replicate (4 * q) zero :: List.replicate (3 * q + 1) pos :: stRows q rs).flatMap
    (· ++ [sep])

/-- The **STEINER TREE** instance of the formula `w`. -/
def STI (w : List SatSym) : List SatSym := STW (qB w) (triRows w)

end Pnp.Karp.Steiner
