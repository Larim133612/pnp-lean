import Pnp.Karp.CliqueRed

/-!
# 3-COLORING: the language and the reduction graph

## Encoding of 3-COLORING instances

An instance is a word `w` over `SatSym` (the fixed output alphabet of
`Pnp.CookLevin.FunBridge.computable_of_cmd_code`), read as its rows `clauses w` (the maximal
`sep`-terminated blocks; symbols after the last `sep` are ignored).  The rows form an adjacency
matrix: there is an edge between `i` and `j` iff the entry `(i, j)` is `pos`, where the entry
`(i, j)` is `((clauses w).getD i []).getD j zero` (missing entries count as `zero`).  A single
`pos` entry in either orientation gives the (undirected) edge; a `pos` on the diagonal is a loop,
which makes the graph not 3-colorable.

`ColLang w` holds iff there is a coloring `c : ℕ → Fin 3` with `c i ≠ c j` for every edge.

## The reduction graph `G w` (from a dense CNF formula `w`)

Let `A = annW w` be the annotated positions of `trunc w` (`(symbol, clause index, index inside the
clause)`, from `Pnp/Karp/CliqueRed.lean`) and `L = |A|`.  Vertices:

* `0 = T`, `1 = F`, `2 = B` (a triangle; their colors name "true", "false", "base");
* `3 + 2j` and `4 + 2j` for `j < L`: the literals `xⱼ` and `¬xⱼ` (adjacent to each other and to `B`);
* for the position `p` of `A`, with base `b = 3 + 2L + 3p`: an OR gadget `x = b`, `y = b + 1`,
  `o = b + 2` with edges `x—acc`, `x—y`, `x—o`, `y—lit`, `y—o`, `o—B`, where
  `acc` is `F` at the start of a clause (index `0`) and the output `b - 1` of the previous
  position otherwise, and `lit` is `3 + 2j` (`pos`), `4 + 2j` (`neg`) or `F` (`zero`, `sep`).
  At a `sep` position additionally `o—F`, forcing the output of the clause to be "true".

The OR gadget: if both inputs are colored `F` then `o` is colored `F`; if one input is `T` the
gadget can be colored with `o = T`.  Hence `G w` is 3-colorable iff `w` is satisfiable
(`sat_iff_col`, in `ColorRed.lean`).
-/

namespace Pnp.Karp.Color

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## The language -/

/-- **3-COLORING** over `SatSym` (see the module docstring for the encoding). -/
def ColLang : Millennium.Language (List SatSym) := fun w =>
  ∃ c : ℕ → Fin 3, ∀ i j, ((clauses w).getD i []).getD j zero = pos → c i ≠ c j

/-! ## The reduction graph -/

/-- Rows of the triangle `T = 0, F = 1, B = 2`. -/
def triRows : List (List SatSym) := [[zero, pos, pos], [zero, zero, pos], []]

/-- Row of the literal `xⱼ` (vertex `3 + 2j`): edges to `B` and to `¬xⱼ` (vertex `4 + 2j`). -/
def vpRow (j : ℕ) : List SatSym := [zero, zero, pos] ++ List.replicate (2 * j + 1) zero ++ [pos]

/-- Row of the literal `¬xⱼ` (vertex `4 + 2j`): edge to `B`. -/
def vnRow : List SatSym := [zero, zero, pos]

/-- The literal rows for the variables `j < L`. -/
def litRows (L : ℕ) : List (List SatSym) :=
  (List.range L).flatMap fun j => [vpRow j, vnRow]

/-- The column of the literal input of a gadget. -/
def litCol : SatSym → ℕ → ℕ
  | pos, j => 3 + 2 * j
  | neg, j => 4 + 2 * j
  | _, _ => 1

/-- Row of `x` (vertex `b`): edges to `acc`, `y = b + 1`, `o = b + 2`. -/
def xRow (b j : ℕ) : List SatSym :=
  if j = 0 then [zero, pos] ++ List.replicate (b - 1) zero ++ [pos, pos]
  else List.replicate (b - 1) zero ++ [pos, zero, pos, pos]

/-- Row of `y` (vertex `b + 1`): edge to the literal input. -/
def yRow (s : SatSym) (j : ℕ) : List SatSym := List.replicate (litCol s j) zero ++ [pos]

/-- Row of `o` (vertex `b + 2`): edges to `B`, `y = b + 1`, and to `F` at a `sep` position. -/
def oRow (s : SatSym) (b : ℕ) : List SatSym :=
  [zero, if s = sep then pos else zero, pos] ++ List.replicate (b - 2) zero ++ [pos]

/-- The base vertex of the gadget of position `p`. -/
def base (L p : ℕ) : ℕ := 3 + 2 * L + 3 * p

/-- The three gadget rows of the annotated position `a` at position `p`. -/
def gadRows (L p : ℕ) (a : SatSym × ℕ × ℕ) : List (List SatSym) :=
  [xRow (base L p) a.2.2, yRow a.1 a.2.2, oRow a.1 (base L p)]

/-- The gadget rows of the positions `p, p + 1, …` (annotated by the list). -/
def gadAll (L : ℕ) : ℕ → List (SatSym × ℕ × ℕ) → List (List SatSym)
  | _, [] => []
  | p, a :: A => gadRows L p a ++ gadAll L (p + 1) A

/-- The adjacency matrix rows of `G w`. -/
def gRows (w : List SatSym) : List (List SatSym) :=
  triRows ++ litRows (annW w).length ++ gadAll (annW w).length 0 (annW w)

/-- The 3-COLORING instance of the formula `w`. -/
def G (w : List SatSym) : List SatSym := (gRows w).flatMap (· ++ [sep])

/-! ## Rows of `G w` -/

theorem sep_not_mem_replicate (n : ℕ) : sep ∉ List.replicate n zero := by
  simp [List.mem_replicate]

theorem sep_not_mem_gadRows (L p : ℕ) (a : SatSym × ℕ × ℕ) : ∀ c ∈ gadRows L p a, sep ∉ c := by
  intro c hc
  simp only [gadRows, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · unfold xRow; split_ifs <;> simp [List.mem_replicate]
  · simp only [yRow, List.mem_append, List.mem_replicate, List.mem_singleton]; simp
  · simp only [oRow, List.mem_append, List.mem_replicate, List.mem_cons]
    split_ifs <;> simp

theorem sep_not_mem_gadAll (L : ℕ) : ∀ (p : ℕ) (A : List (SatSym × ℕ × ℕ)),
    ∀ c ∈ gadAll L p A, sep ∉ c
  | _, [] => by simp [gadAll]
  | p, a :: A => by
    intro c hc
    simp only [gadAll, List.mem_append] at hc
    rcases hc with h | h
    · exact sep_not_mem_gadRows L p a c h
    · exact sep_not_mem_gadAll L (p + 1) A c h

theorem sep_not_mem_gRows (w : List SatSym) : ∀ c ∈ gRows w, sep ∉ c := by
  intro c hc
  simp only [gRows, List.mem_append, triRows, litRows, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl | rfl) | ⟨j, _, rfl | rfl⟩) | h
  · simp
  · simp
  · simp
  · simp [vpRow, List.mem_replicate]
  · simp [vnRow]
  · exact sep_not_mem_gadAll _ _ _ c h

theorem clauses_G (w : List SatSym) : clauses (G w) = gRows w :=
  clauses_flatMap _ (sep_not_mem_gRows w)

end Pnp.Karp.Color
