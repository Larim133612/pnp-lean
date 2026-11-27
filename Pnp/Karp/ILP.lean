import Pnp.Karp.HittingSet
import Pnp.Karp.Knapsack

/-!
# 0-1 INTEGER PROGRAMMING: the language and the reduction instance

## Encoding of instances (coefficients in binary, arbitrary signs)

An instance is a word `w` over `SatSym`, read as its rows `clauses w`; every row is one linear
constraint.  A row `r` is cut at its `neg` symbols into chunks (`ichunks r`); a chunk is a
natural number in binary (`bv`, least significant bit first, `pos` = 1, `zero` = 0, as for
SUBSET SUM).  Consecutive chunks are read as pairs `(P₀, N₀), (P₁, N₁), …` (`Knapsack.pairs`; a
last unpaired chunk is `(P, 0)`), and pair `k` stands for the integer `bv Pₖ - bv Nₖ`.
With `z = true :: x` (the constant `z₀ = 1`, then the variables `z_{j+1} = x_j`) the row is the
constraint
`Σₖ zₖ · (bv Pₖ - bv Nₖ) ≥ 0`, i.e. `Σⱼ cⱼ xⱼ ≥ d` with `cⱼ = bv P_{j+1} - bv N_{j+1}` and
`d = bv N₀ - bv P₀`,
written without subtraction as `Σₖ zₖ bv Nₖ ≤ Σₖ zₖ bv Pₖ` (`selSum`).  Every system `C x ≥ d`
with integer `C`, `d` is of this form.

`ILPLang w` holds iff some `0-1` vector `x` satisfies all the constraints.

## The reduction (from SAT)

Let `N = NV w`.  There are `2N` variables: `x_{2j}` is the literal `x_j`, `x_{2j+1}` is `¬x_j`.
For a `pos`/`zero` pattern `r` (a set of variables) let `posR r` be the constraint
`Σ_{r_k = pos} x_k ≥ 1` and `negR r` the constraint `Σ_{r_k = pos} x_k ≤ 1`.  The constraints are
`posR`, `negR` of every pair `pairRow N i` (exactly one of `x_{2i}`, `x_{2i+1}`), and `posR` of
every doubled clause `c.flatMap dbl` (`Pnp/Karp/HittingSet.lean`): some literal of the clause is
true.
-/

namespace Pnp.Karp.ILP

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.HittingSet
  Pnp.Karp.Knapsack

/-- The `neg`-separated chunks of a row. -/
def ichunks : List SatSym → List (List SatSym)
  | [] => [[]]
  | s :: r =>
    if s = neg then [] :: ichunks r
    else match ichunks r with
      | c :: cs => (s :: c) :: cs
      | [] => [[s]]

/-- The constraint of the row `r` holds for the vector `z` (`z₀ = 1` is the constant). -/
def rowOK (r : List SatSym) (z : List Bool) : Prop :=
  selSum ((pairs (ichunks r)).map Prod.snd) z ≤ selSum ((pairs (ichunks r)).map Prod.fst) z

/-- **0-1 INTEGER PROGRAMMING** over `SatSym` (see the module docstring for the encoding). -/
def ILPLang : Millennium.Language (List SatSym) := fun w =>
  ∃ x : List Bool, ∀ r ∈ clauses w, rowOK r (true :: x)

/-- The constraint `Σ_{r_k = pos} x_k ≥ 1`: pair `0` is `(0, 1)`, pair `k + 1` is `(1, 0)` or
`(0, 0)`. -/
def posR (r : List SatSym) : List SatSym :=
  [neg, pos, neg] ++ r.flatMap fun s => if s = pos then [pos, neg, neg] else [neg, neg]

/-- The constraint `Σ_{r_k = pos} x_k ≤ 1`: pair `0` is `(1, 0)`, pair `k + 1` is `(0, 1)` or
`(0, 0)`. -/
def negR (r : List SatSym) : List SatSym :=
  [pos, neg, neg] ++ r.flatMap fun s => if s = pos then [neg, pos, neg] else [neg, neg]

/-- The constraint rows of the instance. -/
def ilpRows (w : List SatSym) : List (List SatSym) :=
  ((List.range (NV w)).map (pairRow (NV w))).flatMap (fun r => [posR r, negR r]) ++
    (clauses w).map fun c => posR (c.flatMap dbl)

/-- The **0-1 INTEGER PROGRAMMING** instance of the formula `w`. -/
def ILPI (w : List SatSym) : List SatSym := (ilpRows w).flatMap (· ++ [sep])

end Pnp.Karp.ILP
