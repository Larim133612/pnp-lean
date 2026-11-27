import Pnp.Karp.SubNP
import Pnp.Karp.CliqueRed

/-!
# KNAPSACK (0-1, decision version): the language and the reduction instance from SUBSET SUM

## Encoding (numbers in binary, as for SUBSET SUM)

An instance is a word `w` over `SatSym`, read as its rows `clauses w`; a row `r` is the number
`bv r` in binary, least significant bit first (`Pnp/Karp/SubsetSum.lean`).  The rows are
`W :: V :: items`: the capacity `W`, the value goal `V`, and the items as consecutive pairs of
rows (weight, value) (`pairs`; a last unpaired row is a weight with value `0`).
`KnapLang w` holds iff some selection `y` of items has total weight `≤ W` and total value
`≥ V`.

## The reduction from SUBSET SUM

Target `t`, items `as` ↦ capacity `t`, goal `t`, and every item `a` as the pair `(a, a)`
(`KI`).  A word without rows (never in `SSLang`) is sent to `W = 0`, `V = 1`, no items.
-/

namespace Pnp.Karp.Knapsack

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum

/-- The items: consecutive pairs of rows (weight, value). -/
def pairs : List (List SatSym) → List (List SatSym × List SatSym)
  | a :: b :: r => (a, b) :: pairs r
  | [a] => [(a, [])]
  | [] => []

/-- **KNAPSACK** over `SatSym` (see the module docstring). -/
def KnapLang : Millennium.Language (List SatSym) := fun w =>
  ∃ W V items, clauses w = W :: V :: items ∧ ∃ y : List Bool,
    selSum ((pairs items).map Prod.fst) y ≤ bv W ∧ bv V ≤ selSum ((pairs items).map Prod.snd) y

/-- The KNAPSACK instance of a SUBSET SUM instance `w`. -/
def KI (w : List SatSym) : List SatSym :=
  match clauses w with
  | [] => [sep, pos, sep]
  | t :: as => (t :: t :: as.flatMap fun r => [r, r]).flatMap (· ++ [sep])

end Pnp.Karp.Knapsack
