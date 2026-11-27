import Pnp.Karp.SubNP
import Pnp.Karp.CliqueRed

/-!
# PARTITION: the language and the reduction instance from SUBSET SUM

## Encoding (numbers in binary, as for SUBSET SUM)

An instance is a word `w` over `SatSym`, read as its rows `clauses w`; a row `r` is the number
`bv r` in binary, least significant bit first (`Pnp/Karp/SubsetSum.lean`).
`PartLang w` holds iff some selection `y` of rows has exactly half of the total sum, i.e. the
rows can be split into two parts with equal sums.

## The reduction from SUBSET SUM

For a SUBSET SUM instance with target `t` and items `as` (sum `S`), the PARTITION instance has
the items `as` and two more numbers `S` and `2t` (`PI`).  The total is `2S + 2t`; the part
containing `S` either contains `2t` (then `t = 0`) or its other members sum to `t`.
A word without rows (never in `SSLang`) is sent to the single row `1` (odd total).

`S` is written as the program computes it: ripple-carry additions (`sv_addL`, M41) of the item
rows (`accRows`), printed with `toRow` (`true ↦ pos`, `false ↦ zero`).
-/

namespace Pnp.Karp.Partition

open Pnp.Relativize Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum

/-- The sum of all rows. -/
def totSum : List (List SatSym) → ℕ
  | [] => 0
  | r :: rs => bv r + totSum rs

/-- **PARTITION** over `SatSym`: some selection of the rows has half of the total sum. -/
def PartLang : Millennium.Language (List SatSym) := fun w =>
  ∃ y : List Bool, 2 * selSum (clauses w) y = totSum (clauses w)

/-- A bit string as a row (`true ↦ pos`, `false ↦ zero`). -/
def toRow (A : Str) : List SatSym := A.map fun b => if b then pos else zero

/-- Add the rows to the accumulator `A` (ripple carry, as the program does it). -/
def accRows (A : Str) : List (List SatSym) → Str
  | [] => A
  | r :: rs => accRows (sv_addL false A (sv_bits r)) rs

/-- The PARTITION instance of a SUBSET SUM instance `w`. -/
def PI (w : List SatSym) : List SatSym :=
  match clauses w with
  | [] => [pos, sep]
  | t :: as => (as ++ [toRow (accRows [] as), zero :: toRow (sv_bits t)]).flatMap (· ++ [sep])

end Pnp.Karp.Partition
