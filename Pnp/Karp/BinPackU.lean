import Pnp.Karp.ThreePartU

/-!
# Unary BIN PACKING (strong NP-completeness): the language and the reduction instance

## The language (numbers in unary)

An instance is a word `w` over `SatSym`, read as its rows `clauses w = items ++ [C, kr]`; every
number is written in **unary** (the value of a row is its length): the item sizes `|r|`, the
bin capacity `|C|` and the number of bins `k = |kr|`.  `UBPLang w` holds iff the items can be
put into the `k` bins (`f i < k` is the bin of item `i`) so that the sizes in every bin sum to
at most `|C|`.  NP-completeness of this language is NP-completeness of BIN PACKING in the
strong sense (Garey–Johnson).

## The reduction (from unary 3-PARTITION)

`bpuT u` appends to a unary 3-PARTITION instance `u` (rows `items ++ [Bv]`) the row of the
number of bins `⌊|clauses u| / 3⌋` (`= |items| / 3` when `3 ∣ |items|`): capacity `B`, `m`
bins.  For the instances `TPUI w` of M64 the total size of the items is exactly `m B`, so `m`
bins of capacity `B` hold the items iff every bin holds exactly `B`.
-/

namespace Pnp.Karp.BinPackU

open Pnp.CookLevin SatSym Pnp.Karp.ThreePartU

/-- **BIN PACKING with numbers in unary** over `SatSym` (see the module docstring). -/
def UBPLang : Millennium.Language (List SatSym) := fun w =>
  ∃ items C kr, clauses w = items ++ [C, kr] ∧
    ∃ f : ℕ → ℕ, (∀ i < items.length, f i < kr.length) ∧
      ∀ b < kr.length, unSum items f b ≤ C.length

/-- Append the row of `⌊(number of rows) / 3⌋` (the number of bins) to an instance. -/
def bpuT (u : List SatSym) : List SatSym :=
  (clauses u ++ [uRow ((clauses u).length / 3)]).flatMap (· ++ [sep])

/-- The **unary BIN PACKING** instance of the formula `w`. -/
def BPUI (w : List SatSym) : List SatSym := bpuT (TPUI w)

end Pnp.Karp.BinPackU
