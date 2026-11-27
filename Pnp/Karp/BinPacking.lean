import Pnp.Karp.Partition

/-!
# BIN PACKING: the language and the reduction instance from PARTITION

## Encoding (numbers in binary, as for SUBSET SUM / PARTITION)

An instance is a word `w` over `SatSym`, read as its rows `clauses w = items ++ [C, kr]`:
the items `items` (sizes `bv r` in binary, least significant bit first), the bin capacity
`bv C` (binary) and the number of bins `k = |kr|` (unary).
`BPLang w` holds iff the items can be put into the `k` bins (`f i < k` is the bin of item `i`)
so that the sizes in every bin sum to at most `bv C`.

## The reduction from PARTITION

For a PARTITION instance with rows `rs` (total `T`), the BIN PACKING instance has the items
`rs`, capacity `⌊T / 2⌋` and `2` bins (`BPI`).  The capacity is printed as the program
computes it: the binary row of `T` (`toRow (accRows [] rs)`, as in `PI`) without its least
significant bit (`bv r.tail = bv r / 2`).  If `T` is odd neither instance is a yes-instance;
if `T` is even, two bins of capacity `T / 2` hold all items iff each holds exactly `T / 2`.
-/

namespace Pnp.Karp.BinPacking

open Pnp.Relativize Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.Partition

/-- The sum of the sizes of the items put into bin `b` by `f` (item `i` goes to bin `f i`). -/
def binSum : List (List SatSym) → (ℕ → ℕ) → ℕ → ℕ
  | [], _, _ => 0
  | r :: rs, f, b => (if f 0 = b then bv r else 0) + binSum rs (fun i => f (i + 1)) b

/-- **BIN PACKING** over `SatSym` (see the module docstring for the encoding). -/
def BPLang : Millennium.Language (List SatSym) := fun w =>
  ∃ items C kr, clauses w = items ++ [C, kr] ∧
    ∃ f : ℕ → ℕ, (∀ i < items.length, f i < kr.length) ∧
      ∀ b < kr.length, binSum items f b ≤ bv C

/-- The **BIN PACKING** instance of a PARTITION instance `w`: items `clauses w`, capacity
`⌊T / 2⌋`, two bins. -/
def BPI (w : List SatSym) : List SatSym :=
  (clauses w ++ [(toRow (accRows [] (clauses w))).tail, [zero, zero]]).flatMap (· ++ [sep])

end Pnp.Karp.BinPacking
