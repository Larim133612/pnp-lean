import Pnp.Karp.ThreePartU

/-!
# Unary 4-PARTITION (strong NP-completeness): the language and the reduction instance

## The language (numbers in unary)

An instance is a word `w` over `SatSym`, read as its rows `clauses w = items ++ [Bv]`; the
value of a row is its length.  `FPULang w` holds iff the number of items is `4 m`, every size
`a` satisfies `B/5 < a < B/3`, and the items can be split into `m` groups (`f i < m` is the
group of item `i`) each of total size exactly `B`.  NP-completeness of this language is
NP-completeness of 4-PARTITION in the strong sense (Garey–Johnson).

## The reduction (from unary 3-PARTITION, our own construction)

For a unary 3-PARTITION instance `u` (rows `items ++ [Bv]`, `|items| = 3 m`) let `N = |u|`, so
`N` exceeds the total size of the items and `B`.  `fpuT u` has the items `5 N + a` (one per
item `a`), `m` fillers `6 N` and the bound `21 N + B`.  A group summing to `21 N + B` with `k`
items and `j` fillers has `5 k + 6 j = 21`, i.e. `k = 3`, `j = 1`, and the three items sum to
`B`; the bounds hold since `N > B` and `N` exceeds every item.
-/

namespace Pnp.Karp.FourPartU

open Pnp.CookLevin SatSym Pnp.Karp.ThreePartU

/-- **4-PARTITION with numbers in unary** over `SatSym` (see the module docstring). -/
def FPULang : Millennium.Language (List SatSym) := fun w =>
  ∃ items Bv, clauses w = items ++ [Bv] ∧ items.length % 4 = 0 ∧
    (∀ r ∈ items, Bv.length < 5 * r.length ∧ 3 * r.length < Bv.length) ∧
    ∃ f : ℕ → ℕ, (∀ i < items.length, f i < items.length / 4) ∧
      ∀ g < items.length / 4, unSum items f g = Bv.length

/-- The 4-PARTITION instance of a 3-PARTITION instance `u` (see the module docstring):
items `5 N + a`, `⌊|items| / 3⌋` fillers `6 N`, bound `21 N + B`, where `N = |u|`, the items
are all rows but the last one and `B` is the length of the last row. -/
def fpuT (u : List SatSym) : List SatSym :=
  ((clauses u).dropLast.map (fun r => uRow (5 * u.length + r.length)) ++
      List.replicate ((clauses u).dropLast.length / 3) (uRow (6 * u.length)) ++
      [uRow (21 * u.length + ((clauses u).getLastD []).length)]).flatMap (· ++ [sep])

/-- The **unary 4-PARTITION** instance of the formula `w`. -/
def FPUI (w : List SatSym) : List SatSym := fpuT (TPUI w)

end Pnp.Karp.FourPartU
