import Pnp.Karp.ThreePart

/-!
# Unary 3-PARTITION (strong NP-completeness): the language and the reduction instance

## The language (numbers in unary)

An instance is a word `w` over `SatSym`, read as its rows `clauses w = items ++ [Bv]`; a number
is written in **unary**: the value of a row is its length (the reduction writes rows of `pos`).
`TPULang w` holds iff the number of items is `3 m`, every size `a` satisfies `B/4 < a < B/2`,
and the items can be split into `m` groups (`f i < m` is the group of item `i`) each of total
size exactly `B`.  NP-completeness of this language is NP-completeness of 3-PARTITION in the
strong sense (Garey–Johnson): all numbers of a hard instance are polynomially bounded.

## The reduction (from 3-DIMENSIONAL MATCHING, our own construction)

The items `els q ts` are those of the binary reduction (M63, `Pnp/Karp/ThreePart.lean`), but
each one-hot style block of an item is compressed into **one** digit in base `R = 9 L + 1`,
`L = 3 M + 1` (`M = K + 3 q` the tag-block length): a block of length `n` that is all zeros,
the one-hot block of `e`, its complement, or all ones becomes the digit `0`, `L + 1 + e`,
`2 L - n + (n - 1 - e)` (`= 2 L - 1 - e`), or `3 L` (`dv`).  Three such digits (with `e < n ≤ M`)
sum to `3 L` iff they are `{3 L, 0, 0}` or `{L + 1 + e, 2 L - 1 - e, 0}`, i.e. exactly when the
blocks partition the positions; so the groups summing to the bound are the same as in M63
(`IsPat`).  An item has eight digits (three index blocks, three tag blocks, the two state bits)
and a leading digit `1`; the bound has the digits `3 L` (blocks), `1` (states) and the leading
digit `3`.  All values are below `4 R ^ 8`, polynomial in the instance size.
-/

namespace Pnp.Karp.ThreePartU

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

/-! ## The language -/

/-- The total size (unary: the row lengths) of the items in group `b`. -/
def unSum : List (List SatSym) → (ℕ → ℕ) → ℕ → ℕ
  | [], _, _ => 0
  | r :: rs, f, b => (if f 0 = b then r.length else 0) + unSum rs (fun i => f (i + 1)) b

/-- **3-PARTITION with numbers in unary** over `SatSym` (see the module docstring). -/
def TPULang : Millennium.Language (List SatSym) := fun w =>
  ∃ items Bv, clauses w = items ++ [Bv] ∧ items.length % 3 = 0 ∧
    (∀ r ∈ items, Bv.length < 4 * r.length ∧ 2 * r.length < Bv.length) ∧
    ∃ f : ℕ → ℕ, (∀ i < items.length, f i < items.length / 3) ∧
      ∀ g < items.length / 3, unSum items f g = Bv.length

/-! ## The digits of an item -/

/-- The shape of a block: all zeros, one-hot at `e`, the complement of one-hot at `e`,
all ones. -/
inductive Sh
  | z
  | o (e : ℕ)
  | c (e : ℕ)
  | a
  deriving DecidableEq

/-- The shape of the index block `I_{c'}` of an item (as `blkI`). -/
def shI : El → ℕ → Sh
  | .cp c e _, c' => if c' = c then .o e else .z
  | .al c _ _, c' => if c' = (c + 2) % 3 then .a else .z
  | .be c _ e, c' => if c' = c then .c e else if c' = (c + 1) % 3 then .a else .z

/-- The shape of the tag block `L_{c'}` of an item (as `blkL`). -/
def shL : El → ℕ → Sh
  | .cp _ _ _, _ => .z
  | .al c t _, c' => if c' = c then .o t else if c' = (c + 1) % 3 then .c t else .z
  | .be c t _, c' => if c' = c then .c t else if c' = (c + 1) % 3 then .o t else .a

/-- The digit of a block of length `n` and shape `s` (`L` the digit unit). -/
def dv (L n : ℕ) : Sh → ℕ
  | .z => 0
  | .o e => L + 1 + e
  | .c e => 2 * L - n + (n - 1 - e)
  | .a => 3 * L

/-- The digit unit `L = 3 M + 1`. -/
def uL (M : ℕ) : ℕ := 3 * M + 1

/-- The base `R = 9 L + 1`. -/
def uR (M : ℕ) : ℕ := 9 * uL M + 1

/-- Base-`R` value of a digit list (least significant first). -/
def nv (R : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + R * nv R ds

/-- The eight low digits of an item. -/
def udg (q M : ℕ) (x : El) : List ℕ :=
  [dv (uL M) q (shI x 0), dv (uL M) q (shI x 1), dv (uL M) q (shI x 2),
    dv (uL M) M (shL x 0), dv (uL M) M (shL x 1), dv (uL M) M (shL x 2),
    (st1 x).toNat, (st2 x).toNat]

/-- The size of an item: its digits and the leading digit `1`. -/
def uval (q M : ℕ) (x : El) : ℕ := nv (uR M) (udg q M x ++ [1])

/-- The bound: digits `3 L` (blocks), `1` (states), leading digit `3`. -/
def uB (M : ℕ) : ℕ :=
  nv (uR M) [3 * uL M, 3 * uL M, 3 * uL M, 3 * uL M, 3 * uL M, 3 * uL M, 1, 1, 3]

/-- The unary row of a number. -/
def uRow (n : ℕ) : List SatSym := List.replicate n pos

/-- The **unary 3-PARTITION** instance of the triples `ts` over `[0, q)`. -/
def TPUW (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) : List SatSym :=
  ((els q ts).map (fun x => uRow (uval q (mT q ts) x)) ++ [uRow (uB (mT q ts))]).flatMap
    (· ++ [sep])

/-- The **unary 3-PARTITION** instance of the formula `w`, via its 3DM triples (M46). -/
def TPUI (w : List SatSym) : List SatSym := TPUW (qB w) (tris w)

end Pnp.Karp.ThreePartU
