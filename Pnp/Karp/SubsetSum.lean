import Pnp.Karp.CliqueRed

/-!
# SUBSET SUM: the language and the reduction instance

## Encoding of SUBSET SUM instances (numbers in binary)

An instance is a word `w` over `SatSym`, read as its rows `clauses w` (the maximal
`sep`-terminated blocks; symbols after the last `sep` are ignored).  A row `r` is a number in
binary, least significant bit first: `bv r = ∑ᵢ [rᵢ = pos] 2ⁱ` (`zero` and `neg` are the bit
`0`).  The first row is the target `t`, the other rows `as` are the items.

`SSLang w` holds iff there are rows (`clauses w = t :: as`) and a selection `y : List Bool` of
items (item `i` is taken iff `y.getD i false`) whose values sum to `bv t` (`selSum as y`).

## The reduction (from a dense CNF formula `w`): exact cover in base `2^b`

Let `N = |trunc w| + 1` (every literal of a clause sits at a position `< N`), `m = |clauses w|`,
`b = N + 1` bits per digit, and `D = N + (2N + 1) m` digits.  Digits:

* `j < N`: variable `j`;
* `clD N k = N + (2N + 1) k`: clause `k`;
* `pD N k j = clD N k + 1 + 2j`, `qD N k j = clD N k + 2 + 2j` (`j < N`): the pair of
  variable `j` in clause `k`.

Every item is a 0/1 digit vector (`ℕ → Bool`, digits `≥ D` ignored), printed by `digRow b D`
(digit `1` = the block `pos :: 0^(b-1)`, digit `0` = `0^b`); the target is the all-ones vector.
The items (`itemsP w`):

* `tP N m j` ("`x_j` true"): variable `j` and `qD N k j` for all `k < m`;
* `fP N m j` ("`x_j` false"): variable `j` and `pD N k j` for all `k < m`;
* for every clause `k` and position `j < |clause k|` with symbol `s`: `wP N k j s`, the clause
  `k` and `pD N k j` (`s = pos`) or `qD N k j` (`s = neg`); the empty vector otherwise;
* fillers `oneP (pD N k j)`, `oneP (qD N k j)` for all `k < m`, `j < N`.

Every digit lies in fewer than `2^b` items, so there are no carries: a selection sums to the
target iff it is an exact cover of the `D` digits (`ExCov`), and an exact cover is the same as
a satisfying assignment (`x_j` true iff `tP N m j` is taken; the clause digit `k` is covered by
one `wP` of a true literal: its pair digit is not covered by `tP`/`fP` of the wrong value).
-/

namespace Pnp.Karp.SubsetSum

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## The language -/

/-- The value of a row in binary, least significant bit first (`pos` = 1, else 0). -/
def bv : List SatSym → ℕ
  | [] => 0
  | s :: r => (if s = pos then 1 else 0) + 2 * bv r

/-- The sum of the items selected by `y` (item `i` is taken iff `y.getD i false`). -/
def selSum : List (List SatSym) → List Bool → ℕ
  | [], _ => 0
  | r :: rs, y => (if y.headD false then bv r else 0) + selSum rs y.tail

/-- **SUBSET SUM** over `SatSym` (see the module docstring). -/
def SSLang : Millennium.Language (List SatSym) := fun w =>
  ∃ t as, clauses w = t :: as ∧ ∃ y : List Bool, selSum as y = bv t

/-! ## Parameters of the reduction -/

/-- The number of clauses. -/
def mC (w : List SatSym) : ℕ := (clauses w).length

/-- The number of variables. -/
def NV (w : List SatSym) : ℕ := (trunc w).length + 1

/-- Bits per digit. -/
def BW (w : List SatSym) : ℕ := NV w + 1

/-- The number of digits. -/
def DD (N m : ℕ) : ℕ := N + (2 * N + 1) * m

/-- The digit of clause `k`. -/
def clD (N k : ℕ) : ℕ := N + (2 * N + 1) * k

/-- The first digit of the pair of variable `j` in clause `k`. -/
def pD (N k j : ℕ) : ℕ := clD N k + 1 + 2 * j

/-- The second digit of the pair of variable `j` in clause `k`. -/
def qD (N k j : ℕ) : ℕ := clD N k + 2 + 2 * j

/-- The symbol at position `j` of clause `k`. -/
def sy (w : List SatSym) (k j : ℕ) : SatSym := ((clauses w).getD k []).getD j zero

/-! ## Digit vectors and their rows -/

/-- The row of a digit vector: `D` blocks of `b` bits, digit `1` = `pos :: 0^(b-1)`. -/
def digRow (b D : ℕ) (S : ℕ → Bool) : List SatSym :=
  (List.range D).flatMap fun p =>
    if S p then pos :: List.replicate (b - 1) zero else List.replicate b zero

/-- "`x_j` true": variable `j` and the second pair digits of `j`. -/
def tP (N m j : ℕ) : ℕ → Bool := fun p => decide (p = j ∨ ∃ k < m, p = qD N k j)

/-- "`x_j` false": variable `j` and the first pair digits of `j`. -/
def fP (N m j : ℕ) : ℕ → Bool := fun p => decide (p = j ∨ ∃ k < m, p = pD N k j)

/-- The witness item of symbol `s` at position `j` of clause `k`. -/
def wP (N k j : ℕ) : SatSym → ℕ → Bool
  | pos => fun p => decide (p = clD N k ∨ p = pD N k j)
  | neg => fun p => decide (p = clD N k ∨ p = qD N k j)
  | _ => fun _ => false

/-- The single digit `q`. -/
def oneP (q : ℕ) : ℕ → Bool := fun p => decide (p = q)

/-- The items, as digit vectors. -/
def itemsP (w : List SatSym) : List (ℕ → Bool) :=
  (List.range (NV w)).flatMap (fun j => [tP (NV w) (mC w) j, fP (NV w) (mC w) j]) ++
    (List.range (mC w)).flatMap (fun k =>
      (List.range ((clauses w).getD k []).length).map fun j => wP (NV w) k j (sy w k j)) ++
    (List.range (mC w)).flatMap (fun k => (List.range (NV w)).flatMap fun j =>
      [oneP (pD (NV w) k j), oneP (qD (NV w) k j)])

/-- The target row (all digits `1`). -/
def target (w : List SatSym) : List SatSym := digRow (BW w) (DD (NV w) (mC w)) fun _ => true

/-- The item rows. -/
def itemRows (w : List SatSym) : List (List SatSym) :=
  (itemsP w).map (digRow (BW w) (DD (NV w) (mC w)))

/-- The SUBSET SUM instance of the formula `w`. -/
def SS (w : List SatSym) : List SatSym := (target w :: itemRows w).flatMap (· ++ [sep])

/-! ## Exact cover -/

/-- The number of items selected by `y` that contain the digit `p`. -/
def cnt : List (ℕ → Bool) → List Bool → ℕ → ℕ
  | [], _, _ => 0
  | S :: Ss, y, p => (if y.headD false && S p then 1 else 0) + cnt Ss y.tail p

/-- Some selection covers every digit `p < D` exactly once. -/
def ExCov (w : List SatSym) : Prop :=
  ∃ y : List Bool, ∀ p < DD (NV w) (mC w), cnt (itemsP w) y p = 1

end Pnp.Karp.SubsetSum
