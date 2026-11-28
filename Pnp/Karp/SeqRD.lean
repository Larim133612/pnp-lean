import Pnp.Karp.ThreePartU

/-!
# SEQUENCING WITH RELEASE TIMES AND DEADLINES (unary): the language and the instance

## The language (numbers in unary)

An instance is a word `w` over `SatSym`, read as its rows `clauses w`; three consecutive rows
`ℓ, r, d` describe one task (its length `|ℓ|`, release time `|r|` and deadline `|d|`; every
number is a row length, i.e. in unary).  `SRDLang w` holds iff the number of rows is a multiple
of `3` and there are start times `s i` with `r_i ≤ s_i`, `s_i + ℓ_i ≤ d_i`, and no two tasks
overlap on the single machine.  This is problem SS1 of Garey–Johnson; NP-completeness of the
unary version is NP-completeness in the strong sense.

## The reduction (from unary BIN PACKING / 3-PARTITION, Garey–Johnson)

For a unary 3-PARTITION instance `u` (rows `items ++ [Bv]`, `m = ⌊|items| / 3⌋`, `B = |Bv|`),
`srdT u` has a task `(a, 0, m (B + 1) - 1)` per item `a` and `m - 1` separator tasks
`(1, j (B + 1) - 1, j (B + 1))`, `j = 1, …, m - 1`.  The separators are forced to run at
`j (B + 1) - 1`; they cut `[0, m (B + 1) - 1)` into `m` windows of length `B`, so the items can
be scheduled iff they fit into `m` bins of capacity `B`.
-/

namespace Pnp.Karp.SeqRD

open Pnp.CookLevin SatSym Pnp.Karp.ThreePartU

/-- The length, release time and deadline of task `i` (rows `3 i`, `3 i + 1`, `3 i + 2`). -/
def tLen (rs : List (List SatSym)) (i : ℕ) : ℕ := (rs.getD (3 * i) []).length
def tRel (rs : List (List SatSym)) (i : ℕ) : ℕ := (rs.getD (3 * i + 1) []).length
def tDl (rs : List (List SatSym)) (i : ℕ) : ℕ := (rs.getD (3 * i + 2) []).length

/-- **SEQUENCING WITH RELEASE TIMES AND DEADLINES, numbers in unary** (see the module
docstring). -/
def SRDLang : Millennium.Language (List SatSym) := fun w =>
  (clauses w).length % 3 = 0 ∧
    ∃ s : ℕ → ℕ, (∀ i < (clauses w).length / 3,
        tRel (clauses w) i ≤ s i ∧ s i + tLen (clauses w) i ≤ tDl (clauses w) i) ∧
      ∀ i < (clauses w).length / 3, ∀ j < (clauses w).length / 3, i ≠ j →
        s i + tLen (clauses w) i ≤ s j ∨ s j + tLen (clauses w) j ≤ s i

/-- The three rows of the task `(ℓ, r, d)`. -/
def task (l r d : ℕ) : List (List SatSym) := [uRow l, uRow r, uRow d]

/-- The scheduling instance of a 3-PARTITION instance `u` (see the module docstring). -/
def srdT (u : List SatSym) : List SatSym :=
  let items := (clauses u).dropLast
  let B := ((clauses u).getLastD []).length
  let m := items.length / 3
  (items.flatMap (fun r => task r.length 0 (m * (B + 1) - 1)) ++
      (List.range (m - 1)).flatMap (fun j => task 1 ((j + 1) * (B + 1) - 1) ((j + 1) * (B + 1))))
    |>.flatMap (· ++ [sep])

/-- The **unary scheduling** instance of the formula `w`. -/
def SRDI (w : List SatSym) : List SatSym := srdT (TPUI w)

end Pnp.Karp.SeqRD
