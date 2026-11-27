import Pnp.Karp.Partition

/-!
# JOB SEQUENCING: the language and the reduction instance

## Encoding of instances (numbers in binary, as for SUBSET SUM)

A word `w` over `SatSym` is read as its rows `clauses w = K :: js`; every row is a number in
binary (`bv`, least significant bit first).  The rows `js` are read in consecutive triples: job
`j < ⌊|js| / 3⌋` has execution time `T j = bv js[3j]`, deadline `D j = bv js[3j+1]` and penalty
`P j = bv js[3j+2]` (left-over rows are ignored).

A schedule is an ordering `π` of the jobs (a permutation of `[0, m)`, `m = ⌊|js| / 3⌋`) run one
after another on one machine from time `0`; job `j` is *late* if its completion time exceeds
`D j`.  `JSLang w` holds iff some schedule has total penalty of late jobs at most `bv K`
(Karp 1972 "JOB SEQUENCING"; Garey–Johnson SS3, SEQUENCING TO MINIMIZE TARDY TASK WEIGHT).

## The reduction (from SUBSET SUM)

For a SUBSET SUM instance `t :: as` (sum `S`), `JI` has the bound `K = S`, a job `(a, t, a)`
(time `a`, deadline `t`, penalty `a`) for every item `a`, and a job `(1, 0, t)` that is always
late.  A schedule pays `t` for the last job plus the items not finished by `t`; the items on
time sum to at most `t`, so the penalty is `≤ S` iff the items on time sum to exactly `t`.
A word without rows (never in `SSLang`) is sent to a single job `(1, 0, 1)` with bound `0`.

`S` is written as the PARTITION program computes it (`toRow (accRows [] as)`, M42).
-/

namespace Pnp.Karp.JobSeq

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.Partition

/-- The execution time of job `j`. -/
def jT (js : List (List SatSym)) (j : ℕ) : ℕ := bv (js.getD (3 * j) [])

/-- The deadline of job `j`. -/
def jD (js : List (List SatSym)) (j : ℕ) : ℕ := bv (js.getD (3 * j + 1) [])

/-- The penalty of job `j`. -/
def jP (js : List (List SatSym)) (j : ℕ) : ℕ := bv (js.getD (3 * j + 2) [])

/-- The total penalty of the late jobs when the jobs `π` run in this order from time `s`. -/
def latePen (js : List (List SatSym)) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | s, j :: π => (if jD js j < s + jT js j then jP js j else 0) + latePen js (s + jT js j) π

/-- **JOB SEQUENCING** over `SatSym` (see the module docstring). -/
def JSLang : Millennium.Language (List SatSym) := fun w =>
  ∃ K js, clauses w = K :: js ∧
    ∃ π : List ℕ, π.Perm (List.range (js.length / 3)) ∧ latePen js 0 π ≤ bv K

/-- The **JOB SEQUENCING** instance of a SUBSET SUM instance `w`. -/
def JI (w : List SatSym) : List SatSym :=
  match clauses w with
  | [] => ([[], [pos], [], [pos]] : List (List SatSym)).flatMap (· ++ [sep])
  | t :: as =>
      (toRow (accRows [] as) :: (as.flatMap fun a => [a, t, a]) ++ [[pos], [], t]).flatMap
        (· ++ [sep])

end Pnp.Karp.JobSeq
