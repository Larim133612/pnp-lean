import Pnp.Karp.SubsetSum

/-!
# 3-DIMENSIONAL MATCHING and EXACT COVER BY 3-SETS: the languages and the reduction instance

## Encoding of instances

A word `w` over `SatSym` is read as its rows `clauses w` (the maximal `sep`-terminated blocks;
symbols after the last `sep` are ignored).  A row `r` stands for the set of positions `p` with
`r.getD p zero = pos`.  The first row `u` is a header giving the size of the ground set by its
length; the other rows `rs` are the sets.  A selection `y : List Bool` takes row `i` iff
`y.getD i false`; `covC rs y p` counts the selected rows containing `p`.

* **3DM** (`DMLang`): `q = |u|`, the ground set is `X ⊔ Y ⊔ Z` with `X = [0,q)`,
  `Y = [q,2q)`, `Z = [2q,3q)`; every row has length `3q` and exactly one `pos` in each of the
  three blocks of length `q` (`IsTri q`, so it is a triple of `X × Y × Z`); some selection
  covers every `p < 3q` exactly once (a perfect 3-dimensional matching).
* **X3C** (`X3CLang`): the ground set is `[0,n)` with `n = |u|`; every row has length `n` and
  exactly three `pos` (a 3-element subset); some selection covers every `p < n` exactly once.

## The reduction (from a dense CNF formula `w`; Garey–Johnson)

Let `N = NV w = |trunc w| + 1` (variables `i < N`), `m = mC w` (clauses `k < m`) and
`q = 2 N m`.  A triple is `(a, b, c)` with `a, b, c < q` (coordinates inside `X`, `Y`, `Z`).

* `X` holds the tips: `tipI m i k v = 2 (m i + k) + (if v then 0 else 1)` (`x_i[k]` for `v`,
  `¬x_i[k]` for `¬v`).
* `Y` and `Z` hold the same index scheme: the ring elements `a_i[k] = b_i[k] = m i + k`, the
  clause elements `s[k] = N m + k`, and the garbage elements `g[t] = N m + m + t`
  (`t < m (N - 1)`).

The triples (`tris w`):

* ring of variable `i`, for every `k < m`: `(tipI m i k false, m i + k, m i + k)` ("`x_i`
  true" covers the negative tips) and `(tipI m i k true, m i + (k + 1) % m, m i + k)` ("`x_i`
  false" covers the positive tips);
* clause `k`, for every position `j` of the clause with symbol `pos` (resp. `neg`):
  `(tipI m j k true, N m + k, N m + k)` (resp. `tipI m j k false`); nothing for `zero`;
* garbage: `(x, N m + m + t, N m + m + t)` for every tip `x < q` and `t < m (N - 1)`.

The triple `(a, b, c)` is printed as the row `oh q a ++ oh q b ++ oh q c` (`oh q a` is the
one-hot row of length `q` with `pos` at `a`).  The 3DM instance `DMI w` has the header
`zero^q`; the X3C instance `X3I w` has the same rows and the header `zero^(3q)`.
-/

namespace Pnp.Karp.ThreeDM

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum

/-! ## The languages -/

/-- The number of selected rows (row `i` is taken iff `y.getD i false`) containing `p`. -/
def covC : List (List SatSym) → List Bool → ℕ → ℕ
  | [], _, _ => 0
  | r :: rs, y, p =>
      (if y.headD false && decide (r.getD p zero = pos) then 1 else 0) + covC rs y.tail p

/-- A row is a triple of `X × Y × Z` (blocks of length `q`). -/
def IsTri (q : ℕ) (r : List SatSym) : Prop :=
  r.length = 3 * q ∧ (r.take q).count pos = 1 ∧ ((r.drop q).take q).count pos = 1 ∧
    (r.drop (2 * q)).count pos = 1

/-- **3-DIMENSIONAL MATCHING** over `SatSym` (see the module docstring). -/
def DMLang : Millennium.Language (List SatSym) := fun w =>
  ∃ u rs, clauses w = u :: rs ∧ (∀ r ∈ rs, IsTri u.length r) ∧
    ∃ y : List Bool, ∀ p < 3 * u.length, covC rs y p = 1

/-- **EXACT COVER BY 3-SETS** over `SatSym` (see the module docstring). -/
def X3CLang : Millennium.Language (List SatSym) := fun w =>
  ∃ u rs, clauses w = u :: rs ∧ (∀ r ∈ rs, r.length = u.length ∧ r.count pos = 3) ∧
    ∃ y : List Bool, ∀ p < u.length, covC rs y p = 1

/-! ## The triples of the reduction -/

/-- The block length `q = 2 N m`. -/
def qB (w : List SatSym) : ℕ := 2 * NV w * mC w

/-- The tip `x_i[k]` (`v = true`) or `¬x_i[k]` (`v = false`). -/
def tipI (m i k : ℕ) (v : Bool) : ℕ := 2 * (m * i + k) + if v then 0 else 1

/-- The two ring triples of variable `i` at clause index `k`. -/
def ringT (m i k : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(tipI m i k false, m * i + k, m * i + k), (tipI m i k true, m * i + (k + 1) % m, m * i + k)]

/-- The clause triple of symbol `s` at position `j` of clause `k`. -/
def clT (N m k j : ℕ) : SatSym → List (ℕ × ℕ × ℕ)
  | pos => [(tipI m j k true, N * m + k, N * m + k)]
  | neg => [(tipI m j k false, N * m + k, N * m + k)]
  | _ => []

/-- The garbage triples of tip `x`. -/
def garT (N m x : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (m * (N - 1))).map fun t => (x, N * m + m + t, N * m + m + t)

/-- All triples of the reduction. -/
def tris (w : List SatSym) : List (ℕ × ℕ × ℕ) :=
  (List.range (NV w)).flatMap (fun i => (List.range (mC w)).flatMap fun k => ringT (mC w) i k) ++
    (List.range (mC w)).flatMap (fun k =>
      (List.range ((clauses w).getD k []).length).flatMap fun j => clT (NV w) (mC w) k j (sy w k j)) ++
    (List.range (qB w)).flatMap (fun x => garT (NV w) (mC w) x)

/-! ## Rows and instances -/

/-- The one-hot row of length `q` with `pos` at `a`. -/
def oh (q a : ℕ) : List SatSym := (List.range q).map fun i => if i = a then pos else zero

/-- The row of a triple. -/
def triRow (q : ℕ) (t : ℕ × ℕ × ℕ) : List SatSym := oh q t.1 ++ oh q t.2.1 ++ oh q t.2.2

/-- The set rows of the instance. -/
def triRows (w : List SatSym) : List (List SatSym) := (tris w).map (triRow (qB w))

/-- The **3DM** instance of the formula `w` (header `zero^q`). -/
def DMI (w : List SatSym) : List SatSym :=
  (List.replicate (qB w) zero :: triRows w).flatMap (· ++ [sep])

/-- The **X3C** instance of the formula `w` (header `zero^(3q)`, same rows). -/
def X3I (w : List SatSym) : List SatSym :=
  (List.replicate (3 * qB w) zero :: triRows w).flatMap (· ++ [sep])

/-! ## Abstract covering by triples -/

/-- The number of selected triples covering `p` (coordinate `a` is `p = a`, `b` is
`p = q + b`, `c` is `p = 2q + c`). -/
def covT (q : ℕ) : List (ℕ × ℕ × ℕ) → List Bool → ℕ → ℕ
  | [], _, _ => 0
  | t :: ts, y, p =>
      (if y.headD false && decide (p = t.1 ∨ p = q + t.2.1 ∨ p = 2 * q + t.2.2) then 1 else 0) +
        covT q ts y.tail p

end Pnp.Karp.ThreeDM
