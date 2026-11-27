import Pnp.Karp.ThreeSAT

/-!
# NAE-3SAT and MAX 2-SAT: the languages and the reduction instances

## The languages (dense CNF format of `Pnp/CookLevin/SAT.lean`)

* `NAESat a c`: the clause `c` has a true literal **and** a false literal under `a`
  (equivalently: `c` is satisfied by `a` and by the complementary assignment `!a`).
* `NAE3Lang w := Is3 w ∧ ∃ a, ∀ c ∈ clauses w, NAESat a c` (**NAE-3SAT**: at most three
  literals per finished clause, `Is3` as for 3-SAT).
* `M2Lang w` (**MAX 2-SAT**): the finished clauses of `w` are `rs ++ [kr]`; every clause of
  `rs` has at most two literals, and some assignment satisfies at least `K = |kr|` clauses of
  `rs` (counted with multiplicity, i.e. as a set of indices).

## The reductions (both from SAT, by the prefix-OR chain of `Pnp/Karp/ThreeSAT.lean`)

Variables: `b = 0` (a global variable), `x_j = 3j + 1` (original variables),
`y_p = 3p + 2` (chain variable of input position `p`: "a literal of the current clause before
position `p` is true"), `z_p = 3p + 3` (an auxiliary variable of position `p`).  Reading the
input left to right with `j` the position inside the current clause and `d = p - j`, the NAE
clauses (`NC`, a clause with two or three literals) are

* start: `NAE(¬y_0, b)`;
* a symbol `s ≠ sep` at position `p`: `NAE(ℓ, y_p, z_p)` where `ℓ` is the literal `s` at `x_j`
  if `s ≠ zero`, and `ℓ = b` if `s = zero`; then `NAE(b, ¬z_p, ¬y_{p+1})`;
* `sep` at position `p`: `NAE(b, y_p)` and `NAE(b, ¬y_{p+1})`.

With `b = false` (NAE is invariant under complementing the assignment) these say exactly
`¬y_0`, `ℓ ∨ y_p ∨ ¬y_{p+1}` (choose `z_p := !(ℓ ∨ y_p)`), `y_p`, `¬y_{p+1}`: the 3-SAT
instance `red w` of `Pnp/Karp/ThreeSAT.lean` (with `x_j ↦ 2j`, `y_p ↦ 2p + 1`).

* `naeI w`: the NAE-3SAT instance (the dense clauses of the `NC`s).
* `m2I w`: the MAX 2-SAT instance: every NAE clause on literals `ℓ₁, ℓ₂(, ℓ₃)` becomes the
  2-clauses `ℓᵢ ∨ ℓₖ` and `¬ℓᵢ ∨ ¬ℓₖ` for all pairs `i < k` (`NC.gad`).  A 3-literal gadget
  has 5 of its 6 clauses satisfied iff the NAE clause is, and 3 otherwise; a 2-literal gadget
  has 2 of 2 resp. 1 (`NC.tgt` = 5 resp. 2).  The threshold is `K = Σ tgt`.
-/

namespace Pnp.Karp.NAE

open Pnp.CookLevin SatSym Pnp.Karp.ThreeSAT

/-! ## The languages -/

/-- **Not-all-equal** satisfaction: `c` has a true and a false literal under `a`
(`ClauseSat (!a) c` says that some literal of `c` is false under `a`). -/
def NAESat (a : ℕ → Bool) (c : List SatSym) : Prop :=
  ClauseSat a c ∧ ClauseSat (fun i => !a i) c

/-- **NAE-3SAT**: dense CNF formulas with at most three literals per clause (`Is3`) having an
assignment under which every clause has a true and a false literal. -/
def NAE3Lang : Millennium.Language (List SatSym) := fun w =>
  Is3 w ∧ ∃ a : ℕ → Bool, ∀ c ∈ clauses w, NAESat a c

/-- **MAX 2-SAT**: the finished clauses are `rs ++ [kr]`, every clause of `rs` has at most two
literals, and some assignment satisfies at least `|kr|` of the clauses of `rs` (a set `S` of
indices of satisfied clauses with `|S| ≥ |kr|`). -/
def M2Lang : Millennium.Language (List SatSym) := fun w =>
  ∃ rs kr, clauses w = rs ++ [kr] ∧ (∀ c ∈ rs, (c.filter (· ≠ zero)).length ≤ 2) ∧
    ∃ a : ℕ → Bool, ∃ S : Finset ℕ, kr.length ≤ S.card ∧
      ∀ i ∈ S, i < rs.length ∧ ClauseSat a (rs.getD i [])

/-! ## Clause shapes -/

/-- Complementary literal symbol. -/
def swp : SatSym → SatSym
  | pos => neg
  | neg => pos
  | s => s

/-- The dense 2-clause with the literal `s` at variable `u` and `t` at variable `u + g + 1`. -/
def two (u : ℕ) (s : SatSym) (g : ℕ) (t : SatSym) : List SatSym := zs u ++ [s] ++ zs g ++ [t]

/-- An NAE clause with two literals (`duo u s g t`: `s` at `u`, `t` at `u + g + 1`) or three
literals (`tri u s g t h r`: additionally `r` at `u + g + h + 2`). -/
inductive NC where
  | duo (u : ℕ) (s : SatSym) (g : ℕ) (t : SatSym)
  | tri (u : ℕ) (s : SatSym) (g : ℕ) (t : SatSym) (h : ℕ) (r : SatSym)

namespace NC

/-- The dense clause. -/
def dense : NC → List SatSym
  | duo u s g t => two u s g t
  | tri u s g t h r => zs u ++ [s] ++ zs g ++ [t] ++ zs h ++ [r]

/-- The MAX 2-SAT gadget: `ℓᵢ ∨ ℓₖ` and `¬ℓᵢ ∨ ¬ℓₖ` for all pairs of literals. -/
def gad : NC → List (List SatSym)
  | duo u s g t => [two u s g t, two u (swp s) g (swp t)]
  | tri u s g t h r =>
    [two u s g t, two u s (g + h + 1) r, two (u + g + 1) t h r,
     two u (swp s) g (swp t), two u (swp s) (g + h + 1) (swp r),
     two (u + g + 1) (swp t) h (swp r)]

/-- The number of gadget clauses satisfied by an NAE-satisfying assignment (the maximum). -/
def tgt : NC → ℕ
  | duo .. => 2
  | tri .. => 5

end NC

/-! ## The reduction -/

/-- The first NAE clause of position `p = j + d` for the symbol `s ≠ sep`: `NAE(ℓ, y_p, z_p)`
(`ℓ` = the literal `s` at `x_j = 3j + 1`, or `b` if `s = zero`). -/
def c1 (s : SatSym) (j d : ℕ) : NC :=
  if s = zero then .tri 0 pos (3 * (j + d) + 1) pos 0 pos
  else .tri (3 * j + 1) s (3 * d) pos 0 pos

/-- The second NAE clause of position `p = j + d`: `NAE(b, ¬z_p, ¬y_{p+1})`. -/
def c2 (j d : ℕ) : NC := .tri 0 pos (3 * (j + d) + 2) neg 1 neg

/-- `NAE(b, y_p)` (`p = j + d`). -/
def sA (j d : ℕ) : NC := .duo 0 pos (3 * (j + d) + 1) pos

/-- `NAE(b, ¬y_{p+1})` (`p = j + d`). -/
def sB (j d : ℕ) : NC := .duo 0 pos (3 * (j + d) + 4) neg

/-- The NAE clauses produced from the input suffix `w` (`j` = position inside the current
clause, `d = p - j`). -/
def goN : List SatSym → ℕ → ℕ → List NC
  | [], _, _ => []
  | s :: w, j, d =>
    if s = sep then sA j d :: sB j d :: goN w 0 (j + d + 1)
    else c1 s j d :: c2 j d :: goN w (j + 1) d

/-- All NAE clauses: `NAE(b, ¬y_0)`, then `goN`. -/
def NCs (w : List SatSym) : List NC := .duo 0 pos 1 neg :: goN w 0 0

/-- **The NAE-3SAT instance** of the formula `w`. -/
def naeI (w : List SatSym) : List SatSym := ((NCs w).map NC.dense).flatMap (· ++ [sep])

/-- The MAX 2-SAT threshold `K = Σ tgt`. -/
def thr (w : List SatSym) : ℕ := ((NCs w).map NC.tgt).sum

/-- **The MAX 2-SAT instance** of the formula `w`: the gadget clauses, then the threshold row
`zero^K`. -/
def m2I (w : List SatSym) : List SatSym :=
  ((NCs w).flatMap NC.gad ++ [zs (thr w)]).flatMap (· ++ [sep])

end Pnp.Karp.NAE
