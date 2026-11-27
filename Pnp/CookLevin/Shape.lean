import Pnp.CookLevin.SAT

/-!
# Shapes of uniform Cook–Levin formulas (M33)

The uniform Cook–Levin reduction maps an input `gs` (a word over `Fin W`) to a dense CNF formula
(`Pnp.CookLevin.SATLang`).  The formula is a long, very regular concatenation of clauses; this
file fixes its *shape* independently of the Turing machine that it describes:

* `Shape` collects the finitely many fixed clause patterns and three polynomials
  `PM`, `PT`, `PB` (certificate capacity `M`, number of time steps `T`, number of cells `B`
  as functions of the input length `n = |gs|`);
* `Shape.formula sh gs` is the formula.  Variables are laid out in `T + 1` *slices* of length
  `S = L1 + (B + 2D)·w`; inside a slice, *columns* of width `w` start at `L1`, and the real
  column `j` starts at `col j = L1 + (D + j)·w` (columns `0, …, D-1` and `D+B, …, B+2D-1` are
  padding).

Every clause is a pattern placed at some offset (`at_ a c = zero^a ++ c ++ [sep]`), except for
the step clauses `stepC`/`stepX`, which have a gap in the middle.  The machine-specific
instantiation and the semantics are in later files; `Pnp/CookLevin/Generator.lean` computes
`formula` by one of our stack programs.
-/

namespace Pnp.CookLevin.Uniform

open SatSym

/-- `a` zeros. -/
abbrev zs (a : ℕ) : List SatSym := List.replicate a zero

/-- A clause pattern placed at offset `a`, terminated by `sep`. -/
def at_ (a : ℕ) (c : List SatSym) : List SatSym := zs a ++ c ++ [sep]

/-- All clauses of a list of patterns placed at offset `a`. -/
def place (a : ℕ) (cs : List (List SatSym)) : List SatSym := cs.flatMap (at_ a)

/-- Fixed data of a uniform Cook–Levin formula. -/
structure Shape where
  /-- input alphabet `Fin W` -/
  W : ℕ
  /-- column width -/
  w : ℕ
  /-- start of the columns inside a slice -/
  L1 : ℕ
  /-- number of padding columns on each side -/
  D : ℕ
  /-- certificate capacity `M = PM(n)` -/
  PM : Polynomial ℕ
  /-- number of steps `T = PT(n)` -/
  PT : Polynomial ℕ
  /-- number of real columns `B = PB(n)` -/
  PB : Polynomial ℕ
  /-- clauses at offset `0` -/
  init0 : List (List SatSym)
  /-- clauses at every real column `j < B` of slice `0` -/
  initCol : List (List SatSym)
  /-- clauses at column `i` for the `i`-th input symbol -/
  inCol : Fin W → List (List SatSym)
  /-- clauses at column `n` -/
  sepCol : List (List SatSym)
  /-- clauses at the columns `n + 1 + m`, `m < B - n - 1` -/
  certCol : List (List SatSym)
  /-- clauses at column `n + 1 + M` -/
  boundCol : List (List SatSym)
  /-- clauses at the start of every slice `t ≤ T` -/
  sliceCls : List (List SatSym)
  /-- clauses at the right padding `col B` of every slice `t ≤ T` -/
  rpadCls : List (List SatSym)
  /-- step clauses `zs (t S) ++ a ++ zs (B w + c) ++ [l, sep]`, for every `t < T` -/
  stepC : List (List SatSym × ℕ × SatSym)
  /-- step clauses `zs (t S) ++ a₁ ++ zs (j w) ++ a₂ ++ zs (B w + c) ++ [l, sep]`, `t < T`,
  `j < B` -/
  stepX : List (List SatSym × List SatSym × ℕ × SatSym)
  /-- clauses at the start of slice `T` -/
  acc : List (List SatSym)

namespace Shape

variable (sh : Shape)

/-- Start of column `j` (absolute in slice `0`). -/
def col (j : ℕ) : ℕ := sh.L1 + (sh.D + j) * sh.w

/-- Slice length for `B` real columns. -/
def S (B : ℕ) : ℕ := sh.L1 + (B + 2 * sh.D) * sh.w

/-- The input clauses, starting at column `i`. -/
def inPart : ℕ → List (Fin sh.W) → List SatSym
  | _, [] => []
  | i, g :: gs => place (sh.col i) (sh.inCol g) ++ inPart (i + 1) gs

/-- The fixed clauses of slice `t`. -/
def slicePart (B t : ℕ) : List SatSym :=
  place (t * sh.S B) sh.sliceCls ++ place (t * sh.S B + sh.col B) sh.rpadCls

/-- The step clauses from slice `t` to slice `t + 1`. -/
def stepPart (B t : ℕ) : List SatSym :=
  sh.stepC.flatMap (fun p => zs (t * sh.S B) ++ p.1 ++ zs (B * sh.w + p.2.1) ++ [p.2.2, sep]) ++
  (List.range B).flatMap fun j =>
    sh.stepX.flatMap fun p =>
      zs (t * sh.S B) ++ p.1 ++ zs (j * sh.w) ++ p.2.1 ++ zs (B * sh.w + p.2.2.1) ++
        [p.2.2.2, sep]

/-- **The formula** for the input `gs`. -/
noncomputable def formula (gs : List (Fin sh.W)) : List SatSym :=
  let n := gs.length
  let M := sh.PM.eval n
  let T := sh.PT.eval n
  let B := sh.PB.eval n
  place 0 sh.init0 ++
  (List.range B).flatMap (fun j => place (sh.col j) sh.initCol) ++
  sh.inPart 0 gs ++
  place (sh.col n) sh.sepCol ++
  (List.range (B - n - 1)).flatMap (fun m => place (sh.col (n + 1 + m)) sh.certCol) ++
  place (sh.col (n + 1 + M)) sh.boundCol ++
  (List.range T).flatMap (fun t => sh.slicePart B t ++ sh.stepPart B t) ++
  sh.slicePart B T ++
  place (T * sh.S B) sh.acc

end Shape

/-- One-hot input code of a symbol of `Fin W` (width `W`). -/
def oneHotW (W : ℕ) (g : Fin W) : List Bool := List.ofFn fun i : Fin W => decide (i = g)

end Pnp.CookLevin.Uniform
