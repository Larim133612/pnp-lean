import Pnp.Oracle.Relativization

/-!
# Algebraic oracles and low-degree extensions (Aaronson–Wigderson)

Following Aaronson and Wigderson, *Algebrization: A New Barrier in Complexity Theory*
(2008/2009), an *extension* of a Boolean oracle `A` is a family of polynomials
`Ã_{p,m} : 𝔽_p^m → 𝔽_p`, one for every prime field `𝔽_p = ZMod p` and every arity `m`,
that agrees with `A` on the Boolean cube `{0,1}^m` and has degree at most `2` in each
variable (multiquadratic).

* `AlgOracle`: a polynomial `Ã p m ∈ 𝔽_p[X₀, …, X_{m-1}]` for every `p` and `m`
  (only prime `p` are ever used).
* `IsExtension A Ã`: `Ã` is a multiquadratic extension of `A`.
* `toOracle Ã`: `Ã` as an ordinary (Boolean) oracle for the stack machines of
  `Pnp.Oracle.Machine`: the query `encQ p j xs` (a prime `p`, a bit index `j` and a point
  `xs ∈ {0,…,p-1}^m` written as a list of naturals) is answered by bit `j` of
  `Ã_{p,m}(xs)`.  Natural numbers are written in binary with every bit doubled, so a
  machine can write and parse queries efficiently.

`P (toOracle Ã)` and `NP (toOracle Ã)` are then the classes `P^Ã` and `NP^Ã`.

Scope of the model (stated honestly): Aaronson–Wigderson allow extensions over all
finite fields; we use the prime fields `ZMod p` only.
-/

namespace Pnp.Algebrize

open Pnp.Relativize MvPolynomial

/-- An algebraic oracle: a polynomial over `ZMod p` in `m` variables for every `p, m`. -/
abbrev AlgOracle := (p m : ℕ) → MvPolynomial (Fin m) (ZMod p)

/-- A Boolean point of the cube, as a point of `R^m`. -/
def boolPt {R : Type*} [Zero R] [One R] {m : ℕ} (z : Fin m → Bool) : Fin m → R :=
  fun i => if z i then 1 else 0

open Classical in
/-- `Ã` is a multiquadratic extension of `A`: for every prime `p` and arity `m`, the
polynomial `Ã p m` has degree `≤ 2` in each variable and equals the indicator of `A`
on the Boolean cube. -/
def IsExtension (A : Oracle) (Ã : AlgOracle) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ m : ℕ, (∀ i, (Ã p m).degreeOf i ≤ 2) ∧
    ∀ z : Fin m → Bool, eval (boolPt z) (Ã p m) = if List.ofFn z ∈ A then 1 else 0

/-! ### Encoding of algebraic queries as bit strings -/

/-- Binary digits of `n` (least significant first; bijective base-2 numeration). -/
def bin : ℕ → Str
  | 0 => []
  | n + 1 => (n % 2 == 1) :: bin (n / 2)
decreasing_by omega

/-- Self-delimiting code of a natural number: binary digits, each preceded by `true`,
terminated by `false`. -/
def encNat (n : ℕ) : Str := ((bin n).flatMap fun b => [true, b]) ++ [false]

/-- The query string asking for bit `j` of `Ã_{p,m}(xs)`, `m = xs.length`. -/
def encQ (p j : ℕ) (xs : List ℕ) : Str :=
  encNat p ++ encNat j ++ (xs.map encNat).flatten

/-- The point of `(ZMod p)^m` described by a list of naturals of length `m`. -/
def pt (p : ℕ) (xs : List ℕ) : Fin xs.length → ZMod p := fun i => (xs.get i : ZMod p)

/-- The answer to the query `(p, j, xs)`: bit `j` of `Ã_{p,|xs|}(xs)`. -/
def answer (Ã : AlgOracle) (p j : ℕ) (xs : List ℕ) : Prop :=
  ((eval (pt p xs) (Ã p xs.length)).val).testBit j = true

/-- The algebraic oracle `Ã` viewed as a Boolean oracle: a well-formed query `encQ p j xs`
(`p` prime, all coordinates `< p`) is in the oracle iff the answer bit is `1`. -/
def toOracle (Ã : AlgOracle) : Oracle :=
  {s | ∃ p j xs, p.Prime ∧ (∀ v ∈ xs, v < p) ∧ s = encQ p j xs ∧ answer Ã p j xs}

theorem length_encNat_pos (n : ℕ) : 0 < (encNat n).length := by
  simp [encNat]

/-- A query about arity `m` is longer than `m`: every coordinate costs at least one bit,
and so does the prime. -/
theorem length_lt_length_encQ (p j : ℕ) (xs : List ℕ) : xs.length < (encQ p j xs).length := by
  have h : ∀ ys : List ℕ, ys.length ≤ (ys.map encNat).flatten.length := by
    intro ys
    induction ys with
    | nil => simp
    | cons y ys ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      have := length_encNat_pos y
      omega
  have := h xs
  have := length_encNat_pos p
  simp only [encQ, List.length_append]
  omega

/-- `P^Ã` and `NP^Ã`. -/
abbrev PA (Ã : AlgOracle) : Set (Set Str) := P (toOracle Ã)
abbrev NPA (Ã : AlgOracle) : Set (Set Str) := NP (toOracle Ã)

end Pnp.Algebrize
