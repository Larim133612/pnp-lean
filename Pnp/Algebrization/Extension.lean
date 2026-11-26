import Pnp.Oracle.Relativization

/-!
# Algebraic oracles and low-degree extensions (Aaronson–Wigderson)

Following Aaronson and Wigderson, *Algebrization: A New Barrier in Complexity Theory*
(2008/2009), an *extension* of a Boolean oracle `A` is a family of polynomials
`Ã_{𝔽,m} : 𝔽^m → 𝔽`, one for every finite field `𝔽` and every arity `m`, that agrees with
`A` on the Boolean cube `{0,1}^m` and has degree at most `2` in each variable
(multiquadratic).

* Finite fields are named by natural numbers: `Fld q` is the Galois field with
  `charOf q ^ (k + 1)` elements, where `q = Nat.pair p k` and `charOf q = p` if `p` is
  prime (otherwise `2`).  Every finite field is isomorphic to some `Fld q`
  (`exists_ringEquiv_Fld`), so this covers *all* finite fields, including the non-prime
  ones such as `𝔽₄, 𝔽₈, 𝔽₉`.
* `AlgOracle`: a polynomial `Ã q m ∈ (Fld q)[X₀, …, X_{m-1}]` for every `q` and `m`.
* `IsExtension A Ã`: `Ã` is a multiquadratic extension of `A`.
  `IsExtension.exists_poly` transports it to an arbitrary finite field `K`.
* `toOracle Ã`: `Ã` as an ordinary (Boolean) oracle for the stack machines of
  `Pnp.Oracle.Machine`: the query `encQ q j xs` (a field index `q`, a bit index `j` and a
  point `xs` written as a list of naturals, each `< |Fld q|`, coding field elements by a
  fixed bijection `fcode q : Fld q ≃ Fin |Fld q|`) is answered by bit `j` of the code of
  `Ã_{q,m}(xs)`.  Natural numbers are written in binary with every bit doubled, so a
  machine can write and parse queries efficiently.

`P (toOracle Ã)` and `NP (toOracle Ã)` are then the classes `P^Ã` and `NP^Ã`.

Scope of the model (stated honestly): the oracle answers queries about the fixed
representatives `Fld q`; the element coding `fcode q` is an arbitrary (noncomputable) fixed
bijection.  Aaronson–Wigderson's definition is up to such representations.
-/

namespace Pnp.Algebrize

open Pnp.Relativize MvPolynomial

/-! ### Finite fields -/

/-- The characteristic named by the field index `q = Nat.pair p k`: `p` if prime, else `2`. -/
def charOf (q : ℕ) : ℕ := if (Nat.unpair q).1.Prime then (Nat.unpair q).1 else 2

theorem charOf_prime (q : ℕ) : (charOf q).Prime := by
  unfold charOf
  split_ifs with h
  · exact h
  · exact Nat.prime_two

instance (q : ℕ) : Fact (charOf q).Prime := ⟨charOf_prime q⟩

/-- The finite field named by `q = Nat.pair p k`, with `charOf q ^ (k + 1)` elements. -/
abbrev Fld (q : ℕ) : Type := GaloisField (charOf q) ((Nat.unpair q).2 + 1)

noncomputable instance (q : ℕ) : Fintype (Fld q) := Fintype.ofFinite _

noncomputable instance (q : ℕ) : DecidableEq (Fld q) := Classical.decEq _

theorem card_Fld (q : ℕ) :
    Fintype.card (Fld q) = charOf q ^ ((Nat.unpair q).2 + 1) := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card _ _ (by omega)

/-- Example: `Fld (Nat.pair 2 1)` is the field with four elements (not a prime field). -/
theorem card_Fld_four : Fintype.card (Fld (Nat.pair 2 1)) = 4 := by
  rw [card_Fld]
  simp [charOf, Nat.unpair_pair, Nat.prime_two]

/-- **Every finite field is one of the `Fld q`** (up to ring isomorphism). -/
theorem exists_ringEquiv_Fld (K : Type*) [Field K] [Fintype K] :
    ∃ q : ℕ, Nonempty (Fld q ≃+* K) := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  refine ⟨Nat.pair (ringChar K) (n - 1), ⟨FiniteField.ringEquivOfCardEq ?_⟩⟩
  have hn := n.pos
  rw [card_Fld, hcard, Nat.unpair_pair]
  simp only [charOf, Nat.unpair_pair, if_pos hp]
  congr 1
  omega

/-- A fixed coding of the elements of `Fld q` by natural numbers `< |Fld q|`. -/
noncomputable def fcode (q : ℕ) : Fld q ≃ Fin (Fintype.card (Fld q)) := Fintype.equivFin _

/-- The field element with code `v` (taken modulo `|Fld q|`). -/
noncomputable def felt (q v : ℕ) : Fld q :=
  (fcode q).symm ⟨v % Fintype.card (Fld q), Nat.mod_lt _ Fintype.card_pos⟩

/-! ### Algebraic oracles and extensions -/

/-- An algebraic oracle: a polynomial over `Fld q` in `m` variables for every `q, m`. -/
abbrev AlgOracle := (q m : ℕ) → MvPolynomial (Fin m) (Fld q)

/-- A Boolean point of the cube, as a point of `R^m`. -/
def boolPt {R : Type*} [Zero R] [One R] {m : ℕ} (z : Fin m → Bool) : Fin m → R :=
  fun i => if z i then 1 else 0

open Classical in
/-- `Ã` is a multiquadratic extension of `A`: for every finite field `Fld q` and arity
`m`, the polynomial `Ã q m` has degree `≤ 2` in each variable and equals the indicator
of `A` on the Boolean cube. -/
def IsExtension (A : Oracle) (Ã : AlgOracle) : Prop :=
  ∀ q m : ℕ, (∀ i, (Ã q m).degreeOf i ≤ 2) ∧
    ∀ z : Fin m → Bool, eval (boolPt z) (Ã q m) = if List.ofFn z ∈ A then 1 else 0

open Classical in
/-- An extension gives, over **every** finite field `K`, a multiquadratic polynomial that
agrees with `A` on the Boolean cube. -/
theorem IsExtension.exists_poly {A : Oracle} {Ã : AlgOracle} (h : IsExtension A Ã)
    (K : Type*) [Field K] [Fintype K] (m : ℕ) :
    ∃ P : MvPolynomial (Fin m) K, (∀ i, P.degreeOf i ≤ 2) ∧
      ∀ z : Fin m → Bool, eval (boolPt z) P = if List.ofFn z ∈ A then 1 else 0 := by
  obtain ⟨q, ⟨e⟩⟩ := exists_ringEquiv_Fld K
  obtain ⟨hdeg, hval⟩ := h q m
  refine ⟨map (e : Fld q →+* K) (Ã q m), fun i => ?_, fun z => ?_⟩
  · rw [degreeOf_def, degrees_map_of_injective _ e.injective, ← degreeOf_def]
    exact hdeg i
  · have hb : (boolPt z : Fin m → K) = (e : Fld q →+* K) ∘ boolPt z := by
      funext i; simp only [boolPt, Function.comp]; split_ifs <;> simp
    rw [hb, eval_map]
    show eval₂ ((e : Fld q →+* K).comp (RingHom.id _)) _ _ = _
    rw [← eval₂_comp_left]
    change (e : Fld q →+* K) (eval (boolPt z) (Ã q m)) = _
    rw [hval z]
    split_ifs <;> simp

/-! ### Encoding of algebraic queries as bit strings -/

/-- Binary digits of `n` (least significant first; bijective base-2 numeration). -/
def bin : ℕ → Str
  | 0 => []
  | n + 1 => (n % 2 == 1) :: bin (n / 2)
decreasing_by omega

/-- Self-delimiting code of a natural number: binary digits, each preceded by `true`,
terminated by `false`. -/
def encNat (n : ℕ) : Str := ((bin n).flatMap fun b => [true, b]) ++ [false]

/-- The query string asking for bit `j` of (the code of) `Ã_{q,m}(xs)`, `m = xs.length`. -/
def encQ (p j : ℕ) (xs : List ℕ) : Str :=
  encNat p ++ encNat j ++ (xs.map encNat).flatten

/-- The point of `(Fld q)^m` described by a list of naturals of length `m`. -/
noncomputable def pt (q : ℕ) (xs : List ℕ) : Fin xs.length → Fld q := fun i => felt q (xs.get i)

/-- The answer to the query `(q, j, xs)`: bit `j` of the code of `Ã_{q,|xs|}(xs)`. -/
def answer (Ã : AlgOracle) (q j : ℕ) (xs : List ℕ) : Prop :=
  ((fcode q (eval (pt q xs) (Ã q xs.length))).val).testBit j = true

/-- The algebraic oracle `Ã` viewed as a Boolean oracle: a well-formed query `encQ q j xs`
(all coordinates `< |Fld q|`) is in the oracle iff the answer bit is `1`. -/
def toOracle (Ã : AlgOracle) : Oracle :=
  {s | ∃ q j xs, (∀ v ∈ xs, v < Fintype.card (Fld q)) ∧ s = encQ q j xs ∧ answer Ã q j xs}

theorem length_encNat_pos (n : ℕ) : 0 < (encNat n).length := by
  simp [encNat]

/-- A query about arity `m` is longer than `m`: every coordinate costs at least one bit,
and so does the field index. -/
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
