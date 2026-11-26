import Pnp.Circuits.Basic

/-!
# The natural proofs barrier (Razborov–Rudich 1994) (M9)

A *combinatorial property* of Boolean functions is a family `Γ n ⊆ {f : {0,1}ⁿ → {0,1}}`.
Following Razborov–Rudich, measured in the truth-table length `N = 2ⁿ`:

* **constructive** (`Constructive`): membership `f ∈ Γ n` is decided, from the truth table of `f`,
  by a circuit with `q(2ⁿ)` gates for a polynomial `q` (i.e. `Γ ∈ P/poly` as a language of truth
  tables);
* **large** (`Large`): `Γ n` contains at least a `1 / r(2ⁿ)` fraction of all functions;
* **useful against P/poly** (`UsefulAgainstPPoly`): for every polynomial `p` and infinitely many
  `n`, no function of `Γ n` has a circuit with `p(n)` gates. (This is equivalent to the
  Razborov–Rudich formulation "every sequence `fₙ ∈ Γ n` has super-polynomial circuit size".)

A *pseudorandom function family* (`PRFamily`) assigns to every `n` a finite nonempty key space
`K n` and functions `F n k : {0,1}ⁿ → {0,1}`. It is in P/poly if every `F n k` has a circuit of
polynomial size in `n`, and it is *secure* (`PRFamily.Secure`) if every distinguisher circuit of
size `q(2ⁿ)` that reads a whole truth table tells a random key's `F n k` from a uniformly random
function only with advantage `< 1 / r(2ⁿ)`, for all large `n` — the (strong, "exponential")
security notion used by Razborov–Rudich.

Main results:

* `natural_breaks_prf` (one input length, explicit parameters): if `Γ` is decided by a circuit
  `T` of size `c`, has density `≥ δ`, and contains no function with a circuit of size `s`, then
  `T` distinguishes *every* family of functions with circuits of size `s` from random functions
  with advantage `≥ δ`.
* `natural_proofs_barrier`: a constructive, large property useful against P/poly breaks every
  pseudorandom function family in P/poly.
* `no_natural_property_of_secure_prf`: contrapositive — if a secure pseudorandom function family
  in P/poly exists, no property is constructive, large and useful against P/poly.

What is *not* formalized: the meta-level claim that known lower-bound proofs "naturalize", and the
construction of pseudorandom functions from one-way functions (Håstad–Impagliazzo–Levin–Luby,
Goldreich–Goldwasser–Micali). Security of a PRF is an explicit hypothesis.
-/

namespace Pnp.NaturalProofs

open Pnp.Circuits Classical

noncomputable section

/-- Boolean functions on `n` variables. -/
abbrev BoolFun (n : ℕ) := (Fin n → Bool) → Bool

/-- Index the `2ⁿ` inputs by `Fin (2ⁿ)` (binary expansion). -/
def inputEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The truth table of `f`, a bit string of length `2ⁿ`. -/
def truthTable {n : ℕ} (f : BoolFun n) : Fin (2 ^ n) → Bool :=
  fun i => f ((inputEquiv n).symm i)

theorem truthTable_injective (n : ℕ) : Function.Injective (truthTable (n := n)) := by
  intro f g h
  funext x
  simpa [truthTable] using congrFun h (inputEquiv n x)

theorem card_boolFun (n : ℕ) : Fintype.card (BoolFun n) = 2 ^ 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Uniform probability of an event on a finite type. -/
def prob {α : Type} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card α

theorem prob_nonneg {α : Type} [Fintype α] (P : α → Prop) : 0 ≤ prob P := by
  unfold prob; positivity

theorem prob_eq_zero {α : Type} [Fintype α] {P : α → Prop} (h : ∀ a, ¬ P a) : prob P = 0 := by
  unfold prob
  rw [Finset.filter_false_of_mem fun a _ => h a]
  simp

/-- Distinguishing advantage of a truth-table test `T` against the function family `F`:
`|Pr_f[T(f) = 1] − Pr_k[T(F k) = 1]|` with `f` a uniformly random function and `k` a uniformly
random key. -/
def advantage {n : ℕ} {K : Type} [Fintype K] (T : (Fin (2 ^ n) → Bool) → Bool)
    (F : K → BoolFun n) : ℝ :=
  |prob (fun f : BoolFun n => T (truthTable f) = true) - prob (fun k => T (truthTable (F k)) = true)|

theorem HasCircuitOfSize.mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s s' : ℕ}
    (h : HasCircuitOfSize f s) (hs : s ≤ s') : HasCircuitOfSize f s' := by
  obtain ⟨t, ht, C, hC⟩ := h
  exact ⟨t, ht.trans hs, C, hC⟩

/-! ## One input length, explicit parameters -/

/-- **Core of Razborov–Rudich.** Let `Γ` be a property of `n`-variable functions that is
* decided from truth tables by a test `T` with a circuit of size `c`,
* of density at least `δ`, and
* *useful* against size `s`: no member has a circuit of size `s`.

Then `T` (a circuit of size `c`) distinguishes every family `F` of functions with circuits of
size `s` from truly random functions with advantage at least `δ`. -/
theorem natural_breaks_prf {n s c : ℕ} {Γ : Set (BoolFun n)} {δ : ℝ}
    {T : (Fin (2 ^ n) → Bool) → Bool} (hT : HasCircuitOfSize T c)
    (hTΓ : ∀ f, T (truthTable f) = true ↔ f ∈ Γ)
    (hlarge : δ ≤ prob (· ∈ Γ))
    (huseful : ∀ f ∈ Γ, ¬ HasCircuitOfSize f s)
    {K : Type} [Fintype K] (F : K → BoolFun n) (hF : ∀ k, HasCircuitOfSize (F k) s) :
    ∃ T' : (Fin (2 ^ n) → Bool) → Bool, HasCircuitOfSize T' c ∧ δ ≤ advantage T' F := by
  refine ⟨T, hT, ?_⟩
  have h0 : prob (fun k => T (truthTable (F k)) = true) = 0 :=
    prob_eq_zero fun k hk => huseful _ ((hTΓ _).1 hk) (hF k)
  have h1 : prob (fun f : BoolFun n => T (truthTable f) = true) = prob (· ∈ Γ) := by
    simp only [hTΓ]
  rw [advantage, h0, h1, sub_zero, abs_of_nonneg (prob_nonneg _)]
  exact hlarge

/-! ## Asymptotic version -/

/-- `Γ` is constructive: decided from truth tables by circuits of size polynomial in `2ⁿ`. -/
def Constructive (Γ : ∀ n, Set (BoolFun n)) : Prop :=
  ∃ q : Polynomial ℕ, ∀ n, ∃ T : (Fin (2 ^ n) → Bool) → Bool,
    HasCircuitOfSize T (q.eval (2 ^ n)) ∧ ∀ f, T (truthTable f) = true ↔ f ∈ Γ n

/-- `Γ` is large: `|Γ n| ≥ 2^(2ⁿ) / r(2ⁿ)` for a polynomial `r`. -/
def Large (Γ : ∀ n, Set (BoolFun n)) : Prop :=
  ∃ r : Polynomial ℕ, ∀ n,
    2 ^ 2 ^ n ≤ r.eval (2 ^ n) * (Finset.univ.filter (· ∈ Γ n)).card

/-- `Γ` is useful against P/poly: for every polynomial `p`, for infinitely many `n`, no function
in `Γ n` has a circuit with `p(n)` gates. -/
def UsefulAgainstPPoly (Γ : ∀ n, Set (BoolFun n)) : Prop :=
  ∀ p : Polynomial ℕ, ∀ N, ∃ n ≥ N, ∀ f ∈ Γ n, ¬ HasCircuitOfSize f (p.eval n)

/-- A natural property useful against P/poly (Razborov–Rudich). -/
def NaturalAgainstPPoly (Γ : ∀ n, Set (BoolFun n)) : Prop :=
  Constructive Γ ∧ Large Γ ∧ UsefulAgainstPPoly Γ

/-- A keyed family of Boolean functions: for each `n`, a finite nonempty key space and
functions `F n k` on `n` variables. -/
structure PRFamily where
  Key : ℕ → Type
  [fintype : ∀ n, Fintype (Key n)]
  [nonempty : ∀ n, Nonempty (Key n)]
  F : ∀ n, Key n → BoolFun n

attribute [instance] PRFamily.fintype PRFamily.nonempty

/-- Every member `F n k` has a circuit of size polynomial in `n`. -/
def PRFamily.InPPoly (G : PRFamily) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n k, HasCircuitOfSize (G.F n k) (p.eval n)

/-- Security against truth-table distinguishers of size polynomial in `2ⁿ`: for all polynomials
`q`, `r` and all large `n`, every distinguisher with `q(2ⁿ)` gates has advantage `< 1 / r(2ⁿ)`. -/
def PRFamily.Secure (G : PRFamily) : Prop :=
  ∀ q r : Polynomial ℕ, ∃ N, ∀ n ≥ N, ∀ T : (Fin (2 ^ n) → Bool) → Bool,
    HasCircuitOfSize T (q.eval (2 ^ n)) → advantage T (G.F n) * r.eval (2 ^ n) < 1

/-- **Natural proofs barrier (Razborov–Rudich).** A constructive, large property that is useful
against P/poly breaks every pseudorandom function family in P/poly. -/
theorem natural_proofs_barrier {Γ : ∀ n, Set (BoolFun n)} (hΓ : NaturalAgainstPPoly Γ)
    (G : PRFamily) (hG : G.InPPoly) : ¬ G.Secure := by
  obtain ⟨⟨q, hq⟩, ⟨r, hr⟩, hu⟩ := hΓ
  obtain ⟨p, hp⟩ := hG
  intro hsec
  obtain ⟨N, hN⟩ := hsec q r
  obtain ⟨n, hn, hun⟩ := hu p N
  obtain ⟨T, hT, hTΓ⟩ := hq n
  have hpos : (0 : ℝ) < 2 ^ 2 ^ n := by positivity
  have hδ : (1 : ℝ) / r.eval (2 ^ n) ≤ prob (· ∈ Γ n) := by
    rcases Nat.eq_zero_or_pos (r.eval (2 ^ n)) with h0 | h0
    · rw [h0, Nat.cast_zero, div_zero]; exact prob_nonneg _
    · rw [prob, card_boolFun, div_le_div_iff₀ (by exact_mod_cast h0) (by exact_mod_cast hpos),
        one_mul]
      have := hr n
      push_cast
      exact_mod_cast (by simpa [mul_comm] using this)
  obtain ⟨T', hT', hadv⟩ :=
    natural_breaks_prf hT hTΓ hδ hun (G.F n) (fun k => hp n k)
  have hlt := hN n hn T' hT'
  rcases Nat.eq_zero_or_pos (r.eval (2 ^ n)) with h0 | h0
  · -- `r(2ⁿ) = 0` contradicts largeness: `2^(2ⁿ) ≤ 0`.
    have := hr n
    rw [h0, zero_mul] at this
    have h2 : 0 < 2 ^ 2 ^ n := by positivity
    omega
  · have hr0 : (0 : ℝ) < r.eval (2 ^ n) := by exact_mod_cast h0
    have : 1 ≤ advantage T' (G.F n) * r.eval (2 ^ n) := by
      rw [div_le_iff₀ hr0] at hadv
      linarith
    linarith

/-- **Contrapositive.** If some pseudorandom function family in P/poly is secure, then no
property of Boolean functions is simultaneously constructive, large and useful against P/poly:
no "natural proof" can show that a function lies outside P/poly. -/
theorem no_natural_property_of_secure_prf (G : PRFamily) (hG : G.InPPoly) (hsec : G.Secure)
    (Γ : ∀ n, Set (BoolFun n)) : ¬ NaturalAgainstPPoly Γ :=
  fun hΓ => natural_proofs_barrier hΓ G hG hsec

end

end Pnp.NaturalProofs
