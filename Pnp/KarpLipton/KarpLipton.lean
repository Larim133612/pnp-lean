import Pnp.KarpLipton.Search
import Pnp.KarpLipton.Verifier
import Pnp.PPoly.PPoly

/-!
# The Karp–Lipton theorem, circuit form (M30)

Hypothesis: `SmallExistentials T` (“circuit satisfiability has polynomial-size circuits”, see
`Pnp.KarpLipton.Search`).

* `inPPoly_of_smallExistentials`: the hypothesis implies that every language in the official
  class `NP` has polynomial-size circuits (`NP ⊆ P/poly`), via `Pnp.CookLevin.np_circuit_form`.
* `karp_lipton`: under the hypothesis, every language `L` in the official class `Π₂ᴾ`
  (`Millennium.polynomial_hierarchy_pi_level 2`, strings over `α`) — i.e.
  `L w ↔ ∀ b, |b| ≤ p(|w|) → ∃ c, |c| ≤ q(|w#b|) ∧ L''((w, b), c)` with `L''` in `P` — has the
  **Σ₂ form with a circuit witness**: `L w` holds iff there **exist** polynomial-size search
  circuits `S` such that **for all** short `b`, the certificate read off `S(w#b)` satisfies
  `L''((w, b), ·)`.  The order of the quantifiers is swapped from `∀∃` to `∃∀`.

The proof is the classical one: the verifier of the inner `NP` question is turned into circuits
(`verifier_circuits_on`, `nested_circuits`), the hypothesis plus self-reducibility gives search
circuits (`search_circuit`), and one search circuit per length of `b` serves for all `b`.

What is still missing for the fully official statement `Π₂ᴾ ⊆ Σ₂ᴾ` is uniform: a polynomial-time
Turing machine that evaluates an encoded circuit (so that the inner predicate “`S(w#b)` is a valid
certificate” is in `P`), and the same evaluator gives “circuit satisfiability is in `NP`”, which
turns the hypothesis into exactly `NP ⊆ P/poly`.  Nothing here proves or refutes `P ≠ NP`.
-/

namespace Pnp.KarpLipton

open Pnp.Circuits Pnp.PPoly Pnp.CookLevin Classical

noncomputable section

/-! ## The hypothesis implies `NP ⊆ P/poly` -/

/-- `SmallExistentials T` implies that every official `NP` language has polynomial-size
circuits. -/
theorem inPPoly_of_smallExistentials {T : Polynomial ℕ} (hT : SmallExistentials T)
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {L : Millennium.Language (List α)}
    (hL : Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string α) L) :
    InPPoly L := by
  obtain ⟨p, hp⟩ := np_circuit_form hL
  refine ⟨T.comp (Polynomial.X * Polynomial.C (Fintype.card α) + 2 * p), fun n hn => ?_⟩
  obtain ⟨Z, hZ, f, hf, hfL⟩ := hp n hn
  have hpos : 0 < n * Fintype.card α := Nat.mul_pos hn Fintype.card_pos
  refine ⟨_, (hT _ Z _ f hpos hf).mono ?_, fun w hw => ?_⟩
  · simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_ofNat]
    exact eval_le_of_le T (by omega)
  · rw [decide_eq_true_eq, hfL w hw]

/-! ## Karp–Lipton -/

theorem length_le_nCert {γ : Type} {Q : Polynomial ℕ} {n : ℕ} (c : List γ)
    (hc : c.length ≤ Q.eval n) : c.length ≤ nCert γ Q n := by
  by_cases h : Nonempty γ
  · unfold nCert; rw [if_pos h]; exact hc
  · cases c with
    | nil => simp
    | cons a _ => exact absurd ⟨a⟩ h

/-- **Karp–Lipton theorem, circuit form.** If circuit satisfiability has polynomial-size
circuits, then every official `Π₂ᴾ` language `L` has the `∃∀` form: `L w` holds iff some
polynomial-size search circuits `S` (one for every length `m ≤ p(|w|)` of `b`) produce, for
**every** short `b`, a certificate `c = cert (S(w#b))` with `L''((w, b), c)`, where `L''` is in
the official class `P` (through its complement, as in the definition of `Π₂ᴾ`). -/
theorem karp_lipton {T : Polynomial ℕ} (hT : SmallExistentials T)
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Primcodable α]
    {L : Millennium.Language (List α)}
    (hL : Millennium.polynomial_hierarchy_pi_level 2 (Millennium.fin_encoding_string α) L) :
    ∃ (β γ : Type) (_ : Fintype β) (_ : Fintype γ) (_ : Primcodable β) (_ : Primcodable γ)
      (L'' : Millennium.Language ((List α × List β) × List γ)) (p q r : Polynomial ℕ),
      Millennium.InPolynomialTime
        (Millennium.pair_encoding (Millennium.pair_encoding (Millennium.fin_encoding_string α)
          (Millennium.fin_encoding_string β)) (Millennium.fin_encoding_string γ))
        (Millennium.complement L'') ∧
      ∀ n, ∀ w : List α, w.length = n →
        (L w ↔ ∃ S : (m : ℕ) → (Fin ((n + 1 + m) * Fintype.card (α ⊕ Option β)) → Bool) →
            (Fin (nCert γ q (n + 1 + m) * Fintype.card γ) → Bool),
          (∀ m ≤ p.eval n, HasMCircuitOfSize (S m) (r.eval n)) ∧
          ∀ b : List β, b.length ≤ p.eval n →
            ∃ m' ≤ nCert γ q (n + 1 + b.length),
              L'' ((w, b), cert γ (nCert γ q (n + 1 + b.length)) m'
                (S b.length (oneHot (n + 1 + b.length) (pe2 w b))))) := by
  obtain ⟨β, _, _, L', hL', p, hp⟩ := hL
  obtain ⟨γ, _, _, L'', hL'', q, hq⟩ := hL'
  -- the inner verifier, as circuits on `(w#b)` and certificate blocks
  have hR := nested_circuits L'' hL''
  obtain ⟨P, hP⟩ := verifier_circuits_on (fun x : List (α ⊕ Option β) => ∃ w b, x = pe2 w b)
    (fun x y => ∀ w b, x = pe2 w b → L'' ((w, b), y)) q hR
  have hd : 0 < Fintype.card (α ⊕ Option β) := Fintype.card_pos
  -- search circuits for every length `n'`
  have hS : ∀ n', 0 < n' → ∃ F : (Fin (n' * Fintype.card (α ⊕ Option β)) → Bool) →
      (Fin (nCert γ q n' * Fintype.card γ) → Bool),
      HasMCircuitOfSize F (nCert γ q n' * Fintype.card γ *
        ((n' * Fintype.card (α ⊕ Option β) + nCert γ q n' * Fintype.card γ) *
        T.eval (n' * Fintype.card (α ⊕ Option β) + nCert γ q n' * Fintype.card γ +
          nCert γ q n' * Fintype.card γ + (P.eval n' + 1)))) ∧
      ∀ x, (∃ w b, x = pe2 w b) → x.length = n' →
        (∃ z, ∃ m ≤ nCert γ q n', ∀ w b, x = pe2 w b → L'' ((w, b), cert γ (nCert γ q n') m z)) →
        ∃ m ≤ nCert γ q n', ∀ w b, x = pe2 w b →
          L'' ((w, b), cert γ (nCert γ q n') m (F (oneHot n' x))) := by
    intro n' hn'
    obtain ⟨f, hf, hfR⟩ := hP n' hn'
    obtain ⟨F, hF, hFs⟩ := search_circuit hT (Nat.mul_pos hn' hd) hf
    refine ⟨F, hF, fun x hx hlen hz => ?_⟩
    obtain ⟨z, hz⟩ := hz
    rw [← hfR x hx hlen]
    exact hFs _ ⟨z, (hfR x hx hlen z).2 hz⟩
  -- the size bound, uniformly in `m ≤ p(n)`
  let NP : Polynomial ℕ := Polynomial.X + 1 + p
  let ZP : Polynomial ℕ := q.comp NP * Polynomial.C (Fintype.card γ)
  let DP : Polynomial ℕ := NP * Polynomial.C (Fintype.card (α ⊕ Option β))
  let r : Polynomial ℕ := ZP * ((DP + ZP) * T.comp (DP + ZP + ZP + (P.comp NP + 1)))
  refine ⟨β, γ, inferInstance, inferInstance, inferInstance, inferInstance, L'', p, q, r,
    hL'', fun n w hw => ?_⟩
  let S : (m : ℕ) → (Fin ((n + 1 + m) * Fintype.card (α ⊕ Option β)) → Bool) →
      (Fin (nCert γ q (n + 1 + m) * Fintype.card γ) → Bool) :=
    fun m => (hS (n + 1 + m) (by omega)).choose
  have hlenw : ((Millennium.fin_encoding_string α).encode w).length = n := hw
  have hlenwb : ∀ b : List β, ((Millennium.pair_encoding (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string β)).encode (w, b)).length = n + 1 + b.length := by
    intro b; rw [Millennium.pair_encoding.length_eq]; exact congrArg (· + 1 + b.length) hw
  constructor
  · intro hLw
    refine ⟨S, fun m hm => ?_, fun b hb => ?_⟩
    · refine (hS (n + 1 + m) (by omega)).choose_spec.1.mono ?_
      have h1 : n + 1 + m ≤ NP.eval n := by simp only [NP, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_one]; omega
      have hN : nCert γ q (n + 1 + m) * Fintype.card γ ≤ ZP.eval n := by
        simp only [ZP, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C]
        exact Nat.mul_le_mul_right _ ((nCert_le γ q _).trans (eval_le_of_le q h1))
      have hD : (n + 1 + m) * Fintype.card (α ⊕ Option β) ≤ DP.eval n := by
        simp only [DP, Polynomial.eval_mul, Polynomial.eval_C]
        exact Nat.mul_le_mul_right _ h1
      have hPn : P.eval (n + 1 + m) ≤ (P.comp NP).eval n := by
        rw [Polynomial.eval_comp]; exact eval_le_of_le P h1
      simp only [r, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp,
        Polynomial.eval_one]
      rw [Polynomial.eval_comp] at hPn
      gcongr
      exact eval_le_of_le T (by omega)
    · have hpre : ∃ z, ∃ m ≤ nCert γ q (n + 1 + b.length), ∀ w' b', pe2 w b = pe2 w' b' →
          L'' ((w', b'), cert γ (nCert γ q (n + 1 + b.length)) m z) := by
        have hL'b : ¬ L' (w, b) := fun h => (hp w).2 ⟨b, by rw [hlenw]; exact hb, h⟩ hLw
        obtain ⟨c, hc, hcL⟩ := (hq (w, b)).1 hL'b
        rw [hlenwb] at hc
        obtain ⟨z, hz⟩ := exists_cert c (length_le_nCert c hc)
        refine ⟨z, c.length, length_le_nCert c hc, fun w' b' e => ?_⟩
        obtain ⟨rfl, rfl⟩ := pe2_injective e
        rw [hz]; exact hcL
      obtain ⟨m', hm', h⟩ := (hS (n + 1 + b.length) (by omega)).choose_spec.2 (pe2 w b)
        ⟨w, b, rfl⟩ (by rw [length_pe2, hw]) hpre
      exact ⟨m', hm', h w b rfl⟩
  · rintro ⟨S', -, hS'⟩
    by_contra hLw
    obtain ⟨b, hb, hL'b⟩ := (hp w).1 hLw
    rw [hlenw] at hb
    obtain ⟨m', hm', h⟩ := hS' b hb
    refine (hq (w, b)).2 ⟨_, ?_, h⟩ hL'b
    rw [hlenwb, length_cert hm' (nCert_empty q _)]
    exact hm'.trans (nCert_le γ q _)

end

end Pnp.KarpLipton
