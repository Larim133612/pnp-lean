import Pnp.CookLevin.CircuitForm
import Pnp.Upstream.PolynomialHierarchy

/-!
# Polynomial-size circuits for verifiers (Karp–Lipton preparations)

* `verifier_circuits_on`: a generalization of `Pnp.CookLevin.np_circuits_of_relation`. Given
  polynomial-size circuits deciding a relation `R x y` on the pair strings `x#y` (only for inputs
  `x` satisfying a side condition `Sx`), we get, for every input length `n ≥ 1`, one
  polynomial-size circuit on the one-hot bits of `x` and `nCert Γ Q n` certificate blocks that
  decides `∃ m ≤ nCert Γ Q n, R x (cert Γ (nCert Γ Q n) m z)`.
* `nested_circuits`: an official polynomial-time predicate on nested pairs `((w, b), y)` (given
  through its complement) is simulated by polynomial-size circuits on the strings `(w#b)#y`.
-/

namespace Pnp.KarpLipton

open Pnp.Circuits Pnp.PPoly Pnp.CookLevin Classical

noncomputable section

/-- Certificate block count: `Q(n)` blocks if `Γ` is inhabited, else `0`. -/
def nCert (Γ : Type) (Q : Polynomial ℕ) (n : ℕ) : ℕ := if Nonempty Γ then Q.eval n else 0

theorem nCert_le (Γ : Type) (Q : Polynomial ℕ) (n : ℕ) : nCert Γ Q n ≤ Q.eval n := by
  unfold nCert; split_ifs <;> omega

theorem nCert_empty {Γ : Type} (Q : Polynomial ℕ) (n : ℕ) (h : ¬ Nonempty Γ) :
    nCert Γ Q n = 0 := by
  unfold nCert; rw [if_neg h]

/-- **Verifier circuits** for a relation decided by circuits on pair strings `x#y`, for inputs
`x` satisfying `Sx`. -/
theorem verifier_circuits_on {δ Γ : Type} [Fintype δ] [DecidableEq δ] [Nonempty δ]
    [Fintype Γ] [DecidableEq Γ]
    (Sx : List δ → Prop) (R : List δ → List Γ → Prop) (Q : Polynomial ℕ)
    (hR : ∃ p₁ : Polynomial ℕ, ∀ n', 0 < n' →
      ∃ g : (Fin (n' * Fintype.card (δ ⊕ Option Γ)) → Bool) → Bool,
        HasCircuitOfSize g (p₁.eval n') ∧
        ∀ x y, Sx x → (pe2 x y).length = n' → (g (oneHot n' (pe2 x y)) = true ↔ R x y)) :
    ∃ P : Polynomial ℕ, ∀ n, 0 < n →
      ∃ f : (Fin (n * Fintype.card δ + nCert Γ Q n * Fintype.card Γ) → Bool) → Bool,
        HasCircuitOfSize f (P.eval n) ∧
        ∀ x, Sx x → x.length = n → ∀ z : Fin (nCert Γ Q n * Fintype.card Γ) → Bool,
          (f (Fin.append (oneHot n x) z) = true ↔
            ∃ m ≤ nCert Γ Q n, R x (cert Γ (nCert Γ Q n) m z)) := by
  obtain ⟨p₁, hp₁⟩ := hR
  let c := Fintype.card (δ ⊕ Option Γ)
  let J := juntaSize (Fintype.card (Fin (Fintype.card δ) ⊕ Fin (Fintype.card Γ)))
  let mp : Polynomial ℕ := Polynomial.X + 1 + Q
  let Bp : Polynomial ℕ := mp * Polynomial.C (c * J) + p₁.comp mp
  let P : Polynomial ℕ := (Q + 1) * Bp + Q
  refine ⟨P, fun n hn => ?_⟩
  have ha : 0 < Fintype.card δ := Fintype.card_pos
  have hNk : nCert Γ Q n ≤ Q.eval n := nCert_le Γ Q n
  have hNΓ : ¬ Nonempty Γ → nCert Γ Q n = 0 := nCert_empty Q n
  have hN0 : 0 < n * Fintype.card δ + nCert Γ Q n * Fintype.card Γ :=
    Nat.add_pos_left (Nat.mul_pos hn ha) _
  -- the circuit for certificate length `m`
  let Cm : ℕ → (Fin (n * Fintype.card δ + nCert Γ Q n * Fintype.card Γ) → Bool) → Bool :=
    fun m => (hp₁ (n + 1 + m) (by omega)).choose ∘ encN δ Γ n (nCert Γ Q n) m
  let B := (n + 1 + Q.eval n) * c * J + p₁.eval (n + 1 + Q.eval n)
  have hCm : ∀ m ≤ nCert Γ Q n, HasCircuitOfSize (Cm m) B := by
    intro m hm
    have h1 := (hasMCircuitOfSize_encN (α := δ) (Γ := Γ) (n := n) (N := nCert Γ Q n) (m := m)
      hN0).comp_single (hp₁ (n + 1 + m) (by omega)).choose_spec.1
    refine h1.mono ?_
    have hm' : n + 1 + m ≤ n + 1 + Q.eval n := by omega
    have := eval_le_of_le p₁ hm'
    have : (n + 1 + m) * c * J ≤ (n + 1 + Q.eval n) * c * J := by gcongr
    have e : (n + 1 + m) * Fintype.card (δ ⊕ Option Γ) *
        juntaSize (Fintype.card (Fin (Fintype.card δ) ⊕ Fin (Fintype.card Γ))) =
        (n + 1 + m) * c * J := rfl
    omega
  have hCm_spec : ∀ m ≤ nCert Γ Q n, ∀ (x : List δ)
      (z : Fin (nCert Γ Q n * Fintype.card Γ) → Bool), Sx x → x.length = n →
      (Cm m (Fin.append (oneHot n x) z) = true ↔ R x (cert Γ (nCert Γ Q n) m z)) := by
    intro m hm x z hS hx
    simp only [Cm, Function.comp_apply, encN_append, decWord_oneHot x hx]
    have := (hp₁ (n + 1 + m) (by omega)).choose_spec.2 x (cert Γ (nCert Γ Q n) m z) hS
      (by rw [length_pe2, length_cert hm hNΓ, hx])
    convert this
  -- OR over all lengths `m ≤ N`
  let f : (Fin (n * Fintype.card δ + nCert Γ Q n * Fintype.card Γ) → Bool) → Bool :=
    fun u => decide (∃ i : Fin (nCert Γ Q n + 1), Cm i u = true)
  have hf : HasCircuitOfSize f ((nCert Γ Q n + 1) * B + nCert Γ Q n) := by
    have h1 := hasMCircuitOfSize_of_forall (fun u (i : Fin (nCert Γ Q n + 1)) => Cm i u)
      (fun i => hCm i (by omega))
    exact h1.comp_single (Pnp.Derand.hasCircuitOfSize_any (nCert Γ Q n))
  refine ⟨f, hf.mono ?_, fun x hS hx z => ?_⟩
  · have hB : B = Bp.eval n := by
      simp only [B, Bp, mp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
      ring
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, ← hB]
    have : (nCert Γ Q n + 1) * B ≤ (Q.eval n + 1) * B := Nat.mul_le_mul_right _ (by omega)
    omega
  · simp only [f, decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi⟩
      have him : i.val ≤ nCert Γ Q n := by omega
      exact ⟨i.val, him, (hCm_spec _ him x z hS hx).1 hi⟩
    · rintro ⟨m, hm, hRm⟩
      exact ⟨⟨m, by omega⟩, (hCm_spec _ hm x z hS hx).2 hRm⟩

/-- `pe2` is injective. -/
theorem pe2_injective {α Γ : Type} [Fintype α] [Fintype Γ] {w w' : List α} {y y' : List Γ}
    (h : pe2 w y = pe2 w' y') : w = w' ∧ y = y' := by
  have := congrArg (Millennium.pair_encoding (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string Γ)).decode
    (show (Millennium.pair_encoding (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string Γ)).encode (w, y) =
      (Millennium.pair_encoding (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string Γ)).encode (w', y') from h)
  rw [(Millennium.pair_encoding (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string Γ)).decode_encode,
    (Millennium.pair_encoding (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string Γ)).decode_encode] at this
  simpa using this

/-- **Nested simulation.** A predicate on nested pairs `((w, b), y)` whose complement is in the
official class `P` is decided by polynomial-size circuits on the strings `(w#b)#y`. -/
theorem nested_circuits {α β γ : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Primcodable α] [Primcodable β] [Primcodable γ]
    (L'' : Millennium.Language ((List α × List β) × List γ))
    (h : Millennium.InPolynomialTime
      (Millennium.pair_encoding (Millennium.pair_encoding (Millennium.fin_encoding_string α)
        (Millennium.fin_encoding_string β)) (Millennium.fin_encoding_string γ))
      (Millennium.complement L'')) :
    ∃ p₁ : Polynomial ℕ, ∀ n', 0 < n' →
      ∃ g : (Fin (n' * Fintype.card ((α ⊕ Option β) ⊕ Option γ)) → Bool) → Bool,
        HasCircuitOfSize g (p₁.eval n') ∧
        ∀ (x : List (α ⊕ Option β)) (y : List γ), (∃ w b, x = pe2 w b) →
          (pe2 x y).length = n' →
          (g (oneHot n' (pe2 x y)) = true ↔ ∀ w b, x = pe2 w b → L'' ((w, b), y)) := by
  obtain ⟨F, comp, hF⟩ := h
  let PE := Millennium.pair_encoding (Millennium.pair_encoding (Millennium.fin_encoding_string α)
    (Millennium.fin_encoding_string β)) (Millennium.fin_encoding_string γ)
  let dec : List ((α ⊕ Option β) ⊕ Option γ) → (List α × List β) × List γ :=
    fun u => (PE.decode u).getD (([], []), [])
  have hdec : ∀ w b y, dec (pe2 (pe2 w b) y) = ((w, b), y) := fun w b y => by
    simp only [dec]
    rw [show pe2 (pe2 w b) y = PE.encode ((w, b), y) from rfl, PE.decode_encode]; rfl
  let S : List ((α ⊕ Option β) ⊕ Option γ) → Prop := fun u => ∃ w b y, pe2 (pe2 w b) y = u
  obtain ⟨p₁, hp₁⟩ := simulateOn (α := (α ⊕ Option β) ⊕ Option γ) comp.tm comp.inputAlphabet
    comp.time (fun u => comp.outputAlphabet.symm (F (dec u))) (comp.outputAlphabet.symm false) S
    (by
      intro u hS
      have e := hS.choose_spec.choose_spec.choose_spec
      rw [← e, hdec]
      exact comp.outputsFun ((hS.choose, hS.choose_spec.choose), hS.choose_spec.choose_spec.choose))
  refine ⟨p₁, fun n' hn' => ?_⟩
  obtain ⟨g, hg, hgs⟩ := hp₁ n' hn'
  refine ⟨g, hg, fun x y ⟨w, b, hx⟩ hlen => ?_⟩
  subst hx
  rw [hgs _ ⟨w, b, y, rfl⟩ hlen, hdec, Equiv.apply_eq_iff_eq]
  have key : F ((w, b), y) = false ↔ L'' ((w, b), y) := by
    have := hF ((w, b), y)
    unfold Millennium.complement at this
    cases hc : F ((w, b), y) <;> simp_all
  refine key.trans ?_
  constructor
  · intro hL w' b' e
    obtain ⟨rfl, rfl⟩ := pe2_injective e
    exact hL
  · intro hall
    exact hall w b rfl

end

end Pnp.KarpLipton
