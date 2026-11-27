import Pnp.Derandomization.HardFunctions

/-!
# Adleman's theorem: randomness can be hard-wired into circuits (M20)

A *randomized circuit* for `f : {0,1}^n → {0,1}` is a circuit `C(x, r)` with `ℓ` extra random
input bits that errs with probability `≤ 1/3` on every input `x`. Adleman (1978): `f` then has a
deterministic circuit of polynomial size (the circuit form of `BPP ⊆ P/poly`).

* `ex_pi_prod`: for independent copies, `E[∏ g(Rᵢ)] = (E g)^k`.
* `prob_vote_wrong_le` (amplification, exponential-moment method): with `k = 2j` independent
  random strings, the majority vote is wrong on a fixed `x` with probability `≤ (8/9)^j`.
* `adleman`: with `k = 12(n+1)` copies, a union bound over the `2^n` inputs gives one choice of
  the random strings that is correct on *every* input, and the majority of `k` copies of `C` with
  these strings hard-wired is a circuit for `f` with `k (s + 2) + majSize k` gates.
-/

namespace Pnp.Derand

open Pnp.Circuits Pnp.NaturalProofs Classical

noncomputable section

/-! ## Independent copies -/

theorem ex_pi_prod {α : Type} [Fintype α] (k : ℕ) (g : α → ℝ) :
    ex (fun R : Fin k → α => ∏ i, g (R i)) = ex g ^ k := by
  have h := Finset.sum_prod_piFinset (ι := Fin k) (Finset.univ : Finset α) (fun _ a => g a)
  rw [Fintype.piFinset_univ] at h
  rw [ex, ex, h, Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow,
    Fintype.card_fun, Fintype.card_fin]
  push_cast; rfl

/-- Markov's inequality for a weight `g ≥ 0` that is `≥ c` on `P`. -/
theorem prob_mul_le_ex {α : Type} [Fintype α] {P : α → Prop} {g : α → ℝ} {c : ℝ}
    (hg : ∀ a, 0 ≤ g a) (hc : ∀ a, P a → c ≤ g a) : prob P * c ≤ ex g := by
  rw [prob_eq_ex, ← ex_mul_const]
  refine ex_mono fun a => ?_
  unfold ind
  split_ifs with h
  · rw [one_mul]; exact hc a h
  · rw [zero_mul]; exact hg a

/-! ## Amplification by majority vote -/

section Amplify

variable {n ℓ : ℕ} (C : (Fin (n + ℓ) → Bool) → Bool) (f : (Fin n → Bool) → Bool)

/-- `1` if `C` errs on `x` with random string `r`. -/
def wrong (x : Fin n → Bool) (r : Fin ℓ → Bool) : ℕ := if C (Fin.append x r) = f x then 0 else 1

/-- Majority vote of `k` copies. -/
def vote {k : ℕ} (x : Fin n → Bool) (R : Fin k → Fin ℓ → Bool) : Bool :=
  maj (fun i => C (Fin.append x (R i)))

/-- A wrong majority means at least half of the copies are wrong. -/
theorem half_le_wrong {k : ℕ} (x : Fin n → Bool) (R : Fin k → Fin ℓ → Bool)
    (h : vote C x R ≠ f x) : k ≤ 2 * ∑ i, wrong C f x (R i) := by
  have hsum : ∑ i, wrong C f x (R i) =
      (Finset.univ.filter (fun i => C (Fin.append x (R i)) ≠ f x)).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [wrong]
    split_ifs <;> simp_all
  rw [hsum]
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k))) (fun i => C (Fin.append x (R i)) = true)
  rw [Finset.card_univ, Fintype.card_fin] at htot
  simp only [vote, maj, ne_eq] at h
  cases hf : f x
  · rw [hf] at h
    have h1 : k < 2 * (Finset.univ.filter fun j => C (Fin.append x (R j)) = true).card := by
      by_contra hc; exact h (decide_eq_false hc)
    have he : (Finset.univ.filter fun i => C (Fin.append x (R i)) ≠ false) =
        Finset.univ.filter fun j => C (Fin.append x (R j)) = true := by
      ext i; simp
    rw [he]; omega
  · rw [hf] at h
    have h1 : ¬ k < 2 * (Finset.univ.filter fun j => C (Fin.append x (R j)) = true).card := by
      intro hc; exact h (decide_eq_true hc)
    have he : (Finset.univ.filter fun i => C (Fin.append x (R i)) ≠ true) =
        Finset.univ.filter fun j => ¬ C (Fin.append x (R j)) = true := by
      ext i; simp
    rw [he]; omega

/-- **Amplification.** If `C` errs on `x` with probability `≤ 1/3`, the majority of `2j`
independent copies errs with probability `≤ (8/9)^j`. -/
theorem prob_vote_wrong_le (x : Fin n → Bool)
    (herr : prob (fun r : Fin ℓ → Bool => C (Fin.append x r) ≠ f x) ≤ 1 / 3) (j : ℕ) :
    prob (fun R : Fin (2 * j) → Fin ℓ → Bool => vote C x R ≠ f x) ≤ (8 / 9) ^ j := by
  have hw : ex (fun r : Fin ℓ → Bool => (2 : ℝ) ^ wrong C f x r) ≤ 4 / 3 := by
    have : (fun r : Fin ℓ → Bool => (2 : ℝ) ^ wrong C f x r) =
        fun r => 1 + ind (fun r : Fin ℓ → Bool => C (Fin.append x r) ≠ f x) r := by
      funext r; unfold wrong ind; split_ifs <;> simp_all <;> norm_num
    rw [this, ex_add, ex_const, ← prob_eq_ex]
    linarith
  have hE : ex (fun R : Fin (2 * j) → Fin ℓ → Bool => ∏ i, (2 : ℝ) ^ wrong C f x (R i)) ≤
      (16 / 9) ^ j := by
    have hp := ex_pi_prod (2 * j) (fun r : Fin ℓ → Bool => (2 : ℝ) ^ wrong C f x r)
    beta_reduce at hp
    rw [hp, pow_mul]
    have h0 : 0 ≤ ex (fun r : Fin ℓ → Bool => (2 : ℝ) ^ wrong C f x r) :=
      ex_nonneg fun r => by positivity
    calc _ ≤ ((4 / 3 : ℝ) ^ 2) ^ j := pow_le_pow_left₀ (pow_nonneg h0 2)
          (pow_le_pow_left₀ h0 hw 2) j
      _ = _ := by norm_num
  have hM := prob_mul_le_ex (P := fun R : Fin (2 * j) → Fin ℓ → Bool => vote C x R ≠ f x)
    (g := fun R => ∏ i, (2 : ℝ) ^ wrong C f x (R i)) (c := 2 ^ j)
    (fun R => Finset.prod_nonneg fun i _ => by positivity) (fun R hR => by
      rw [Finset.prod_pow_eq_pow_sum]
      have := half_le_wrong C f x R hR
      exact pow_le_pow_right₀ (by norm_num) (by omega))
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have h3 := hM.trans hE
  rw [← le_div_iff₀ h2] at h3
  calc _ ≤ _ := h3
    _ = _ := by
      rw [div_pow, div_pow, show (16 : ℝ) ^ j = 8 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]
      field_simp

end Amplify

/-! ## Adleman's theorem -/

theorem eight_ninths_pow_six : ((8 : ℝ) / 9) ^ 6 ≤ 1 / 2 := by norm_num

/-- **Adleman's theorem** (circuit form of `BPP ⊆ P/poly`). If a circuit `C` with `s` gates,
reading `x` and `ℓ` random bits, computes `f x` with error probability `≤ 1/3` for every `x`,
then `f` has a deterministic circuit with `k (s + 2) + majSize k` gates, `k = 12 (n + 1)`. -/
theorem adleman {n ℓ s : ℕ} (hn : 0 < n) {C : (Fin (n + ℓ) → Bool) → Bool}
    (hC : HasCircuitOfSize C s) (f : (Fin n → Bool) → Bool)
    (herr : ∀ x, prob (fun r : Fin ℓ → Bool => C (Fin.append x r) ≠ f x) ≤ 1 / 3) :
    HasCircuitOfSize f (12 * (n + 1) * (s + 2) + majSize (12 * (n + 1))) := by
  set j := 6 * (n + 1)
  have hk : 12 * (n + 1) = 2 * j := by omega
  -- some choice of the random strings is correct on every input
  have hbad : prob (fun R : Fin (2 * j) → Fin ℓ → Bool => ∃ x, vote C x R ≠ f x) < 1 := by
    rw [prob_eq_ex]
    have hu := ex_ind_exists_le (fun x (R : Fin (2 * j) → Fin ℓ → Bool) => vote C x R ≠ f x)
    have hx : ∀ x : Fin n → Bool,
        ex (ind (fun R : Fin (2 * j) → Fin ℓ → Bool => vote C x R ≠ f x)) ≤ (1 / 2) ^ (n + 1) := by
      intro x
      rw [← prob_eq_ex]
      refine (prob_vote_wrong_le C f x (herr x) j).trans ?_
      rw [show j = 6 * (n + 1) from rfl, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) eight_ninths_pow_six _
    calc _ ≤ _ := hu
      _ ≤ ∑ _x : Fin n → Bool, ((1 : ℝ) / 2) ^ (n + 1) := Finset.sum_le_sum fun x _ => hx x
      _ = 1 / 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
      _ < 1 := by norm_num
  obtain ⟨R, hR⟩ : ∃ R : Fin (2 * j) → Fin ℓ → Bool, ∀ x, vote C x R = f x := by
    by_contra hne
    push Not at hne
    have : prob (fun R : Fin (2 * j) → Fin ℓ → Bool => ∃ x, vote C x R ≠ f x) = 1 := by
      have : (0 : ℝ) < Fintype.card (Fin (2 * j) → Fin ℓ → Bool) := by
        exact_mod_cast Fintype.card_pos
      simp only [prob, hne, Finset.filter_true, Finset.card_univ]
      field_simp
    linarith
  -- the circuit
  have hcopies : HasMCircuitOfSize (fun x : Fin n → Bool => fun i : Fin (2 * j) =>
      C (Fin.append x (R i))) (2 * j * (2 + s)) :=
    hasMCircuitOfSize_of_forall _ fun i =>
      (hasMCircuitOfSize_append_const hn (R i)).comp_single hC
  have hv := hcopies.comp_single (hasCircuitOfSize_maj (m := 2 * j) (by omega))
  have hfv : f = fun x => vote C x R := funext fun x => (hR x).symm
  rw [hfv, hk]
  refine hv.mono (by rw [show 2 * j * (2 + s) = 2 * j * (s + 2) by ring])

end

end Pnp.Derand
