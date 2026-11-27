import Pnp.Circuits.Majority
import Pnp.Derandomization.HardFunctions

/-!
# Impagliazzo's hardcore lemma (M37)

If every small circuit errs on at least a `δ` fraction of the inputs of `f`, then there is a
*hardcore measure* `M : X → [0,1]` of density `≥ δ` on which every (somewhat smaller) circuit
agrees with `f` with weight at most `1/2 + γ`: on the "core" `f` looks like a coin flip.

The proof is a boosting argument with a truncated-linear potential.

* Score: after hypotheses `h₀, …, h_{t-1}` the score of `x` is `S_t(x) = Σᵢ ±1` (`+1` when
  `hᵢ x = f x`). The measure is `M_t(x) = m(S_t(x))` with `m(k) = 1` for `k ≤ 0`,
  `m(k) = 1 - k/L` for `0 ≤ k ≤ L`, `m(k) = 0` for `k ≥ L` (`mval`).
* Potential `Ψ` (`pot`) with `Ψ(k+1) - Ψ(k) = m(k)`; then `a · m(k) ≤ Ψ(k+a) - Ψ(k) + 1/L` for
  `a = ±1` (`pot_step`) and `Ψ ≤ (L+1)/2` (`pot_le`). Summing along the run of one input:
  `Σ_t a_t m(S_t) ≤ (L+1)/2 + T/L` (`sum_step_le`).
* If at every step the measure is `δ`-dense and some hypothesis has correlation `≥ 2γ` with
  `f` under it, the total correlation is `≥ 2γδNT`, which beats `N((L+1)/2 + T/L)` once
  `γδL ≥ 1` and `L + 1 < 2γδT`. So some step has a sparse measure; then the strict majority of
  the hypotheses so far is wrong only where `S ≤ 0`, i.e. on `< δN` inputs.

Main results:
* `hardcore_or_boost` (abstract, any hypothesis class `H` on a finite type),
* `hardcore_lemma` (circuits: hard for size `T s + majSize T` ⇒ hardcore measure for size `s`),
* `hardcore_lemma_nat` (`γ = 1/a`, `δ = 1/b`, `T = ab(ab+1)`),
* `exists_hardcore` (non-vacuity, via the average-case hard functions of M19).
-/

namespace Pnp.Derand

open Pnp.Circuits Classical

noncomputable section

/-! ## The truncated-linear measure and its potential -/

/-- Weight of an input with score `k`. -/
def mval (L : ℕ) (k : ℤ) : ℝ :=
  if k ≤ 0 then 1 else if k ≤ L then 1 - (k : ℝ) / L else 0

/-- Discrete antiderivative of `mval`. -/
def pot (L : ℕ) (k : ℤ) : ℝ :=
  if k ≤ 0 then k else if k ≤ L then k - (k : ℝ) * (k - 1) / (2 * L) else ((L : ℝ) + 1) / 2

theorem mval_nonneg (L : ℕ) (k : ℤ) : 0 ≤ mval L k := by
  unfold mval
  split_ifs with h1 h2
  · norm_num
  · have hL : (0 : ℝ) < L := by
      have : (0 : ℤ) < L := by omega
      exact_mod_cast this
    rw [sub_nonneg, div_le_one hL]; exact_mod_cast h2
  · exact le_rfl

theorem mval_le_one (L : ℕ) (k : ℤ) : mval L k ≤ 1 := by
  unfold mval
  split_ifs with h1 h2
  · exact le_rfl
  · have hL : (0 : ℝ) < L := by
      have : (0 : ℤ) < L := by omega
      exact_mod_cast this
    have hk : (0 : ℝ) < k := by exact_mod_cast (show (0 : ℤ) < k by omega)
    have := div_pos hk hL
    linarith
  · norm_num

theorem pot_zero (L : ℕ) : pot L 0 = 0 := by simp [pot]

theorem pot_le (L : ℕ) (hL : 1 ≤ L) (k : ℤ) : pot L k ≤ ((L : ℝ) + 1) / 2 := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  unfold pot
  split_ifs with h1 h2
  · have : (k : ℝ) ≤ 0 := by exact_mod_cast h1
    linarith
  · rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
    have : (k : ℝ) ≤ L := by exact_mod_cast h2
    nlinarith [sq_nonneg ((k : ℝ) - L)]
  · exact le_rfl

/-- Key one-step inequality: `a · m(k) ≤ Ψ(k + a) - Ψ(k) + 1/L` for `a = ±1`. -/
theorem pot_step (L : ℕ) (hL : 1 ≤ L) (k a : ℤ) (ha : a = 1 ∨ a = -1) :
    (a : ℝ) * mval L k ≤ pot L (k + a) - pot L k + 1 / L := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hinv : (0 : ℝ) ≤ 1 / L := by positivity
  rcases ha with rfl | rfl
  · simp only [Int.cast_one, one_mul]
    unfold mval pot
    by_cases h0 : k + 1 ≤ 0
    · have h0' : k ≤ 0 := by omega
      simp only [h0, h0', if_true]; push_cast; linarith
    by_cases hk0 : k ≤ 0
    · have hk : k = 0 := by omega
      subst hk
      have h1 : (0 : ℤ) + 1 ≤ L := by omega
      simp only [h0, h1, if_true, if_false, le_refl]
      push_cast; field_simp; linarith
    by_cases hkL : k + 1 ≤ L
    · have hkL' : k ≤ L := by omega
      simp only [h0, hk0, hkL, hkL', if_true, if_false]
      push_cast
      have : (k : ℝ) + 1 - ((k : ℝ) + 1) * ((k : ℝ) + 1 - 1) / (2 * L) -
          ((k : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / (2 * L)) = 1 - (k : ℝ) / L := by
        field_simp; ring
      linarith
    by_cases hkL' : k ≤ L
    · have hk : k = L := by omega
      subst hk
      simp only [h0, hk0, hkL, le_refl, if_true, if_false]
      push_cast
      have : ((L : ℝ) + 1) / 2 - ((L : ℝ) - (L : ℝ) * ((L : ℝ) - 1) / (2 * L)) = 0 := by
        field_simp; ring
      have : (1 : ℝ) - (L : ℝ) / L = 0 := by field_simp; ring
      linarith
    · simp only [h0, hk0, hkL, hkL', if_false]
      linarith
  · simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
    unfold mval pot
    by_cases hk0 : k ≤ 0
    · have h0 : k + -1 ≤ 0 := by omega
      simp only [h0, hk0, if_true]; push_cast; linarith
    by_cases hk1 : k = 1
    · subst hk1
      have h1 : (1 : ℤ) ≤ L := by exact_mod_cast hL
      simp only [show (1 : ℤ) + -1 ≤ 0 by norm_num, hk0, h1, if_true, if_false]
      push_cast; field_simp; linarith
    by_cases hkL : k ≤ L
    · have h0 : ¬ k + -1 ≤ 0 := by omega
      have h1 : k + -1 ≤ L := by omega
      simp only [h0, hk0, hkL, h1, if_true, if_false]
      push_cast
      have : (k : ℝ) + -1 - ((k : ℝ) + -1) * ((k : ℝ) + -1 - 1) / (2 * L) -
          ((k : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / (2 * L)) + 1 / L = -(1 - (k : ℝ) / L) := by
        field_simp; ring
      linarith
    by_cases hkL1 : k = L + 1
    · subst hkL1
      have h0 : ¬ (L : ℤ) + 1 + -1 ≤ 0 := by omega
      have h1 : (L : ℤ) + 1 + -1 ≤ L := by omega
      simp only [h0, hk0, hkL, h1, if_true, if_false]
      push_cast
      have : (L : ℝ) + 1 + -1 - ((L : ℝ) + 1 + -1) * ((L : ℝ) + 1 + -1 - 1) / (2 * L) -
          ((L : ℝ) + 1) / 2 = 0 := by
        field_simp; ring
      linarith
    · have h0 : ¬ k + -1 ≤ 0 := by omega
      have h1 : ¬ k + -1 ≤ L := by omega
      simp only [h0, hk0, hkL, h1, if_false]
      linarith

/-- Along one run `a₀, a₁, …` of `±1` steps (scores `S_t = Σ_{i<t} aᵢ`), the total weighted
correlation is at most `Ψ(S_T) + T/L`. -/
theorem sum_step_le (L : ℕ) (hL : 1 ≤ L) (a : ℕ → ℤ) (ha : ∀ i, a i = 1 ∨ a i = -1) (T : ℕ) :
    ∑ i ∈ Finset.range T, (a i : ℝ) * mval L (∑ j ∈ Finset.range i, a j) ≤
      pot L (∑ j ∈ Finset.range T, a j) + T / L := by
  induction T with
  | zero => simp [pot_zero]
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have := pot_step L hL (∑ j ∈ Finset.range T, a j) (a T) (ha T)
    push_cast
    rw [add_div]
    linarith

/-! ## Majority and correlation -/

section Abstract

variable {X : Type} [Fintype X]

/-- `±1` correlation of a hypothesis with the target at `x`. -/
def corr (h f : X → Bool) (x : X) : ℤ := if h x = f x then 1 else -1

omit [Fintype X] in
theorem corr_pm (h f : X → Bool) (x : X) : corr h f x = 1 ∨ corr h f x = -1 := by
  unfold corr; split_ifs <;> simp

/-- Agreement indicator. -/
def agr (h f : X → Bool) (x : X) : ℝ := if h x = f x then 1 else 0

omit [Fintype X] in
theorem corr_eq_agr (h f : X → Bool) (x : X) : (corr h f x : ℝ) = 2 * agr h f x - 1 := by
  unfold corr agr; split_ifs <;> norm_num

/-- If strictly more of the bits `g i` equal `b` than differ from it, the strict majority
is `b`. -/
theorem maj_eq_of_sum_pos {t : ℕ} (g : Fin t → Bool) (b : Bool)
    (hpos : 0 < ∑ i, (if g i = b then (1 : ℤ) else -1)) : maj g = b := by
  have hsplit : ∑ i, (if g i = b then (1 : ℤ) else -1) =
      2 * ((Finset.univ.filter fun i => g i = b).card : ℤ) - t := by
    have h1 : ∑ i, (if g i = b then (1 : ℤ) else -1) =
        ∑ i, (2 * (if g i = b then (1 : ℤ) else 0) - 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> norm_num
    rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp
  rw [hsplit] at hpos
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin t => g i = true)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  unfold maj
  cases b with
  | true =>
    simp only [decide_eq_true_eq]
    omega
  | false =>
    have : (Finset.univ.filter fun i => g i = false) =
        (Finset.univ.filter fun i => ¬ g i = true) := by
      ext i; simp
    rw [this] at hpos
    simp only [decide_eq_false_iff_not, not_lt]
    omega

/-- Score of `x` after the first `t` hypotheses of the sequence `hs`. -/
def score (hs : ℕ → X → Bool) (f : X → Bool) (t : ℕ) (x : X) : ℤ :=
  ∑ i ∈ Finset.range t, corr (hs i) f x

/-- **Abstract hardcore lemma / boosting dichotomy.** Let `H` be any class of hypotheses,
`δ ≤ 1`, `γ > 0`, `γ δ L ≥ 1` and `L + 1 < 2 γ δ T`. Either there is a measure of density
`≥ δ` under which every `h ∈ H` agrees with `f` with weight `≤ (1/2 + γ)`, or the strict
majority of some `0 < t < T` hypotheses from `H` errs on fewer than `δ |X|` inputs. -/
theorem hardcore_or_boost [Nonempty X] (H : Set (X → Bool)) (f : X → Bool) {δ γ : ℝ}
    (hδ1 : δ ≤ 1) (hγ : 0 < γ) {L T : ℕ} (hL : 1 ≤ L)
    (hLδ : 1 ≤ γ * δ * L) (hT : (L : ℝ) + 1 < 2 * γ * δ * T) :
    (∃ M : X → ℝ, (∀ x, 0 ≤ M x ∧ M x ≤ 1) ∧ δ * Fintype.card X ≤ ∑ x, M x ∧
        ∀ h ∈ H, ∑ x, M x * agr h f x ≤ (1 / 2 + γ) * ∑ x, M x) ∨
      ∃ t, 0 < t ∧ t < T ∧ ∃ hs : Fin t → X → Bool, (∀ i, hs i ∈ H) ∧
        (((Finset.univ.filter fun x => maj (fun i => hs i x) ≠ f x).card : ℕ) : ℝ) <
          δ * Fintype.card X := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hno, hnob⟩ := hcon
  push Not at hno hnob
  set N : ℝ := (Fintype.card X : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  -- the measure at step `t`
  let Mt (hs : ℕ → X → Bool) (t : ℕ) (x : X) : ℝ := mval L (score hs f t x)
  -- density at every step `t < T`
  have hdense : ∀ (hs : ℕ → X → Bool) (t : ℕ), t < T → (∀ i < t, hs i ∈ H) →
      δ * N ≤ ∑ x, Mt hs t x := by
    intro hs t htT hH
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · have : ∀ x, Mt hs 0 x = 1 := fun x => by simp [Mt, score, mval]
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [← hN]; nlinarith
    · have hb := hnob t ht0 htT (fun i => hs i) (fun i => hH i i.2)
      refine hb.trans ?_
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs with hw
      · -- the majority errs, so the score is `≤ 0` and the weight is `1`
        have hS : score hs f t x ≤ 0 := by
          by_contra hS
          push Not at hS
          apply hw
          apply maj_eq_of_sum_pos
          have : score hs f t x = ∑ i : Fin t, (if hs i x = f x then (1 : ℤ) else -1) := by
            rw [score, ← Fin.sum_univ_eq_sum_range (fun i => corr (hs i) f x)]
            rfl
          rw [← this]; exact hS
        simp [Mt, mval, hS]
      · exact mval_nonneg L _
  -- build `T` hypotheses with large total correlation
  have hbuild : ∀ t ≤ T, ∃ hs : ℕ → X → Bool, (∀ i < t, hs i ∈ H) ∧
      2 * γ * δ * N * t ≤ ∑ i ∈ Finset.range t, ∑ x, Mt hs i x * (corr (hs i) f x : ℝ) := by
    intro t
    induction t with
    | zero => intro _; exact ⟨fun _ => f, fun i hi => absurd hi (Nat.not_lt_zero _), by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨hs, hH, hsum⟩ := ih (by omega)
      have hd := hdense hs t (by omega) hH
      obtain ⟨h, hhH, hh⟩ := hno (Mt hs t)
        (fun x => ⟨mval_nonneg L _, mval_le_one L _⟩) hd
      let hs' : ℕ → X → Bool := fun i => if i < t then hs i else h
      have hagree : ∀ i ≤ t, ∀ x, score hs' f i x = score hs f i x := by
        intro i hi x
        unfold score
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_range] at hj
        simp [hs', show j < t by omega]
      refine ⟨hs', fun i hi => ?_, ?_⟩
      · by_cases hit : i < t
        · simp only [hs', hit, if_true]; exact hH i hit
        · simp only [hs', hit, if_false]; exact hhH
      rw [Finset.sum_range_succ]
      have hold : ∑ i ∈ Finset.range t, ∑ x, Mt hs' i x * (corr (hs' i) f x : ℝ) =
          ∑ i ∈ Finset.range t, ∑ x, Mt hs i x * (corr (hs i) f x : ℝ) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_range] at hi
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Mt, hagree i hi.le x]
        simp [hs', hi]
      have hnew : ∑ x, Mt hs' t x * (corr (hs' t) f x : ℝ) =
          ∑ x, Mt hs t x * (2 * agr h f x - 1) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Mt, hagree t le_rfl x]
        simp [hs', corr_eq_agr]
      have hlast : 2 * γ * δ * N ≤ ∑ x, Mt hs t x * (2 * agr h f x - 1) := by
        have e : ∑ x, Mt hs t x * (2 * agr h f x - 1) =
            2 * ∑ x, Mt hs t x * agr h f x - ∑ x, Mt hs t x := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
        rw [e]
        nlinarith
      rw [hold, hnew]
      push_cast
      nlinarith
  obtain ⟨hs, -, hsum⟩ := hbuild T le_rfl
  -- upper bound, input by input
  have hup : ∑ i ∈ Finset.range T, ∑ x, Mt hs i x * (corr (hs i) f x : ℝ) ≤
      N * (((L : ℝ) + 1) / 2 + T / L) := by
    rw [Finset.sum_comm]
    calc ∑ x, ∑ i ∈ Finset.range T, Mt hs i x * (corr (hs i) f x : ℝ)
        ≤ ∑ _x : X, (((L : ℝ) + 1) / 2 + T / L) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have := sum_step_le L hL (fun i => corr (hs i) f x) (fun i => corr_pm _ _ _) T
          have h2 := pot_le L hL (∑ j ∈ Finset.range T, corr (hs j) f x)
          calc ∑ i ∈ Finset.range T, Mt hs i x * (corr (hs i) f x : ℝ)
              = ∑ i ∈ Finset.range T, ((corr (hs i) f x : ℤ) : ℝ) *
                  mval L (∑ j ∈ Finset.range i, corr (hs j) f x) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                simp only [Mt, score]; ring
            _ ≤ _ := this
            _ ≤ _ := by linarith
      _ = N * (((L : ℝ) + 1) / 2 + T / L) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
  -- contradiction
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hTL : (T : ℝ) / L ≤ γ * δ * T := by
    rw [div_le_iff₀ hLpos]
    have : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    nlinarith
  have := hsum.trans hup
  have h3 : 2 * γ * δ * T ≤ ((L : ℝ) + 1) / 2 + γ * δ * T := by
    have h4 : 2 * γ * δ * N * T ≤ N * (((L : ℝ) + 1) / 2 + γ * δ * T) := by
      have : N * ((T : ℝ) / L) ≤ N * (γ * δ * T) := mul_le_mul_of_nonneg_left hTL hNpos.le
      nlinarith
    have h5 : N * (2 * γ * δ * T) ≤ N * (((L : ℝ) + 1) / 2 + γ * δ * T) := by linarith
    exact le_of_mul_le_mul_left h5 hNpos
  linarith

end Abstract

/-! ## The circuit form -/

theorem majSize_mono {a b : ℕ} (h : a ≤ b) : majSize a ≤ majSize b := by
  unfold majSize
  have : a * ((2 * a + 1) * 32) ≤ b * ((2 * b + 1) * 32) := by gcongr
  omega

/-- **Impagliazzo's hardcore lemma** (measure form, circuits). Let `δ ≤ 1`, `γ > 0`,
`γ δ L ≥ 1`, `L + 1 < 2 γ δ T`. If every circuit with `T s + majSize T` gates disagrees with
`f` on at least `δ 2^n` inputs, then there is a measure `M : {0,1}^n → [0,1]` of total weight
`≥ δ 2^n` under which every circuit with `s` gates agrees with `f` with weight at most
`(1/2 + γ) Σ M`. -/
theorem hardcore_lemma {n s : ℕ} (f : (Fin n → Bool) → Bool) {δ γ : ℝ}
    (hδ1 : δ ≤ 1) (hγ : 0 < γ) {L T : ℕ} (hL : 1 ≤ L) (hLδ : 1 ≤ γ * δ * L)
    (hT : (L : ℝ) + 1 < 2 * γ * δ * T)
    (hhard : ∀ C : (Fin n → Bool) → Bool, HasCircuitOfSize C (T * s + majSize T) →
      δ * 2 ^ n ≤ (((Finset.univ.filter fun x => C x ≠ f x).card : ℕ) : ℝ)) :
    ∃ M : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ M x ∧ M x ≤ 1) ∧ δ * 2 ^ n ≤ ∑ x, M x ∧
      ∀ C : (Fin n → Bool) → Bool, HasCircuitOfSize C s →
        ∑ x, M x * agr C f x ≤ (1 / 2 + γ) * ∑ x, M x := by
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring
  rcases hardcore_or_boost {C | HasCircuitOfSize C s} f hδ1 hγ hL hLδ hT with
    ⟨M, hM1, hM2, hM3⟩ | ⟨t, ht0, htT, hs, hH, hfew⟩
  · exact ⟨M, hM1, by rw [← hcard]; exact hM2, fun C hC => hM3 C hC⟩
  · exfalso
    have hcopies : HasMCircuitOfSize (fun x i => hs i x) (t * s) :=
      hasMCircuitOfSize_of_forall _ fun i => hH i
    have hv := hcopies.comp_single (hasCircuitOfSize_maj (m := t) ht0)
    have hle : t * s + majSize t ≤ T * s + majSize T :=
      Nat.add_le_add (Nat.mul_le_mul_right _ htT.le) (majSize_mono htT.le)
    have := hhard _ (hv.mono hle)
    rw [hcard] at hfew
    exact absurd (this.trans_lt hfew) (lt_irrefl _)

/-- **Hardcore lemma with explicit parameters** `γ = 1/a`, `δ = 1/b`: hardness against
circuits with `T s + majSize T` gates, `T = ab(ab+1)`, gives a hardcore measure of density
`≥ 1/b` against circuits with `s` gates and advantage `1/a`. -/
theorem hardcore_lemma_nat {n s : ℕ} (f : (Fin n → Bool) → Bool) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hhard : ∀ C : (Fin n → Bool) → Bool,
      HasCircuitOfSize C (a * b * (a * b + 1) * s + majSize (a * b * (a * b + 1))) →
      (1 / b : ℝ) * 2 ^ n ≤ (((Finset.univ.filter fun x => C x ≠ f x).card : ℕ) : ℝ)) :
    ∃ M : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ M x ∧ M x ≤ 1) ∧ (1 / b : ℝ) * 2 ^ n ≤ ∑ x, M x ∧
      ∀ C : (Fin n → Bool) → Bool, HasCircuitOfSize C s →
        ∑ x, M x * agr C f x ≤ (1 / 2 + 1 / a) * ∑ x, M x := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (by positivity)
  refine hardcore_lemma f (by rw [div_le_one (by linarith)]; exact hb')
    (by positivity) (L := a * b) (T := a * b * (a * b + 1)) hab ?_ ?_ hhard
  · push_cast; field_simp; exact le_rfl
  · push_cast
    have e : 2 * (1 / (a : ℝ)) * (1 / b) * (a * b * (a * b + 1)) = 2 * (a * b + 1) := by
      field_simp
    rw [e]
    nlinarith

/-! ## Non-vacuity: average-case hard functions satisfy the hypothesis -/

/-- An `(s, ε)`-average-case hard function disagrees with every circuit of size `s` on at least
a `1/2 - ε` fraction of the inputs. -/
theorem disagree_of_avgHard {m s : ℕ} {f : (Fin m → Bool) → Bool} {ε : ℝ} (hf : AvgHard f s ε)
    (C : (Fin m → Bool) → Bool) (hC : HasCircuitOfSize C s) :
    (1 / 2 - ε) * 2 ^ m ≤ (((Finset.univ.filter fun x => C x ≠ f x).card : ℕ) : ℝ) := by
  have hp := hf C hC
  have hcard : (Fintype.card (Fin m → Bool) : ℝ) = 2 ^ m := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x : Fin m → Bool => C x = f x)
  rw [Finset.card_univ] at hsplit
  have hsplit' : (((Finset.univ.filter fun x => C x = f x).card : ℕ) : ℝ) +
      (((Finset.univ.filter fun x => C x ≠ f x).card : ℕ) : ℝ) = 2 ^ m := by
    rw [← hcard]; exact_mod_cast hsplit
  unfold Pnp.NaturalProofs.prob at hp
  rw [hcard, div_le_iff₀ (by positivity)] at hp
  have e1 : (((Finset.univ.filter fun x => C x = f x).card : ℕ) : ℝ) ≤ (1 / 2 + ε) * 2 ^ m := by
    convert hp using 2
    · rfl
    · congr 1
      ext x; simp
  linarith

/-- **The hardcore lemma is not vacuous.** For `k ≥ 2`, `a ≥ 1` and any `s` with
`T s + majSize T ≤ 4^k` (`T = 4a(4a+1)`), some `f : {0,1}^(8k) → {0,1}` has a hardcore measure
of density `≥ 1/4` against circuits with `s` gates, with advantage `1/a`. -/
theorem exists_hardcore (k a s : ℕ) (hk : 2 ≤ k) (ha : 1 ≤ a)
    (hs : a * 4 * (a * 4 + 1) * s + majSize (a * 4 * (a * 4 + 1)) ≤ 4 ^ k) :
    ∃ f : (Fin (8 * k) → Bool) → Bool, ∃ M : (Fin (8 * k) → Bool) → ℝ,
      (∀ x, 0 ≤ M x ∧ M x ≤ 1) ∧ (1 / 4 : ℝ) * 2 ^ (8 * k) ≤ ∑ x, M x ∧
      ∀ C : (Fin (8 * k) → Bool) → Bool, HasCircuitOfSize C s →
        ∑ x, M x * agr C f x ≤ (1 / 2 + 1 / a) * ∑ x, M x := by
  obtain ⟨f, hf⟩ := exists_avgHard_explicit k (by omega)
  refine ⟨f, ?_⟩
  have h4 : (1 : ℝ) / 2 ^ k ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have := hardcore_lemma_nat (s := s) f (a := a) (b := 4) ha (by norm_num) fun C hC => by
    have hd := disagree_of_avgHard hf C (hC.mono hs)
    have hpos : (0 : ℝ) < 2 ^ (8 * k) := by positivity
    push_cast
    nlinarith
  simpa using this

end

end Pnp.Derand

