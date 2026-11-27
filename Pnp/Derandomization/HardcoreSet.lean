import Pnp.Derandomization.Hardcore

/-!
# Impagliazzo's hardcore lemma, set version (M39)

M37 gives a *hardcore measure* `M : {0,1}^n → [0,1]`. Here we turn it into a *hardcore set*
by the probabilistic method: put each input `x` into a random set `S` independently with
probability `M x`. Every event is written as a finite weighted sum over all subsets
`S ⊆ X` with weight `sampW M S = ∏_{x ∈ S} M x · ∏_{x ∉ S} (1 - M x)` (these weights sum to
`1`), so no measure theory is needed.

* `sum_sampW_mul_prod`: `Σ_S sampW M S · ∏_{x ∈ S} u x = ∏_x (M x · u x + 1 - M x)`.
* `sampW_tail`: Chernoff/Markov bound for the size of `S ∩ A`, for any real slope `c`:
  the weight of `{S | c a ≤ c |S ∩ A|}` is at most `exp((e^c - 1) Σ_{x∈A} M x - c a)`.
* `exists_sample_set` (abstract): for a finite hypothesis class `H` with
  `(|H| + 1) exp(-τ² N / 4) < 1`, some set `S` has `|S| > Σ M - τ N` and, for every `h ∈ H`,
  `|{x ∈ S | h x = f x}| < (1/2 + γ) Σ M + τ N`.
* `hardcore_set_lemma` (circuits): under the hypotheses of `hardcore_lemma` and a counting
  condition, there is a set `S` of density `≥ δ/2` on which every circuit with `s` gates
  agrees with `f` on at most a `1/2 + 3γ` fraction.
* `exists_hardcore_set`: non-vacuity, via the average-case hard functions of M19.
-/

namespace Pnp.Derand

open Pnp.Circuits Classical

noncomputable section

section Sampling

variable {X : Type} [Fintype X]

/-- Weight of the subset `S` when each `x` is included independently with probability `M x`. -/
def sampW (M : X → ℝ) (S : Finset X) : ℝ :=
  (∏ x ∈ S, M x) * ∏ x ∈ Finset.univ \ S, (1 - M x)

theorem sampW_nonneg (M : X → ℝ) (hM : ∀ x, 0 ≤ M x ∧ M x ≤ 1) (S : Finset X) :
    0 ≤ sampW M S :=
  mul_nonneg (Finset.prod_nonneg fun x _ => (hM x).1)
    (Finset.prod_nonneg fun x _ => sub_nonneg.2 (hM x).2)

theorem sum_sampW_mul_prod (M u : X → ℝ) :
    ∑ S : Finset X, sampW M S * ∏ x ∈ S, u x = ∏ x, (M x * u x + (1 - M x)) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [sampW, Finset.prod_mul_distrib]
  ring

theorem sum_sampW (M : X → ℝ) : ∑ S : Finset X, sampW M S = 1 := by
  have := sum_sampW_mul_prod M (fun _ => 1)
  simp only [Finset.prod_const_one, mul_one, add_sub_cancel, Finset.prod_const_one] at this
  exact this

/-- Exponential moment of `|S ∩ A|`. -/
theorem sum_sampW_exp_le (M : X → ℝ) (hM : ∀ x, 0 ≤ M x ∧ M x ≤ 1) (p : X → Prop) [DecidablePred p] (c : ℝ) :
    ∑ S : Finset X, sampW M S * Real.exp (c * ((S.filter p).card : ℝ)) ≤
      Real.exp ((Real.exp c - 1) * ∑ x ∈ Finset.univ.filter p, M x) := by
  let u : X → ℝ := fun x => Real.exp (c * if p x then 1 else 0)
  have hS : ∀ S : Finset X, Real.exp (c * ((S.filter p).card : ℝ)) = ∏ x ∈ S, u x := by
    intro S
    rw [← Real.exp_sum, Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
  simp only [hS]
  rw [sum_sampW_mul_prod]
  have hfac : ∀ x, M x * u x + (1 - M x) ≤ Real.exp (M x * (u x - 1)) := by
    intro x
    have := Real.add_one_le_exp (M x * (u x - 1))
    linarith
  calc ∏ x, (M x * u x + (1 - M x)) ≤ ∏ x, Real.exp (M x * (u x - 1)) := by
        refine Finset.prod_le_prod (fun x _ => ?_) (fun x _ => hfac x)
        have h1 := (hM x).1
        have h2 := (hM x).2
        have h3 : 0 ≤ u x := (Real.exp_pos _).le
        nlinarith
    _ = Real.exp (∑ x, M x * (u x - 1)) := (Real.exp_sum _ _).symm
    _ = _ := by
        congr 1
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hp : p x
        · simp [u, hp]; ring
        · simp [u, hp]

/-- **Chernoff–Markov tail bound** for `|S ∩ A|` with an arbitrary real slope `c`. -/
theorem sampW_tail (M : X → ℝ) (hM : ∀ x, 0 ≤ M x ∧ M x ≤ 1) (p : X → Prop) [DecidablePred p] (c a : ℝ) :
    ∑ S : Finset X, sampW M S * (if c * a ≤ c * ((S.filter p).card : ℝ) then 1 else 0) ≤
      Real.exp ((Real.exp c - 1) * ∑ x ∈ Finset.univ.filter p, M x - c * a) := by
  calc ∑ S : Finset X, sampW M S * (if c * a ≤ c * ((S.filter p).card : ℝ) then 1 else 0)
      ≤ ∑ S : Finset X, sampW M S * (Real.exp (c * ((S.filter p).card : ℝ)) *
          Real.exp (-(c * a))) := by
        refine Finset.sum_le_sum fun S _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (sampW_nonneg M hM S)
        split_ifs with h
        · rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith)
        · positivity
    _ = (∑ S : Finset X, sampW M S * Real.exp (c * ((S.filter p).card : ℝ))) *
          Real.exp (-(c * a)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun S _ => ?_
        ring
    _ ≤ Real.exp ((Real.exp c - 1) * ∑ x ∈ Finset.univ.filter p, M x) *
          Real.exp (-(c * a)) :=
        mul_le_mul_of_nonneg_right (sum_sampW_exp_le M hM p c) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

theorem exp_sub_one_sub_le {u : ℝ} (hu : |u| ≤ 1) : Real.exp u - 1 - u ≤ u ^ 2 :=
  (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hu)

theorem sum_filter_M_le (M : X → ℝ) (hM : ∀ x, 0 ≤ M x ∧ M x ≤ 1) (p : X → Prop)
    [DecidablePred p] :
    ∑ x ∈ Finset.univ.filter p, M x ≤ Fintype.card X := by
  calc ∑ x ∈ Finset.univ.filter p, M x ≤ ∑ x : X, M x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => (hM x).1)
    _ ≤ ∑ _x : X, (1 : ℝ) := Finset.sum_le_sum fun x _ => (hM x).2
    _ = _ := by simp

theorem sum_M_agr (M : X → ℝ) (h f : X → Bool) :
    ∑ x, M x * agr h f x = ∑ x ∈ Finset.univ.filter (fun x => h x = f x), M x := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold agr; split_ifs <;> simp

/-- **Sampling a hardcore set from a hardcore measure** (abstract form). -/
theorem exists_sample_set (H : Finset (X → Bool)) (f : X → Bool) (M : X → ℝ)
    (hM : ∀ x, 0 ≤ M x ∧ M x ≤ 1) {γ τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ ≤ 2)
    (hH : ∀ h ∈ H, ∑ x, M x * agr h f x ≤ (1 / 2 + γ) * ∑ x, M x)
    (hcount : ((H.card : ℝ) + 1) * Real.exp (-(τ ^ 2 * Fintype.card X / 4)) < 1) :
    ∃ S : Finset X, ∑ x, M x - τ * Fintype.card X < (S.card : ℝ) ∧
      ∀ h ∈ H, (((S.filter fun x => h x = f x).card : ℕ) : ℝ) <
        (1 / 2 + γ) * ∑ x, M x + τ * Fintype.card X := by
  set N : ℝ := (Fintype.card X : ℝ) with hN
  set μ : ℝ := ∑ x, M x with hμ
  set lam : ℝ := τ / 2 with hlam
  have hlam0 : 0 < lam := by rw [hlam]; linarith
  have hlam1 : lam ≤ 1 := by rw [hlam]; linarith
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set E : ℝ := Real.exp (-(τ ^ 2 * N / 4)) with hE
  have hexpo : lam ^ 2 * N - lam * (τ * N) = -(τ ^ 2 * N / 4) := by rw [hlam]; ring
  -- lower tail for `|S|`
  obtain ⟨low, hlowd⟩ : ∃ low : Finset X → ℝ, low = fun S =>
      if (-lam) * (μ - τ * N) ≤ (-lam) * ((S.filter fun _ => True).card : ℝ) then 1 else 0 :=
    ⟨_, rfl⟩
  have hlow : ∑ S : Finset X, sampW M S * low S ≤ E := by
    rw [hlowd]
    refine (sampW_tail M hM (fun _ => True) (-lam) (μ - τ * N)).trans ?_
    rw [hE, ← hexpo]
    apply Real.exp_le_exp.2
    have hsum : ∑ x ∈ Finset.univ.filter (fun _ : X => True), M x = μ := by
      rw [Finset.filter_true]
    rw [hsum]
    have hμN : μ ≤ N := by
      have := sum_filter_M_le M hM (fun _ => True); rwa [hsum] at this
    have hμ0 : 0 ≤ μ := Finset.sum_nonneg fun x _ => (hM x).1
    have hb := exp_sub_one_sub_le (u := -lam) (by rw [abs_neg, abs_of_pos hlam0]; exact hlam1)
    have : (Real.exp (-lam) - 1 + lam) * μ ≤ lam ^ 2 * N := by
      have h1 : Real.exp (-lam) - 1 + lam ≤ lam ^ 2 := by linarith [neg_sq lam]
      have h2 : 0 ≤ Real.exp (-lam) - 1 + lam := by linarith [Real.add_one_le_exp (-lam)]
      calc (Real.exp (-lam) - 1 + lam) * μ ≤ lam ^ 2 * μ :=
            mul_le_mul_of_nonneg_right h1 hμ0
        _ ≤ lam ^ 2 * N := mul_le_mul_of_nonneg_left hμN (sq_nonneg _)
    nlinarith
  -- upper tail for each hypothesis
  obtain ⟨up, hupd⟩ : ∃ up : (X → Bool) → Finset X → ℝ, up = fun h S =>
      if lam * ((1 / 2 + γ) * μ + τ * N) ≤
        lam * ((S.filter fun x => h x = f x).card : ℝ) then 1 else 0 :=
    ⟨_, rfl⟩
  have hup : ∀ h ∈ H, ∑ S : Finset X, sampW M S * up h S ≤ E := by
    intro h hh
    rw [hupd]
    refine (sampW_tail M hM (fun x => h x = f x) lam ((1 / 2 + γ) * μ + τ * N)).trans ?_
    rw [hE, ← hexpo]
    apply Real.exp_le_exp.2
    set μA := ∑ x ∈ Finset.univ.filter (fun x => h x = f x), M x with hμA
    have hA : μA ≤ (1 / 2 + γ) * μ := by rw [hμA, ← sum_M_agr]; exact hH h hh
    have hAN : μA ≤ N := sum_filter_M_le M hM _
    have hA0 : 0 ≤ μA := Finset.sum_nonneg fun x _ => (hM x).1
    have hb := exp_sub_one_sub_le (u := lam) (by rw [abs_of_pos hlam0]; exact hlam1)
    have h1 : (Real.exp lam - 1 - lam) * μA ≤ lam ^ 2 * N :=
      calc (Real.exp lam - 1 - lam) * μA ≤ lam ^ 2 * μA := mul_le_mul_of_nonneg_right hb hA0
        _ ≤ lam ^ 2 * N := mul_le_mul_of_nonneg_left hAN (sq_nonneg _)
    have h2 : lam * μA ≤ lam * ((1 / 2 + γ) * μ) := mul_le_mul_of_nonneg_left hA hlam0.le
    nlinarith
  -- some subset avoids all bad events
  by_contra hcon
  push Not at hcon
  have hbad : ∀ S : Finset X, 1 ≤ low S + ∑ h ∈ H, up h S := by
    intro S
    have hlow0 : 0 ≤ low S := by rw [hlowd]; dsimp only; split_ifs <;> norm_num
    have hup0 : ∀ h, 0 ≤ up h S := fun h => by rw [hupd]; dsimp only; split_ifs <;> norm_num
    by_cases hS : (S.card : ℝ) ≤ μ - τ * N
    · have : low S = 1 := by
        rw [hlowd]; dsimp only
        rw [if_pos]
        rw [Finset.filter_true]; exact mul_le_mul_of_nonpos_left hS (by linarith)
      rw [this]
      linarith [Finset.sum_nonneg fun h (_ : h ∈ H) => hup0 h]
    · push Not at hS
      obtain ⟨h, hh, hge⟩ := hcon S hS
      have : up h S = 1 := by
        rw [hupd]; dsimp only
        rw [if_pos]
        exact mul_le_mul_of_nonneg_left hge hlam0.le
      have := Finset.single_le_sum (fun h (_ : h ∈ H) => hup0 h) hh
      linarith
  have htot : (1 : ℝ) ≤ ((H.card : ℝ) + 1) * E := by
    calc (1 : ℝ) = ∑ S : Finset X, sampW M S * 1 := by simp [sum_sampW]
      _ ≤ ∑ S : Finset X, sampW M S * (low S + ∑ h ∈ H, up h S) :=
          Finset.sum_le_sum fun S _ =>
            mul_le_mul_of_nonneg_left (hbad S) (sampW_nonneg M hM S)
      _ = ∑ S : Finset X, sampW M S * low S +
            ∑ h ∈ H, ∑ S : Finset X, sampW M S * up h S := by
          rw [Finset.sum_comm (s := H)]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [mul_add, Finset.mul_sum]
      _ ≤ E + ∑ _h ∈ H, E := add_le_add hlow (Finset.sum_le_sum hup)
      _ = ((H.card : ℝ) + 1) * E := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  linarith

end Sampling

/-! ## The circuit form -/

/-- The functions on `n` bits computable with at most `s` gates, as a finite set. -/
def smallFns (n s : ℕ) : Finset ((Fin n → Bool) → Bool) :=
  Finset.univ.filter fun C => HasCircuitOfSize C s

theorem card_smallFns_le (n s : ℕ) : (smallFns n s).card ≤ circCount n s := by
  have hsub : smallFns n s ⊆ (Finset.range (s + 1)).biUnion fun t =>
      (Finset.univ : Finset (Circuit n t)).image Circuit.eval := by
    intro C hC
    simp only [smallFns, Finset.mem_filter, Finset.mem_univ, true_and] at hC
    obtain ⟨t, ht, D, rfl⟩ := hC
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨t, by omega, D, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ t ∈ Finset.range (s + 1), ((Finset.univ : Finset (Circuit n t)).image
        Circuit.eval).card
      ≤ ∑ _t ∈ Finset.range (s + 1), (n + s) * (16 * (n + s) ^ 2) ^ s := by
        refine Finset.sum_le_sum fun t ht => ?_
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_univ]
        exact card_circuit_le n t s (by simp at ht; omega)
    _ = circCount n s := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, circCount]

/-- **Impagliazzo's hardcore lemma, set version.** Let `δ ≤ 1`, `0 < γ ≤ 1`, `γ δ L ≥ 1`,
`L + 1 < 2 γ δ T`, and `(circCount n s + 1) · exp(-γ²δ² 2^n / 64) < 1`. If every circuit with
`T s + majSize T` gates disagrees with `f` on at least `δ 2^n` inputs, then there is a set `S`
of at least `(δ/2) 2^n` inputs on which every circuit with `s` gates agrees with `f` on at most
a `1/2 + 3γ` fraction of `S`. -/
theorem hardcore_set_lemma {n s : ℕ} (f : (Fin n → Bool) → Bool) {δ γ : ℝ}
    (hδ1 : δ ≤ 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) {L T : ℕ} (hL : 1 ≤ L)
    (hLδ : 1 ≤ γ * δ * L) (hT : (L : ℝ) + 1 < 2 * γ * δ * T)
    (hcount : ((circCount n s : ℝ) + 1) * Real.exp (-(γ ^ 2 * δ ^ 2 * 2 ^ n / 64)) < 1)
    (hhard : ∀ C : (Fin n → Bool) → Bool, HasCircuitOfSize C (T * s + majSize T) →
      δ * 2 ^ n ≤ (((Finset.univ.filter fun x => C x ≠ f x).card : ℕ) : ℝ)) :
    ∃ S : Finset (Fin n → Bool), δ / 2 * 2 ^ n ≤ (S.card : ℝ) ∧
      ∀ C : (Fin n → Bool) → Bool, HasCircuitOfSize C s →
        (((S.filter fun x => C x = f x).card : ℕ) : ℝ) ≤ (1 / 2 + 3 * γ) * S.card := by
  obtain ⟨M, hM, hdens, hagr⟩ := hardcore_lemma f hδ1 hγ hL hLδ hT hhard
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hδ0 : 0 < δ := by
    by_contra h
    push Not at h
    have : γ * δ * L ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hγ.le h) hLpos.le
    linarith
  set τ : ℝ := γ * δ / 4 with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ2 : τ ≤ 2 := by
    rw [hτ]
    have : γ * δ ≤ 1 := by nlinarith
    linarith
  have hc : (((smallFns n s).card : ℝ) + 1) *
      Real.exp (-(τ ^ 2 * Fintype.card (Fin n → Bool) / 4)) < 1 := by
    have he : τ ^ 2 * Fintype.card (Fin n → Bool) / 4 = γ ^ 2 * δ ^ 2 * 2 ^ n / 64 := by
      rw [hcard, hτ]; ring
    rw [he]
    refine lt_of_le_of_lt ?_ hcount
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have := card_smallFns_le n s
    have : ((smallFns n s).card : ℝ) ≤ circCount n s := by exact_mod_cast this
    linarith
  obtain ⟨S, hS, hSagr⟩ := exists_sample_set (smallFns n s) f M hM hτ0 hτ2
    (fun C hC => hagr C (by simpa [smallFns] using hC)) hc
  rw [hcard] at hS hSagr
  set N : ℝ := (2 : ℝ) ^ n with hN
  set μ := ∑ x, M x with hμ
  have hN0 : 0 < N := by positivity
  have hSbig : δ / 2 * N ≤ (S.card : ℝ) := by
    have : τ * N ≤ δ / 4 * N := by
      rw [hτ]
      have : γ * δ ≤ δ := by nlinarith
      nlinarith
    nlinarith
  refine ⟨S, hSbig, fun C hC => ?_⟩
  have h1 := hSagr C (by simp [smallFns, hC])
  have h2 : μ < S.card + τ * N := by linarith
  have h3 : (1 / 2 + γ) * μ ≤ (1 / 2 + γ) * (S.card + τ * N) :=
    mul_le_mul_of_nonneg_left h2.le (by linarith)
  have h4 : (3 / 2 + γ) * τ * N ≤ 5 / 8 * γ * δ * N := by
    rw [hτ]
    have : 0 ≤ γ * δ * N := by positivity
    nlinarith
  have h5 : 5 / 8 * γ * δ * N ≤ 5 / 4 * γ * S.card := by nlinarith
  nlinarith

/-! ## Non-vacuity -/

theorem circCount_mono {m s t : ℕ} (h : s ≤ t) : circCount m s ≤ circCount m t := by
  unfold circCount
  have h1 : (m + s) ≤ (m + t) := by omega
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · obtain rfl : s = 0 := by omega
    exact le_rfl
  have hmt : 0 < m + t := by omega
  have h2 : (16 * (m + s) ^ 2) ^ s ≤ (16 * (m + t) ^ 2) ^ t :=
    (Nat.pow_le_pow_left (by gcongr) s).trans
      (Nat.pow_le_pow_right (by positivity) h)
  gcongr

/-- **The set version is not vacuous.** For `k ≥ 2`, `a ≥ 1` with `4096 a² ≤ 4^k`, and any `s`
with `T s + majSize T ≤ 4^k` (`T = 4a(4a+1)`), some `f : {0,1}^(8k) → {0,1}` has a hardcore
set of at least `2^(8k) / 8` inputs on which every circuit with `s` gates agrees with `f` on at
most a `1/2 + 3/a` fraction. -/
theorem exists_hardcore_set (k a s : ℕ) (hk : 2 ≤ k) (ha : 1 ≤ a) (hak : 4096 * a ^ 2 ≤ 4 ^ k)
    (hs : a * 4 * (a * 4 + 1) * s + majSize (a * 4 * (a * 4 + 1)) ≤ 4 ^ k) :
    ∃ f : (Fin (8 * k) → Bool) → Bool, ∃ S : Finset (Fin (8 * k) → Bool),
      (1 / 8 : ℝ) * 2 ^ (8 * k) ≤ (S.card : ℝ) ∧
      ∀ C : (Fin (8 * k) → Bool) → Bool, HasCircuitOfSize C s →
        (((S.filter fun x => C x = f x).card : ℕ) : ℝ) ≤ (1 / 2 + 3 * (1 / a)) * S.card := by
  obtain ⟨f, hf⟩ := exists_avgHard_explicit k (by omega)
  refine ⟨f, ?_⟩
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab : 1 ≤ a * 4 := by omega
  have hsle : s ≤ 4 ^ k := by
    have : 1 ≤ a * 4 * (a * 4 + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  -- the counting condition
  have hcount : ((circCount (8 * k) s : ℝ) + 1) *
      Real.exp (-((1 / (a : ℝ)) ^ 2 * (1 / 4) ^ 2 * 2 ^ (8 * k) / 64)) < 1 := by
    have hc1 : (circCount (8 * k) s : ℝ) + 1 ≤ 2 ^ (2 * 64 ^ k) := by
      have := (circCount_mono (m := 8 * k) hsle).trans_lt (circCount_lt k (by omega))
      have : circCount (8 * k) s + 1 ≤ 2 ^ (2 * 64 ^ k) := this
      exact_mod_cast this
    have hc2 : (2 : ℝ) ^ (2 * 64 ^ k) ≤ Real.exp ((2 * 64 ^ k : ℕ) : ℝ) := two_pow_le_exp _
    have hX : 4 * (64 : ℝ) ^ k ≤ (1 / (a : ℝ)) ^ 2 * (1 / 4) ^ 2 * 2 ^ (8 * k) / 64 := by
      have e : (2 : ℝ) ^ (8 * k) = 4 ^ k * 64 ^ k := by
        rw [← mul_pow]; norm_num [pow_mul]
      rw [e]
      have hak' : 4096 * (a : ℝ) ^ 2 ≤ 4 ^ k := by exact_mod_cast hak
      have hapos : (0 : ℝ) < a := by linarith
      rw [le_div_iff₀ (by norm_num)]
      field_simp
      have : (0 : ℝ) ≤ 64 ^ k := by positivity
      nlinarith
    have hpos : (0 : ℝ) < 64 ^ k := by positivity
    calc ((circCount (8 * k) s : ℝ) + 1) *
          Real.exp (-((1 / (a : ℝ)) ^ 2 * (1 / 4) ^ 2 * 2 ^ (8 * k) / 64))
        ≤ Real.exp ((2 * 64 ^ k : ℕ) : ℝ) * Real.exp (-(4 * (64 : ℝ) ^ k)) := by
          apply mul_le_mul (hc1.trans hc2) (Real.exp_le_exp.2 (by linarith))
            (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (-(2 * (64 : ℝ) ^ k)) := by rw [← Real.exp_add]; push_cast; ring_nf
      _ < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h4 : (1 : ℝ) / 2 ^ k ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hδ1 : (1 / 4 : ℝ) ≤ 1 := by norm_num
  have hγ : (0 : ℝ) < 1 / a := by positivity
  have hγ1 : (1 : ℝ) / a ≤ 1 := by rw [div_le_one (by linarith)]; exact ha'
  obtain ⟨S, hS1, hS2⟩ := hardcore_set_lemma (s := s) f hδ1 hγ hγ1 (L := a * 4)
    (T := a * 4 * (a * 4 + 1)) hab
    (by push_cast; field_simp; exact le_rfl)
    (by
      push_cast
      have e : 2 * (1 / (a : ℝ)) * (1 / 4) * (a * 4 * (a * 4 + 1)) = 2 * (a * 4 + 1) := by
        field_simp
      rw [e]
      nlinarith)
    hcount
    (fun C hC => by
      have hd := disagree_of_avgHard hf C (hC.mono hs)
      have hpos : (0 : ℝ) < 2 ^ (8 * k) := by positivity
      nlinarith)
  refine ⟨S, ?_, hS2⟩
  have : (1 / 4 : ℝ) / 2 * 2 ^ (8 * k) = 1 / 8 * 2 ^ (8 * k) := by ring
  linarith

end

end Pnp.Derand
