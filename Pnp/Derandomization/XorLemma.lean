import Pnp.Derandomization.Hardcore

/-!
# Yao's XOR lemma (M38)

If `f : {0,1}^n → {0,1}` is mildly hard (every circuit of a certain size errs on a `δ`
fraction of inputs), then `f^{⊕k}(x₁, …, x_k) = f(x₁) ⊕ ⋯ ⊕ f(x_k)` is very hard: every
somewhat smaller circuit agrees with it on at most a `1/2 + γ + (1 - δ)^k` fraction of inputs.

The proof goes through the hardcore measure `M` of M37 (Impagliazzo's proof of the XOR lemma):

* Write `1 = M(x) + (1 - M(x))` at every coordinate and expand the product (`Finset.prod_add`):
  the uniform weight on `X^k` splits into weights `w_S(x) = ∏_{i∈S} M(xᵢ) ∏_{i∉S} (1 - M(xᵢ))`
  over subsets `S` of coordinates.
* For `S ≠ ∅` pick `i ∈ S`. Fixing all other coordinates turns a test `D` for `f^{⊕k}` into a
  test `y ↦ D(…, y, …) ⊕ b` for `f` under `M`, so the agreement under `w_S` is at most
  `(1/2 + γ)` of its total weight (`agree_wS_le`; resampling coordinate `i`, `resample`).
* `S = ∅` has total weight `(Σ (1 - M))^k ≤ ((1 - δ) N)^k`.

Main results:
* `xor_lemma_measure` (abstract: finite `X`, any hardcore measure),
* `xor_lemma` (circuits; tests on `k n` input bits).
-/

namespace Pnp.Derand

open Pnp.Circuits Classical

noncomputable section

section Abstract

variable {X : Type} [Fintype X] {k : ℕ}

/-- Parity indicator in `ZMod 2`. -/
def bit2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- `f^{⊕k}`. -/
def xorK (f : X → Bool) (x : Fin k → X) : Bool := decide (∑ i, bit2 (f (x i)) = 1)

/-- Parity of all coordinates except `i`. -/
def xorRest (f : X → Bool) (i : Fin k) (x : Fin k → X) : Bool :=
  decide (∑ j ∈ Finset.univ.erase i, bit2 (f (x j)) = 1)

omit [Fintype X] in
theorem xorK_update (f : X → Bool) (i : Fin k) (x : Fin k → X) (y : X) :
    xorK f (Function.update x i y) = xor (f y) (xorRest f i x) := by
  unfold xorK xorRest
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have : ∑ j ∈ Finset.univ.erase i, bit2 (f (Function.update x i y j)) =
      ∑ j ∈ Finset.univ.erase i, bit2 (f (x j)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this]
  generalize ∑ j ∈ Finset.univ.erase i, bit2 (f (x j)) = r
  cases f y <;> revert r <;> decide

omit [Fintype X] in
theorem xorRest_update (f : X → Bool) (i : Fin k) (x : Fin k → X) (y : X) :
    xorRest f i (Function.update x i y) = xorRest f i x := by
  unfold xorRest
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Resampling one coordinate.** `|X| · Σ_x F(x) = Σ_x Σ_y F(x[i ↦ y])`. -/
theorem resample (i : Fin k) (F : (Fin k → X) → ℝ) :
    (Fintype.card X : ℝ) * ∑ x, F x = ∑ x, ∑ y, F (Function.update x i y) := by
  -- the involution `(x, y) ↦ (x[i ↦ y], x i)`
  let Φ : (Fin k → X) × X ≃ (Fin k → X) × X :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have h := Fintype.sum_equiv Φ (fun p => F (Function.update p.1 i p.2)) (fun p => F p.1)
    (fun p => by simp [Φ])
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  simp only at h
  rw [h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- The weight of the term `S` in the expansion of `∏ᵢ (M(xᵢ) + (1 - M(xᵢ)))`. -/
def wS (M : X → ℝ) (S : Finset (Fin k)) (x : Fin k → X) : ℝ :=
  (∏ j ∈ S, M (x j)) * ∏ j ∈ Finset.univ \ S, (1 - M (x j))

omit [Fintype X] in
theorem wS_nonneg {M : X → ℝ} (hM : ∀ x, 0 ≤ M x ∧ M x ≤ 1) (S : Finset (Fin k))
    (x : Fin k → X) : 0 ≤ wS M S x := by
  unfold wS
  refine mul_nonneg (Finset.prod_nonneg fun j _ => (hM _).1)
    (Finset.prod_nonneg fun j _ => sub_nonneg.2 (hM _).2)

/-- Agreement of a test `D` with `f^{⊕k}` under `w_S`, `S ∋ i`, is at most `1/2 + γ` of the
weight, provided every one-coordinate restriction of `D` (xored with a constant) agrees with
`f` under `M` with weight `≤ (1/2 + γ) Σ M`. -/
theorem agree_wS_le (f : X → Bool) {M : X → ℝ} (hM : ∀ x, 0 ≤ M x ∧ M x ≤ 1) {γ : ℝ}
    (D : (Fin k → X) → Bool)
    (hD : ∀ (i : Fin k) (x : Fin k → X) (b : Bool),
      ∑ y, M y * agr (fun y => xor (D (Function.update x i y)) b) f y ≤ (1 / 2 + γ) * ∑ y, M y)
    [Nonempty X] (S : Finset (Fin k)) {i : Fin k} (hi : i ∈ S) :
    ∑ x, wS M S x * agr D (xorK f) x ≤ (1 / 2 + γ) * ∑ x, wS M S x := by
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos (α := X)
  -- `w_S = M(xᵢ) · W` with `W` independent of coordinate `i`
  let W : (Fin k → X) → ℝ := fun x =>
    (∏ j ∈ S.erase i, M (x j)) * ∏ j ∈ Finset.univ \ S, (1 - M (x j))
  have hW : ∀ x y, W (Function.update x i y) = W x := by
    intro x y
    simp only [W]
    congr 1
    · refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    · refine Finset.prod_congr rfl fun j hj => ?_
      have : j ≠ i := by
        rintro rfl; simp [hi] at hj
      rw [Function.update_of_ne this]
  have hWn : ∀ x, 0 ≤ W x := fun x =>
    mul_nonneg (Finset.prod_nonneg fun j _ => (hM _).1)
      (Finset.prod_nonneg fun j _ => sub_nonneg.2 (hM _).2)
  have hwS : ∀ x, wS M S x = M (x i) * W x := by
    intro x
    simp only [wS, W]
    rw [← mul_assoc, Finset.mul_prod_erase _ (fun j => M (x j)) hi]
  have hagr : ∀ x y, agr D (xorK f) (Function.update x i y) =
      agr (fun y => xor (D (Function.update x i y)) (xorRest f i x)) f y := by
    intro x y
    unfold agr
    rw [xorK_update]
    congr 1
    beta_reduce
    generalize D (Function.update x i y) = d
    generalize xorRest f i x = b
    apply propext
    cases d <;> cases b <;> cases f y <;> decide
  refine le_of_mul_le_mul_left ?_ hN
  rw [mul_left_comm, resample i, resample i, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have e1 : ∑ y, wS M S (Function.update x i y) * agr D (xorK f) (Function.update x i y) =
      W x * ∑ y, M y * agr (fun y => xor (D (Function.update x i y)) (xorRest f i x)) f y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hwS, hW, hagr, Function.update_self]; ring
  have e2 : ∑ y, wS M S (Function.update x i y) = W x * ∑ y, M y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hwS, hW, Function.update_self]; ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left (hD i x (xorRest f i x)) (hWn x)
  linarith

/-- **Yao's XOR lemma, measure form.** Let `M : X → [0,1]` have weight `≥ δ |X|`. If every
one-coordinate restriction of `D` (xored with any constant) agrees with `f` under `M` with
weight `≤ (1/2 + γ) Σ M`, then `D` agrees with `f^{⊕k}` on at most
`(1/2 + γ + (1 - δ)^k) |X|^k` inputs. -/
theorem xor_lemma_measure [Nonempty X] (f : X → Bool) {M : X → ℝ}
    (hM : ∀ x, 0 ≤ M x ∧ M x ≤ 1) {δ γ : ℝ} (hγ : 0 ≤ 1 / 2 + γ)
    (hdense : δ * Fintype.card X ≤ ∑ x, M x) (D : (Fin k → X) → Bool)
    (hD : ∀ (i : Fin k) (x : Fin k → X) (b : Bool),
      ∑ y, M y * agr (fun y => xor (D (Function.update x i y)) b) f y ≤ (1 / 2 + γ) * ∑ y, M y) :
    ∑ x, agr D (xorK f) x ≤ (1 / 2 + γ + (1 - δ) ^ k) * (Fintype.card X : ℝ) ^ k := by
  set N : ℝ := (Fintype.card X : ℝ)
  have hagr01 : ∀ x, 0 ≤ agr D (xorK f) x ∧ agr D (xorK f) x ≤ 1 := by
    intro x; unfold agr; split_ifs <;> norm_num
  -- expansion
  have hexp : ∀ x : Fin k → X, ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, wS M S x = 1 := by
    intro x
    have := Finset.prod_add (fun j => M (x j)) (fun j => 1 - M (x j)) Finset.univ
    simp only [add_sub_cancel, Finset.prod_const_one] at this
    rw [this]; rfl
  have htot : ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, ∑ x, wS M S x = N ^ k := by
    rw [Finset.sum_comm]
    simp only [hexp, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    push_cast; rfl
  have hsplit : ∑ x, agr D (xorK f) x =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, ∑ x, wS M S x * agr D (xorK f) x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, hexp, one_mul]
  have hmem : (∅ : Finset (Fin k)) ∈ (Finset.univ : Finset (Fin k)).powerset :=
    Finset.empty_mem_powerset _
  rw [hsplit, ← Finset.add_sum_erase _ _ hmem]
  rw [← Finset.add_sum_erase _ _ hmem] at htot
  -- the empty term
  have hempty : ∑ x, wS M ∅ x * agr D (xorK f) x ≤ ((1 - δ) * N) ^ k := by
    calc ∑ x, wS M ∅ x * agr D (xorK f) x ≤ ∑ x, wS M ∅ x := by
          refine Finset.sum_le_sum fun x _ => ?_
          have := wS_nonneg hM ∅ x
          nlinarith [hagr01 x]
      _ = (∑ y, (1 - M y)) ^ k := by
          simp only [wS, Finset.prod_empty, one_mul, Finset.sdiff_empty]
          rw [← Fin.prod_const k (∑ y, (1 - M y)), Finset.prod_univ_sum, Fintype.piFinset_univ]
      _ ≤ ((1 - δ) * N) ^ k := by
          apply pow_le_pow_left₀
          · exact Finset.sum_nonneg fun y _ => sub_nonneg.2 (hM y).2
          · rw [Finset.sum_sub_distrib]
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
            linarith
  -- the other terms
  have hrest : ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅,
      ∑ x, wS M S x * agr D (xorK f) x ≤
        (1 / 2 + γ) * ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, ∑ x, wS M S x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun S hS => ?_
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hS)
    exact agree_wS_le f hM D hD S hi
  have hE0 : 0 ≤ ∑ x : Fin k → X, wS M ∅ x := Finset.sum_nonneg fun x _ => wS_nonneg hM ∅ x
  have hNk : ((1 - δ) * N) ^ k = (1 - δ) ^ k * N ^ k := mul_pow _ _ _
  have : (1 / 2 + γ) * ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset.erase ∅, ∑ x, wS M S x ≤
      (1 / 2 + γ) * N ^ k := by
    apply mul_le_mul_of_nonneg_left _ hγ
    linarith
  have hfin : (1 / 2 + γ + (1 - δ) ^ k) * N ^ k = (1 - δ) ^ k * N ^ k + (1 / 2 + γ) * N ^ k := by
    ring
  rw [hfin]
  linarith

end Abstract

/-! ## The circuit form -/

/-- Flattening `k` blocks of `n` bits into `k n` bits. -/
def blocksEquiv {k n : ℕ} : (Fin (k * n) → Bool) ≃ (Fin k → Fin n → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- Hard-wiring all blocks but one is cheap: `y ↦ blocksEquiv.symm (x[i ↦ y])` has a multi-output
circuit with `k n` gates. -/
theorem hasMCircuitOfSize_plug {k n : ℕ} (hn : 0 < n) (i : Fin k) (x : Fin k → Fin n → Bool) :
    HasMCircuitOfSize (fun y : Fin n → Bool => blocksEquiv.symm (Function.update x i y)) (k * n) := by
  have h := hasMCircuitOfSize_of_forall (n := n) (m := k * n)
    (fun y : Fin n → Bool => blocksEquiv.symm (Function.update x i y)) (s := 1) (fun p => ?_)
  · simpa using h
  obtain ⟨⟨j, q⟩, rfl⟩ := finProdFinEquiv.surjective p
  have e : ∀ y : Fin n → Bool, blocksEquiv.symm (Function.update x i y) (finProdFinEquiv (j, q)) =
      Function.update x i y j q := by
    intro y; simp [blocksEquiv, Equiv.arrowCongr, Equiv.curry]
  simp only [e]
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    exact (hasCircuitOfSize_var q).mono (Nat.zero_le 1)
  · simp only [Function.update_of_ne hj]
    exact hasCircuitOfSize_const hn _

/-- **Yao's XOR lemma** (circuits). Let `0 < n`, `δ ≤ 1`, `γ > 0`, `γ δ L ≥ 1`,
`L + 1 < 2 γ δ T`. If every circuit with `T (k n + s + 1) + majSize T` gates errs on at least
`δ 2^n` inputs of `f`, then every circuit with `s` gates on `k n` input bits agrees with
`f^{⊕k}` on at most a `1/2 + γ + (1 - δ)^k` fraction of the `2^{kn}` inputs. -/
theorem xor_lemma {n k s : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) {δ γ : ℝ}
    (hδ1 : δ ≤ 1) (hγ : 0 < γ) {L T : ℕ} (hL : 1 ≤ L) (hLδ : 1 ≤ γ * δ * L)
    (hT : (L : ℝ) + 1 < 2 * γ * δ * T)
    (hhard : ∀ C : (Fin n → Bool) → Bool, HasCircuitOfSize C (T * (k * n + s + 1) + majSize T) →
      δ * 2 ^ n ≤ (((Finset.univ.filter fun x => C x ≠ f x).card : ℕ) : ℝ))
    (D : (Fin (k * n) → Bool) → Bool) (hD : HasCircuitOfSize D s) :
    (((Finset.univ.filter fun z => D z = xorK f (blocksEquiv z)).card : ℕ) : ℝ) ≤
      (1 / 2 + γ + (1 - δ) ^ k) * 2 ^ (k * n) := by
  obtain ⟨M, hM, hdense, hcore⟩ := hardcore_lemma (s := k * n + s + 1) f hδ1 hγ hL hLδ hT hhard
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring
  let D' : (Fin k → Fin n → Bool) → Bool := fun x => D (blocksEquiv.symm x)
  have hD' : ∀ (i : Fin k) (x : Fin k → Fin n → Bool) (b : Bool),
      ∑ y, M y * agr (fun y => xor (D' (Function.update x i y)) b) f y ≤
        (1 / 2 + γ) * ∑ y, M y := by
    intro i x b
    apply hcore
    have h1 := (hasMCircuitOfSize_plug hn i x).comp_single hD
    have h2 := ((h1.toM 1).comp_single (hasCircuitOfSize_xor_const b))
    exact h2.mono le_rfl
  have hmain := xor_lemma_measure f hM (by linarith) (by rw [hcard]; exact hdense) D' hD'
  rw [hcard, ← pow_mul] at hmain
  calc (((Finset.univ.filter fun z => D z = xorK f (blocksEquiv z)).card : ℕ) : ℝ)
      = ∑ z, agr D' (xorK f) (blocksEquiv z) := by
        rw [Finset.card_filter]; push_cast
        refine Finset.sum_congr rfl fun z _ => ?_
        simp [agr, D']
    _ = ∑ x, agr D' (xorK f) x := Fintype.sum_equiv blocksEquiv _ _ (fun _ => rfl)
    _ ≤ _ := by rw [mul_comm n k] at hmain; exact hmain

end

end Pnp.Derand
