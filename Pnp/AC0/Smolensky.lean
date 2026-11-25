import Mathlib

/-!
# Smolensky's lemma over `𝔽₃` (Razborov–Smolensky, second half)

A polynomial `P` over `ZMod 3` of total degree `≤ D`, evaluated on `{0,1}ⁿ`, agrees with
PARITY on at most `#{T ⊆ [n] | |T| ≤ n/2 + D} = ∑_{i ≤ n/2 + D} C(n, i)` points
(`smolensky`, `smolensky_choose`).

Proof: substitute `yᵢ = 1 + xᵢ ∈ {1, -1}` (mod 3). Every function `{0,1}ⁿ → 𝔽₃` is a linear
combination of characters `χ_T = ∏_{i ∈ T} yᵢ`. On the agreement set `G`,
`χ_univ = 1 + parity = 1 + P`, so for `|T| > n/2`, `χ_T = χ_univ · χ_{Tᶜ} = (1 + P) · χ_{Tᶜ}`,
a polynomial in `y` of degree `≤ D + n/2`, which multilinearises (using `yᵢ² = 1`) to a
combination of characters of size `≤ n/2 + D`. Hence every function `G → 𝔽₃` is the image of
a coefficient vector indexed by small sets, so `3^|G| ≤ 3^#{small sets}`.
-/

namespace Pnp.AC0.Smolensky

open MvPolynomial Finset

noncomputable section

variable {n : ℕ}

/-- Evaluation of a polynomial over `𝔽₃` at a 0/1 point. -/
def eval01 (P : MvPolynomial (Fin n) (ZMod 3)) (x : Fin n → Bool) : ZMod 3 :=
  MvPolynomial.eval (fun i => if x i then 1 else 0) P

/-- PARITY as an element of `𝔽₃`. -/
def parityVal (x : Fin n → Bool) : ZMod 3 :=
  if (univ.filter (fun i => x i = true)).card % 2 = 1 then 1 else 0

/-- The `±1` variable `yᵢ = 1 - 2xᵢ = 1 + xᵢ` (mod 3). -/
def yv (x : Fin n → Bool) (i : Fin n) : ZMod 3 := if x i then -1 else 1

/-- The character `χ_T = ∏_{i ∈ T} yᵢ`. -/
def chi (T : Finset (Fin n)) (x : Fin n → Bool) : ZMod 3 := ∏ i ∈ T, yv x i

/-- `f` is the evaluation, at `y(x)`, of a polynomial of total degree `≤ B`. -/
def Rep (B : ℕ) (f : (Fin n → Bool) → ZMod 3) : Prop :=
  ∃ Q : MvPolynomial (Fin n) (ZMod 3), Q.totalDegree ≤ B ∧ ∀ x, f x = eval (yv x) Q

/-- The span of the characters of size `≤ B`. -/
def V (n B : ℕ) : Submodule (ZMod 3) ((Fin n → Bool) → ZMod 3) :=
  Submodule.span (ZMod 3)
    (Set.range (fun T : {T : Finset (Fin n) // T.card ≤ B} => chi T.1))

lemma yv_mul_self (x : Fin n → Bool) (i : Fin n) : yv x i * yv x i = 1 := by
  unfold yv; split <;> decide

lemma chi_mul_self (T : Finset (Fin n)) (x : Fin n → Bool) : chi T x * chi T x = 1 := by
  unfold chi; rw [← prod_mul_distrib]; simp [yv_mul_self]

lemma yv_pow (x : Fin n → Bool) (i : Fin n) (k : ℕ) :
    yv x i ^ k = if Odd k then yv x i else 1 := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have : ¬ Odd (2 * m) := by simp [Nat.not_odd_iff_even]
    rw [if_neg this, pow_mul, sq, yv_mul_self, one_pow]
  · have : Odd (2 * m + 1) := ⟨m, rfl⟩
    rw [if_pos this, pow_succ, pow_mul, sq, yv_mul_self, one_pow, one_mul]

lemma chi_univ (x : Fin n → Bool) : chi univ x = 1 + parityVal x := by
  unfold chi yv parityVal
  rw [prod_ite]
  simp only [prod_const, one_pow, mul_one]
  rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (univ.filter (fun i => x i = true)).card with h | h <;>
    rw [h] <;> decide

/-! ### Closure properties of `Rep` -/

lemma Rep.mono {A B : ℕ} {f : (Fin n → Bool) → ZMod 3} (h : A ≤ B) (hf : Rep A f) :
    Rep B f := by
  obtain ⟨Q, hQ, hf⟩ := hf; exact ⟨Q, hQ.trans h, hf⟩

lemma Rep.add {A B : ℕ} {f g : (Fin n → Bool) → ZMod 3} (hf : Rep A f) (hg : Rep B g) :
    Rep (max A B) (fun x => f x + g x) := by
  obtain ⟨Q, hQ, hf⟩ := hf; obtain ⟨R, hR, hg⟩ := hg
  exact ⟨Q + R, (totalDegree_add _ _).trans (max_le_max hQ hR), fun x => by simp [hf, hg]⟩

lemma Rep.mul {A B : ℕ} {f g : (Fin n → Bool) → ZMod 3} (hf : Rep A f) (hg : Rep B g) :
    Rep (A + B) (fun x => f x * g x) := by
  obtain ⟨Q, hQ, hf⟩ := hf; obtain ⟨R, hR, hg⟩ := hg
  exact ⟨Q * R, (totalDegree_mul _ _).trans (add_le_add hQ hR), fun x => by simp [hf, hg]⟩

lemma Rep.const (c : ZMod 3) : Rep (n := n) 0 (fun _ => c) :=
  ⟨C c, by simp, fun x => by simp⟩

lemma Rep.y (i : Fin n) : Rep 1 (fun x => yv x i) :=
  ⟨X i, (totalDegree_X i).le, fun x => by simp⟩

lemma Rep.x01 (i : Fin n) : Rep 1 (fun x : Fin n → Bool => if x i then (1 : ZMod 3) else 0) := by
  refine (Rep.add (Rep.const 2) (Rep.y i)).mono (by simp) |>.imp fun Q hQ => ⟨hQ.1, fun x => ?_⟩
  rw [← hQ.2 x]; show (if x i then (1 : ZMod 3) else 0) = 2 + yv x i
  unfold yv; cases x i <;> decide

lemma Rep.prod {ι : Type*} (s : Finset ι) (B : ι → ℕ) (f : ι → (Fin n → Bool) → ZMod 3)
    (h : ∀ i ∈ s, Rep (B i) (f i)) : Rep (∑ i ∈ s, B i) (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rep.const (n := n) 1
  | insert a s ha ih =>
    simp only [prod_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

lemma Rep.sum {ι : Type*} (s : Finset ι) (B : ℕ) (f : ι → (Fin n → Bool) → ZMod 3)
    (h : ∀ i ∈ s, Rep B (f i)) : Rep B (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Rep.const (n := n) 0).mono (Nat.zero_le B)
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact ((h a (mem_insert_self a s)).add
      (ih fun i hi => h i (mem_insert_of_mem hi))).mono (by simp)

lemma Rep.pow {A : ℕ} {f : (Fin n → Bool) → ZMod 3} (hf : Rep A f) (k : ℕ) :
    Rep (k * A) (fun x => f x ^ k) := by
  have := Rep.prod (range k) (fun _ => A) (fun _ => f) (fun _ _ => hf)
  simp at this; exact this

lemma Rep.of_chi (T : Finset (Fin n)) : Rep T.card (chi T) := by
  have := Rep.prod T (fun _ => 1) (fun i x => yv x i) (fun i _ => Rep.y i)
  simp only [sum_const, smul_eq_mul, mul_one] at this
  exact this

lemma Rep.of_eval01 (P : MvPolynomial (Fin n) (ZMod 3)) :
    Rep P.totalDegree (eval01 P) := by
  have key : ∀ d ∈ P.support, Rep P.totalDegree
      (fun x => coeff d P * ∏ i, (if x i then (1 : ZMod 3) else 0) ^ d i) := by
    intro d hd
    refine ((Rep.const _).mul (Rep.prod univ _ _ fun i _ => (Rep.x01 i).pow (d i))).mono ?_
    have := le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (by simp)] at this
    simpa using this
  have := Rep.sum _ _ _ key
  refine this.imp fun Q hQ => ⟨hQ.1, fun x => ?_⟩
  rw [← hQ.2 x, eval01, eval_eq']

/-- Multilinearisation: a `Rep B` function is in the span of characters of size `≤ B`. -/
lemma Rep.mem_V {B : ℕ} {f : (Fin n → Bool) → ZMod 3} (hf : Rep B f) : f ∈ V n B := by
  obtain ⟨Q, hQ, hf⟩ := hf
  let odd (d : Fin n →₀ ℕ) : Finset (Fin n) := univ.filter (fun i => Odd (d i))
  have hmon : ∀ d : Fin n →₀ ℕ, ∀ x, ∏ i, yv x i ^ d i = chi (odd d) x := by
    intro d x
    simp only [yv_pow, chi, odd]
    rw [prod_filter]
  have hcard : ∀ d ∈ Q.support, (odd d).card ≤ B := by
    intro d hd
    have h1 := le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (by simp)] at h1
    calc (odd d).card = ∑ i ∈ odd d, 1 := by simp
      _ ≤ ∑ i ∈ odd d, d i := sum_le_sum fun i hi => by
          simp only [odd, mem_filter] at hi; exact hi.2.pos
      _ ≤ ∑ i, d i := sum_le_sum_of_subset (subset_univ _)
      _ ≤ B := h1.trans hQ
  have hfeq : f = ∑ d ∈ Q.support, coeff d Q • chi (odd d) := by
    funext x
    rw [hf x, eval_eq']
    simp [Finset.sum_apply, hmon]
  rw [hfeq]
  refine Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨⟨odd d, hcard d hd⟩, rfl⟩

lemma V_mono {A B : ℕ} (h : A ≤ B) : V n A ≤ V n B := by
  refine Submodule.span_mono ?_
  rintro _ ⟨T, rfl⟩
  exact ⟨⟨T.1, T.2.trans h⟩, rfl⟩

/-- Interpolation: every function on `{0,1}ⁿ` has a `y`-representation of degree `≤ n`. -/
lemma Rep.all (f : (Fin n → Bool) → ZMod 3) : Rep n f := by
  have hfac : ∀ a : Fin n → Bool, ∀ i : Fin n, Rep 1
      (fun x => 2 * (1 + yv x i * yv a i)) := fun a i =>
    ((Rep.const 2).mul ((Rep.const 1).add ((Rep.y i).mul (Rep.const _)))).mono (by simp)
  have hind : ∀ a : Fin n → Bool, Rep n
      (fun x => f a * ∏ i, (2 * (1 + yv x i * yv a i))) := fun a =>
    ((Rep.const _).mul (Rep.prod univ _ _ fun i _ => hfac a i)).mono (by simp)
  refine (Rep.sum univ n _ fun a _ => hind a).imp fun Q hQ => ⟨hQ.1, fun x => ?_⟩
  rw [← hQ.2 x]
  have h1 : ∀ a : Fin n → Bool, ∀ i, (2 : ZMod 3) * (1 + yv x i * yv a i) =
      if x i = a i then 1 else 0 := by
    intro a i; unfold yv
    cases x i <;> cases a i <;> decide
  simp only [h1, prod_boole, mem_univ, true_implies]
  have h2 : ∀ a : Fin n → Bool, (∀ i, x i = a i) ↔ x = a := fun a => funext_iff.symm
  simp [h2]

lemma mem_V_all (f : (Fin n → Bool) → ZMod 3) : f ∈ V n n := (Rep.all f).mem_V

/-- **Smolensky's lemma** (counting form): a polynomial over `𝔽₃` of total degree `≤ D`
agrees with PARITY on at most `#{T ⊆ [n] | |T| ≤ n/2 + D}` points of `{0,1}ⁿ`. -/
theorem smolensky (P : MvPolynomial (Fin n) (ZMod 3)) (D : ℕ) (hP : P.totalDegree ≤ D) :
    (univ.filter (fun x : Fin n → Bool => eval01 P x = parityVal x)).card ≤
      (univ.filter (fun T : Finset (Fin n) => T.card ≤ n / 2 + D)).card := by
  classical
  set B := n / 2 + D with hB
  set G := univ.filter (fun x : Fin n → Bool => eval01 P x = parityVal x) with hG
  -- every character agrees on `G` with an element of `V n B`
  have claim1 : ∀ T : Finset (Fin n), ∃ g ∈ V n B, ∀ x ∈ G, chi T x = g x := by
    intro T
    by_cases hT : T.card ≤ B
    · exact ⟨chi T, Submodule.subset_span ⟨⟨T, hT⟩, rfl⟩, fun _ _ => rfl⟩
    · refine ⟨fun x => (1 + eval01 P x) * chi Tᶜ x, ?_, fun x hx => ?_⟩
      · have hr := (((Rep.const 1).add (Rep.of_eval01 P)).mul (Rep.of_chi Tᶜ))
        refine V_mono ?_ hr.mem_V
        have hc : Tᶜ.card = n - T.card := by rw [card_compl, Fintype.card_fin]
        have hTn : T.card ≤ n := by simpa using card_le_univ T
        simp only [zero_max, hc]
        omega
      · simp only [hG, mem_filter, mem_univ, true_and] at hx
        show chi T x = (1 + eval01 P x) * chi Tᶜ x
        rw [hx, ← chi_univ]
        unfold chi
        rw [← prod_mul_prod_compl T, mul_assoc]
        change chi T x = chi T x * (chi Tᶜ x * chi Tᶜ x)
        rw [chi_mul_self, mul_one]
  -- hence every function agrees on `G` with an element of `V n B`
  have claim2 : ∀ f : (Fin n → Bool) → ZMod 3, ∃ g ∈ V n B, ∀ x ∈ G, f x = g x := by
    intro f
    have hf := mem_V_all f
    induction hf using Submodule.span_induction with
    | mem x h =>
      obtain ⟨T, rfl⟩ := h
      exact claim1 T.1
    | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩
    | add f₁ f₂ _ _ ih₁ ih₂ =>
      obtain ⟨g₁, hg₁, e₁⟩ := ih₁
      obtain ⟨g₂, hg₂, e₂⟩ := ih₂
      exact ⟨g₁ + g₂, Submodule.add_mem _ hg₁ hg₂, fun x hx => by simp [e₁ x hx, e₂ x hx]⟩
    | smul a f₁ _ ih =>
      obtain ⟨g, hg, e⟩ := ih
      exact ⟨a • g, Submodule.smul_mem _ a hg, fun x hx => by simp [e x hx]⟩
  -- counting
  let S := {T : Finset (Fin n) // T.card ≤ B}
  let Ψ : (S → ZMod 3) → (G → ZMod 3) := fun c x => ∑ T, c T * chi T.1 x.1
  have hsurj : Function.Surjective Ψ := by
    intro g
    obtain ⟨g', hg', e⟩ := claim2 (fun x => if h : x ∈ G then g ⟨x, h⟩ else 0)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).1 hg'
    refine ⟨c, funext fun x => ?_⟩
    have h1 := e x.1 x.2
    rw [dif_pos x.2] at h1
    rw [h1, ← hc]
    simp [Ψ, Finset.sum_apply]
    rfl
  have hcard := Fintype.card_le_of_surjective Ψ hsurj
  rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_coe,
    Nat.pow_le_pow_iff_right (by norm_num)] at hcard
  simpa [S, Fintype.card_subtype] using hcard

/-- The number of subsets of `Fin n` of size `≤ B` is `∑_{i ≤ B} C(n, i)`. -/
lemma card_subsets_le (B : ℕ) :
    (univ.filter (fun T : Finset (Fin n) => T.card ≤ B)).card =
      ∑ i ∈ range (B + 1), n.choose i := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := range (B + 1))]
  · refine sum_congr rfl fun i hi => ?_
    have : (univ.filter (fun T : Finset (Fin n) => T.card ≤ B)).filter (fun T => T.card = i) =
        powersetCard i univ := by
      ext T
      simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]
      simp only [mem_range] at hi
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by omega, h⟩
    rw [this, card_powersetCard, card_univ, Fintype.card_fin]
  · intro T hT
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hT
    simp only [coe_range, Set.mem_Iio]
    omega

/-- **Smolensky's lemma**, binomial form: agreement with PARITY is at most
`∑_{i ≤ n/2 + D} C(n, i)`. -/
theorem smolensky_choose (P : MvPolynomial (Fin n) (ZMod 3)) (D : ℕ) (hP : P.totalDegree ≤ D) :
    (univ.filter (fun x : Fin n → Bool => eval01 P x = parityVal x)).card ≤
      ∑ i ∈ range (n / 2 + D + 1), n.choose i :=
  (smolensky P D hP).trans_eq (card_subsets_le _)

/-- Lower half of the binomial row: `2 · ∑_{i < n/2} C(n, i) ≤ 2ⁿ`. -/
lemma two_mul_sum_choose_lt_half (n : ℕ) : 2 * ∑ i ∈ range (n / 2), n.choose i ≤ 2 ^ n := by
  have hdisj : Disjoint (range (n / 2)) ((range (n / 2)).image (fun i => n - i)) := by
    rw [disjoint_left]
    intro a ha hb
    simp only [mem_image, mem_range] at ha hb
    obtain ⟨i, hi, rfl⟩ := hb
    omega
  have himg : ∑ i ∈ (range (n / 2)).image (fun i => n - i), n.choose i
      = ∑ i ∈ range (n / 2), n.choose i := by
    rw [sum_image]
    · refine sum_congr rfl fun i hi => ?_
      simp only [mem_range] at hi
      exact Nat.choose_symm (by omega)
    · intro a ha b hb h
      simp only [coe_range, Set.mem_Iio] at ha hb
      simp only at h
      omega
  have hsub : range (n / 2) ∪ (range (n / 2)).image (fun i => n - i) ⊆ range (n + 1) := by
    intro a ha
    simp only [mem_union, mem_image, mem_range] at ha ⊢
    omega
  calc 2 * ∑ i ∈ range (n / 2), n.choose i
      = ∑ i ∈ range (n / 2) ∪ (range (n / 2)).image (fun i => n - i), n.choose i := by
        rw [sum_union hdisj, himg]; ring
    _ ≤ ∑ i ∈ range (n + 1), n.choose i := sum_le_sum_of_subset hsub
    _ = 2 ^ n := Nat.sum_range_choose n

/-- Tail bound: `2 · ∑_{i ≤ n/2 + D} C(n, i) ≤ 2ⁿ + 2(D+1)·C(n, ⌊n/2⌋)`. -/
lemma two_mul_sum_choose_le (n D : ℕ) :
    2 * ∑ i ∈ range (n / 2 + D + 1), n.choose i ≤ 2 ^ n + 2 * ((D + 1) * n.choose (n / 2)) := by
  rw [← sum_range_add_sum_Ico _ (show n / 2 ≤ n / 2 + D + 1 by omega), mul_add]
  have h2 : ∑ i ∈ Ico (n / 2) (n / 2 + D + 1), n.choose i ≤ (D + 1) * n.choose (n / 2) := by
    have := sum_le_card_nsmul (Ico (n / 2) (n / 2 + D + 1)) (fun i => n.choose i)
      (n.choose (n / 2)) (fun i _ => Nat.choose_le_middle i n)
    rwa [Nat.card_Ico, smul_eq_mul, show n / 2 + D + 1 - n / 2 = D + 1 by omega] at this
  have h1 := two_mul_sum_choose_lt_half n
  omega

/-- **Smolensky's lemma**, quantitative form: the agreement set `G` satisfies
`2|G| ≤ 2ⁿ + 2(D+1)·C(n, ⌊n/2⌋)`, i.e. `|G| ≤ 2ⁿ⁻¹ + (D+1)·C(n, ⌊n/2⌋)`
(`= 2ⁿ (1/2 + O(D/√n))`). -/
theorem smolensky_tail (P : MvPolynomial (Fin n) (ZMod 3)) (D : ℕ) (hP : P.totalDegree ≤ D) :
    2 * (univ.filter (fun x : Fin n → Bool => eval01 P x = parityVal x)).card ≤
      2 ^ n + 2 * ((D + 1) * n.choose (n / 2)) :=
  (Nat.mul_le_mul_left 2 (smolensky_choose P D hP)).trans (two_mul_sum_choose_le n D)

end

end Pnp.AC0.Smolensky
