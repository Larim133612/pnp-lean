import Pnp.AC0.Formula

/-!
# Razborov–Smolensky approximation of AC⁰ formulas by `𝔽₃` polynomials (M4a)

For every `ℓ` and every AC⁰ formula `F` there is a polynomial `P` over `ZMod 3` of total
degree `≤ (2ℓ)^{depth F}` that agrees with `F` on all 0/1 points outside a set `E`
with `|E| · 2^ℓ ≤ size F · 2ⁿ` (`ac0_approx`).

OR gate with child approximants `p₁ … p_t`: for a choice `S : Fin ℓ → Finset (Fin t)`,
`q = 1 - ∏_j (1 - (∑_{i ∈ S j} p_i)²)`. On 0/1 values, `q` equals the OR unless some
child is `1` while all `ℓ` sums vanish. For a fixed nonzero 0/1 vector, at most half of
all `S ⊆ [t]` have vanishing sum (`card_sum_eq_zero_mul_two_le`); double counting over
inputs and choices yields a good choice (`or_step`). AND is handled via De Morgan.
No probability is used.
-/

namespace Pnp.AC0

open Finset MvPolynomial

variable {n : ℕ}

/-- Evaluation of a polynomial at the 0/1 point corresponding to `x`. -/
noncomputable def eval01 (P : MvPolynomial (Fin n) (ZMod 3)) (x : Fin n → Bool) : ZMod 3 :=
  MvPolynomial.eval (fun i => if x i then 1 else 0) P

/-- The 0/1 indicator of a Boolean in `𝔽₃`. -/
def ind (b : Bool) : ZMod 3 := if b then 1 else 0

/-- **Halving lemma.** If `v i₀ ≠ 0`, at most half of the subsets `S` of `Fin t` satisfy
`∑_{i ∈ S} v i = 0`: toggling `i₀` maps them injectively to subsets with nonzero sum. -/
lemma card_sum_eq_zero_mul_two_le {t : ℕ} (v : Fin t → ZMod 3) {i₀ : Fin t}
    (h₀ : v i₀ ≠ 0) :
    (univ.filter fun S : Finset (Fin t) => ∑ i ∈ S, v i = 0).card * 2 ≤ 2 ^ t := by
  set A := univ.filter fun S : Finset (Fin t) => ∑ i ∈ S, v i = 0
  let f : Finset (Fin t) → Finset (Fin t) := fun S => if i₀ ∈ S then S.erase i₀ else insert i₀ S
  have hsum : ∀ S, ∑ i ∈ f S, v i ≠ ∑ i ∈ S, v i := by
    intro S
    by_cases hS : i₀ ∈ S
    · simp only [f, hS, if_true]
      rw [← Finset.add_sum_erase S v hS]
      intro h
      apply h₀
      linear_combination -h
    · simp only [f, hS, if_false]
      rw [Finset.sum_insert hS]
      intro h
      apply h₀
      linear_combination h
  have hmaps : Set.MapsTo f ↑A ↑(Aᶜ) := by
    intro S hS
    rw [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_compl]
    simp only [A, mem_filter, mem_univ, true_and] at hS ⊢
    intro h
    exact hsum S (h.trans hS.symm)
  have hinj : Set.InjOn f A := by
    intro S _ T _ hST
    simp only [f] at hST
    by_cases hS : i₀ ∈ S <;> by_cases hT : i₀ ∈ T <;> simp only [hS, hT, if_true, if_false] at hST
    · rw [← Finset.insert_erase hS, ← Finset.insert_erase hT, hST]
    · exact absurd (hST ▸ Finset.mem_insert_self i₀ T) (Finset.notMem_erase i₀ S)
    · exact absurd (hST ▸ Finset.mem_insert_self i₀ S) (Finset.notMem_erase i₀ T)
    · rw [← Finset.erase_insert hS, ← Finset.erase_insert hT, hST]
  have h1 := Finset.card_le_card_of_injOn f hmaps hinj
  have h2 : A.card + Aᶜ.card = 2 ^ t := by
    rw [Finset.card_add_card_compl, Fintype.card_finset, Fintype.card_fin]
  omega

/-- Tuples of `ℓ` subsets all with vanishing sum: at most `(2^{t-1})^ℓ`, stated
multiplicatively. -/
lemma card_tuples_mul_le {t : ℕ} (ℓ : ℕ) (v : Fin t → ZMod 3) {i₀ : Fin t}
    (h₀ : v i₀ ≠ 0) :
    (univ.filter fun c : Fin ℓ → Finset (Fin t) => ∀ j, ∑ i ∈ c j, v i = 0).card * 2 ^ ℓ
      ≤ (2 ^ t) ^ ℓ := by
  have hpi : (univ.filter fun c : Fin ℓ → Finset (Fin t) => ∀ j, ∑ i ∈ c j, v i = 0) =
      Fintype.piFinset fun _ => univ.filter fun S : Finset (Fin t) => ∑ i ∈ S, v i = 0 := by
    ext c; simp [Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← mul_pow]
  exact Nat.pow_le_pow_left (card_sum_eq_zero_mul_two_le v h₀) ℓ

lemma sq_eq_one_of_ne_zero (s : ZMod 3) (hs : s ≠ 0) : s ^ 2 = 1 := by
  revert s; decide

/-- The OR approximant for a choice `c` of `ℓ` subsets. -/
noncomputable def orPoly {t ℓ : ℕ} (p : Fin t → MvPolynomial (Fin n) (ZMod 3))
    (c : Fin ℓ → Finset (Fin t)) : MvPolynomial (Fin n) (ZMod 3) :=
  1 - ∏ j, (1 - (∑ i ∈ c j, p i) ^ 2)

lemma totalDegree_orPoly {t ℓ : ℕ} (p : Fin t → MvPolynomial (Fin n) (ZMod 3))
    (c : Fin ℓ → Finset (Fin t)) {D : ℕ} (hD : ∀ i, (p i).totalDegree ≤ D) :
    (orPoly p c).totalDegree ≤ 2 * ℓ * D := by
  unfold orPoly
  refine (totalDegree_sub _ _).trans ?_
  rw [totalDegree_one, Nat.zero_max]
  refine (totalDegree_finsetProd _ _).trans ?_
  have : ∀ j : Fin ℓ, (1 - (∑ i ∈ c j, p i) ^ 2).totalDegree ≤ 2 * D := by
    intro j
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_one, Nat.zero_max]
    refine (totalDegree_pow _ _).trans ?_
    refine Nat.mul_le_mul_left 2 ?_
    refine (totalDegree_finsetSum _ _).trans ?_
    exact Finset.sup_le fun i _ => hD i
  refine (Finset.sum_le_sum fun j _ => this j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  nlinarith

/-- A choice `c` is bad at `x` if some child is true but all `ℓ` sums vanish. -/
def Bad {t ℓ : ℕ} (g : Fin t → (Fin n → Bool) → Bool) (c : Fin ℓ → Finset (Fin t))
    (x : Fin n → Bool) : Prop :=
  (∃ i, g i x = true) ∧ ∀ j, ∑ i ∈ c j, ind (g i x) = 0

lemma eval01_orPoly {t ℓ : ℕ} (p : Fin t → MvPolynomial (Fin n) (ZMod 3))
    (g : Fin t → (Fin n → Bool) → Bool) (c : Fin ℓ → Finset (Fin t)) (x : Fin n → Bool)
    (hp : ∀ i, eval01 (p i) x = ind (g i x)) (hx : ¬ Bad g c x) :
    eval01 (orPoly p c) x = ind (decide (∃ i, g i x = true)) := by
  have hev : eval01 (orPoly p c) x = 1 - ∏ j, (1 - (∑ i ∈ c j, ind (g i x)) ^ 2) := by
    simp only [eval01, orPoly, map_sub, map_one, map_prod, map_pow, map_sum] at hp ⊢
    simp only [hp]
  rw [hev]
  by_cases hex : ∃ i, g i x = true
  · have : ∃ j, ∑ i ∈ c j, ind (g i x) ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hx ⟨hex, hne⟩
    obtain ⟨j, hj⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [sq_eq_one_of_ne_zero _ hj, sub_self]),
      decide_eq_true hex]
    simp [ind]
  · push Not at hex
    have h0 : ∀ i, ind (g i x) = 0 := fun i => by simp [ind, hex i]
    simp [ind, hex]

/-- **OR step.** Given child approximants of degree `≤ D`, some choice yields an OR
approximant of degree `≤ 2ℓD` that is correct wherever all children are, except on a set
`E` with `|E| · 2^ℓ ≤ 2ⁿ`. -/
theorem or_step {t : ℕ} (ℓ : ℕ) (p : Fin t → MvPolynomial (Fin n) (ZMod 3))
    (g : Fin t → (Fin n → Bool) → Bool) {D : ℕ} (hD : ∀ i, (p i).totalDegree ≤ D) :
    ∃ (q : MvPolynomial (Fin n) (ZMod 3)) (E : Finset (Fin n → Bool)),
      q.totalDegree ≤ 2 * ℓ * D ∧ E.card * 2 ^ ℓ ≤ 2 ^ n ∧
      ∀ x ∉ E, (∀ i, eval01 (p i) x = ind (g i x)) →
        eval01 q x = ind (decide (∃ i, g i x = true)) := by
  classical
  -- double counting over inputs `x` and choices `c`
  let C : Finset (Fin ℓ → Finset (Fin t)) := univ
  have hC : C.card = (2 ^ t) ^ ℓ := by
    simp only [C, Finset.card_univ, Fintype.card_fun, Fintype.card_finset, Fintype.card_fin]
  have hrow : ∀ x : Fin n → Bool, (C.filter fun c => Bad g c x).card * 2 ^ ℓ ≤ C.card := by
    intro x
    by_cases hex : ∃ i, g i x = true
    · obtain ⟨i₀, hi₀⟩ := hex
      have h₀ : ind (g i₀ x) ≠ 0 := by simp [ind, hi₀]
      have hsub : (C.filter fun c => Bad g c x) ⊆
          univ.filter fun c : Fin ℓ → Finset (Fin t) => ∀ j, ∑ i ∈ c j, ind (g i x) = 0 := by
        intro c hc
        simp only [C, mem_filter, mem_univ, true_and, Bad] at hc ⊢
        exact hc.2
      rw [hC]
      exact (Nat.mul_le_mul_right _ (card_le_card hsub)).trans
        (card_tuples_mul_le ℓ (fun i => ind (g i x)) h₀)
    · have : (C.filter fun c => Bad g c x) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro c _ hc
        exact hex hc.1
      simp [this]
  have hsum : ∑ c ∈ C, (univ.filter fun x => Bad g c x).card * 2 ^ ℓ ≤
      ∑ c ∈ C, 2 ^ n := by
    rw [← Finset.sum_mul]
    have hcomm : ∑ c ∈ C, (univ.filter fun x => Bad g c x).card =
        ∑ x : Fin n → Bool, (C.filter fun c => Bad g c x).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hcomm, Finset.sum_mul, Finset.sum_const, smul_eq_mul]
    calc ∑ x : Fin n → Bool, (C.filter fun c => Bad g c x).card * 2 ^ ℓ
        ≤ ∑ _x : Fin n → Bool, C.card := Finset.sum_le_sum fun x _ => hrow x
      _ = C.card * 2 ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, smul_eq_mul, mul_comm]
  have hne : C.Nonempty := ⟨fun _ => ∅, mem_univ _⟩
  obtain ⟨c, -, hc⟩ := Finset.exists_le_of_sum_le hne hsum
  refine ⟨orPoly p c, univ.filter fun x => Bad g c x, totalDegree_orPoly p c hD, hc, ?_⟩
  intro x hx hp
  exact eval01_orPoly p g c x hp (by simpa using hx)

lemma totalDegree_one_sub_le (P : MvPolynomial (Fin n) (ZMod 3)) :
    (1 - P).totalDegree ≤ P.totalDegree := by
  refine (totalDegree_sub _ _).trans ?_
  rw [totalDegree_one, Nat.zero_max]

lemma eval01_one_sub (P : MvPolynomial (Fin n) (ZMod 3)) (x : Fin n → Bool) :
    eval01 (1 - P) x = 1 - eval01 P x := by
  simp [eval01]

lemma one_sub_ind (b : Bool) : 1 - ind b = ind (!b) := by
  cases b <;> simp [ind]

/-- **Razborov–Smolensky approximation.** Every AC⁰ formula `F` agrees with a polynomial
over `𝔽₃` of total degree `≤ (2ℓ)^{depth F}` on all 0/1 inputs outside a set `E` with
`|E| · 2^ℓ ≤ size F · 2ⁿ` (`size` = number of gates). -/
theorem ac0_approx (ℓ : ℕ) (F : Formula n) :
    ∃ (P : MvPolynomial (Fin n) (ZMod 3)) (E : Finset (Fin n → Bool)),
      P.totalDegree ≤ (2 * ℓ) ^ F.depth ∧ E.card * 2 ^ ℓ ≤ F.size * 2 ^ n ∧
      ∀ x ∉ E, eval01 P x = if F.eval x then 1 else 0 := by
  classical
  -- degree bookkeeping shared by both gate types
  have hdeg : ∀ {t : ℕ} (f : Fin t → Formula n) (P : Fin t → MvPolynomial (Fin n) (ZMod 3)),
      (∀ i, (P i).totalDegree ≤ (2 * ℓ) ^ (f i).depth) →
      (∀ q : MvPolynomial (Fin n) (ZMod 3),
        q.totalDegree ≤ 2 * ℓ * (univ.sup fun i => (P i).totalDegree) →
        q.totalDegree ≤ (2 * ℓ) ^ ((univ.sup fun i => (f i).depth) + 1)) := by
    intro t f P hP q hq
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · simp at hq; omega
    · refine hq.trans ?_
      rw [pow_succ']
      refine Nat.mul_le_mul_left _ (Finset.sup_le fun i _ => (hP i).trans ?_)
      exact Nat.pow_le_pow_right (by omega) (Finset.le_sup (f := fun i => (f i).depth)
        (mem_univ i))
  -- error bookkeeping shared by both gate types
  have herr : ∀ {t : ℕ} (f : Fin t → Formula n) (E : Fin t → Finset (Fin n → Bool))
      (E' : Finset (Fin n → Bool)), (∀ i, (E i).card * 2 ^ ℓ ≤ (f i).size * 2 ^ n) →
      E'.card * 2 ^ ℓ ≤ 2 ^ n →
      ((univ.biUnion E) ∪ E').card * 2 ^ ℓ ≤ ((∑ i, (f i).size) + 1) * 2 ^ n := by
    intro t f E E' hE hE'
    calc ((univ.biUnion E) ∪ E').card * 2 ^ ℓ
        ≤ ((∑ i, (E i).card) + E'.card) * 2 ^ ℓ :=
          Nat.mul_le_mul_right _ ((card_union_le _ _).trans
            (Nat.add_le_add_right card_biUnion_le _))
      _ = (∑ i, (E i).card * 2 ^ ℓ) + E'.card * 2 ^ ℓ := by rw [add_mul, Finset.sum_mul]
      _ ≤ (∑ i, (f i).size * 2 ^ n) + 2 ^ n :=
          Nat.add_le_add (Finset.sum_le_sum fun i _ => hE i) hE'
      _ = ((∑ i, (f i).size) + 1) * 2 ^ n := by rw [add_mul, Finset.sum_mul, one_mul]
  induction F with
  | lit i c =>
    refine ⟨if c then X i else 1 - X i, ∅, ?_, by simp [Formula.size], ?_⟩
    · simp only [Formula.depth, pow_zero]
      split
      · exact (totalDegree_X _).le
      · exact (totalDegree_one_sub_le _).trans (totalDegree_X _).le
    · intro x _
      cases c <;> cases hx : x i <;> simp [eval01, hx]
  | or t f ih =>
    choose P E hPdeg hE hP using ih
    obtain ⟨q, E', hq, hE', hq'⟩ := or_step ℓ P (fun i => (f i).eval)
      (D := univ.sup fun i => (P i).totalDegree) (fun i => Finset.le_sup (f := fun i => (P i).totalDegree) (mem_univ i))
    refine ⟨q, (univ.biUnion E) ∪ E', hdeg f P hPdeg q hq, herr f E E' hE hE', ?_⟩
    intro x hx
    simp only [mem_union, mem_biUnion, mem_univ, true_and, not_or, not_exists] at hx
    have := hq' x hx.2 fun i => by rw [hP i x (hx.1 i)]; rfl
    rw [this, Formula.eval_or]; rfl
  | and t f ih =>
    choose P E hPdeg hE hP using ih
    obtain ⟨q, E', hq, hE', hq'⟩ := or_step ℓ (fun i => 1 - P i) (fun i x => !(f i).eval x)
      (D := univ.sup fun i => (P i).totalDegree)
      (fun i => (totalDegree_one_sub_le _).trans (Finset.le_sup (f := fun i => (P i).totalDegree)
        (mem_univ i)))
    refine ⟨1 - q, (univ.biUnion E) ∪ E',
      hdeg f P hPdeg _ ((totalDegree_one_sub_le q).trans hq), herr f E E' hE hE', ?_⟩
    intro x hx
    simp only [mem_union, mem_biUnion, mem_univ, true_and, not_or, not_exists] at hx
    have := hq' x hx.2 fun i => by
      rw [eval01_one_sub, hP i x (hx.1 i), ← one_sub_ind]; rfl
    rw [eval01_one_sub, this, one_sub_ind, Formula.eval_and]
    by_cases h : ∀ i, (f i).eval x = true
    · simp [h, ind]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have : ∃ i, (!(f i).eval x) = true := ⟨i, by simpa using hi⟩
      simp [ind, show ¬ ∀ i, (f i).eval x = true from fun h' => hi (h' i)]

end Pnp.AC0
