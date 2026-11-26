import Pnp.Algebrization.Extension

/-!
# Multiquadratic polynomials vanishing on few points (Aaronson–Wigderson)

Proof sketch (Aaronson–Wigderson):

* `boolDelta z = ∏ i, (if z i then X i else 1 - X i)` is the multilinear indicator of the
  Boolean point `z` on the cube (`eval_boolPt_boolDelta`).
* `combo g = ∑ z, C (g z) * boolDelta z` is the multilinear polynomial whose restriction to the
  cube is `g`.  Evaluating `combo g` on `Y` is a linear map `Φ : (cube → F) → (Y → F)`.
* `Bad` is the set of `z` with `g z = 0` for every `g ∈ ker Φ`.  Extending functions on `Bad`
  by zero and composing with `Φ` gives an injective linear map `(Bad → F) → (Y → F)`, so
  `|Bad| ≤ |Y|`.
* For `z ∉ Bad`, pick `g ∈ ker Φ` with `g z ≠ 0`; then `q = C (g z)⁻¹ * combo g * boolDelta z`
  vanishes on `Y`, is multiquadratic, and restricts to the indicator of `z`.
-/

namespace Pnp.Algebrize

open MvPolynomial

/-- The multilinear indicator polynomial of the Boolean point `z`. -/
noncomputable def boolDelta {F : Type*} [CommRing F] {n : ℕ} (z : Fin n → Bool) :
    MvPolynomial (Fin n) F :=
  ∏ i, (if z i then X i else 1 - X i)

theorem eval_boolPt_boolDelta {F : Type*} [CommRing F] [Nontrivial F] {n : ℕ}
    (z z' : Fin n → Bool) :
    eval (boolPt z') (boolDelta (F := F) z) = if z' = z then 1 else 0 := by
  classical
  unfold boolDelta
  rw [map_prod]
  have h : ∀ i, eval (boolPt z') (if z i then X i else 1 - X i : MvPolynomial (Fin n) F) =
      if z' i = z i then 1 else 0 := by
    intro i
    cases hz : z i <;> cases hz' : z' i <;> simp [boolPt, hz']
  simp_rw [h]
  rw [Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

theorem degreeOf_boolDelta_le {F : Type*} [CommRing F] {n : ℕ} (z : Fin n → Bool)
    (j : Fin n) : (boolDelta (F := F) z).degreeOf j ≤ 1 := by
  classical
  unfold boolDelta
  refine (degreeOf_prod_le j _ _).trans ?_
  have h : ∀ i, (if z i then X i else 1 - X i : MvPolynomial (Fin n) F).degreeOf j ≤
      if i = j then 1 else 0 := by
    intro i
    have hX : (X i : MvPolynomial (Fin n) F).degreeOf j ≤ if i = j then 1 else 0 := by
      split_ifs with hij
      · subst hij
        rw [degreeOf_def]
        exact (Multiset.count_le_of_le _ (degrees_X' i)).trans (by simp)
      · rw [degreeOf_def]
        have := Multiset.count_le_of_le j (degrees_X' (R := F) i)
        simpa [Multiset.count_singleton, Ne.symm hij] using this
    by_cases hz : z i
    · simpa [hz] using hX
    · simp only [hz, Bool.false_eq_true, if_false]
      refine (degreeOf_sub_le j _ _).trans ?_
      simpa using hX
  refine (Finset.sum_le_sum fun i _ => h i).trans ?_
  simp

/-- The multilinear polynomial whose restriction to the Boolean cube is `g`. -/
noncomputable def combo {F : Type*} [CommRing F] {n : ℕ} (g : (Fin n → Bool) → F) :
    MvPolynomial (Fin n) F :=
  ∑ z, C (g z) * boolDelta z

theorem eval_boolPt_combo {F : Type*} [CommRing F] [Nontrivial F] {n : ℕ}
    (g : (Fin n → Bool) → F) (w : Fin n → Bool) : eval (boolPt w) (combo g) = g w := by
  classical
  unfold combo
  simp [eval_boolPt_boolDelta]

theorem degreeOf_combo_le {F : Type*} [CommRing F] {n : ℕ} (g : (Fin n → Bool) → F)
    (j : Fin n) : (combo g).degreeOf j ≤ 1 := by
  unfold combo
  refine (degreeOf_sum_le j _ _).trans ?_
  refine Finset.sup_le fun z _ => ?_
  exact (degreeOf_C_mul_le _ _ _).trans (degreeOf_boolDelta_le z j)

/-- Evaluation of `combo g` on the points of `Y`, as a linear map. -/
noncomputable def comboEval {F : Type*} [Field F] (n : ℕ) (Y : Finset (Fin n → F)) :
    ((Fin n → Bool) → F) →ₗ[F] (Y → F) where
  toFun g y := eval y.1 (combo g)
  map_add' g h := by
    funext y
    simp [combo, add_mul, Finset.sum_add_distrib]
  map_smul' c g := by
    funext y
    simp [combo, Finset.mul_sum, mul_assoc]

/-- For any set `Y` of `t` points of `F^n`, all but at most `t` Boolean points `z` admit a
multiquadratic polynomial that vanishes on `Y` and restricts to the indicator of `z` on
the Boolean cube. -/
theorem exists_vanishing_indicator {F : Type*} [Field F] (n : ℕ) (Y : Finset (Fin n → F)) :
    ∃ Bad : Finset (Fin n → Bool), Bad.card ≤ Y.card ∧ ∀ z ∉ Bad,
      ∃ q : MvPolynomial (Fin n) F, (∀ i, q.degreeOf i ≤ 2) ∧ (∀ y ∈ Y, eval y q = 0) ∧
        ∀ z' : Fin n → Bool, eval (boolPt z') q = if z' = z then 1 else 0 := by
  classical
  set Φ := comboEval n Y
  let Bad : Finset (Fin n → Bool) :=
    Finset.univ.filter fun z => ∀ g, Φ g = 0 → g z = 0
  refine ⟨Bad, ?_, ?_⟩
  · -- extension by zero from `Bad`, composed with `Φ`, is injective
    let E : (Bad → F) →ₗ[F] ((Fin n → Bool) → F) :=
      { toFun := fun f z => if h : z ∈ Bad then f ⟨z, h⟩ else 0
        map_add' := fun f g => by
          funext z
          by_cases h : z ∈ Bad <;> simp [h]
        map_smul' := fun c f => by
          funext z
          by_cases h : z ∈ Bad <;> simp [h] }
    have hinj : Function.Injective (Φ ∘ₗ E) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro f hf
      funext ⟨z, hz⟩
      have hmem := (Finset.mem_filter.mp hz).2 (E f) hf
      simpa [E, hz] using hmem
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_coe] at this
    exact this
  · intro z hz
    have hz' : ¬ ∀ g, Φ g = 0 → g z = 0 := by
      intro h
      exact hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    push Not at hz'
    obtain ⟨g, hg, hgz⟩ := hz'
    refine ⟨C (g z)⁻¹ * combo g * boolDelta z, ?_, ?_, ?_⟩
    · intro i
      refine (degreeOf_mul_le i _ _).trans ?_
      have h1 := (degreeOf_C_mul_le (combo g) i (g z)⁻¹).trans (degreeOf_combo_le g i)
      have h2 := degreeOf_boolDelta_le (F := F) z i
      omega
    · intro y hy
      have : eval y (combo g) = 0 := congrFun hg ⟨y, hy⟩
      simp [this]
    · intro z'
      rw [map_mul, map_mul, eval_boolPt_combo, eval_boolPt_boolDelta, eval_C]
      split_ifs with h
      · subst h
        rw [mul_one]; exact inv_mul_cancel₀ hgz
      · simp

end Pnp.Algebrize
