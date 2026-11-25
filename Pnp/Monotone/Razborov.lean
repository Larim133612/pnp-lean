import Pnp.Monotone.Pluck

/-!
# Razborov's theorem via Alon–Boppana approximators (M3c, M3d)

Parameters: `m` vertices, clique size `k`, maximal set size `ℓ ≥ 2`, `p ≥ 2` petals, and a
size bound `L ≥ ℓ! (p-1)^ℓ` for approximators (Erdős–Rado).

* `Good L ℓ A`: `A` has at most `L` members, each with at most `ℓ` elements, each empty or
  of size `≥ 2` (`SizeOK`).
* `abAop`: OR is `pluck (a ∪ c)`, AND is `pluck {X ∪ Y | X ∈ a, Y ∈ c, |X ∪ Y| ≤ ℓ}`.

Main results:
* `abAop_posErr` / `abAop_negErr` (M3c): each approximate gate makes at most
  `L² · C(m-ℓ-1, k-ℓ-1)` positive errors and at most `L² · (ℓ²)^p · (k-1)^(m-p)`
  negative errors.
* `razborov_alon_boppana` (M3d): every monotone circuit with `s` gates computing
  `CLIQUE(m,k)` satisfies
  `C(m,k) ≤ s · L² C(m-ℓ-1, k-ℓ-1)` or
  `(k-1)^m - ℓ² (k-1)^(m-1) ≤ s · L² (ℓ²)^p (k-1)^(m-p)`.
-/

namespace Pnp.Monotone

open Finset

variable {m : ℕ}

/-- The invariant of Alon–Boppana approximators. -/
def Good (L ℓ : ℕ) (A : Finset (Finset (Fin m))) : Prop :=
  A.card ≤ L ∧ ∀ X ∈ A, SizeOK ℓ X

/-- The exact AND of two approximators, keeping only sets of size `≤ ℓ`. -/
def andPre (ℓ : ℕ) (a c : Finset (Finset (Fin m))) : Finset (Finset (Fin m)) :=
  ((a ×ˢ c).image fun XY => XY.1 ∪ XY.2).filter fun X => X.card ≤ ℓ

/-- The Alon–Boppana approximate gates: `true` = AND, `false` = OR. -/
noncomputable def abAop (L ℓ p : ℕ) :
    Bool → Finset (Finset (Fin m)) → Finset (Finset (Fin m)) → Finset (Finset (Fin m))
  | true, a, c => pluck L p (andPre ℓ a c)
  | false, a, c => pluck L p (a ∪ c)

/-! ## Basic facts -/

lemma sizeOK_union {ℓ : ℕ} {X Y : Finset (Fin m)} (hX : SizeOK ℓ X) (hY : SizeOK ℓ Y)
    (h : (X ∪ Y).card ≤ ℓ) : SizeOK ℓ (X ∪ Y) := by
  refine ⟨h, ?_⟩
  rcases hX.2 with hX0 | hX2
  · rw [hX0, empty_union]; exact hY.2
  · exact Or.inr (hX2.trans (card_le_card subset_union_left))

lemma sizeOK_andPre {ℓ : ℕ} {a c : Finset (Finset (Fin m))} (ha : ∀ X ∈ a, SizeOK ℓ X)
    (hc : ∀ X ∈ c, SizeOK ℓ X) : ∀ Z ∈ andPre ℓ a c, SizeOK ℓ Z := by
  intro Z hZ
  simp only [andPre, mem_filter, mem_image, mem_product] at hZ
  obtain ⟨⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩, hcard⟩ := hZ
  exact sizeOK_union (ha X hX) (hc Y hY) hcard

lemma card_andPre_le (ℓ : ℕ) (a c : Finset (Finset (Fin m))) :
    (andPre ℓ a c).card ≤ a.card * c.card :=
  (card_filter_le _ _).trans (card_image_le.trans (card_product a c).le)

/-- `L ≥ 2` when `ℓ ≥ 2`, `p ≥ 2`. -/
lemma two_le_L {L ℓ p : ℕ} (hℓ : 2 ≤ ℓ) (hp : 2 ≤ p) (hL : ℓ.factorial * (p - 1) ^ ℓ ≤ L) :
    2 ≤ L := by
  have h1 : 2 ≤ ℓ.factorial := (Nat.factorial_le hℓ).trans' (by decide)
  have h2 : 1 ≤ (p - 1) ^ ℓ := Nat.one_le_pow _ _ (by omega)
  nlinarith

lemma good_abAop {L ℓ p : ℕ} (hp : 2 ≤ p) (hL : ℓ.factorial * (p - 1) ^ ℓ ≤ L)
    (o : Bool) {a c : Finset (Finset (Fin m))} (ha : Good L ℓ a) (hc : Good L ℓ c) :
    Good L ℓ (abAop L ℓ p o a c) := by
  have key : ∀ B : Finset (Finset (Fin m)), (∀ X ∈ B, SizeOK ℓ X) → Good L ℓ (pluck L p B) :=
    fun B hB => ⟨card_pluck_le hp hL hB, sizeOK_pluckN (by omega) _ B hB⟩
  cases o
  · refine key _ fun X hX => ?_
    rcases mem_union.1 hX with h | h
    · exact ha.2 X h
    · exact hc.2 X h
  · exact key _ (sizeOK_andPre ha.2 hc.2)

lemma good_inputApprox {L ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hL : 1 ≤ L) {N : ℕ}
    {lab : Fin N → Fin m × Fin m} (hlab : OffDiag lab) (i : Fin N) :
    Good L ℓ (inputApprox lab i) := by
  refine ⟨by simpa [inputApprox] using hL, ?_⟩
  intro X hX
  simp only [inputApprox, mem_singleton] at hX
  have h2 : X.card = 2 := by rw [hX]; exact card_pair (hlab i)
  exact ⟨by omega, Or.inr h2.ge⟩

/-! ## Cliques on positive tests -/

lemma isClique_cliqueGraph_of_subset {K X : Finset (Fin m)} (h : X ⊆ K) :
    (cliqueGraph K).IsClique (X : Set (Fin m)) :=
  fun _ hu _ hv huv => ⟨huv, h hu, h hv⟩

lemma subset_of_isClique_cliqueGraph {ℓ : ℕ} {K X : Finset (Fin m)} (hX : SizeOK ℓ X)
    (h : (cliqueGraph K).IsClique (X : Set (Fin m))) : X ⊆ K := by
  rcases hX.2 with h0 | h2
  · rw [h0]; exact empty_subset _
  · exact (isClique_cliqueGraph_iff K X h2).1 h

/-- At most `C(m - |Z|, k - |Z|)` positive tests contain `Z`. -/
lemma card_posTests_supset_le (k : ℕ) (Z : Finset (Fin m)) :
    ((posTests m k).filter fun K => Z ⊆ K).card ≤ (m - Z.card).choose (k - Z.card) := by
  classical
  have h := card_le_card_of_injOn (fun K => K \ Z)
    (s := (posTests m k).filter fun K => Z ⊆ K) (t := powersetCard (k - Z.card) Zᶜ)
    (by
      intro K hK
      simp only [coe_filter, mem_posTests, Set.mem_setOf_eq] at hK
      rw [mem_coe, mem_powersetCard]
      refine ⟨fun x hx => mem_compl.2 (mem_sdiff.1 hx).2, ?_⟩
      rw [card_sdiff_of_subset hK.2, hK.1])
    (by
      intro K hK K' hK' hKK
      simp only [coe_filter, Set.mem_setOf_eq] at hK hK'
      simp only at hKK
      rw [← sdiff_union_of_subset hK.2, ← sdiff_union_of_subset hK'.2, hKK])
  rwa [card_powersetCard, card_compl, Fintype.card_fin] at h

/-- At most `C(m-ℓ-1, k-ℓ-1)` positive tests contain a given set of more than `ℓ`
vertices. -/
lemma card_posTests_supset_le' (k ℓ : ℕ) (Z : Finset (Fin m)) (hZ : ℓ < Z.card) :
    ((posTests m k).filter fun K => Z ⊆ K).card ≤ (m - (ℓ + 1)).choose (k - (ℓ + 1)) := by
  obtain ⟨Z', hZ'Z, hZ'⟩ := exists_subset_card_eq (s := Z) (n := ℓ + 1) hZ
  refine le_trans (card_le_card ?_) (hZ' ▸ card_posTests_supset_le k Z')
  intro K hK
  simp only [mem_filter] at hK ⊢
  exact ⟨hK.1, hZ'Z.trans hK.2⟩

/-! ## Per-gate error bounds (M3c) -/

/-- **Positive errors of an approximate gate.** -/
theorem abAop_posErr {L ℓ p k : ℕ} (o : Bool) {a c : Finset (Finset (Fin m))}
    (ha : Good L ℓ a) (hc : Good L ℓ c) :
    ((posTests m k).filter fun K =>
        gateOp o (approxSem a (cliqueGraph K)) (approxSem c (cliqueGraph K)) = true ∧
          approxSem (abAop L ℓ p o a c) (cliqueGraph K) = false).card ≤
      L ^ 2 * (m - (ℓ + 1)).choose (k - (ℓ + 1)) := by
  classical
  cases o
  · -- OR: no positive errors at all
    refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    rw [card_eq_zero]
    refine filter_false_of_mem fun K _ h => ?_
    rw [gateOp_false, ← approxSem_union] at h
    have := approxSem_pluck L p h.1
    simp only [abAop] at h
    rw [this] at h
    exact Bool.noConfusion h.2
  · -- AND: errors only on `K` containing some large `X ∪ Y`
    set W := (a ×ˢ c).filter fun XY => ℓ < (XY.1 ∪ XY.2).card
    have hsub : ((posTests m k).filter fun K =>
        gateOp true (approxSem a (cliqueGraph K)) (approxSem c (cliqueGraph K)) = true ∧
          approxSem (abAop L ℓ p true a c) (cliqueGraph K) = false) ⊆
        W.biUnion fun XY => (posTests m k).filter fun K => XY.1 ∪ XY.2 ⊆ K := by
      intro K hK
      simp only [mem_filter, gateOp_true, Bool.and_eq_true] at hK
      obtain ⟨hKP, ⟨hA, hC⟩, hpl⟩ := hK
      rw [approxSem_eq_true] at hA hC
      obtain ⟨X, hX, hXK⟩ := hA
      obtain ⟨Y, hY, hYK⟩ := hC
      have hXK' := subset_of_isClique_cliqueGraph (ha.2 X hX) hXK
      have hYK' := subset_of_isClique_cliqueGraph (hc.2 Y hY) hYK
      have hU : X ∪ Y ⊆ K := union_subset hXK' hYK'
      have hlarge : ℓ < (X ∪ Y).card := by
        by_contra hle
        push Not at hle
        have hpre : approxSem (andPre ℓ a c) (cliqueGraph K) = true := by
          rw [approxSem_eq_true]
          refine ⟨X ∪ Y, ?_, isClique_cliqueGraph_of_subset hU⟩
          simp only [andPre, mem_filter, mem_image, mem_product]
          exact ⟨⟨(X, Y), ⟨hX, hY⟩, rfl⟩, hle⟩
        have := approxSem_pluck L p hpre
        simp only [abAop] at hpl
        rw [this] at hpl
        exact Bool.noConfusion hpl
      rw [mem_biUnion]
      exact ⟨(X, Y), mem_filter.2 ⟨mem_product.2 ⟨hX, hY⟩, hlarge⟩, mem_filter.2 ⟨hKP, hU⟩⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    have hb : ∀ XY ∈ W, ((posTests m k).filter fun K => XY.1 ∪ XY.2 ⊆ K).card ≤
        (m - (ℓ + 1)).choose (k - (ℓ + 1)) :=
      fun XY hXY => card_posTests_supset_le' k ℓ _ (mem_filter.1 hXY).2
    refine (sum_le_sum hb).trans ?_
    rw [sum_const, smul_eq_mul]
    apply Nat.mul_le_mul_right
    calc W.card ≤ (a ×ˢ c).card := card_filter_le _ _
      _ = a.card * c.card := card_product a c
      _ ≤ L * L := Nat.mul_le_mul ha.1 hc.1
      _ = L ^ 2 := (sq L).symm

/-- **Negative errors of an approximate gate.** -/
theorem abAop_negErr {L ℓ p k : ℕ} (hℓ : 2 ≤ ℓ) (hp : 2 ≤ p)
    (hL : ℓ.factorial * (p - 1) ^ ℓ ≤ L) (o : Bool) {a c : Finset (Finset (Fin m))}
    (ha : Good L ℓ a) (hc : Good L ℓ c) :
    ((univ : Finset (Fin m → Fin (k - 1))).filter fun f =>
        gateOp o (approxSem a (colorGraph f)) (approxSem c (colorGraph f)) = false ∧
          approxSem (abAop L ℓ p o a c) (colorGraph f) = true).card ≤
      L ^ 2 * ((ℓ ^ 2) ^ p * (k - 1) ^ (m - p)) := by
  classical
  have hL2 := two_le_L hℓ hp hL
  -- the general pattern: errors lie in the plucking errors of the pre-plucked family `B`
  have gen : ∀ B : Finset (Finset (Fin m)), (∀ X ∈ B, SizeOK ℓ X) → B.card ≤ L ^ 2 →
      ∀ (P : (Fin m → Fin (k - 1)) → Prop) [DecidablePred P],
      (∀ f, P f → approxSem B (colorGraph f) = false) →
      ((univ : Finset (Fin m → Fin (k - 1))).filter fun f =>
        P f ∧ approxSem (pluck L p B) (colorGraph f) = true).card ≤
        L ^ 2 * ((ℓ ^ 2) ^ p * (k - 1) ^ (m - p)) := by
    intro B hB hBc P _ hPB
    refine le_trans (card_le_card ?_)
      ((card_negErr_pluck (k - 1) L p ℓ (by omega) hB).trans (Nat.mul_le_mul_right _ hBc))
    intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    simp only [negErr, mem_filter, mem_univ, true_and]
    exact ⟨hf.2, hPB f hf.1⟩
  cases o
  · refine gen (a ∪ c) (fun X hX => ?_) ?_ _ (fun f h => ?_)
    · rcases mem_union.1 hX with h | h
      · exact ha.2 X h
      · exact hc.2 X h
    · calc (a ∪ c).card ≤ a.card + c.card := card_union_le _ _
        _ ≤ L + L := Nat.add_le_add ha.1 hc.1
        _ ≤ L ^ 2 := by nlinarith
    · rw [approxSem_union]; exact h
  · refine gen (andPre ℓ a c) (sizeOK_andPre ha.2 hc.2) ?_ _ (fun f h => ?_)
    · calc (andPre ℓ a c).card ≤ a.card * c.card := card_andPre_le ℓ a c
        _ ≤ L * L := Nat.mul_le_mul ha.1 hc.1
        _ = L ^ 2 := (sq L).symm
    · rw [gateOp_true] at h
      cases hB : approxSem (andPre ℓ a c) (colorGraph f)
      · rfl
      · exfalso
        rw [approxSem_eq_true] at hB
        obtain ⟨Z, hZ, hZf⟩ := hB
        simp only [andPre, mem_filter, mem_image, mem_product] at hZ
        obtain ⟨⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩, -⟩ := hZ
        have h1 : approxSem a (colorGraph f) = true :=
          (approxSem_eq_true _ _).2 ⟨X, hX, hZf.subset (coe_subset.2 subset_union_left)⟩
        have h2 : approxSem c (colorGraph f) = true :=
          (approxSem_eq_true _ _).2 ⟨Y, hY, hZf.subset (coe_subset.2 subset_union_right)⟩
        rw [h1, h2] at h
        exact Bool.noConfusion h

/-! ## The lower bound (M3d) -/

/-- **Razborov's theorem, Alon–Boppana form (general `L`).** -/
theorem razborov_alon_boppana_gen {N s k ℓ p L : ℕ} (hk : 1 ≤ k) (hℓ : 2 ≤ ℓ) (hp : 2 ≤ p)
    (hL : ℓ.factorial * (p - 1) ^ ℓ ≤ L) {lab : Fin N → Fin m × Fin m} (hlab : OffDiag lab)
    (C : MCircuit N s) (hC : ComputesClique lab k C) :
    m.choose k ≤ s * (L ^ 2 * (m - (ℓ + 1)).choose (k - (ℓ + 1))) ∨
      (k - 1) ^ m - ℓ ^ 2 * (k - 1) ^ (m - 1) ≤
        s * (L ^ 2 * ((ℓ ^ 2) ^ p * (k - 1) ^ (m - p))) := by
  classical
  have hL2 := two_le_L hℓ hp hL
  obtain ⟨hgood, hpos, hneg⟩ := clique_approximation hk hlab C hC (abAop L ℓ p) (Good L ℓ)
    (good_inputApprox hℓ (by omega) hlab) (fun o _ _ ha hc => good_abAop hp hL o ha hc)
    (L ^ 2 * (m - (ℓ + 1)).choose (k - (ℓ + 1))) (L ^ 2 * ((ℓ ^ 2) ^ p * (k - 1) ^ (m - p)))
    (fun o _ _ ha hc => abAop_posErr o ha hc)
    (fun o _ _ ha hc => abAop_negErr hℓ hp hL o ha hc)
  set A := C.approx (inputApprox lab) (abAop L ℓ p)
  rcases A.eq_empty_or_nonempty with h0 | ⟨X, hX⟩
  · left
    refine le_trans (le_of_eq ?_) hpos
    rw [← card_posTests]
    congr 1
    symm
    refine filter_true_of_mem fun K _ => ?_
    rw [h0, approxSem_eq_false]
    simp
  · right
    have hXl := (hgood.2 X hX).1
    have hsub : (univ.filter fun f : Fin m → Fin (k - 1) => Set.InjOn f (X : Set (Fin m))) ⊆
        univ.filter fun f => approxSem A (colorGraph f) = true := by
      intro f hf
      simp only [mem_filter, mem_univ, true_and] at hf ⊢
      exact (approxSem_eq_true _ _).2 ⟨X, hX, (isClique_colorGraph_iff f _).2 hf⟩
    have hsplit := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin m → Fin (k - 1)))) fun f => Set.InjOn f (X : Set (Fin m))
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hsplit
    have hbad := card_not_injOn_le (k - 1) ℓ X hXl
    have h1 := card_le_card hsub
    omega

/-- **Razborov's theorem (Alon–Boppana form).** Let `ℓ ≥ 2`, `p ≥ 2`, `k ≥ 1` and
`L = ℓ! (p-1)^ℓ`. If a monotone circuit with `s` gates computes `CLIQUE(m,k)` (reading
graphs through any off-diagonal edge labelling), then
`C(m,k) ≤ s · L² · C(m-ℓ-1, k-ℓ-1)` or
`(k-1)^m - ℓ² (k-1)^(m-1) ≤ s · L² · (ℓ²)^p · (k-1)^(m-p)`. -/
theorem razborov_alon_boppana {N s k ℓ p : ℕ} (hk : 1 ≤ k) (hℓ : 2 ≤ ℓ) (hp : 2 ≤ p)
    {lab : Fin N → Fin m × Fin m} (hlab : OffDiag lab)
    (C : MCircuit N s) (hC : ComputesClique lab k C) :
    m.choose k ≤ s * ((ℓ.factorial * (p - 1) ^ ℓ) ^ 2 * (m - (ℓ + 1)).choose (k - (ℓ + 1))) ∨
      (k - 1) ^ m - ℓ ^ 2 * (k - 1) ^ (m - 1) ≤
        s * ((ℓ.factorial * (p - 1) ^ ℓ) ^ 2 * ((ℓ ^ 2) ^ p * (k - 1) ^ (m - p))) :=
  razborov_alon_boppana_gen hk hℓ hp le_rfl hlab C hC

end Pnp.Monotone
