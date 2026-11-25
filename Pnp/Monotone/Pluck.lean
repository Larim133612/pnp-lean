import Pnp.Monotone.Clique
import Pnp.Monotone.Sunflower

/-!
# Plucking sunflowers (M3c, part 1)

The Alon–Boppana approximators are families `A : Finset (Finset (Fin m))` of vertex sets,
read as `⋁_{X ∈ A} ⌈X⌉` (`approxSem`). To keep families small, *plucking* repeatedly
replaces a sunflower `S ⊆ A` with `p` petals by its core (`pluckStep`, `pluckN`,
`pluck`). Cores of size `≤ 1` are *normalised* to `∅` (`normSet`): such sets are cliques
of every graph anyway, and with this normalisation every set in an approximator has
size `0` or `≥ 2`, so that on the positive test `cliqueGraph K` a set is a clique iff it
lies in `K`.

Main results:
* `card_petal_collisions` (**the key counting lemma**): if `P i` (`i : ι`) are sets of
  size `≤ ℓ` whose pairwise intersections lie in `C`, then at most
  `(ℓ²)^|ι| · r^(m-|ι|)` colourings `Fin m → Fin r` are injective on `C` but on no `P i`.
* `pluckN_shrink`, `approxSem_pluckN`: plucking only replaces sets by subsets, so the
  approximated function can only grow (no positive errors).
* `sizeOK_pluckN`, `card_pluckN_le`: plucking preserves "every set has size `≤ ℓ` and is
  empty or has `≥ 2` elements", and `pluck` brings the family down to `≤ L` members when
  `ℓ! (p-1)^ℓ ≤ L` (Erdős–Rado).
* `card_negErr_pluckN`: `n` plucking steps create at most `n · (ℓ²)^p (k-1)^(m-p)`
  negative errors (colourings on which the plucked family becomes true).
-/

namespace Pnp.Monotone

open Finset

variable {m : ℕ}

/-! ## The key counting lemma -/

/-- Colourings that agree on `u i` and `v i` for all `i` are determined by their values
off the range of `u`, provided `u` is injective and no `v i` lies in the range of `u`. -/
lemma card_fiber_le {ι : Type*} [Fintype ι] (r : ℕ) (u v : ι → Fin m)
    (hu : Function.Injective u) (hv : ∀ i j, v i ≠ u j) :
    (univ.filter fun f : Fin m → Fin r => ∀ i, f (u i) = f (v i)).card ≤
      r ^ (m - Fintype.card ι) := by
  classical
  set U : Finset (Fin m) := univ.image u with hU
  have hUc : U.card = Fintype.card ι := by
    rw [hU, card_image_of_injective _ hu, card_univ]
  let g : (Fin m → Fin r) → ({x // x ∈ Uᶜ} → Fin r) := fun f x => f x.1
  have hinj : Set.InjOn g
      ((univ.filter fun f : Fin m → Fin r => ∀ i, f (u i) = f (v i) : Finset _) : Set _) := by
    intro f hf f' hf' hff
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hf hf'
    funext x
    by_cases hx : x ∈ U
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      have hvi : v i ∈ Uᶜ := by
        rw [mem_compl, hU, mem_image]
        rintro ⟨j, -, hj⟩
        exact hv i j hj.symm
      rw [hf i, hf' i]
      exact congrFun hff ⟨v i, hvi⟩
    · exact congrFun hff ⟨x, mem_compl.2 hx⟩
  have := card_le_card_of_injOn g (t := univ) (fun _ _ => mem_coe.2 (mem_univ _)) hinj
  refine this.trans (le_of_eq ?_)
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, card_compl,
    Fintype.card_fin, hUc]

/-- **Key counting lemma (negative errors of plucking).** Let `P i` (`i : ι`) be sets of
at most `ℓ` vertices whose pairwise intersections lie in `C`. Then at most
`(ℓ²)^|ι| · r^(m - |ι|)` colourings `f : Fin m → Fin r` are injective on `C` but injective
on no `P i`.

Proof: for such `f`, each `P i` has a collision `f (u i) = f (v i)`, `u i ≠ v i`, with
`u i ∉ C` (as `f` is injective on `C`). The `u i` are distinct and no `v i` is a `u j`,
since `P i ∩ P j ⊆ C`; so `f` is determined by the choice of pairs (at most `(ℓ²)^|ι|`)
and its values off `{u i}` (at most `r^(m-|ι|)`). -/
theorem card_petal_collisions {ι : Type*} [Fintype ι] [DecidableEq ι] (r ℓ : ℕ)
    (P : ι → Finset (Fin m)) (C : Finset (Fin m))
    (hP : ∀ i, (P i).card ≤ ℓ) (hC : ∀ i j, i ≠ j → P i ∩ P j ⊆ C) :
    (univ.filter fun f : Fin m → Fin r =>
        Set.InjOn f (C : Set (Fin m)) ∧ ∀ i, ¬ Set.InjOn f (P i : Set (Fin m))).card ≤
      (ℓ ^ 2) ^ Fintype.card ι * r ^ (m - Fintype.card ι) := by
  classical
  set V := (Fintype.piFinset fun i => P i ×ˢ P i).filter
      (fun π : ι → Fin m × Fin m => ∀ i, (π i).1 ∉ C ∧ (π i).1 ≠ (π i).2) with hV
  have hsub : (univ.filter fun f : Fin m → Fin r =>
        Set.InjOn f (C : Set (Fin m)) ∧ ∀ i, ¬ Set.InjOn f (P i : Set (Fin m))) ⊆
      V.biUnion (fun π => univ.filter fun f : Fin m → Fin r => ∀ i, f (π i).1 = f (π i).2) := by
    intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    obtain ⟨hfC, hfP⟩ := hf
    have : ∀ i, ∃ q : Fin m × Fin m, q ∈ P i ×ˢ P i ∧ (q.1 ∉ C ∧ q.1 ≠ q.2) ∧
        f q.1 = f q.2 := by
      intro i
      have h := hfP i
      simp only [Set.InjOn, not_forall, mem_coe] at h
      obtain ⟨a, ha, b, hb, hab, hne⟩ := h
      by_cases haC : a ∈ C
      · have hbC : b ∉ C := fun hbC => hne (hfC (mem_coe.2 haC) (mem_coe.2 hbC) hab)
        exact ⟨(b, a), mem_product.2 ⟨hb, ha⟩, ⟨hbC, Ne.symm hne⟩, hab.symm⟩
      · exact ⟨(a, b), mem_product.2 ⟨ha, hb⟩, ⟨haC, hne⟩, hab⟩
    choose π hπP hπV hπf using this
    rw [mem_biUnion]
    refine ⟨π, ?_, ?_⟩
    · rw [hV, mem_filter, Fintype.mem_piFinset]
      exact ⟨hπP, hπV⟩
    · simp only [mem_filter, mem_univ, true_and]
      exact hπf
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  have hfib : ∀ π ∈ V, (univ.filter fun f : Fin m → Fin r => ∀ i, f (π i).1 = f (π i).2).card ≤
      r ^ (m - Fintype.card ι) := by
    intro π hπ
    rw [hV, mem_filter, Fintype.mem_piFinset] at hπ
    obtain ⟨hπP, hπV⟩ := hπ
    apply card_fiber_le r (fun i => (π i).1) (fun i => (π i).2)
    · intro i j hij
      by_contra hne
      have hi := (mem_product.1 (hπP i)).1
      have hj := (mem_product.1 (hπP j)).1
      simp only at hij
      rw [hij] at hi
      exact (hπV j).1 (hC i j hne (mem_inter.2 ⟨hi, hj⟩))
    · intro i j hij
      by_cases h : i = j
      · subst h
        exact (hπV i).2 hij.symm
      · have hi := (mem_product.1 (hπP i)).2
        have hj := (mem_product.1 (hπP j)).1
        rw [hij] at hi
        exact (hπV j).1 (hC i j h (mem_inter.2 ⟨hi, hj⟩))
  refine (sum_le_sum hfib).trans ?_
  rw [sum_const, smul_eq_mul]
  apply Nat.mul_le_mul_right
  refine (card_filter_le _ _).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ i, (P i ×ˢ P i).card ≤ (ℓ ^ 2) ^ (univ : Finset ι).card :=
        prod_le_pow_card _ _ _ fun i _ => by
          rw [card_product, ← sq]
          exact Nat.pow_le_pow_left (hP i) 2
    _ = (ℓ ^ 2) ^ Fintype.card ι := by rw [card_univ]

/-- Special case `ι = Unit`, `C = ∅`: at most `ℓ² · r^(m-1)` colourings are not injective
on a given set of at most `ℓ` vertices. -/
theorem card_not_injOn_le (r ℓ : ℕ) (X : Finset (Fin m)) (hX : X.card ≤ ℓ) :
    (univ.filter fun f : Fin m → Fin r => ¬ Set.InjOn f (X : Set (Fin m))).card ≤
      ℓ ^ 2 * r ^ (m - 1) := by
  have h := card_petal_collisions (ι := Unit) r ℓ (fun _ => X) ∅ (fun _ => hX)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
  rw [Fintype.card_unit, pow_one] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine filter_congr fun f _ => ?_
  simp

/-! ## Normalised sets -/

/-- Normalisation: sets of size `≤ 1` (cliques of every graph) become `∅`. -/
def normSet (X : Finset (Fin m)) : Finset (Fin m) := if X.card ≤ 1 then ∅ else X

lemma normSet_subset (X : Finset (Fin m)) : normSet X ⊆ X := by
  unfold normSet
  split_ifs
  · exact empty_subset _
  · exact Subset.rfl

lemma injOn_of_injOn_normSet {α : Type*} (f : Fin m → α) {X : Finset (Fin m)}
    (h : Set.InjOn f (normSet X : Set (Fin m))) : Set.InjOn f (X : Set (Fin m)) := by
  unfold normSet at h
  split_ifs at h with hX
  · intro a ha b hb _
    exact card_le_one.1 hX a ha b hb
  · exact h

/-- Size condition on the sets of an approximator: at most `ℓ` elements, and empty or of
size at least `2`. -/
def SizeOK (ℓ : ℕ) (X : Finset (Fin m)) : Prop := X.card ≤ ℓ ∧ (X = ∅ ∨ 2 ≤ X.card)

lemma sizeOK_normSet {ℓ : ℕ} {X Y : Finset (Fin m)} (hXY : X ⊆ Y) (hY : Y.card ≤ ℓ) :
    SizeOK ℓ (normSet X) := by
  unfold normSet
  split_ifs with hX
  · exact ⟨by simp, Or.inl rfl⟩
  · exact ⟨(card_le_card hXY).trans hY, Or.inr (by omega)⟩

/-! ## Plucking -/

/-- `SC = (S, C)` certifies a plucking step on `A`: `S ⊆ A` has `p` members, any two
distinct of which meet exactly in `C`, and `C` lies in every member of `S`. -/
def IsPluckable (p : ℕ) (A : Finset (Finset (Fin m)))
    (SC : Finset (Finset (Fin m)) × Finset (Fin m)) : Prop :=
  SC.1 ⊆ A ∧ SC.1.card = p ∧ (∀ Y ∈ SC.1, ∀ Z ∈ SC.1, Y ≠ Z → Y ∩ Z = SC.2) ∧
    ∀ Y ∈ SC.1, SC.2 ⊆ Y

/-- One plucking step: if `A` has more than `L` members and contains a sunflower with `p`
petals, replace it by its normalised core; otherwise do nothing. -/
noncomputable def pluckStep (L p : ℕ) (A : Finset (Finset (Fin m))) : Finset (Finset (Fin m)) :=
  open Classical in
  if h : L < A.card ∧ ∃ SC : Finset (Finset (Fin m)) × Finset (Fin m), IsPluckable p A SC then
    A \ (Classical.choose h.2).1 ∪ {normSet (Classical.choose h.2).2}
  else A

/-- `n` plucking steps. -/
noncomputable def pluckN (L p : ℕ) : ℕ → Finset (Finset (Fin m)) → Finset (Finset (Fin m))
  | 0, A => A
  | n + 1, A => pluckN L p n (pluckStep L p A)

/-- Plucking: `|A|` plucking steps (enough to bring the family down to `≤ L` members). -/
noncomputable def pluck (L p : ℕ) (A : Finset (Finset (Fin m))) : Finset (Finset (Fin m)) :=
  pluckN L p A.card A

lemma pluckStep_cases (L p : ℕ) (A : Finset (Finset (Fin m))) :
    pluckStep L p A = A ∨
      ∃ SC, IsPluckable p A SC ∧ pluckStep L p A = A \ SC.1 ∪ {normSet SC.2} := by
  unfold pluckStep
  split_ifs with h
  · exact Or.inr ⟨_, Classical.choose_spec h.2, rfl⟩
  · exact Or.inl rfl

lemma pluckStep_pos {L p : ℕ} {A : Finset (Finset (Fin m))} (hA : L < A.card)
    (hS : ∃ SC, IsPluckable p A SC) :
    ∃ SC, IsPluckable p A SC ∧ pluckStep L p A = A \ SC.1 ∪ {normSet SC.2} := by
  unfold pluckStep
  rw [dif_pos ⟨hA, hS⟩]
  exact ⟨_, Classical.choose_spec hS, rfl⟩

lemma pluckStep_of_le {L p : ℕ} {A : Finset (Finset (Fin m))} (hA : A.card ≤ L) :
    pluckStep L p A = A := by
  unfold pluckStep
  rw [dif_neg (fun h => by omega)]

/-- Every set of `A` contains a set of `pluckStep A`. -/
lemma pluckStep_shrink (L p : ℕ) (A : Finset (Finset (Fin m))) :
    ∀ X ∈ A, ∃ X' ∈ pluckStep L p A, X' ⊆ X := by
  intro X hX
  rcases pluckStep_cases L p A with h | ⟨SC, hSC, h⟩
  · exact ⟨X, by rw [h]; exact hX, Subset.rfl⟩
  · rw [h]
    by_cases hXS : X ∈ SC.1
    · exact ⟨normSet SC.2, mem_union_right _ (mem_singleton_self _),
        (normSet_subset _).trans (hSC.2.2.2 X hXS)⟩
    · exact ⟨X, mem_union_left _ (mem_sdiff.2 ⟨hX, hXS⟩), Subset.rfl⟩

lemma pluckN_shrink (L p : ℕ) :
    ∀ (n : ℕ) (A : Finset (Finset (Fin m))), ∀ X ∈ A, ∃ X' ∈ pluckN L p n A, X' ⊆ X := by
  intro n
  induction n with
  | zero => intro A X hX; exact ⟨X, hX, Subset.rfl⟩
  | succ n ih =>
    intro A X hX
    obtain ⟨X₁, hX₁, h₁⟩ := pluckStep_shrink L p A X hX
    obtain ⟨X₂, hX₂, h₂⟩ := ih _ X₁ hX₁
    exact ⟨X₂, hX₂, h₂.trans h₁⟩

/-- Plucking can only make the approximated function larger. -/
lemma approxSem_pluckN (L p n : ℕ) {A : Finset (Finset (Fin m))} {G : SimpleGraph (Fin m)}
    (h : approxSem A G = true) : approxSem (pluckN L p n A) G = true := by
  rw [approxSem_eq_true] at h ⊢
  obtain ⟨X, hX, hG⟩ := h
  obtain ⟨X', hX', hsub⟩ := pluckN_shrink L p n A X hX
  exact ⟨X', hX', hG.subset (coe_subset.2 hsub)⟩

lemma approxSem_pluck (L p : ℕ) {A : Finset (Finset (Fin m))} {G : SimpleGraph (Fin m)}
    (h : approxSem A G = true) : approxSem (pluck L p A) G = true :=
  approxSem_pluckN L p _ h

lemma sizeOK_pluckStep {L p ℓ : ℕ} (hp : 1 ≤ p) {A : Finset (Finset (Fin m))}
    (hA : ∀ X ∈ A, SizeOK ℓ X) : ∀ X ∈ pluckStep L p A, SizeOK ℓ X := by
  rcases pluckStep_cases L p A with h | ⟨SC, hSC, h⟩
  · rw [h]; exact hA
  · rw [h]
    intro X hX
    rcases mem_union.1 hX with hX | hX
    · exact hA X (mem_sdiff.1 hX).1
    · rw [mem_singleton.1 hX]
      obtain ⟨Y, hY⟩ : SC.1.Nonempty := card_pos.1 (by rw [hSC.2.1]; omega)
      exact sizeOK_normSet (hSC.2.2.2 Y hY) (hA Y (hSC.1 hY)).1

lemma sizeOK_pluckN {L p ℓ : ℕ} (hp : 1 ≤ p) :
    ∀ (n : ℕ) (A : Finset (Finset (Fin m))), (∀ X ∈ A, SizeOK ℓ X) →
      ∀ X ∈ pluckN L p n A, SizeOK ℓ X := by
  intro n
  induction n with
  | zero => intro A hA; exact hA
  | succ n ih => intro A hA; exact ih _ (sizeOK_pluckStep hp hA)

/-- Plucking `n` times brings a family of size `≤ n + L` down to size `≤ L`
(Erdős–Rado guarantees a sunflower while the family has more than `ℓ!(p-1)^ℓ` members). -/
lemma card_pluckN_le {L p ℓ : ℕ} (hp : 2 ≤ p) (hL : ℓ.factorial * (p - 1) ^ ℓ ≤ L) :
    ∀ (n : ℕ) (A : Finset (Finset (Fin m))), (∀ X ∈ A, SizeOK ℓ X) →
      A.card ≤ n + L → (pluckN L p n A).card ≤ L := by
  intro n
  induction n with
  | zero => intro A _ hc; show A.card ≤ L; omega
  | succ n ih =>
    intro A hA hc
    show (pluckN L p n (pluckStep L p A)).card ≤ L
    by_cases hAL : L < A.card
    · obtain ⟨S, hSA, hScard, C, hC⟩ :=
        erdos_rado p ℓ A (fun X hX => (hA X hX).1) (lt_of_le_of_lt hL hAL)
      have hsub : ∀ Y ∈ S, C ⊆ Y := by
        intro Y hY
        obtain ⟨Z, hZ, hZY⟩ := exists_mem_ne (by omega : 1 < S.card) Y
        rw [← hC Y hY Z hZ hZY.symm]
        exact inter_subset_left
      obtain ⟨SC, hSC, h⟩ := pluckStep_pos (L := L) hAL ⟨(S, C), hSA, hScard, hC, hsub⟩
      apply ih _ (sizeOK_pluckStep (by omega) hA)
      rw [h]
      have h1 := card_union_le (A \ SC.1) {normSet SC.2}
      have h2 := card_sdiff_of_subset hSC.1
      have h3 := card_le_card hSC.1
      rw [card_singleton] at h1
      rw [hSC.2.1] at h2 h3
      omega
    · rw [pluckStep_of_le (by omega)]
      exact ih A hA (by omega)

lemma card_pluck_le {L p ℓ : ℕ} (hp : 2 ≤ p) (hL : ℓ.factorial * (p - 1) ^ ℓ ≤ L)
    {A : Finset (Finset (Fin m))} (hA : ∀ X ∈ A, SizeOK ℓ X) : (pluck L p A).card ≤ L :=
  card_pluckN_le hp hL _ A hA (Nat.le_add_right _ _)

/-! ## Negative errors of plucking -/

/-- Negative errors of replacing `A` by `B`: colourings on which `B` is true and `A` false. -/
noncomputable def negErr (r : ℕ) (A B : Finset (Finset (Fin m))) : Finset (Fin m → Fin r) :=
  univ.filter fun f => approxSem B (colorGraph f) = true ∧ approxSem A (colorGraph f) = false

lemma negErr_self (r : ℕ) (A : Finset (Finset (Fin m))) : negErr r A A = ∅ := by
  unfold negErr
  refine filter_false_of_mem fun f _ h => ?_
  rw [h.1] at h
  exact Bool.noConfusion h.2

/-- **One plucking step creates at most `(ℓ²)^p · r^(m-p)` negative errors.** -/
theorem card_negErr_pluckStep (r L p ℓ : ℕ) {A : Finset (Finset (Fin m))}
    (hA : ∀ X ∈ A, X.card ≤ ℓ) :
    (negErr r A (pluckStep L p A)).card ≤ (ℓ ^ 2) ^ p * r ^ (m - p) := by
  classical
  rcases pluckStep_cases L p A with h | ⟨SC, hSC, h⟩
  · rw [h, negErr_self]; simp
  · obtain ⟨hSA, hScard, hC, -⟩ := hSC
    have key := card_petal_collisions (ι := SC.1) r ℓ (fun Y => Y.1) SC.2
      (fun Y => hA _ (hSA Y.2))
      (fun Y Z hYZ => (hC Y.1 Y.2 Z.1 Z.2 fun h => hYZ (Subtype.ext h)).le)
    rw [Fintype.card_coe, hScard] at key
    refine le_trans (card_le_card ?_) key
    intro f hf
    simp only [negErr, mem_filter, mem_univ, true_and, approxSem_eq_true,
      approxSem_eq_false, isClique_colorGraph_iff] at hf
    obtain ⟨⟨X, hX, hfX⟩, hfA⟩ := hf
    simp only [mem_filter, mem_univ, true_and]
    rw [h] at hX
    rcases mem_union.1 hX with hX | hX
    · exact absurd hfX (hfA X (mem_sdiff.1 hX).1)
    · rw [mem_singleton.1 hX] at hfX
      exact ⟨injOn_of_injOn_normSet f hfX, fun Y => hfA Y.1 (hSA Y.2)⟩

/-- **`n` plucking steps create at most `n · (ℓ²)^p · r^(m-p)` negative errors.** -/
theorem card_negErr_pluckN (r L p ℓ : ℕ) (hp : 1 ≤ p) :
    ∀ (n : ℕ) (A : Finset (Finset (Fin m))), (∀ X ∈ A, SizeOK ℓ X) →
      (negErr r A (pluckN L p n A)).card ≤ n * ((ℓ ^ 2) ^ p * r ^ (m - p)) := by
  intro n
  induction n with
  | zero => intro A _; rw [pluckN, negErr_self]; simp
  | succ n ih =>
    intro A hA
    show (negErr r A (pluckN L p n (pluckStep L p A))).card ≤ _
    set B := pluckStep L p A
    have hsub : negErr r A (pluckN L p n B) ⊆ negErr r A B ∪ negErr r B (pluckN L p n B) := by
      intro f hf
      simp only [negErr, mem_filter, mem_univ, true_and, mem_union] at hf ⊢
      cases hB : approxSem B (colorGraph f)
      · exact Or.inr ⟨hf.1, rfl⟩
      · exact Or.inl ⟨rfl, hf.2⟩
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    have h1 : (negErr r A B).card ≤ (ℓ ^ 2) ^ p * r ^ (m - p) :=
      card_negErr_pluckStep r L p ℓ (A := A) fun X hX => (hA X hX).1
    have h2 := ih B (sizeOK_pluckStep hp hA)
    rw [Nat.succ_mul]
    generalize (ℓ ^ 2) ^ p * r ^ (m - p) = D at h1 h2 ⊢
    omega

theorem card_negErr_pluck (r L p ℓ : ℕ) (hp : 1 ≤ p) {A : Finset (Finset (Fin m))}
    (hA : ∀ X ∈ A, SizeOK ℓ X) :
    (negErr r A (pluck L p A)).card ≤ A.card * ((ℓ ^ 2) ^ p * r ^ (m - p)) :=
  card_negErr_pluckN r L p ℓ hp _ A hA

end Pnp.Monotone
