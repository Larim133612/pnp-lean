import Mathlib

/-!
# The Erdős–Rado sunflower lemma (M3a)

A family `S` of sets is a *sunflower* if all pairwise intersections of distinct members
are the same set (the core).

**Erdős–Rado (1960).** If every set in `F` has at most `ℓ` elements and
`|F| > ℓ! (p-1)^ℓ`, then `F` contains a sunflower with `p` petals.

This is the combinatorial engine of Razborov's monotone lower bound for CLIQUE.
-/

namespace Pnp.Monotone

open Finset

variable {α : Type*} [DecidableEq α]

/-- `S` is a sunflower: all pairwise intersections of distinct members coincide. -/
def IsSunflower (S : Finset (Finset α)) : Prop :=
  ∃ C : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = C

lemma isSunflower_of_pairwiseDisjoint {S : Finset (Finset α)}
    (h : (S : Set (Finset α)).PairwiseDisjoint id) : IsSunflower S :=
  ⟨∅, fun _ hA _ hB hAB => disjoint_iff_inter_eq_empty.1 (h hA hB hAB)⟩

/-- Lifting a sunflower of sets avoiding `x` by adding `x` to every petal. -/
lemma isSunflower_image_insert {S : Finset (Finset α)} (x : α)
    (h : IsSunflower S) : IsSunflower (S.image (insert x)) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨insert x C, ?_⟩
  intro A hA B hB hAB
  obtain ⟨A', hA', rfl⟩ := mem_image.1 hA
  obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
  have hne : A' ≠ B' := fun h => hAB (h ▸ rfl)
  rw [← insert_inter_distrib, hC A' hA' B' hB' hne]

lemma insert_injOn {S : Finset (Finset α)} {x : α} (hx : ∀ A ∈ S, x ∉ A) :
    Set.InjOn (insert x) (S : Set (Finset α)) := by
  intro A hA B hB h
  have := congrArg (Finset.erase · x) h
  simpa [erase_insert (hx A hA), erase_insert (hx B hB)] using this

/-- **Erdős–Rado sunflower lemma.** -/
theorem erdos_rado (p : ℕ) : ∀ (ℓ : ℕ) (F : Finset (Finset α)), (∀ A ∈ F, A.card ≤ ℓ) →
    ℓ.factorial * (p - 1) ^ ℓ < F.card → ∃ S ⊆ F, S.card = p ∧ IsSunflower S := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro F hF hcard
    exfalso
    have : F ⊆ {∅} := fun A hA => by
      simpa using card_eq_zero.1 (Nat.le_zero.1 (hF A hA))
    have := card_le_card this
    simp at hcard this
    omega
  | succ k ih =>
    intro F hF hcard
    classical
    set M := k.factorial * (p - 1) ^ k with hM
    -- a maximum-size pairwise disjoint subfamily of the nonempty members
    let P := (F.erase ∅).powerset.filter fun D : Finset (Finset α) => (D : Set (Finset α)).PairwiseDisjoint id
    have hPne : P.Nonempty := ⟨∅, by simp [P]⟩
    obtain ⟨D, hDP, hDmax⟩ := exists_max_image P card hPne
    simp only [P, mem_filter, mem_powerset] at hDP
    obtain ⟨hDF, hDdisj⟩ := hDP
    -- Case 1: at least `p` pairwise disjoint sets
    by_cases h1 : p ≤ D.card
    · obtain ⟨S, hSD, hS⟩ := exists_subset_card_eq h1
      exact ⟨S, hSD.trans (hDF.trans (erase_subset _ _)), hS,
        isSunflower_of_pairwiseDisjoint (hDdisj.subset (by exact_mod_cast hSD))⟩
    push Not at h1
    -- Case 2: `∅ ∈ F` and exactly `p - 1` disjoint nonempty sets
    by_cases h2 : ∅ ∈ F ∧ D.card + 1 = p
    · refine ⟨insert ∅ D, insert_subset h2.1 (hDF.trans (erase_subset _ _)), ?_, ?_⟩
      · rw [card_insert_of_notMem (fun h => by simpa using hDF h)]; exact h2.2
      · apply isSunflower_of_pairwiseDisjoint
        rw [coe_insert]
        refine hDdisj.insert fun B _ _ => ?_
        simp
    -- Case 3: every nonempty member meets `U = ⋃ D`
    set U := D.biUnion id with hU
    have hmeet : ∀ A ∈ F, A ≠ ∅ → ∃ x ∈ U, x ∈ A := by
      intro A hA hA0
      by_cases hAD : A ∈ D
      · obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hA0
        exact ⟨x, mem_biUnion.2 ⟨A, hAD, hx⟩, hx⟩
      · by_contra hno
        push Not at hno
        have hins : insert A D ∈ P := by
          simp only [P, mem_filter, mem_powerset]
          refine ⟨insert_subset (mem_erase.2 ⟨hA0, hA⟩) hDF, ?_⟩
          rw [coe_insert]
          refine hDdisj.insert fun B hB _ => ?_
          show Disjoint A B
          rw [disjoint_left]
          intro y hyA hyB
          exact hno y (mem_biUnion.2 ⟨B, hB, hyB⟩) hyA
        have := hDmax _ hins
        rw [card_insert_of_notMem hAD] at this
        omega
    have hUcard : U.card ≤ D.card * (k + 1) := by
      calc U.card ≤ ∑ A ∈ D, (id A).card := card_biUnion_le
        _ ≤ ∑ _A ∈ D, (k + 1) := sum_le_sum fun A hA =>
            hF A (mem_of_mem_erase (hDF hA))
        _ = D.card * (k + 1) := by simp
    -- some element lies in more than `M` members
    obtain ⟨x, hxU, hx⟩ : ∃ x ∈ U, M < (F.filter (x ∈ ·)).card := by
      by_contra hno
      push Not at hno
      have hcov : F.erase ∅ ⊆ U.biUnion fun x => F.filter (x ∈ ·) := by
        intro A hA
        obtain ⟨hA0, hAF⟩ := mem_erase.1 hA
        obtain ⟨x, hxU, hxA⟩ := hmeet A hAF hA0
        exact mem_biUnion.2 ⟨x, hxU, mem_filter.2 ⟨hAF, hxA⟩⟩
      have hle : (F.erase ∅).card ≤ U.card * M := by
        calc (F.erase ∅).card ≤ (U.biUnion fun x => F.filter (x ∈ ·)).card := card_le_card hcov
          _ ≤ ∑ x ∈ U, (F.filter (x ∈ ·)).card := card_biUnion_le
          _ ≤ ∑ _x ∈ U, M := sum_le_sum hno
          _ = U.card * M := by simp
      have hfact : (k + 1).factorial * (p - 1) ^ (k + 1) = (k + 1) * (p - 1) * M := by
        rw [hM, Nat.factorial_succ, pow_succ]; ring
      rw [hfact] at hcard
      by_cases h0 : ∅ ∈ F
      · have hD2 : D.card + 2 ≤ p := by
          have : D.card + 1 ≠ p := fun h => h2 ⟨h0, h⟩
          omega
        have hMpos : 1 ≤ M := by
          rw [hM]
          exact Nat.one_le_iff_ne_zero.2
            (Nat.mul_ne_zero (Nat.factorial_ne_zero k) (pow_ne_zero _ (by omega)))
        have := card_erase_add_one h0
        have hU' : U.card * M ≤ D.card * (k + 1) * M := Nat.mul_le_mul_right _ hUcard
        have : (D.card + 1) * (k + 1) * M ≤ (p - 1) * (k + 1) * M := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
        nlinarith
      · rw [erase_eq_of_notMem h0] at hle
        have hU' : U.card * M ≤ D.card * (k + 1) * M := Nat.mul_le_mul_right _ hUcard
        have : D.card * (k + 1) * M ≤ (p - 1) * (k + 1) * M := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega
        nlinarith
    -- recurse on the link of `x`
    set Fx := F.filter (x ∈ ·)
    set G := Fx.image (·.erase x) with hG
    have hGcard : G.card = Fx.card := by
      apply card_image_of_injOn
      intro A hA B hB h
      simp only [Fx, coe_filter, Set.mem_setOf_eq] at hA hB
      have := congrArg (insert x) h
      simpa [insert_erase hA.2, insert_erase hB.2] using this
    have hGsize : ∀ B ∈ G, B.card ≤ k := by
      intro B hB
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
      have hA' := mem_filter.1 hA
      rw [card_erase_of_mem hA'.2]
      have := hF A hA'.1
      omega
    obtain ⟨S, hSG, hS, hSf⟩ := ih G hGsize (by rw [hGcard]; exact hx)
    have hxS : ∀ B ∈ S, x ∉ B := by
      intro B hB
      obtain ⟨A, _, rfl⟩ := mem_image.1 (hSG hB)
      exact notMem_erase x A
    refine ⟨S.image (insert x), ?_, ?_, isSunflower_image_insert x hSf⟩
    · intro A hA
      obtain ⟨B, hB, rfl⟩ := mem_image.1 hA
      obtain ⟨A', hA', rfl⟩ := mem_image.1 (hSG hB)
      rw [insert_erase (mem_filter.1 hA').2]
      exact (mem_filter.1 hA').1
    · rw [card_image_of_injOn (insert_injOn hxS), hS]

end Pnp.Monotone
