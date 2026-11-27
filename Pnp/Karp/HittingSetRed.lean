import Pnp.Karp.HittingSet

/-!
# HITTING SET: correctness of the reduction from SAT

`sat_iff_hs`: a formula `w` is satisfiable iff its instance `HSI w` has a hitting set of size
at most `N = NV w`.  The rows of `HSI w` are the header `zero^(2N)`, the budget `zero^N`, the
pairs `{2i, 2i + 1}` (`i < N`) and the doubled clauses `c.flatMap dbl`.

* (→) the assignment `a` gives the hitting set `{2i + (if a i then 0 else 1) | i < N}`;
* (←) a hitting set `H` with `|H| ≤ N` meets each of the `N` disjoint pairs, so it contains
  exactly one element of each pair (`hsr_not_both`, a counting argument); the assignment
  `a j := (2j ∈ H)` then satisfies every clause.
-/

namespace Pnp.Karp.HittingSet

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum

/-- Every clause of `w` has fewer than `NV w` symbols. -/
theorem hsr_len_lt (w : List SatSym) {c : List SatSym} (hc : c ∈ clauses w) :
    c.length < NV w := by
  have h : List.Sublist (c ++ [sep]) (trunc w) := by
    unfold trunc; rw [List.flatMap_def]
    exact List.sublist_flatten_of_mem (List.mem_map.2 ⟨_, hc, rfl⟩)
  have := h.length_le; simp at this; unfold NV; omega

theorem hsr_sep_pairRow (N i : ℕ) : sep ∉ pairRow N i := by
  simp only [pairRow, List.mem_map, List.mem_range, not_exists, not_and]
  intro p _ h; split at h <;> cases h

theorem hsr_sep_dbl (c : List SatSym) : sep ∉ c.flatMap dbl := by
  simp only [List.mem_flatMap, not_exists, not_and]
  intro s _ h; cases s <;> simp [dbl] at h

/-- The rows of the instance. -/
theorem hsr_clauses (w : List SatSym) :
    clauses (HSI w) = List.replicate (2 * NV w) zero :: List.replicate (NV w) zero :: hsRows w := by
  refine clauses_flatMap _ fun c hc => ?_
  simp only [List.mem_cons, hsRows, List.mem_append, List.mem_map] at hc
  rcases hc with rfl | rfl | ⟨i, _, rfl⟩ | ⟨c, _, rfl⟩
  · simp [List.mem_replicate]
  · simp [List.mem_replicate]
  · exact hsr_sep_pairRow _ _
  · exact hsr_sep_dbl _

theorem hsr_pair_getD (N i p : ℕ) :
    (pairRow N i).getD p zero = pos ↔ p < 2 * N ∧ p / 2 = i := by
  by_cases hp : p < 2 * N
  · rw [List.getD_eq_getElem _ _ (by simpa [pairRow] using hp)]
    simp only [pairRow, List.getElem_map, List.getElem_range]
    split <;> simp_all
  · rw [List.getD_eq_default _ _ (by simp [pairRow]; omega)]; simp [hp]

theorem hsr_dbl_getD : ∀ (c : List SatSym) (p : ℕ),
    (c.flatMap dbl).getD p zero = pos ↔
      (p % 2 = 0 ∧ c.getD (p / 2) zero = pos) ∨ (p % 2 = 1 ∧ c.getD (p / 2) zero = neg)
  | [], p => by simp
  | s :: c, 0 => by cases s <;> simp [dbl]
  | s :: c, 1 => by cases s <;> simp [dbl]
  | s :: c, p + 2 => by
    have ih := hsr_dbl_getD c p
    have e1 : (p + 2) / 2 = p / 2 + 1 := by omega
    have e2 : (p + 2) % 2 = p % 2 := by omega
    rw [e1, e2, List.getD_cons_succ, ← ih]
    cases s <;> simp [dbl]

/-- A hitting set of size `≤ N` of the `N` pairs never contains both elements of a pair. -/
theorem hsr_not_both {N : ℕ} {H : Finset ℕ} (hcard : H.card ≤ N)
    (hpair : ∀ i < N, ∃ p ∈ H, p / 2 = i) {i : ℕ} (hi : i < N) (h0 : 2 * i ∈ H)
    (h1 : 2 * i + 1 ∈ H) : False := by
  have hsub : Finset.range N ⊆ (H.erase (2 * i + 1)).image (· / 2) := by
    intro i' hi'
    obtain ⟨p, hp, rfl⟩ := hpair i' (Finset.mem_range.1 hi')
    rw [Finset.mem_image]
    by_cases hq : p = 2 * i + 1
    · exact ⟨2 * i, Finset.mem_erase.2 ⟨by omega, h0⟩, by omega⟩
    · exact ⟨p, Finset.mem_erase.2 ⟨hq, hp⟩, rfl⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_range, Finset.card_erase_of_mem h1] at this
  omega

/-- **SAT ≤ HITTING SET**: correctness of the instance `HSI w`. -/
theorem sat_iff_hs (w : List SatSym) : SATLang w ↔ HSLang (HSI w) := by
  rw [clauses_sat_iff]
  unfold HSLang
  rw [hsr_clauses]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨_, _, _, rfl, (Finset.range (NV w)).image fun i => 2 * i + if a i then 0 else 1,
      ?_, ?_, ?_⟩
    · simpa using (Finset.card_image_le).trans (Finset.card_range (NV w)).le
    · intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      have := Finset.mem_range.1 hi
      simp only [List.length_replicate]; split <;> omega
    · intro r hr
      simp only [hsRows, List.mem_append, List.mem_map, List.mem_range] at hr
      rcases hr with ⟨i, hi, rfl⟩ | ⟨c, hc, rfl⟩
      · refine ⟨_, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩, ?_⟩
        rw [hsr_pair_getD]; split <;> omega
      · obtain ⟨j, hj, hl⟩ := ha c hc
        have hjN : j < NV w := lt_trans hj (hsr_len_lt w hc)
        cases h : c.getD j zero <;> rw [h] at hl <;> simp only [litTrue] at hl
        · refine ⟨2 * j, Finset.mem_image.2 ⟨j, Finset.mem_range.2 hjN, by simp [hl]⟩, ?_⟩
          rw [hsr_dbl_getD]; left; refine ⟨by omega, ?_⟩
          rw [show 2 * j / 2 = j by omega, h]
        · refine ⟨2 * j + 1, Finset.mem_image.2 ⟨j, Finset.mem_range.2 hjN, by simp [hl]⟩, ?_⟩
          rw [hsr_dbl_getD]; right; refine ⟨by omega, ?_⟩
          rw [show (2 * j + 1) / 2 = j by omega, h]
  · rintro ⟨u, kr, rs, he, H, hcard, -, hrows⟩
    simp only [List.cons.injEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    rw [List.length_replicate] at hcard
    have hpair : ∀ i < NV w, ∃ p ∈ H, p / 2 = i := by
      intro i hi
      obtain ⟨p, hp, hg⟩ := hrows (pairRow (NV w) i)
        (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
      exact ⟨p, hp, ((hsr_pair_getD _ _ _).1 hg).2⟩
    refine ⟨fun j => decide (2 * j ∈ H), fun c hc => ?_⟩
    obtain ⟨p, hp, hg⟩ := hrows (c.flatMap dbl)
      (List.mem_append_right _ (List.mem_map.2 ⟨c, hc, rfl⟩))
    have hjl : ∀ s, s ≠ zero → c.getD (p / 2) zero = s → p / 2 < c.length := by
      intro s hs h
      by_contra hn
      rw [List.getD_eq_default _ _ (by omega)] at h
      exact hs h.symm
    rw [hsr_dbl_getD] at hg
    rcases hg with ⟨h2, h⟩ | ⟨h2, h⟩
    · refine ⟨p / 2, hjl pos (by decide) h, ?_⟩
      rw [h]; simp only [litTrue, decide_eq_true_eq]
      rwa [show 2 * (p / 2) = p by omega]
    · have hj := hjl neg (by decide) h
      refine ⟨p / 2, hj, ?_⟩
      rw [h]; simp only [litTrue, decide_eq_false_iff_not]
      intro h0
      exact hsr_not_both hcard hpair (hj.trans (hsr_len_lt w hc)) h0
        (by rwa [show 2 * (p / 2) + 1 = p by omega])

end Pnp.Karp.HittingSet
