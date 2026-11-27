import Pnp.Karp.DomSet
import Pnp.Karp.HittingSetRed

/-!
# DOMINATING SET: correctness of the reduction from SAT

`sat_iff_ds`: a formula `w` is satisfiable iff its instance `DSI w` has a dominating set of
size at most `N = NV w`.  The rows of `DSI w` are the budget `zero^N`, the triangle rows
`triRow N u` (`u < 3N`) and the clause rows `c.flatMap trp`.

* (→) the assignment `a` gives the dominating set `{3j + (if a j then 0 else 1) | j < N}`: it
  dominates every triangle internally, and the clause vertex `3N + i` by its true literal;
* (←) the private vertex `3j + 2` is adjacent only to its triangle, so a dominating set `D`
  meets each of the `N` disjoint triangles; as `|D| ≤ N` it contains no clause vertex and not
  both `3j` and `3j + 1` (`dsr_count`); the clause vertex `3N + i` is then dominated by a
  literal vertex of `cᵢ` and the assignment `a j := (3j ∈ D)` satisfies `cᵢ`.
-/

namespace Pnp.Karp.DomSet

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.HittingSet

theorem dsr_sep_triRow (N u : ℕ) : sep ∉ triRow N u := by
  simp only [triRow, List.mem_map, List.mem_range, not_exists, not_and]
  intro p _ h; split at h <;> cases h

theorem dsr_sep_trp (c : List SatSym) : sep ∉ c.flatMap trp := by
  simp only [List.mem_flatMap, not_exists, not_and]
  intro s _ h; cases s <;> simp [trp] at h

/-- The rows of the instance. -/
theorem dsr_clauses (w : List SatSym) :
    clauses (DSI w) = List.replicate (NV w) zero :: dsRows w := by
  refine clauses_flatMap _ fun c hc => ?_
  simp only [List.mem_cons, dsRows, List.mem_append, List.mem_map] at hc
  rcases hc with rfl | ⟨i, _, rfl⟩ | ⟨c, _, rfl⟩
  · simp [List.mem_replicate]
  · exact dsr_sep_triRow _ _
  · exact dsr_sep_trp _

theorem dsr_len (w : List SatSym) : (dsRows w).length = 3 * NV w + (clauses w).length := by
  simp [dsRows]

theorem dsr_row_tri (w : List SatSym) {u : ℕ} (hu : u < 3 * NV w) :
    (dsRows w).getD u [] = triRow (NV w) u := by
  rw [List.getD_eq_getElem _ _ (by rw [dsr_len]; omega)]
  simp only [dsRows]
  rw [List.getElem_append_left (by simpa using hu)]
  simp

theorem dsr_row_cl (w : List SatSym) {i : ℕ} (hi : i < (clauses w).length) :
    (dsRows w).getD (3 * NV w + i) [] = (clauses w)[i].flatMap trp := by
  rw [List.getD_eq_getElem _ _ (by rw [dsr_len]; omega)]
  simp only [dsRows]
  rw [List.getElem_append_right (by simp)]
  simp

theorem dsr_tri_getD (N u v : ℕ) :
    (triRow N u).getD v zero = pos ↔ v < 3 * N ∧ v / 3 = u / 3 := by
  by_cases hv : v < 3 * N
  · rw [List.getD_eq_getElem _ _ (by simpa [triRow] using hv)]
    simp only [triRow, List.getElem_map, List.getElem_range]
    split <;> simp_all
  · rw [List.getD_eq_default _ _ (by simp [triRow]; omega)]; simp [hv]

theorem dsr_trp_getD : ∀ (c : List SatSym) (p : ℕ),
    (c.flatMap trp).getD p zero = pos ↔
      (p % 3 = 0 ∧ c.getD (p / 3) zero = pos) ∨ (p % 3 = 1 ∧ c.getD (p / 3) zero = neg)
  | [], p => by simp
  | s :: c, 0 => by cases s <;> simp [trp]
  | s :: c, 1 => by cases s <;> simp [trp]
  | s :: c, 2 => by cases s <;> simp [trp]
  | s :: c, p + 3 => by
    have ih := dsr_trp_getD c p
    have e1 : (p + 3) / 3 = p / 3 + 1 := by omega
    have e2 : (p + 3) % 3 = p % 3 := by omega
    rw [e1, e2, List.getD_cons_succ, ← ih]
    cases s <;> simp [trp]

/-- If `D` (with `|D| ≤ N`) meets every triangle even without `x ∈ D`, we have a contradiction. -/
theorem dsr_count {N : ℕ} {D : Finset ℕ} (hcard : D.card ≤ N) {x : ℕ} (hx : x ∈ D)
    (h : ∀ j < N, ∃ u ∈ D, u ≠ x ∧ u / 3 = j) : False := by
  have hsub : Finset.range N ⊆ (D.erase x).image (· / 3) := by
    intro j hj
    obtain ⟨u, hu, hux, rfl⟩ := h j (Finset.mem_range.1 hj)
    exact Finset.mem_image.2 ⟨u, Finset.mem_erase.2 ⟨hux, hu⟩, rfl⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hpos := Finset.card_pos.2 ⟨x, hx⟩
  rw [Finset.card_range, Finset.card_erase_of_mem hx] at this
  omega

/-- **SAT ≤ DOMINATING SET**: correctness of the instance `DSI w`. -/
theorem sat_iff_ds (w : List SatSym) : SATLang w ↔ DSLang (DSI w) := by
  rw [clauses_sat_iff]
  unfold DSLang
  rw [dsr_clauses]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨_, _, rfl, (Finset.range (NV w)).image fun j => 3 * j + if a j then 0 else 1,
      ?_, ?_, ?_⟩
    · simpa using (Finset.card_image_le).trans (Finset.card_range (NV w)).le
    · intro u hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hu
      have := Finset.mem_range.1 hj
      rw [dsr_len]; split <;> omega
    · intro v hv
      right
      rw [dsr_len] at hv
      by_cases hv3 : v < 3 * NV w
      · refine ⟨_, Finset.mem_image.2 ⟨v / 3, Finset.mem_range.2 (by omega), rfl⟩, Or.inl ?_⟩
        rw [dsr_row_tri w (by split <;> omega), dsr_tri_getD]
        split <;> omega
      · obtain ⟨i, rfl⟩ : ∃ i, v = 3 * NV w + i := ⟨v - 3 * NV w, by omega⟩
        have hi : i < (clauses w).length := by omega
        obtain ⟨j, hj, hl⟩ := ha _ (List.getElem_mem hi)
        have hjN : j < NV w := lt_trans hj (hsr_len_lt w (List.getElem_mem hi))
        cases h : (clauses w)[i].getD j zero <;> rw [h] at hl <;> simp only [litTrue] at hl
        · refine ⟨3 * j, Finset.mem_image.2 ⟨j, Finset.mem_range.2 hjN, by simp [hl]⟩, Or.inr ?_⟩
          rw [dsr_row_cl w hi, dsr_trp_getD]; left; refine ⟨by omega, ?_⟩
          rw [show 3 * j / 3 = j by omega, h]
        · refine ⟨3 * j + 1, Finset.mem_image.2 ⟨j, Finset.mem_range.2 hjN, by simp [hl]⟩,
            Or.inr ?_⟩
          rw [dsr_row_cl w hi, dsr_trp_getD]; right; refine ⟨by omega, ?_⟩
          rw [show (3 * j + 1) / 3 = j by omega, h]
  · rintro ⟨kr, rs, he, D, hcard, hlt, hdom⟩
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [List.length_replicate] at hcard
    rw [dsr_len] at hlt hdom
    -- a vertex of `D` is a triangle vertex or a clause vertex
    have hcase : ∀ u ∈ D, u < 3 * NV w ∨ ∃ i < (clauses w).length, u = 3 * NV w + i := by
      intro u hu
      by_cases h : u < 3 * NV w
      · exact Or.inl h
      · exact Or.inr ⟨u - 3 * NV w, by have := hlt u hu; omega, by omega⟩
    -- `D` meets every triangle
    have htri : ∀ j < NV w, ∃ u ∈ D, u < 3 * NV w ∧ u / 3 = j := by
      intro j hj
      rcases hdom (3 * j + 2) (by omega) with hin | ⟨u, hu, hadj⟩
      · exact ⟨_, hin, by omega, by omega⟩
      · rcases hadj with hadj | hadj
        · rcases hcase u hu with hu3 | ⟨i, hi, rfl⟩
          · rw [dsr_row_tri w hu3, dsr_tri_getD] at hadj
            exact ⟨u, hu, hu3, by omega⟩
          · rw [dsr_row_cl w hi, dsr_trp_getD] at hadj
            omega
        · rw [dsr_row_tri w (by omega), dsr_tri_getD] at hadj
          exact ⟨u, hu, hadj.1, by omega⟩
    -- no clause vertex in `D`
    have hD3 : ∀ u ∈ D, u < 3 * NV w := by
      intro x hx
      by_contra hn
      refine dsr_count hcard hx fun j hj => ?_
      obtain ⟨u, hu, hu3, hj⟩ := htri j hj
      exact ⟨u, hu, by omega, hj⟩
    -- not both literals of a variable
    have hnb : ∀ j < NV w, 3 * j ∈ D → 3 * j + 1 ∈ D → False := by
      intro j hjN h0 h1
      refine dsr_count hcard h1 fun j' hj' => ?_
      obtain ⟨u, hu, -, hj⟩ := htri j' hj'
      by_cases hux : u = 3 * j + 1
      · exact ⟨3 * j, h0, by omega, by omega⟩
      · exact ⟨u, hu, hux, hj⟩
    refine ⟨fun j => decide (3 * j ∈ D), fun c hc => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
    rcases hdom (3 * NV w + i) (by omega) with hin | ⟨u, hu, hadj⟩
    · exact absurd (hD3 _ hin) (by omega)
    have hu3 := hD3 u hu
    have hg : ((clauses w)[i].flatMap trp).getD u zero = pos := by
      rcases hadj with hadj | hadj
      · rw [dsr_row_tri w hu3, dsr_tri_getD] at hadj; omega
      · rwa [dsr_row_cl w hi] at hadj
    have hjl : ∀ s, s ≠ zero → (clauses w)[i].getD (u / 3) zero = s →
        u / 3 < (clauses w)[i].length := by
      intro s hs h
      by_contra hn
      rw [List.getD_eq_default _ _ (by omega)] at h
      exact hs h.symm
    rw [dsr_trp_getD] at hg
    rcases hg with ⟨h3, h⟩ | ⟨h3, h⟩
    · refine ⟨u / 3, hjl pos (by decide) h, ?_⟩
      rw [h]; simp only [litTrue, decide_eq_true_eq]
      rwa [show 3 * (u / 3) = u by omega]
    · refine ⟨u / 3, hjl neg (by decide) h, ?_⟩
      rw [h]; simp only [litTrue, decide_eq_false_iff_not]
      intro h0
      exact hnb (u / 3) (by omega) h0 (by rwa [show 3 * (u / 3) + 1 = u by omega])

end Pnp.Karp.DomSet
