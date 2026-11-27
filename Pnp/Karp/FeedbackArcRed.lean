import Pnp.Karp.FeedbackArc

/-!
# The reduction FEEDBACK VERTEX SET ≤ FEEDBACK ARC SET (correctness)

`far_arc` classifies the arcs of `splitRows rows`: `2v → 2v+1`, and `2u+1 → 2v` for the arcs
`u → v` of `rows`.  A feedback vertex set `F` gives the feedback arc set
`{(2v, 2v+1) | v ∈ F}` (`far_fwd`, walks from out vertices project, `far_proj`); a feedback arc
set `F` gives `{p.2 / 2 | p ∈ F} ∩ [0, n)` (`far_bwd`, arcs lift to two-step walks).
-/

namespace Pnp.Karp.FeedbackArc

open Pnp.CookLevin SatSym Pnp.Karp.Clique

theorem far_pairs_length {β : Type} (g h : ℕ → β) (n : ℕ) :
    ((List.range n).flatMap fun v => [g v, h v]).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; ring

theorem far_pairs_get {β : Type} (g h : ℕ → β) (n : ℕ) (d : β) :
    ∀ v < n, ((List.range n).flatMap fun v => [g v, h v]).getD (2 * v) d = g v ∧
      ((List.range n).flatMap fun v => [g v, h v]).getD (2 * v + 1) d = h v := by
  induction n with
  | zero => intro v hv; omega
  | succ n ih =>
    intro v hv
    rw [List.range_succ, List.flatMap_append]
    have hl := far_pairs_length g h n
    rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
    · obtain ⟨h1, h2⟩ := ih v hv
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD, h1,
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD, h2]
      exact ⟨rfl, rfl⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]
      simp

theorem far_inRow_entry (v c : ℕ) : (inRow v).getD c zero = pos ↔ c = 2 * v + 1 := by
  unfold inRow
  rw [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy c (2 * v + 1) with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega)]; simp [h]; omega
  · rw [List.getElem?_append_right (by simp)]; simp
  · rw [List.getElem?_append_right (by simp; omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp; omega

theorem far_pairsZ (l : List SatSym) :
    ∀ j, (l.flatMap fun e => [e, zero]).getD (2 * j) zero = l.getD j zero ∧
      (l.flatMap fun e => [e, zero]).getD (2 * j + 1) zero = zero := by
  induction l with
  | nil => intro j; simp
  | cons e l ih =>
    intro j
    rcases j with _ | j
    · simp
    · have := ih j
      simp only [List.flatMap_cons, List.cons_append, List.nil_append] at this ⊢
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      simp only [List.getD_cons_succ]; exact this

theorem far_outRow_even (r : List SatSym) (v j : ℕ) :
    (outRow r v).getD (2 * j) zero = pos ↔ j ≠ v ∧ r.getD j zero = pos := by
  unfold outRow
  rw [(far_pairsZ _ j).1, List.getD_eq_getElem?_getD, List.getElem?_set,
    List.getD_eq_getElem?_getD]
  by_cases h : v = j
  · subst h
    by_cases hl : v < r.length <;> simp [hl]
  · simp [h, Ne.symm h]

theorem far_outRow_odd (r : List SatSym) (v j : ℕ) :
    (outRow r v).getD (2 * j + 1) zero ≠ pos := by
  unfold outRow; rw [(far_pairsZ _ j).2]; decide

theorem far_length (rows : List (List SatSym)) : (splitRows rows).length = 2 * rows.length :=
  far_pairs_length _ _ _

theorem far_row_even (rows : List (List SatSym)) (v : ℕ) (hv : v < rows.length) :
    (splitRows rows).getD (2 * v) [] = inRow v :=
  (far_pairs_get _ _ _ _ v hv).1

theorem far_row_odd (rows : List (List SatSym)) (v : ℕ) (hv : v < rows.length) :
    (splitRows rows).getD (2 * v + 1) [] = outRow (rows.getD v []) v :=
  (far_pairs_get _ _ _ _ v hv).2

/-- Classification of the arcs of the split digraph. -/
theorem far_arc (rows : List (List SatSym)) (a b : ℕ) (ha : a < 2 * rows.length)
    (hb : b < 2 * rows.length) (he : ((splitRows rows).getD a []).getD b zero = pos) :
    (∃ v < rows.length, a = 2 * v ∧ b = 2 * v + 1) ∨
      (∃ u v, u < rows.length ∧ v < rows.length ∧ u ≠ v ∧
        (rows.getD u []).getD v zero = pos ∧ a = 2 * u + 1 ∧ b = 2 * v) := by
  obtain ⟨u, rfl | rfl⟩ := Nat.even_or_odd' a
  · rw [far_row_even rows u (by omega), far_inRow_entry] at he
    exact Or.inl ⟨u, by omega, rfl, he⟩
  · rw [far_row_odd rows u (by omega)] at he
    obtain ⟨v, rfl | rfl⟩ := Nat.even_or_odd' b
    · rw [far_outRow_even] at he
      exact Or.inr ⟨u, v, by omega, by omega, Ne.symm he.1, he.2, rfl, rfl⟩
    · exact absurd he (far_outRow_odd _ _ _)

theorem far_arc_in (rows : List (List SatSym)) (v : ℕ) (hv : v < rows.length) :
    ((splitRows rows).getD (2 * v) []).getD (2 * v + 1) zero = pos := by
  rw [far_row_even rows v hv, far_inRow_entry]

theorem far_arc_out (rows : List (List SatSym)) (u v : ℕ) (hu : u < rows.length)
    (huv : u ≠ v) (he : (rows.getD u []).getD v zero = pos) :
    ((splitRows rows).getD (2 * u + 1) []).getD (2 * v) zero = pos := by
  rw [far_row_odd rows u hu, far_outRow_even]; exact ⟨Ne.symm huv, he⟩

/-- Walks from an out vertex project to walks of the original digraph. -/
theorem far_proj (rows : List (List SatSym)) (F : Finset ℕ) (u : ℕ) (hu : u < rows.length)
    (huF : u ∉ F) (b : ℕ)
    (h : Relation.TransGen (arcF (splitRows rows) (F.image fun v => (2 * v, 2 * v + 1)))
      (2 * u + 1) b) :
    (∀ v, b = 2 * v + 1 → v ∉ F ∧ Relation.TransGen (FeedbackVS.arcOut rows F) u v) ∧
      (∀ v, b = 2 * v → ∃ w, w ∉ F ∧ Relation.ReflTransGen (FeedbackVS.arcOut rows F) u w ∧
        w < rows.length ∧ v < rows.length ∧ w ≠ v ∧ (rows.getD w []).getD v zero = pos) := by
  induction h with
  | single hs =>
    obtain ⟨ha, hb, _, he, _⟩ := hs
    rw [far_length] at ha hb
    rcases far_arc rows _ _ ha hb he with ⟨v, _, h1, _⟩ | ⟨u', v, hu', hv, huv, he', h1, rfl⟩
    · omega
    · have : u' = u := by omega
      subst this
      refine ⟨fun v' h => by omega, fun v' h => ?_⟩
      have : v' = v := by omega
      subst this
      exact ⟨u', huF, Relation.ReflTransGen.refl, hu', hv, huv, he'⟩
  | tail _ hs ih =>
    rename_i b c _
    obtain ⟨ha, hb, _, he, hnF⟩ := hs
    rw [far_length] at ha hb
    rcases far_arc rows _ _ ha hb he with ⟨v, hv, rfl, rfl⟩ | ⟨w, v, hw, hv, hwv, he', rfl, rfl⟩
    · obtain ⟨w, hwF, hr, hw, _, hwv, he'⟩ := ih.2 v rfl
      have hvF : v ∉ F := fun hv' => hnF (Finset.mem_image.2 ⟨v, hv', rfl⟩)
      refine ⟨fun v' h => ?_, fun v' h => by omega⟩
      have : v' = v := by omega
      subst this
      exact ⟨hvF, Relation.TransGen.tail' hr ⟨hw, hv, hwF, hvF, hwv, he'⟩⟩
    · obtain ⟨hwF, _⟩ := ih.1 w rfl
      refine ⟨fun v' h => by omega, fun v' h => ?_⟩
      have : v' = v := by omega
      subst this
      exact ⟨w, hwF, (ih.1 w rfl).2.to_reflTransGen, hw, hv, hwv, he'⟩

theorem far_fwd (rows : List (List SatSym)) (F : Finset ℕ)
    (hF : ∀ u, ¬ Relation.TransGen (FeedbackVS.arcOut rows F) u u) (a : ℕ) :
    ¬ Relation.TransGen (arcF (splitRows rows) (F.image fun v => (2 * v, 2 * v + 1))) a a := by
  set R := arcF (splitRows rows) (F.image fun v => (2 * v, 2 * v + 1))
  -- reduce to an odd vertex on the cycle
  have hodd : ∀ u, ¬ Relation.TransGen R (2 * u + 1) (2 * u + 1) := by
    intro u h
    have hlast : ∃ c, R c (2 * u + 1) := by
      cases h with
      | single h => exact ⟨_, h⟩
      | tail _ h => exact ⟨_, h⟩
    obtain ⟨c, hc⟩ := hlast
    obtain ⟨hcl, hbl, _, he, hnF⟩ := hc
    rw [far_length] at hcl hbl
    rcases far_arc rows _ _ hcl hbl he with ⟨v, hv, rfl, h2⟩ | ⟨_, _, _, _, _, _, _, h2⟩
    · have : v = u := by omega
      subst this
      have huF : v ∉ F := fun hv' => hnF (Finset.mem_image.2 ⟨v, hv', rfl⟩)
      exact hF v ((far_proj rows F v hv huF _ h).1 v rfl).2
    · omega
  intro h
  obtain ⟨u, rfl | rfl⟩ := Nat.even_or_odd' a
  · obtain ⟨c, h1, h2⟩ := Relation.TransGen.head'_iff.1 h
    · obtain ⟨hal, hcl, _, he, _⟩ := id h1
      rw [far_length] at hal hcl
      rcases far_arc rows _ _ hal hcl he with ⟨v, _, h3, rfl⟩ | ⟨_, _, _, _, _, _, h3, _⟩
      · have : v = u := by omega
        subst this
        exact hodd v (Relation.TransGen.tail' h2 h1)
      · omega
  · exact hodd u h

theorem far_bwd (rows : List (List SatSym)) (F : Finset (ℕ × ℕ))
    (hF : ∀ u, ¬ Relation.TransGen (arcF (splitRows rows) F) u u) (u : ℕ) :
    ¬ Relation.TransGen (FeedbackVS.arcOut rows
      ((F.image fun p => p.2 / 2).filter (· < rows.length))) u u := by
  set V := (F.image fun p => p.2 / 2).filter (· < rows.length)
  have hnot : ∀ p ∈ F, p.2 / 2 < rows.length → p.2 / 2 ∈ V := fun p hp hl =>
    Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨p, hp, rfl⟩, hl⟩
  have step : ∀ a b, FeedbackVS.arcOut rows V a b →
      Relation.TransGen (arcF (splitRows rows) F) (2 * a + 1) (2 * b + 1) := by
    rintro a b ⟨ha, hb, _, hbV, hab, he⟩
    refine Relation.TransGen.head ⟨by rw [far_length]; omega, by rw [far_length]; omega, by omega,
      far_arc_out rows a b ha hab he, fun hp => hbV ?_⟩ (Relation.TransGen.single
        ⟨by rw [far_length]; omega, by rw [far_length]; omega, by omega,
          far_arc_in rows b hb, fun hp => hbV ?_⟩)
    · have := hnot _ hp (by simp only; omega); simpa using this
    · have := hnot _ hp (by simp only; omega)
      simp only at this; rwa [show (2 * b + 1) / 2 = b by omega] at this
  have key : ∀ v, Relation.TransGen (FeedbackVS.arcOut rows V) u v →
      Relation.TransGen (arcF (splitRows rows) F) (2 * u + 1) (2 * v + 1) := by
    intro v h
    induction h with
    | single h => exact step _ _ h
    | tail _ h ih => exact ih.trans (step _ _ h)
  exact fun h => hF _ (key u h)

theorem far_sep_split (rows : List (List SatSym)) (h : ∀ r ∈ rows, sep ∉ r) :
    ∀ r ∈ splitRows rows, sep ∉ r := by
  intro r hr
  simp only [splitRows, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false] at hr
  obtain ⟨v, hv, rfl | rfl⟩ := hr
  · simp [inRow]
  · simp only [outRow, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false, not_exists,
      not_and]
    intro e he hs
    rcases hs with rfl | hs
    · rcases List.mem_or_eq_of_mem_set he with he | he
      · rw [List.getD_eq_getElem _ _ hv] at he
        exact h _ (List.getElem_mem hv) he
      · cases he
    · cases hs

theorem fvs_iff_fas (x : List SatSym) : FeedbackVS.FVSLang x ↔ FASLang (splitW x) := by
  unfold FeedbackVS.FVSLang FASLang splitW
  rcases hc : clauses x with _ | ⟨kr, rows⟩
  · simp only
    rw [show clauses ([] : List SatSym) = [] from rfl]
  · simp only
    have hsep := sep_not_mem_clauses x
    rw [hc] at hsep
    rw [Pnp.Karp.Clique.clauses_flatMap _ (by
      intro c hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact hsep _ (List.mem_cons_self ..)
      · exact far_sep_split rows (fun r hr => hsep r (List.mem_cons_of_mem _ hr)) c hc')]
    simp only
    constructor
    · rintro ⟨F, hk, _, hac⟩
      exact ⟨F.image fun v => (2 * v, 2 * v + 1), Finset.card_image_le.trans hk,
        far_fwd rows F hac⟩
    · rintro ⟨F, hk, hac⟩
      exact ⟨_, (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans hk),
        fun i hi => (Finset.mem_filter.1 hi).2, far_bwd rows F hac⟩

end Pnp.Karp.FeedbackArc
