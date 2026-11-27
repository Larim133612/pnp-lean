import Pnp.Karp.SetCoverVer
import Pnp.Karp.X3CNP

/-!
# SET COVER ∈ NP (official definition)

The checking relation is `scv_vres w y = true` (`Pnp/Karp/SetCoverVer.lean`).

* `scv_or_getD`: the row scan ORs the selected row into the covered vector;
* `scv_go_iff`: the main loop accepts iff the number of selected rows is at most the budget
  and every position of `V` is covered by `V` or by a selected row;
* `scv_scLang_iff`: `SCLang w ↔ ∃ y, |y| ≤ |w| ∧ scv_vres w y` (the certificate is the
  indicator list of the finset `S`);
* `sc_in_np`: `SCLang ∈ NP`, via `scv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.SetCover

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM

/-! ## The row scan -/

theorem scv_or_cons (sel : Bool) (s : SatSym) (r : List SatSym) (v : Bool) (V : Str) :
    scv_or sel (s :: r) (v :: V) = (v || (sel && decide (s = pos))) :: scv_or sel r V := by
  simp [scv_or, scv_pre]

theorem scv_or_getD (sel : Bool) : ∀ (r : List SatSym) (V : Str) (p : ℕ), p < V.length →
    (scv_or sel r V).getD p false = (V.getD p false || (sel && decide (r.getD p zero = pos)))
  | [], V, p, _ => by simp [scv_or, scv_pre]
  | _ :: _, [], p, hp => by simp at hp
  | s :: r, v :: V, p, hp => by
    rw [scv_or_cons]
    rcases p with _ | p
    · simp
    · simpa using scv_or_getD sel r V p (by simpa using hp)

theorem scv_getD_succ (y : Str) (i : ℕ) : y.getD (i + 1) false = y.tail.getD i false := by
  cases y <;> simp

theorem scv_getD_zero (y : Str) : y.getD 0 false = y.headD false := by
  cases y <;> simp

/-! ## The main loop -/

theorem scv_go_iff : ∀ (rows : List (List SatSym)) (V K y : Str),
    scv_go V K rows y = true ↔
      (∑ i ∈ Finset.range rows.length, if y.getD i false = true then 1 else 0) ≤ K.length ∧
      ∀ p < V.length, V.getD p false = true ∨
        ∃ i < rows.length, y.getD i false = true ∧ (rows.getD i []).getD p zero = pos
  | [], V, K, y => by
    simp only [scv_go, xv_all_iff, List.length_nil, Finset.range_zero, Finset.sum_empty,
      zero_le, true_and, Nat.not_lt_zero, false_and, exists_false, or_false]
  | r :: rows, V, K, y => by
    rw [scv_go, List.length_cons, Finset.sum_range_succ']
    simp only [scv_getD_succ, scv_getD_zero]
    have hcov : ∀ p < V.length, ((V.getD p false = true ∨ ∃ i < rows.length + 1,
        y.getD i false = true ∧ ((r :: rows).getD i []).getD p zero = pos) ↔
        ((scv_or (y.headD false) r V).getD p false = true ∨ ∃ i < rows.length,
          y.tail.getD i false = true ∧ (rows.getD i []).getD p zero = pos)) := by
      intro p hp
      rw [scv_or_getD _ _ _ _ hp]
      constructor
      · rintro (h | ⟨i, hi, h1, h2⟩)
        · left; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; exact Or.inl h
        · rcases i with _ | i
          · left
            rw [scv_getD_zero] at h1
            simp only [List.getD_cons_zero] at h2
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            exact Or.inr ⟨h1, h2⟩
          · right
            exact ⟨i, by omega, by rwa [scv_getD_succ] at h1, by simpa using h2⟩
      · rintro (h | ⟨i, hi, h1, h2⟩)
        · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with h | ⟨h1, h2⟩
          · left; exact h
          · right; exact ⟨0, by omega, by rwa [scv_getD_zero], by simpa using h2⟩
        · right; exact ⟨i + 1, by omega, by rwa [scv_getD_succ], by simpa using h2⟩
    by_cases hc : (y.headD false && K.isEmpty) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
      obtain ⟨h1, rfl⟩ := hc
      rw [h1]
      simp only [if_true, List.length_nil]
      constructor
      · intro h; exact absurd h Bool.false_ne_true
      · rintro ⟨h, -⟩; omega
    · rw [if_neg hc, scv_go_iff rows, scv_or_length]
      refine and_congr ?_ (forall₂_congr fun p hp => (hcov p hp).symm)
      rcases hb : y.headD false with _ | _
      · simp
      · rw [hb] at hc
        simp only [Bool.true_and, List.isEmpty_iff] at hc
        simp only [if_true, List.length_tail]
        have : 0 < K.length := List.length_pos_iff.2 hc
        omega

theorem scv_vres_iff (w : List SatSym) (y : Str) :
    scv_vres w y = true ↔ ∃ u kr rs, clauses w = u :: kr :: rs ∧
      (∑ i ∈ Finset.range rs.length, if y.getD i false = true then 1 else 0) ≤ kr.length ∧
      ∀ p < u.length, ∃ i < rs.length, y.getD i false = true ∧ (rs.getD i []).getD p zero = pos := by
  unfold scv_vres
  rcases clauses w with _ | ⟨u, _ | ⟨kr, rs⟩⟩
  · simp
  · simp
  · simp only [scv_go_iff, List.length_replicate, xv_getD_rep, Bool.false_eq_true, false_or,
      List.cons.injEq]
    constructor
    · intro h; exact ⟨u, kr, rs, ⟨rfl, rfl, rfl⟩, h⟩
    · rintro ⟨u', kr', rs', ⟨rfl, rfl, rfl⟩, h⟩; exact h

/-! ## The language -/

theorem scv_scLang_iff (w : List SatSym) :
    SCLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ scv_vres w y = true := by
  unfold SCLang
  simp only [scv_vres_iff]
  constructor
  · rintro ⟨u, kr, rs, hw, S, hS, hSr, hcov⟩
    let y : Str := (List.range rs.length).map (fun i => decide (i ∈ S))
    have hy : ∀ i < rs.length, y.getD i false = decide (i ∈ S) := by
      intro i hi
      rw [List.getD_eq_getElem _ _ (by simpa [y] using hi)]
      simp [y]
    refine ⟨y, ?_, u, kr, rs, hw, ?_, fun p hp => ?_⟩
    · have h1 := length_clauses_le w
      rw [hw] at h1
      simp only [List.length_cons] at h1
      simp only [y, List.length_map, List.length_range]
      omega
    · rw [← Finset.card_filter]
      refine le_trans (Finset.card_le_card fun i hi => ?_) hS
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [hy i hi.1] at hi
      simpa using hi.2
    · obtain ⟨i, hi, h⟩ := hcov p hp
      exact ⟨i, hSr i hi, by rw [hy i (hSr i hi)]; simpa using hi, h⟩
  · rintro ⟨y, -, u, kr, rs, hw, hcnt, hcov⟩
    refine ⟨u, kr, rs, hw, (Finset.range rs.length).filter (fun i => y.getD i false = true),
      ?_, fun i hi => ?_, fun p hp => ?_⟩
    · rw [Finset.card_filter]; exact hcnt
    · exact Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    · obtain ⟨i, hi, h1, h2⟩ := hcov p hp
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, h1⟩, h2⟩

/-! ## Transfer to the official class -/

/-- **SET COVER ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem sc_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym) SCLang := by
  classical
  have hrun := fun z => ((scv_exec_ver z).mono (scv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg scv_ver) (tb 5 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg scv_ver, 5, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => scv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => scv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [scv_scLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.SetCover
