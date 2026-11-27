import Pnp.Karp.MaxCutVer
import Pnp.Karp.CliqueNP

/-!
# MAX CUT ∈ NP (official definition)

The checking relation is `mcv_vres w y = true` (`Pnp/Karp/MaxCutVer.lean`): the certificate `y`
puts vertex `v` on the side `y.getD v false`.

* `mcv_rowCnt_eq`: the count of one row as a `Finset` cardinality;
* `mcv_vres_eq`: the verifier accepts iff `|kr| ≤ cutVal rows (y.getD · false)`;
* `mcv_lang_iff`: `MCLang w ↔ ∃ y, |y| ≤ |w|^2 ∧ mcv_vres w y`;
* `mc_in_np`: `MCLang ∈ NP`, via `mcv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.MaxCut

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics of the main loop -/

theorem mcv_isPos_iff (s : SatSym) : isPos s = true ↔ s = pos := by
  cases s <;> simp [isPos]

theorem mcv_rowCnt_eq (b : Bool) : ∀ (r : List SatSym) (Y : Str),
    mcv_rowCnt b r Y = ((Finset.range Y.length).filter
      fun j => r.getD j zero = pos ∧ b ≠ Y.getD j false).card
  | [], Y => by simp [mcv_rowCnt]
  | s :: r, [] => by
    rw [mcv_rowCnt, List.tail_nil, mcv_rowCnt_eq b r []]
    simp [mcv_inc]
  | s :: r, x :: Y => by
    rw [mcv_rowCnt, List.tail_cons, mcv_rowCnt_eq b r Y, Finset.card_filter, Finset.card_filter,
      List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, mcv_inc]
    rw [Nat.add_comm]
    congr 1
    cases s <;> cases x <;> cases b <;> simp [isPos]

theorem mcv_headD_drop (y : Str) (m : ℕ) : (y.drop m).headD false = y.getD m false := by
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

theorem mcv_rowCnt_cut (L : List (List SatSym)) (S : ℕ → Bool) (m : ℕ) (hm : m < L.length) :
    mcv_rowCnt (S m) L[m] ((List.range m).map S) = rowCut L S m := by
  rw [mcv_rowCnt_eq, rowCut, List.length_map, List.length_range, List.getD_eq_getElem _ _ hm]
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [Finset.mem_range] at hj
  rw [List.getD_eq_getElem ((List.range m).map S) false (by simpa using hj), List.getElem_map,
    List.getElem_range]

theorem mcv_go_eq (K : ℕ) (L : List (List SatSym)) (y : Str) :
    ∀ (n m c : ℕ), L.length - m = n →
    mcv_go K (L.drop m) (y.drop m) ((List.range m).map (fun i => y.getD i false)).reverse c =
      decide (K ≤ c + ∑ i ∈ Finset.Ico m L.length, rowCut L (fun i => y.getD i false) i)
  | 0, m, c, h => by
    rw [List.drop_eq_nil_of_le (by omega), Finset.Ico_eq_empty_of_le (by omega)]
    simp [mcv_go]
  | n + 1, m, c, h => by
    have hm : m < L.length := by omega
    have hc := mcv_rowCnt_cut L (fun i => y.getD i false) m hm
    rw [List.drop_eq_getElem_cons hm, mcv_go, List.reverse_reverse, mcv_headD_drop,
      List.tail_drop, hc, Finset.sum_eq_sum_Ico_succ_bot hm]
    have e : y.getD m false :: ((List.range m).map (fun i => y.getD i false)).reverse =
        ((List.range (m + 1)).map (fun i => y.getD i false)).reverse := by
      rw [List.range_succ, List.map_append, List.reverse_append]; rfl
    rw [e, mcv_go_eq K L y n (m + 1) _ (by omega), Nat.add_assoc]

theorem mcv_vres_eq (kr : List SatSym) (rows : List (List SatSym)) (y : Str) :
    mcv_go kr.length rows y [] 0 = decide (kr.length ≤ cutVal rows (fun i => y.getD i false)) := by
  have h := mcv_go_eq kr.length rows y _ 0 0 rfl
  simp only [List.drop_zero, List.range_zero, List.map_nil, List.reverse_nil, Nat.zero_add] at h
  rw [h, cutVal, Finset.range_eq_Ico]

theorem mcv_cutVal_congr (rows : List (List SatSym)) (s s' : ℕ → Bool)
    (h : ∀ i < rows.length, s i = s' i) : cutVal rows s = cutVal rows s' := by
  unfold cutVal
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  unfold rowCut
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [Finset.mem_range] at hj
  rw [h i hi, h j (by omega)]

/-! ## Short certificates -/

theorem mcv_lang_iff (w : List SatSym) :
    MCLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ mcv_vres w y = true := by
  have hcl := length_clauses_le w
  unfold MCLang mcv_vres
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · simp
  rw [hcw] at hcl
  simp only [mcv_vres_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(List.range rows.length).map s, ?_, ?_⟩
    · simp only [List.length_map, List.length_range]
      simp only [List.length_cons] at hcl
      exact le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    · rw [mcv_cutVal_congr rows _ s (fun i hi => by
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
          List.getElem_range])]
      exact hs
  · rintro ⟨y, -, h⟩
    exact ⟨_, h⟩

/-! ## Transfer to the official class -/

/-- **MAX CUT ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem mc_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      MCLang := by
  classical
  have hrun := fun z => ((mcv_exec_ver z).mono (mcv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg mcv_ver) (tb 6 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg mcv_ver, 6, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => mcv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => mcv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [mcv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.MaxCut
