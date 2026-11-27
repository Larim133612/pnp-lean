import Pnp.Karp.SetPackVer
import Pnp.Karp.SetCoverNP

/-!
# SET PACKING ∈ NP (official definition)

The checking relation is `spkv_vres w y = true` (`Pnp/Karp/SetPackVer.lean`).

* `spkv_clash_iff`: a selected row clashes with `V` iff it has `pos` at a point set in `V`;
* `spkv_go_iff`: the main loop accepts iff the number of selected rows is at least the target,
  no selected row hits a point of `V`, and the selected rows are pairwise disjoint on the
  points `p < |V|`;
* `spkv_spLang_iff`: `SPLang w ↔ ∃ y, |y| ≤ |w| ∧ spkv_vres w y` (the certificate is the
  indicator list of the finset `S`);
* `spk_in_np`: `SPLang ∈ NP`, via `spkv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.SetPacking

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM Pnp.Karp.SetCover

/-! ## The row scan -/

theorem spkv_clash_iff (sel : Bool) : ∀ (r : List SatSym) (V : Str),
    spkv_clash sel r V = true ↔
      ∃ p < V.length, sel = true ∧ V.getD p false = true ∧ r.getD p zero = pos
  | [], V => by
    simp only [spkv_clash, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro p _ _ _ h
    simp at h
  | _ :: _, [] => by simp [spkv_clash]
  | s :: r, v :: V => by
    simp only [spkv_clash, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      spkv_clash_iff sel r V]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨p, hp, h1, h2, h3⟩)
      · exact ⟨0, by simp, h1, by simpa using h2, by simpa using h3⟩
      · exact ⟨p + 1, by simpa using hp, h1, by simpa using h2, by simpa using h3⟩
    · rintro ⟨p, hp, h1, h2, h3⟩
      rcases p with _ | p
      · exact Or.inl ⟨⟨h1, by simpa using h2⟩, by simpa using h3⟩
      · exact Or.inr ⟨p, by simpa using hp, h1, by simpa using h2, by simpa using h3⟩

/-! ## The main loop -/

theorem spkv_go_iff : ∀ (rows : List (List SatSym)) (V K y : Str),
    spkv_go V K rows y = true ↔
      K.length ≤ (∑ i ∈ Finset.range rows.length, if y.getD i false = true then 1 else 0) ∧
      ((∀ i < rows.length, y.getD i false = true → ∀ p < V.length,
          (rows.getD i []).getD p zero = pos → V.getD p false = false) ∧
        ∀ i < rows.length, ∀ j < rows.length, i ≠ j → y.getD i false = true →
          y.getD j false = true → ∀ p < V.length,
            ¬((rows.getD i []).getD p zero = pos ∧ (rows.getD j []).getD p zero = pos))
  | [], V, K, y => by
    simp [spkv_go]
  | r :: rows, V, K, y => by
    rw [spkv_go, List.length_cons, Finset.sum_range_succ']
    simp only [scv_getD_succ, scv_getD_zero]
    by_cases hc : spkv_clash (y.headD false) r V = true
    · rw [if_pos hc]
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ h2 _
      obtain ⟨p, hp, hs, hv, hr⟩ := (spkv_clash_iff _ _ _).1 hc
      have := h2 0 (by omega) (by rwa [scv_getD_zero]) p hp (by simpa using hr)
      rw [hv] at this
      exact absurd this (by decide)
    · rw [if_neg hc, spkv_go_iff rows, scv_or_length]
      refine and_congr ?_ ⟨fun ⟨h2, h3⟩ => ⟨fun i hi hy p hp hr => ?_,
        fun i hi j hj hij hyi hyj p hp => ?_⟩, fun ⟨h2, h3⟩ => ⟨fun i hi hy p hp hr => ?_,
        fun i hi j hj hij hyi hyj p hp => ?_⟩⟩
      · cases y.headD false
        · simp
        · simp only [if_true, List.length_tail]; omega
      · -- C2 for `r :: rows` from the loop invariant
        rcases i with _ | i
        · rw [scv_getD_zero] at hy
          simp only [List.getD_cons_zero] at hr
          by_contra hv
          exact hc ((spkv_clash_iff _ _ _).2 ⟨p, hp, hy, by simpa using hv, hr⟩)
        · rw [scv_getD_succ] at hy
          simp only [List.getD_cons_succ] at hr
          have := h2 i (by simpa using hi) hy p hp hr
          rw [scv_or_getD _ _ _ _ hp, Bool.or_eq_false_iff] at this
          exact this.1
      · rcases i with _ | i <;> rcases j with _ | j
        · exact absurd rfl hij
        · rintro ⟨h1, h1'⟩
          rw [scv_getD_zero] at hyi
          rw [scv_getD_succ] at hyj
          simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h1'
          have := h2 j (by simpa using hj) hyj p hp h1'
          rw [scv_or_getD _ _ _ _ hp, hyi, h1] at this
          simp at this
        · rintro ⟨h1', h1⟩
          rw [scv_getD_zero] at hyj
          rw [scv_getD_succ] at hyi
          simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h1'
          have := h2 i (by simpa using hi) hyi p hp h1'
          rw [scv_or_getD _ _ _ _ hp, hyj, h1] at this
          simp at this
        · rw [scv_getD_succ] at hyi hyj
          simpa using h3 i (by simpa using hi) j (by simpa using hj) (by omega) hyi hyj p hp
      · rw [scv_or_getD _ _ _ _ hp]
        have hv := h2 (i + 1) (by simp; omega) (by rwa [scv_getD_succ]) p hp (by simpa using hr)
        rw [hv, Bool.false_or]
        cases hs : y.headD false
        · rfl
        · simp only [Bool.true_and, decide_eq_false_iff_not]
          intro hrp
          exact h3 0 (by simp) (i + 1) (by simp; omega) (by omega) (by rwa [scv_getD_zero])
            (by rwa [scv_getD_succ]) p hp ⟨by simpa using hrp, by simpa using hr⟩
      · exact h3 (i + 1) (by simp; omega) (j + 1) (by simp; omega) (by omega)
          (by rwa [scv_getD_succ]) (by rwa [scv_getD_succ]) p hp

theorem spkv_vres_iff (w : List SatSym) (y : Str) :
    spkv_vres w y = true ↔ ∃ u kr rs, clauses w = u :: kr :: rs ∧
      kr.length ≤ (∑ i ∈ Finset.range rs.length, if y.getD i false = true then 1 else 0) ∧
      ∀ i < rs.length, ∀ j < rs.length, i ≠ j → y.getD i false = true →
        y.getD j false = true → ∀ p < u.length,
          ¬((rs.getD i []).getD p zero = pos ∧ (rs.getD j []).getD p zero = pos) := by
  unfold spkv_vres
  rcases clauses w with _ | ⟨u, _ | ⟨kr, rs⟩⟩
  · simp
  · simp
  · simp only [spkv_go_iff, List.length_replicate, xv_getD_rep, List.cons.injEq]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨u, kr, rs, ⟨rfl, rfl, rfl⟩, h1, h3⟩
    · rintro ⟨u', kr', rs', ⟨rfl, rfl, rfl⟩, h1, h3⟩
      exact ⟨h1, fun _ _ _ _ _ _ => trivial, h3⟩

/-! ## The language -/

theorem spkv_spLang_iff (w : List SatSym) :
    SPLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ spkv_vres w y = true := by
  unfold SPLang
  simp only [spkv_vres_iff]
  constructor
  · rintro ⟨u, kr, rs, hw, S, hS, hSr, hdis⟩
    let y : Str := (List.range rs.length).map (fun i => decide (i ∈ S))
    have hy : ∀ i < rs.length, y.getD i false = decide (i ∈ S) := by
      intro i hi
      rw [List.getD_eq_getElem _ _ (by simpa [y] using hi)]
      simp [y]
    refine ⟨y, ?_, u, kr, rs, hw, ?_, fun i hi j hj hij hyi hyj p hp => ?_⟩
    · have h1 := length_clauses_le w
      rw [hw] at h1
      simp only [List.length_cons] at h1
      simp only [y, List.length_map, List.length_range]
      omega
    · rw [← Finset.card_filter]
      refine le_trans hS (Finset.card_le_card fun i hi => ?_)
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hSr i hi, by rw [hy i (hSr i hi)]; simpa using hi⟩
    · rw [hy i hi] at hyi
      rw [hy j hj] at hyj
      exact hdis i (by simpa using hyi) j (by simpa using hyj) hij p hp
  · rintro ⟨y, -, u, kr, rs, hw, hcnt, hdis⟩
    refine ⟨u, kr, rs, hw, (Finset.range rs.length).filter (fun i => y.getD i false = true),
      ?_, fun i hi => ?_, fun i hi j hj hij p hp => ?_⟩
    · rw [Finset.card_filter]; exact hcnt
    · exact Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    · rw [Finset.mem_filter, Finset.mem_range] at hi hj
      exact hdis i hi.1 j hj.1 hij hi.2 hj.2 p hp

/-! ## Transfer to the official class -/

/-- **SET PACKING ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem spk_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym) SPLang := by
  classical
  have hrun := fun z => ((spkv_exec_ver z).mono (spkv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg spkv_ver) (tb 5 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg spkv_ver, 5, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => spkv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => spkv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [spkv_spLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.SetPacking
