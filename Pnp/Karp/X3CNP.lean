import Pnp.Karp.X3CVer
import Pnp.Karp.CliqueNP

/-!
# EXACT COVER BY 3-SETS ∈ NP (official definition)

The checking relation is `xv_vres w y = true` (`Pnp/Karp/X3CVer.lean`).

* `xv_rs_some`, `xv_rs_ok`: the row scan succeeds iff the row has length `|V|`, exactly `k`
  entries `pos` and (if selected) no `pos` at a covered position; the new vector is the union;
* `xv_go_iff`: the main loop accepts iff all rows are 3-sets of `[0, |V|)` and every position
  is covered exactly once by `V` and the selected rows;
* `xv_x3cLang_iff`: `X3CLang w ↔ ∃ y, |y| ≤ |w| ∧ xv_vres w y`;
* `x3c_in_np`: `X3CLang ∈ NP`, via `xv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.ThreeDM

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

/-! ## The row scan -/

theorem xv_rs_some (sel : Bool) : ∀ (r : List SatSym) (V : Str) (k : ℕ) (V' : Str),
    xv_rs sel r V k = some V' →
    r.length = V.length ∧ r.count pos = k ∧ V'.length = V.length ∧
      ∀ p, V'.getD p false = (V.getD p false || (sel && decide (r.getD p zero = pos))) ∧
        (sel && decide (r.getD p zero = pos) && V.getD p false) = false
  | [], [], k, V', h => by
    simp only [xv_rs] at h; split_ifs at h with hk; cases h; subst hk; simp
  | [], _ :: _, _, _, h => by simp [xv_rs] at h
  | _ :: _, [], _, _, h => by simp [xv_rs] at h
  | s :: r, v :: V, k, V', h => by
    simp only [xv_rs] at h
    by_cases hs : s = pos
    · subst hs
      rw [if_pos rfl] at h
      split_ifs at h with hk hsv
      obtain ⟨V'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨a1, a2, a3, a4⟩ := xv_rs_some sel r V (k - 1) V'' h1
      refine ⟨by simp [a1], by simp [a2]; omega, by simp [a3], fun p => ?_⟩
      rcases p with _ | p
      · simp only [List.getD_cons_zero, decide_true, Bool.and_true]
        cases sel <;> cases v <;> simp_all
      · simpa using a4 p
    · rw [if_neg hs] at h
      obtain ⟨V'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨a1, a2, a3, a4⟩ := xv_rs_some sel r V k V'' h1
      refine ⟨by simp [a1], by simp [a2, hs], by simp [a3], fun p => ?_⟩
      rcases p with _ | p
      · simp [hs]
      · simpa using a4 p

theorem xv_rs_ok (sel : Bool) : ∀ (r : List SatSym) (V : Str) (k : ℕ),
    r.length = V.length → r.count pos = k →
    (∀ p, (sel && decide (r.getD p zero = pos) && V.getD p false) = false) →
    ∃ V', xv_rs sel r V k = some V'
  | [], [], k, _, hc, _ => by subst hc; simp [xv_rs]
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | s :: r, v :: V, k, hl, hc, hp => by
    have hl' : r.length = V.length := by simpa using hl
    have hp' : ∀ p, (sel && decide (r.getD p zero = pos) && V.getD p false) = false :=
      fun p => by simpa using hp (p + 1)
    simp only [xv_rs]
    by_cases hs : s = pos
    · subst hs
      have h0 := hp 0
      simp only [List.getD_cons_zero, decide_true, Bool.and_true] at h0
      simp only [List.count_cons, beq_self_eq_true, if_true] at hc
      obtain ⟨V', h⟩ := xv_rs_ok sel r V (k - 1) hl' (by omega) hp'
      rw [if_pos rfl, if_neg (by omega), if_neg (by simp [h0]), h]
      exact ⟨_, rfl⟩
    · have hc' : r.count pos = k := by simpa [List.count_cons, hs] using hc
      obtain ⟨V', h⟩ := xv_rs_ok sel r V k hl' hc' hp'
      rw [if_neg hs, h]
      exact ⟨_, rfl⟩

/-! ## The main loop -/

theorem xv_all_iff : ∀ V : Str, V.all id = true ↔ ∀ p < V.length, V.getD p false = true
  | [] => by simp
  | v :: V => by
    rw [List.all_cons, Bool.and_eq_true, xv_all_iff V]
    constructor
    · rintro ⟨h1, h2⟩ p hp
      rcases p with _ | p
      · simpa using h1
      · simpa using h2 p (by simpa using hp)
    · intro h
      exact ⟨by simpa using h 0 (by simp), fun p hp => by simpa using h (p + 1) (by simpa using hp)⟩

theorem xv_go_iff : ∀ (rows : List (List SatSym)) (V y : Str),
    xv_go V rows y = true ↔ (∀ r ∈ rows, r.length = V.length ∧ r.count pos = 3) ∧
      ∀ p < V.length, (if V.getD p false then 1 else 0) + covC rows y p = 1
  | [], V, y => by
    simp only [xv_go, xv_all_iff, List.not_mem_nil, false_imp_iff, implies_true, true_and,
      covC, add_zero]
    refine forall₂_congr fun p _ => ?_
    cases V.getD p false <;> simp
  | r :: rows, V, y => by
    simp only [xv_go, covC]
    constructor
    · intro h
      rcases hs : xv_rs (y.headD false) r V 3 with _ | V'
      · rw [hs] at h; simp at h
      · rw [hs] at h
        obtain ⟨a1, a2, a3, a4⟩ := xv_rs_some _ r V 3 V' hs
        obtain ⟨b1, b2⟩ := (xv_go_iff rows V' y.tail).1 h
        refine ⟨fun r' hr' => ?_, fun p hp => ?_⟩
        · rcases List.mem_cons.1 hr' with rfl | hr'
          · exact ⟨a1, a2⟩
          · rw [← a3]; exact b1 r' hr'
        · have h1 := b2 p (by omega)
          obtain ⟨c1, c2⟩ := a4 p
          rw [c1] at h1
          revert c2 h1
          cases V.getD p false <;> cases y.headD false <;>
            cases decide (r.getD p zero = pos) <;> simp
    · rintro ⟨h1, h2⟩
      obtain ⟨hl, hc⟩ := h1 r (by simp)
      have hnc : ∀ p, (y.headD false && decide (r.getD p zero = pos) && V.getD p false) = false := by
        intro p
        by_cases hp : p < V.length
        · have := h2 p hp
          revert this
          cases V.getD p false <;> cases y.headD false <;>
            cases decide (r.getD p zero = pos) <;> simp
        · have : V.getD p false = false := by
            rw [List.getD_eq_default _ _ (by omega)]
          rw [this]; simp
      obtain ⟨V', hs⟩ := xv_rs_ok _ r V 3 hl hc hnc
      obtain ⟨a1, a2, a3, a4⟩ := xv_rs_some _ r V 3 V' hs
      rw [hs]
      refine (xv_go_iff rows V' y.tail).2 ⟨fun r' hr' => ?_, fun p hp => ?_⟩
      · rw [a3]; exact h1 r' (by simp [hr'])
      · have := h2 p (by omega)
        obtain ⟨c1, c2⟩ := a4 p
        rw [c1]
        revert c2 this
        cases V.getD p false <;> cases y.headD false <;>
          cases decide (r.getD p zero = pos) <;> simp

theorem xv_getD_rep (n p : ℕ) : (List.replicate n false).getD p false = false := by
  by_cases h : p < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

theorem xv_vres_iff (w : List SatSym) (y : Str) :
    xv_vres w y = true ↔ ∃ u rs, clauses w = u :: rs ∧
      (∀ r ∈ rs, r.length = u.length ∧ r.count pos = 3) ∧ ∀ p < u.length, covC rs y p = 1 := by
  unfold xv_vres
  rcases clauses w with _ | ⟨u, rs⟩
  · simp
  · simp only [xv_go_iff, List.length_replicate, xv_getD_rep, Bool.false_eq_true, if_false,
      zero_add, List.cons.injEq]
    constructor
    · intro h; exact ⟨u, rs, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨u', rs', ⟨rfl, rfl⟩, h⟩; exact h

theorem xv_covC_take : ∀ (rs : List (List SatSym)) (y : List Bool) (p : ℕ),
    covC rs (y.take rs.length) p = covC rs y p
  | [], y, p => by simp [covC]
  | r :: rs, [], p => by simp [covC]
  | r :: rs, b :: y, p => by
    simp [covC, xv_covC_take rs y p]

theorem xv_x3cLang_iff (w : List SatSym) :
    X3CLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ xv_vres w y = true := by
  unfold X3CLang
  simp only [xv_vres_iff]
  constructor
  · rintro ⟨u, rs, hw, hr, y, hy⟩
    refine ⟨y.take rs.length, ?_, u, rs, hw, hr, fun p hp => by rw [xv_covC_take, hy p hp]⟩
    have h1 := length_clauses_le w
    rw [hw] at h1
    simp only [List.length_cons] at h1
    simp only [List.length_take]
    omega
  · rintro ⟨y, -, u, rs, hw, hr, hy⟩
    exact ⟨u, rs, hw, hr, y, hy⟩

/-! ## Transfer to the official class -/

/-- **EXACT COVER BY 3-SETS ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem x3c_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      X3CLang := by
  classical
  have hrun := fun z => ((xv_exec_ver z).mono (xv_Tver_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg xv_ver) (tb 5 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg xv_ver, 5, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => xv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => xv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [xv_x3cLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.ThreeDM
