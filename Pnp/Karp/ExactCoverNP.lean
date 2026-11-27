import Pnp.Karp.ExactCoverVer
import Pnp.Karp.CliqueNP

/-!
# EXACT COVER ∈ NP (official definition)

The checking relation is `ecv_vres w y = true` (`Pnp/Karp/ExactCoverVer.lean`).

* `ecv_rs_some`, `ecv_rs_ok`: the row scan succeeds iff the row has length `|V|` and (if
  selected) no `pos` at a covered position; the new vector is the union;
* `ecv_go_iff`: the main loop accepts iff all rows have length `|V|` and every position is
  covered exactly once by `V` and the selected rows;
* `ecv_ecLang_iff`: `ECLang w ↔ ∃ y, |y| ≤ |w| ∧ ecv_vres w y`;
* `ec_in_np`: `ECLang ∈ NP`, via `ecv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.ExactCover

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM

/-! ## The row scan -/

theorem ecv_rs_some (sel : Bool) : ∀ (r : List SatSym) (V : Str) (V' : Str),
    ecv_rs sel r V = some V' →
    r.length = V.length ∧ V'.length = V.length ∧
      ∀ p, V'.getD p false = (V.getD p false || (sel && decide (r.getD p zero = pos))) ∧
        (sel && decide (r.getD p zero = pos) && V.getD p false) = false
  | [], [], V', h => by
    simp only [ecv_rs] at h; cases h; simp
  | [], _ :: _, _, h => by simp [ecv_rs] at h
  | _ :: _, [], _, h => by simp [ecv_rs] at h
  | s :: r, v :: V, V', h => by
    simp only [ecv_rs] at h
    by_cases hs : s = pos
    · subst hs
      rw [if_pos rfl] at h
      split_ifs at h with hsv
      obtain ⟨V'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨a1, a3, a4⟩ := ecv_rs_some sel r V V'' h1
      refine ⟨by simp [a1], by simp [a3], fun p => ?_⟩
      rcases p with _ | p
      · simp only [List.getD_cons_zero, decide_true, Bool.and_true]
        cases sel <;> cases v <;> simp_all
      · simpa using a4 p
    · rw [if_neg hs] at h
      obtain ⟨V'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨a1, a3, a4⟩ := ecv_rs_some sel r V V'' h1
      refine ⟨by simp [a1], by simp [a3], fun p => ?_⟩
      rcases p with _ | p
      · simp [hs]
      · simpa using a4 p

theorem ecv_rs_ok (sel : Bool) : ∀ (r : List SatSym) (V : Str),
    r.length = V.length →
    (∀ p, (sel && decide (r.getD p zero = pos) && V.getD p false) = false) →
    ∃ V', ecv_rs sel r V = some V'
  | [], [], _, _ => by simp [ecv_rs]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | s :: r, v :: V, hl, hp => by
    have hl' : r.length = V.length := by simpa using hl
    have hp' : ∀ p, (sel && decide (r.getD p zero = pos) && V.getD p false) = false :=
      fun p => by simpa using hp (p + 1)
    simp only [ecv_rs]
    by_cases hs : s = pos
    · subst hs
      have h0 := hp 0
      simp only [List.getD_cons_zero, decide_true, Bool.and_true] at h0
      obtain ⟨V', h⟩ := ecv_rs_ok sel r V hl' hp'
      rw [if_pos rfl, if_neg (by simp [h0]), h]
      exact ⟨_, rfl⟩
    · obtain ⟨V', h⟩ := ecv_rs_ok sel r V hl' hp'
      rw [if_neg hs, h]
      exact ⟨_, rfl⟩

/-! ## The main loop -/

theorem ecv_all_iff : ∀ V : Str, V.all id = true ↔ ∀ p < V.length, V.getD p false = true
  | [] => by simp
  | v :: V => by
    rw [List.all_cons, Bool.and_eq_true, ecv_all_iff V]
    constructor
    · rintro ⟨h1, h2⟩ p hp
      rcases p with _ | p
      · simpa using h1
      · simpa using h2 p (by simpa using hp)
    · intro h
      exact ⟨by simpa using h 0 (by simp), fun p hp => by simpa using h (p + 1) (by simpa using hp)⟩

theorem ecv_go_iff : ∀ (rows : List (List SatSym)) (V y : Str),
    ecv_go V rows y = true ↔ (∀ r ∈ rows, r.length = V.length) ∧
      ∀ p < V.length, (if V.getD p false then 1 else 0) + covC rows y p = 1
  | [], V, y => by
    simp only [ecv_go, ecv_all_iff, List.not_mem_nil, false_imp_iff, implies_true, true_and,
      covC, add_zero]
    refine forall₂_congr fun p _ => ?_
    cases V.getD p false <;> simp
  | r :: rows, V, y => by
    simp only [ecv_go, covC]
    constructor
    · intro h
      rcases hs : ecv_rs (y.headD false) r V with _ | V'
      · rw [hs] at h; simp at h
      · rw [hs] at h
        obtain ⟨a1, a3, a4⟩ := ecv_rs_some _ r V V' hs
        obtain ⟨b1, b2⟩ := (ecv_go_iff rows V' y.tail).1 h
        refine ⟨fun r' hr' => ?_, fun p hp => ?_⟩
        · rcases List.mem_cons.1 hr' with rfl | hr'
          · exact a1
          · rw [← a3]; exact b1 r' hr'
        · have h1 := b2 p (by omega)
          obtain ⟨c1, c2⟩ := a4 p
          rw [c1] at h1
          revert c2 h1
          cases V.getD p false <;> cases y.headD false <;>
            cases decide (r.getD p zero = pos) <;> simp
    · rintro ⟨h1, h2⟩
      have hl := h1 r (by simp)
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
      obtain ⟨V', hs⟩ := ecv_rs_ok _ r V hl hnc
      obtain ⟨a1, a3, a4⟩ := ecv_rs_some _ r V V' hs
      rw [hs]
      refine (ecv_go_iff rows V' y.tail).2 ⟨fun r' hr' => ?_, fun p hp => ?_⟩
      · rw [a3]; exact h1 r' (by simp [hr'])
      · have := h2 p (by omega)
        obtain ⟨c1, c2⟩ := a4 p
        rw [c1]
        revert c2 this
        cases V.getD p false <;> cases y.headD false <;>
          cases decide (r.getD p zero = pos) <;> simp

theorem ecv_getD_rep (n p : ℕ) : (List.replicate n false).getD p false = false := by
  by_cases h : p < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

theorem ecv_vres_iff (w : List SatSym) (y : Str) :
    ecv_vres w y = true ↔ ∃ u rs, clauses w = u :: rs ∧
      (∀ r ∈ rs, r.length = u.length) ∧ ∀ p < u.length, covC rs y p = 1 := by
  unfold ecv_vres
  rcases clauses w with _ | ⟨u, rs⟩
  · simp
  · simp only [ecv_go_iff, List.length_replicate, ecv_getD_rep, Bool.false_eq_true, if_false,
      zero_add, List.cons.injEq]
    constructor
    · intro h; exact ⟨u, rs, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨u', rs', ⟨rfl, rfl⟩, h⟩; exact h

theorem ecv_covC_take : ∀ (rs : List (List SatSym)) (y : List Bool) (p : ℕ),
    covC rs (y.take rs.length) p = covC rs y p
  | [], y, p => by simp [covC]
  | r :: rs, [], p => by simp [covC]
  | r :: rs, b :: y, p => by
    simp [covC, ecv_covC_take rs y p]

theorem ecv_ecLang_iff (w : List SatSym) :
    ECLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ ecv_vres w y = true := by
  unfold ECLang
  simp only [ecv_vres_iff]
  constructor
  · rintro ⟨u, rs, hw, hr, y, hy⟩
    refine ⟨y.take rs.length, ?_, u, rs, hw, hr, fun p hp => by rw [ecv_covC_take, hy p hp]⟩
    have h1 := length_clauses_le w
    rw [hw] at h1
    simp only [List.length_cons] at h1
    simp only [List.length_take]
    omega
  · rintro ⟨y, -, u, rs, hw, hr, hy⟩
    exact ⟨u, rs, hw, hr, y, hy⟩

/-! ## Transfer to the official class -/

/-- **EXACT COVER ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem ec_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      ECLang := by
  classical
  have hrun := fun z => ((ecv_exec_ver z).mono (ecv_Tver_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg ecv_ver) (tb 5 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg ecv_ver, 5, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => ecv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => ecv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [ecv_ecLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.ExactCover
