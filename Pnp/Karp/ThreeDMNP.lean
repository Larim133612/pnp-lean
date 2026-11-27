import Pnp.Karp.ThreeDMVer
import Pnp.Karp.CliqueNP

/-!
# 3-DIMENSIONAL MATCHING ∈ NP (official definition)

The checking relation is `mv_vres w y = true` (`Pnp/Karp/ThreeDMVer.lean`).

* `mv_row_eq`: the row loop splits into the triple check `mv_tri`, the conflict check `mv_cov`
  and the coverage update `mv_newC`;
* `mv_tri_E`: the triple check against the markers `mv_E k` is `IsTri (k + 1)`;
* `mv_go_iff`: the main loop accepts iff every row is a triple and every position is covered
  exactly once (counting the initial coverage bits);
* `mv_dmLang_iff`: `DMLang w ↔ ∃ y, |y| ≤ |w| ∧ mv_vres w y`;
* `dm_in_np`: `DMLang ∈ NP`, via `mv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.ThreeDM

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Splitting the row loop -/

/-- The triple check of a row against markers `E`. -/
def mv_tri : List SatSym → Str → Bool → Bool
  | [], [], _ => true
  | [], _ :: _, _ => false
  | _ :: _, [], _ => false
  | s :: r, e :: E, f =>
    !((isPos s && f) || (e && !(f || isPos s))) && mv_tri r E (mv_nf (isPos s) e f)

/-- No selected `pos` at a covered position. -/
def mv_cov (sel : Bool) : List SatSym → Str → Bool
  | [], _ => true
  | s :: r, C => !(sel && isPos s && C.headD false) && mv_cov sel r C.tail

/-- The new coverage bits. -/
def mv_newC (sel : Bool) : List SatSym → Str → Str
  | [], C => C
  | s :: r, C => (C.headD false || sel && isPos s) :: mv_newC sel r C.tail

theorem mv_row_eq (sel : Bool) : ∀ (r : List SatSym) (E C : Str) (f : Bool),
    mv_row sel r E C f =
      if mv_tri r E f && mv_cov sel r C then some (mv_newC sel r C) else none
  | [], [], C, f => by simp [mv_row, mv_tri, mv_cov, mv_newC]
  | [], _ :: _, _, _ => by simp [mv_row, mv_tri]
  | _ :: _, [], _, _ => by simp [mv_row, mv_tri]
  | s :: r, e :: E, C, f => by
    rw [mv_row, mv_row_eq sel r E C.tail]
    simp only [mv_tri, mv_cov, mv_newC, mv_bad]
    cases isPos s <;> cases e <;> cases f <;> cases sel <;> cases C.headD false <;>
      cases mv_tri r E (mv_nf _ _ _) <;> cases mv_cov _ r C.tail <;> simp

/-! ## The triple check -/

theorem mv_tri_nil : ∀ (r : List SatSym) (f : Bool), mv_tri r [] f = true ↔ r = []
  | [], f => by simp [mv_tri]
  | _ :: _, f => by simp [mv_tri]

theorem mv_count_pos (s : SatSym) : (if isPos s then 1 else 0) = ([s].count pos) := by
  cases s <;> simp [isPos]

theorem mv_tri_blk : ∀ (k : ℕ) (r : List SatSym) (E' : Str) (f : Bool),
    mv_tri r (List.replicate k false ++ true :: E') f = true ↔
      k < r.length ∧ (r.take (k + 1)).count pos + (if f then 1 else 0) = 1 ∧
        mv_tri (r.drop (k + 1)) E' false = true
  | k, [], E', f => by cases k <;> simp [mv_tri, List.replicate_succ]
  | 0, s :: r, E', f => by
    have h := mv_count_pos s
    simp only [List.replicate_zero, List.nil_append, mv_tri, mv_nf, Bool.not_true,
      Bool.false_and, Bool.and_eq_true, List.length_cons, zero_add, List.take_succ_cons,
      List.take_zero, List.drop_succ_cons, List.drop_zero]
    cases hs : isPos s <;> cases f <;> simp [hs] at h ⊢ <;> omega
  | k + 1, s :: r, E', f => by
    have h := mv_count_pos s
    have ih := mv_tri_blk k r E' (f || isPos s)
    simp only [List.replicate_succ, List.cons_append, mv_tri, mv_nf, Bool.not_false,
      Bool.true_and, Bool.false_and, Bool.or_false, Bool.and_eq_true, ih,
      List.length_cons, List.take_succ_cons, List.drop_succ_cons]
    rw [← List.singleton_append, List.count_append]
    cases hs : isPos s <;> cases f <;> simp [hs] at h ⊢ <;> omega

theorem mv_tri_E (k : ℕ) (r : List SatSym) :
    mv_tri r (mv_E k) false = true ↔ IsTri (k + 1) r := by
  unfold mv_E IsTri
  rw [mv_tri_blk, mv_tri_blk, mv_tri_blk, mv_tri_nil]
  simp only [Bool.false_eq_true, if_false, add_zero, List.drop_drop, List.length_drop,
    List.drop_eq_nil_iff]
  rw [show 2 * (k + 1) = k + 1 + (k + 1) by ring]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have ht : List.take (k + 1) (List.drop (k + 1 + (k + 1)) r) = List.drop (k + 1 + (k + 1)) r :=
      List.take_of_length_le (by simp; omega)
    exact ⟨by omega, h2, h4, ht ▸ h6⟩
  · rintro ⟨h1, h2, h4, h6⟩
    have ht : List.take (k + 1) (List.drop (k + 1 + (k + 1)) r) = List.drop (k + 1 + (k + 1)) r :=
      List.take_of_length_le (by simp; omega)
    exact ⟨by omega, h2, by omega, h4, by omega, by rw [ht]; exact h6, by omega⟩

/-! ## Coverage -/

theorem mv_newC_getD (sel : Bool) : ∀ (r : List SatSym) (C : Str) (p : ℕ),
    (mv_newC sel r C).getD p false =
      if p < r.length then (C.getD p false || sel && decide (r.getD p zero = pos))
      else C.getD p false
  | [], C, p => by simp [mv_newC]
  | s :: r, C, 0 => by
    cases C <;> cases s <;> simp [mv_newC, isPos]
  | s :: r, C, p + 1 => by
    have ih := mv_newC_getD sel r C.tail p
    rw [mv_newC, List.getD_cons_succ, ih, List.getD_cons_succ]
    have e : C.getD (p + 1) false = C.tail.getD p false := by
      cases C <;> simp only [List.getD_nil, List.tail_nil, List.getD_cons_succ, List.tail_cons]
    rw [e]; simp only [List.length_cons, Nat.add_lt_add_iff_right]

theorem mv_newC_length (sel : Bool) : ∀ (r : List SatSym) (C : Str), C.length = r.length →
    (mv_newC sel r C).length = r.length
  | [], C, h => by simpa [mv_newC] using h
  | s :: r, C, h => by
    have := mv_newC_length sel r C.tail (by simp at h ⊢; omega)
    simp [mv_newC, this]

theorem mv_cov_iff (sel : Bool) : ∀ (r : List SatSym) (C : Str),
    mv_cov sel r C = true ↔
      ∀ p < r.length, ¬ (sel = true ∧ r.getD p zero = pos ∧ C.getD p false = true)
  | [], C => by simp [mv_cov]
  | s :: r, C => by
    have ih := mv_cov_iff sel r C.tail
    rw [mv_cov, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h⟩ p hp
      rcases p with _ | p
      · cases C <;> cases s <;> cases sel <;> simp_all [isPos]
      · have := h p (by simp at hp; omega)
        cases C <;> simp_all
    · intro h
      refine ⟨?_, fun p hp => ?_⟩
      · have := h 0 (by simp)
        cases C <;> cases s <;> cases sel <;> simp_all [isPos]
      · have := h (p + 1) (by simp; omega)
        cases C <;> simp_all

theorem mv_all_iff : ∀ C : Str, C.all id = true ↔ ∀ p < C.length, C.getD p false = true
  | [] => by simp
  | b :: C => by
    rw [List.all_cons, Bool.and_eq_true, mv_all_iff C]
    constructor
    · rintro ⟨hb, h⟩ p hp
      rcases p with _ | p
      · simpa using hb
      · simpa using h p (by simp at hp; omega)
    · intro h
      exact ⟨by simpa using h 0 (by simp), fun p hp => by simpa using h (p + 1) (by simp; omega)⟩

theorem mv_go_iff (k : ℕ) : ∀ (rows : List (List SatSym)) (R C : Str), C.length = 3 * (k + 1) →
    (mv_go (mv_E k) rows R C = true ↔ (∀ r ∈ rows, IsTri (k + 1) r) ∧
      ∀ p < 3 * (k + 1), (if C.getD p false then 1 else 0) + covC rows R p = 1)
  | [], R, C, hC => by
    rw [mv_go, mv_all_iff, hC]
    constructor
    · intro h; exact ⟨by simp, fun p hp => by rw [covC, if_pos (h p hp)]⟩
    · rintro ⟨-, h⟩ p hp
      have := h p hp
      rw [covC, add_zero] at this
      by_contra hc; rw [if_neg hc] at this; exact absurd this (by decide)
  | r :: rows, R, C, hC => by
    rw [mv_go, mv_row_eq]
    by_cases ht : mv_tri r (mv_E k) false = true
    · have hT : IsTri (k + 1) r := (mv_tri_E k r).1 ht
      have hr : r.length = 3 * (k + 1) := hT.1
      by_cases hc : mv_cov (R.headD false) r C = true
      · simp only [ht, hc, Bool.and_self, if_true]
        rw [mv_go_iff k rows R.tail _ (by rw [mv_newC_length _ _ _ (by omega)]; exact hr)]
        have hcov := (mv_cov_iff _ r C).1 hc
        simp only [List.forall_mem_cons, hT, true_and]
        refine and_congr_right fun _ => forall_congr' fun p => imp_congr_right fun hp => ?_
        have h1 := hcov p (by omega)
        rw [mv_newC_getD, if_pos (show p < r.length by omega), covC]
        cases hCp : C.getD p false <;> cases hs : R.headD false <;>
          by_cases hrp : r.getD p zero = pos <;> simp_all
      · simp only [ht, hc, Bool.and_false, Bool.false_eq_true, if_false]
        have hc' := hc
        rw [mv_cov_iff] at hc'
        push Not at hc'
        obtain ⟨p, hp, h1, h2, h3⟩ := hc'
        simp only [false_iff, not_and]
        intro _ h
        have := h p (by omega)
        rw [covC] at this
        simp only [h3, h1, h2, decide_true, Bool.and_true, if_true] at this
        omega
    · simp only [ht, Bool.false_and, Bool.false_eq_true, if_false, false_iff, not_and]
      intro h
      exact absurd ((mv_tri_E k r).2 (h r (by simp))) ht

/-! ## The language -/

theorem mv_C_getD (k p : ℕ) : (mv_C k).getD p false = false := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (mv_C k)[p]? with
  | none => rfl
  | some b =>
    have hb := List.mem_of_getElem? h
    have : b = false := by simp [mv_C, List.mem_replicate] at hb; tauto
    simp [this]

theorem mv_vres_iff (w : List SatSym) (y : Str) :
    mv_vres w y = true ↔ ∃ u rs, clauses w = u :: rs ∧ (∀ r ∈ rs, IsTri u.length r) ∧
      ∀ p < 3 * u.length, covC rs y p = 1 := by
  unfold mv_vres
  rcases hcw : clauses w with _ | ⟨u, rs⟩
  · simp
  · rcases u with _ | ⟨x, u⟩
    · constructor
      · intro h
        have h' : rs = [] := by simpa using h
        subst h'
        exact ⟨[], [], rfl, by simp, by simp⟩
      · rintro ⟨u', rs', h1, h2, -⟩
        injection h1 with e1 e2
        subst e1 e2
        cases rs with
        | nil => rfl
        | cons r rs => exact absurd (h2 r (by simp)).2.1 (by simp)
    · have hCl : (mv_C u.length).length = 3 * (u.length + 1) := by simp [mv_C]; omega
      rw [mv_go_iff _ _ _ _ hCl]
      simp only [mv_C_getD, Bool.false_eq_true, if_false, zero_add]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨x :: u, rs, rfl, h1, h2⟩
      · rintro ⟨u', rs', h1, h2, h3⟩
        injection h1 with e1 e2
        subst e1 e2
        exact ⟨h2, h3⟩

theorem mv_covC_take : ∀ (rs : List (List SatSym)) (y : List Bool) (p : ℕ),
    covC rs (y.take rs.length) p = covC rs y p
  | [], y, p => by simp [covC]
  | r :: rs, [], p => by simp [covC]
  | r :: rs, b :: y, p => by
    simp [covC, mv_covC_take rs y p]

theorem mv_dmLang_iff (w : List SatSym) :
    DMLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ mv_vres w y = true := by
  unfold DMLang
  simp only [mv_vres_iff]
  constructor
  · rintro ⟨u, rs, hw, ht, y, hy⟩
    refine ⟨y.take rs.length, ?_, u, rs, hw, ht, fun p hp => by rw [mv_covC_take, hy p hp]⟩
    have h1 := length_clauses_le w
    rw [hw] at h1
    simp only [List.length_cons] at h1
    simp only [List.length_take]
    omega
  · rintro ⟨y, -, u, rs, hw, ht, hy⟩
    exact ⟨u, rs, hw, ht, y, hy⟩

/-! ## Transfer to the official class -/

/-- **3-DIMENSIONAL MATCHING ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem dm_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      DMLang := by
  classical
  have hrun := fun z => ((mv_exec_ver z).mono (mv_Tver_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg mv_ver) (tb 8 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg mv_ver, 8, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => mv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => mv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [mv_dmLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.ThreeDM
