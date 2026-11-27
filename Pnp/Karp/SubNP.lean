import Pnp.Karp.SubVer
import Pnp.Karp.CliqueNP

/-!
# SUBSET SUM ∈ NP (official definition)

The checking relation is `sv_vres w y = true` (`Pnp/Karp/SubVer.lean`).

* `sv_bval_addL`: the program's ripple-carry addition is addition of values;
* `sv_goS_iff`: the main loop accepts iff accumulator + selected items = target;
* `sv_ssLang_iff`: `SSLang w ↔ ∃ y, |y| ≤ |w| ∧ sv_vres w y` (a selection can be cut to the
  number of items);
* `ss_in_np`: `SSLang ∈ NP`, via `sv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.SubsetSum

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Values -/

theorem sv_bval_bits : ∀ r : List SatSym, sv_bval (sv_bits r) = bv r
  | [] => rfl
  | s :: r => by
    have ih := sv_bval_bits r
    simp only [sv_bits, List.map_cons] at ih ⊢
    rw [sv_bval, bv, ih]
    cases s <;> simp [isPos]

theorem sv_bval_head (A : Str) :
    sv_bval A = (if A.headD false then 1 else 0) + 2 * sv_bval A.tail := by
  cases A <;> simp [sv_bval]

theorem sv_bval_propL : ∀ (c : Bool) (A : Str),
    sv_bval (sv_propL c A) = sv_bval A + (if c then 1 else 0)
  | c, [] => by cases c <;> simp [sv_propL, sv_bval]
  | c, a :: A => by
    have ih := sv_bval_propL (a && c) A
    simp only [sv_propL, sv_bval, ih]
    cases a <;> cases c <;> simp <;> omega

theorem sv_bval_addL : ∀ (c : Bool) (A bs : Str),
    sv_bval (sv_addL c A bs) = sv_bval A + sv_bval bs + (if c then 1 else 0)
  | c, A, [] => by simp [sv_addL, sv_bval_propL, sv_bval]
  | c, A, b :: bs => by
    have ih := sv_bval_addL (sv_maj (A.headD false) b c) A.tail bs
    rw [sv_addL, sv_bval, ih, sv_bval_head A, sv_bval]
    cases A.headD false <;> cases b <;> cases c <;> simp [sv_maj, sv_x3] <;> omega

theorem sv_eqB_iff : ∀ A T : Str, sv_eqB A T = true ↔ sv_bval A = sv_bval T
  | [], [] => by simp [sv_eqB]
  | [], b :: T => by
    have ih := sv_eqB_iff [] T
    simp only [sv_eqB, Bool.and_eq_true, ih, sv_bval]
    cases b <;> simp <;> omega
  | a :: A, [] => by
    have ih := sv_eqB_iff A []
    simp only [sv_eqB, Bool.and_eq_true, ih, sv_bval]
    cases a <;> simp
  | a :: A, b :: T => by
    have ih := sv_eqB_iff A T
    simp only [sv_eqB, Bool.and_eq_true, ih, sv_bval]
    cases a <;> cases b <;> simp <;> omega

theorem sv_goS_iff (T : Str) : ∀ (rows : List (List SatSym)) (R A : Str),
    sv_goS T rows R A = true ↔ sv_bval A + selSum rows R = sv_bval T
  | [], R, A => by simp [sv_goS, selSum, sv_eqB_iff]
  | r :: rows, R, A => by
    rw [sv_goS, sv_goS_iff T rows R.tail, selSum]
    cases R.headD false
    · simp
    · simp only [if_true, sv_bval_addL, sv_bval_bits, Bool.false_eq_true, if_false, add_zero]
      constructor <;> intro h <;> omega

theorem sv_vres_iff (w : List SatSym) (y : Str) :
    sv_vres w y = true ↔ ∃ t as, clauses w = t :: as ∧ selSum as y = bv t := by
  unfold sv_vres
  rcases clauses w with _ | ⟨t, as⟩
  · simp
  · simp only [sv_goS_iff, sv_bval, sv_bval_bits, zero_add, List.cons.injEq]
    constructor
    · intro h; exact ⟨t, as, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨t', as', ⟨rfl, rfl⟩, h⟩; exact h

theorem sv_selSum_take : ∀ (as : List (List SatSym)) (y : List Bool),
    selSum as (y.take as.length) = selSum as y
  | [], y => by simp [selSum]
  | r :: as, [] => by simp [selSum]
  | r :: as, b :: y => by
    simp [selSum, sv_selSum_take as y]

theorem sv_ssLang_iff (w : List SatSym) :
    SSLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ sv_vres w y = true := by
  unfold SSLang
  simp only [sv_vres_iff]
  constructor
  · rintro ⟨t, as, hw, y, hy⟩
    refine ⟨y.take as.length, ?_, t, as, hw, by rw [sv_selSum_take, hy]⟩
    have h1 := length_clauses_le w
    rw [hw] at h1
    simp only [List.length_cons] at h1
    simp only [List.length_take]
    omega
  · rintro ⟨y, -, t, as, hw, hy⟩
    exact ⟨t, as, hw, y, hy⟩

/-! ## Transfer to the official class -/

/-- **SUBSET SUM ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem ss_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      SSLang := by
  classical
  have hrun := fun z => ((sv_exec_ver z).mono (sv_Tver_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg sv_ver) (tb 6 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg sv_ver, 6, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => sv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => sv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [sv_ssLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.SubsetSum
