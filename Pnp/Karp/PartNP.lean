import Pnp.Karp.PartVer

/-!
# PARTITION ∈ NP (official definition)

The checking relation is `pv_vres w y = true` (`Pnp/Karp/PartVer.lean`).

* `pv_go_iff`: the main loop accepts iff `A + 2·(selected sum) = B + (total sum)`; started with
  empty accumulators, iff `2 * selSum = totSum`;
* `pv_partLang_iff`: `PartLang w ↔ ∃ y, |y| ≤ |w| ∧ pv_vres w y` (a selection can be cut to the
  number of rows, `sv_selSum_take`);
* `part_in_np`: `PartLang ∈ NP`, via `pv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.Partition

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

theorem pv_go_iff : ∀ (rows : List (List SatSym)) (R A B : Str),
    pv_go rows R A B = true ↔ sv_bval A + 2 * selSum rows R = sv_bval B + totSum rows
  | [], R, A, B => by simp [pv_go, selSum, totSum, sv_eqB_iff]
  | r :: rows, R, A, B => by
    rw [pv_go, selSum, totSum]
    cases R.headD false
    · simp only [Bool.false_eq_true, if_false, pv_go_iff rows, sv_bval_addL, sv_bval_bits]
      constructor <;> intro h <;> omega
    · simp only [if_true, pv_go_iff rows, sv_bval_addL, sv_bval_bits, Bool.false_eq_true,
        if_false]
      constructor <;> intro h <;> omega

theorem pv_vres_iff (w : List SatSym) (y : Str) :
    pv_vres w y = true ↔ 2 * selSum (clauses w) y = totSum (clauses w) := by
  simp [pv_vres, pv_go_iff, sv_bval]

theorem pv_partLang_iff (w : List SatSym) :
    PartLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ pv_vres w y = true := by
  unfold PartLang
  simp only [pv_vres_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y.take (clauses w).length, ?_, by rw [sv_selSum_take, hy]⟩
    have h1 := length_clauses_le w
    simp only [List.length_take]
    omega
  · rintro ⟨y, -, hy⟩
    exact ⟨y, hy⟩

/-! ## Transfer to the official class -/

/-- **PARTITION ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem part_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      PartLang := by
  classical
  have hrun := fun z => ((pv_exec_ver z).mono (pv_Tver_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg pv_ver) (tb 6 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg pv_ver, 6, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => pv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => pv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [pv_partLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.Partition
