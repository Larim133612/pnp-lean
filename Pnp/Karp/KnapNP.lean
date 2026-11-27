import Pnp.Karp.KnapVer

/-!
# KNAPSACK ∈ NP (official definition)

The checking relation is `kv_vres w y = true` (`Pnp/Karp/KnapVer.lean`).

* `kv_leF_iff`: the program's comparison loop compares values (`sv_bval`);
* `kv_go_iff`: the main loop accepts iff accumulated weight + selected weights `≤ W` and
  `V ≤` accumulated value + selected values (items as in `pairs`);
* `kv_knapLang_iff`: `KnapLang w ↔ ∃ y, |y| ≤ |w| ∧ kv_vres w y` (a selection can be cut to the
  number of items);
* `knap_in_np`: `KnapLang ∈ NP`, via `kv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.Knapsack

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

theorem kv_leF_iff : ∀ (g : Bool) (A B : Str),
    kv_leF g A B = true ↔ sv_bval A < sv_bval B ∨ (sv_bval A = sv_bval B ∧ g = true)
  | g, [], [] => by simp [kv_leF, sv_bval]
  | g, [], y :: B => by
    rw [kv_leF, kv_leF_iff]
    cases y <;> cases g <;> simp [kv_stp, sv_bval] <;> omega
  | g, x :: A, [] => by
    rw [kv_leF, kv_leF_iff]
    cases x <;> cases g <;> simp [kv_stp, sv_bval]
  | g, x :: A, y :: B => by
    rw [kv_leF, kv_leF_iff]
    cases x <;> cases y <;> cases g <;> simp [kv_stp, sv_bval] <;> omega

theorem kv_le_iff (A B : Str) : kv_leF true A B = true ↔ sv_bval A ≤ sv_bval B := by
  rw [kv_leF_iff]; simp only [and_true]; omega

theorem kv_go_iff (W V : Str) : ∀ (rows : List (List SatSym)) (R AW AV : Str),
    kv_go W V rows R AW AV = true ↔
      sv_bval AW + selSum ((pairs rows).map Prod.fst) R ≤ sv_bval W ∧
        sv_bval V ≤ sv_bval AV + selSum ((pairs rows).map Prod.snd) R
  | [], R, AW, AV => by simp [kv_go, pairs, selSum, kv_le_iff]
  | [a], R, AW, AV => by
    simp only [kv_go, pairs, List.map_cons, List.map_nil, selSum, Bool.and_eq_true, kv_le_iff]
    cases R.headD false <;> simp [sv_bval_addL, sv_bval_bits, bv]
  | a :: b :: rows, R, AW, AV => by
    simp only [kv_go, pairs, List.map_cons, selSum]
    cases R.headD false
    · simp only [Bool.false_eq_true, if_false, kv_go_iff W V rows]; omega
    · simp only [if_true, kv_go_iff W V rows, sv_bval_addL, sv_bval_bits, Bool.false_eq_true,
        if_false, add_zero]; omega

theorem kv_vres_iff (w : List SatSym) (y : Str) :
    kv_vres w y = true ↔ ∃ W V items, clauses w = W :: V :: items ∧
      selSum ((pairs items).map Prod.fst) y ≤ bv W ∧
        bv V ≤ selSum ((pairs items).map Prod.snd) y := by
  unfold kv_vres
  rcases clauses w with _ | ⟨W, _ | ⟨V, items⟩⟩
  · simp
  · simp
  · simp only [kv_go_iff, sv_bval, sv_bval_bits, zero_add, List.cons.injEq]
    constructor
    · intro h; exact ⟨W, V, items, ⟨rfl, rfl, rfl⟩, h⟩
    · rintro ⟨W', V', items', ⟨rfl, rfl, rfl⟩, h⟩; exact h

theorem kv_pairs_length : ∀ rows : List (List SatSym), (pairs rows).length ≤ rows.length
  | [] => by simp [pairs]
  | [a] => by simp [pairs]
  | a :: b :: rows => by have := kv_pairs_length rows; simp [pairs]; omega

theorem kv_knapLang_iff (w : List SatSym) :
    KnapLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ kv_vres w y = true := by
  unfold KnapLang
  simp only [kv_vres_iff]
  constructor
  · rintro ⟨W, V, items, hw, y, h1, h2⟩
    refine ⟨y.take (pairs items).length, ?_, W, V, items, hw, ?_, ?_⟩
    · have h1 := length_clauses_le w
      have h2 := kv_pairs_length items
      rw [hw] at h1
      simp only [List.length_cons] at h1
      simp only [List.length_take]
      omega
    · have := sv_selSum_take ((pairs items).map Prod.fst) y
      rw [List.length_map] at this
      rw [this]; exact h1
    · have := sv_selSum_take ((pairs items).map Prod.snd) y
      rw [List.length_map] at this
      rw [this]; exact h2
  · rintro ⟨y, -, W, V, items, hw, h1, h2⟩
    exact ⟨W, V, items, hw, y, h1, h2⟩

/-! ## Transfer to the official class -/

/-- **KNAPSACK ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem knap_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      KnapLang := by
  classical
  have hrun := fun z => ((kv_exec_ver z).mono (kv_Tver_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg kv_ver) (tb 8 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg kv_ver, 8, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => kv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => kv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [kv_knapLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.Knapsack
