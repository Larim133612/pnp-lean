import Pnp.Karp.ThreePartUProgF

/-!
# Unary 3-PARTITION reduction program, part G: the program and its computability

`tpup_redCmd` parses the input word (as M63's `tpp_redCmd`) and runs `tpup_main`;
`tpup_F_computable` with the time bound `tb 150`.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.ThreePartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.BinPacking Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

/-! ## The program -/

/-- The transformer program. -/
def tpup_redCmd : Cmd := .seq parseLoop (.seq (trimC 4) (.seq (move 4 1) tpup_main))

/-- The time bound of the program. -/
def tpup_Tr (n : ℕ) : ℕ := 20001 * (n + 2) * (tpup_V (4 * n) (5 * n + 5) + 1) ^ 2

theorem tpup_exec_redCmd (x : Str) : ∃ σ', ExecLe tpup_redCmd (init [x]).stk (.norm σ')
    (tpup_Tr x.length) ∧ σ' 0 = ((tpup_F (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ₁ := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := exec_trimC_word 4 w σ₁ (by simp [σ₁, he 4 (by decide)])
  set σ₂ := update σ₁ 4 (((trunc w).flatMap ic).reverse)
  have p3 := exec_move (a := 4) (b := 1) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 4 []) 1 ((σ₂ 4).reverse ++ σ₂ 1) =
      (tpup_s0 (((clauses w).flatMap (· ++ [sep])).flatMap ic)).st := by
    funext j
    by_cases hj : j < 18
    · interval_cases j <;> simp [σ₂, σ₁, he, trunc, tpup_S.st, tpup_s0]
    · rw [tpup_st_big _ _ (by omega)]
      simp [σ₂, σ₁, he j (by omega), show j ≠ 0 by omega, show j ≠ 1 by omega,
        show j ≠ 4 by omega, tpup_s0]
  rw [hσ] at p3
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  obtain ⟨s, p4, hs⟩ := tpup_ex_main (clauses w) (sep_not_mem_clauses w) x.length
    (by have : (trunc w).length = ((clauses w).flatMap (· ++ [sep])).length := rfl; omega)
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm p4))).cast rfl ?_, ?_⟩
  · have htl : (σ₂ 4).length = 2 * (trunc w).length := by
      simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
    rw [htl]
    unfold tpup_Tm tpup_Tr
    have hX : 64 ≤ (tpup_V (4 * x.length) (5 * x.length + 5) + 1) ^ 2 := by
      have h1 := Nat.one_le_pow 8 _ (tpup_R_pos (4 * x.length))
      have h2 : 8 ≤ tpup_V (4 * x.length) (5 * x.length + 5) + 1 := by unfold tpup_V; omega
      have := Nat.pow_le_pow_left h2 2
      omega
    generalize (tpup_V (4 * x.length) (5 * x.length + 5) + 1) ^ 2 = X at hX ⊢
    have hY : 64 * (x.length + 2) ≤ (x.length + 2) * X := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hX
    have e1 : 20000 * (x.length + 2) * X = 20000 * ((x.length + 2) * X) := Nat.mul_assoc _ _ _
    have e2 : 20001 * (x.length + 2) * X = 20001 * ((x.length + 2) * X) := Nat.mul_assoc _ _ _
    rw [e1, e2]
    generalize (x.length + 2) * X = Y at hY ⊢
    clear e1 e2
    have a1 : w.length ≤ x.length := hwx
    have a2 : (trunc w).length ≤ w.length := hw
    omega
  · rw [tpup_st0, hs]; rfl

theorem tpup_T_aux (P R z : ℕ) (hP2 : 2 ≤ P) (hR0 : R ≤ 128 * P) (hz : z ≤ 5 * P) :
    20001 * P * (2 * R ^ 8 + z + 1) ^ 2 ≤ P ^ 150 := by
  have p7 : 2 ^ 7 ≤ P ^ 7 := Nat.pow_le_pow_left hP2 7
  have p3 : 2 ^ 3 ≤ P ^ 3 := Nat.pow_le_pow_left hP2 3
  have p15 : 2 ^ 15 ≤ P ^ 15 := Nat.pow_le_pow_left hP2 15
  have hR : R ≤ P ^ 8 := by
    calc R ≤ 128 * P := hR0
      _ ≤ P ^ 7 * P := Nat.mul_le_mul_right _ (le_trans (by norm_num) p7)
      _ = P ^ 8 := by ring
  have hR8 : R ^ 8 ≤ P ^ 64 := by
    calc R ^ 8 ≤ (P ^ 8) ^ 8 := Nat.pow_le_pow_left hR 8
      _ = P ^ 64 := by ring
  have hP64 : P ≤ P ^ 64 := Nat.le_self_pow (by norm_num) P
  have hV : 2 * R ^ 8 + z + 1 ≤ P ^ 67 := by
    calc 2 * R ^ 8 + z + 1 ≤ 8 * P ^ 64 := by omega
      _ ≤ P ^ 3 * P ^ 64 := Nat.mul_le_mul_right _ (le_trans (by norm_num) p3)
      _ = P ^ 67 := by ring
  have hV2 : (2 * R ^ 8 + z + 1) ^ 2 ≤ P ^ 134 := by
    calc _ ≤ (P ^ 67) ^ 2 := Nat.pow_le_pow_left hV 2
      _ = P ^ 134 := by ring
  calc 20001 * P * (2 * R ^ 8 + z + 1) ^ 2 ≤ P ^ 15 * P * P ^ 134 :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (le_trans (by norm_num) p15)) hV2
    _ = P ^ 150 := by ring

theorem tpup_T_le (n : ℕ) : tpup_Tr n ≤ tb 150 n := by
  unfold tpup_Tr tb tpup_V
  exact tpup_T_aux (n + 2) (uR (4 * n)) (5 * n + 5) (by omega) (by unfold uR uL; omega)
    (by omega)

/-- **`tpup_F` is polynomial-time computable.** -/
theorem tpup_F_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    tpup_F) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    tpup_redCmd 0 150 (fun x => tpup_F (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := tpup_exec_redCmd x
      exact ⟨σ', h1.mono (tpup_T_le _), h2⟩)
    tpup_F (fun t => (congrArg tpup_F (FunBridge.dec2_flatMap_ic t)).symm)

end Pnp.Karp.ThreePartU

