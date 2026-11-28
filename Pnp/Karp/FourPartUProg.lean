import Pnp.Karp.FourPartUProgB

/-!
# The unary 4-PARTITION reduction program and SAT ≤ₚ unary 4-PARTITION

`fpup_redCmd`, on the bit string `x` on stack `0`, prints `fpuT w` (`w = dec2 x`,
`Pnp/Karp/FourPartU.lean`) on stack `0`:

1. `parseLoop`; `marks 4 8 3` (stack `8` gets `2 |w|` marks); `trimC 4`, `move 4 1` (stack `1`
   holds the code of the rows of `w`);
2. `fpup_half 8 9` (`false ^ N`, `N = |w|`), `fpup_unL 9 10` (`rv (uRow N)`), and the
   constants `rv (uRow (5 N))`, `rv (uRow (6 N))`, `rv (uRow (21 N))` on stacks `5`, `6`, `7`;
3. the row loop, the filler loop and the last row (`Pnp/Karp/FourPartUProgB.lean`).

`fpuT_computable` (time bound `tb 12`) follows from `FunBridge.computable_of_cmd_code`;
`sat_le_fpu_of` composes it with the unary 3-PARTITION reduction `tpup_F ∘ DMI`.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.FourPartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.ThreePartU Pnp.Karp.ThreePart Pnp.Karp.ThreeDM

/-- The preparation phase. -/
def fpup_pre : Cmd :=
  .seq parseLoop (.seq (marks 4 8 3) (.seq (trimC 4) (.seq (move 4 1) (.seq (fpup_half 8 9)
    (.seq (fpup_unL 9 10) (.seq (fpup_cpN 10 5 5) (.seq (fpup_cpN 10 6 6)
    (.seq (fpup_cpN 10 7 21) (drain 10)))))))))

/-- The reduction program. -/
def fpup_redCmd : Cmd := .seq fpup_pre (.seq fpup_rowL (.seq fpup_filL fpup_fin))

set_option maxHeartbeats 1000000 in
theorem fpup_ex_pre (x : Str) :
    ExecLe fpup_pre (init [x]).stk
      (.norm (fpup_ss (FunBridge.dec2 x).length [] (fpup_code (clauses (FunBridge.dec2 x))) [] []))
      (400 * x.length + 200) := by
  set w := FunBridge.dec2 x
  set N := w.length
  have hwx : N ≤ x.length := FunBridge.length_dec2_le x
  have hLw : (trunc w).length ≤ w.length := length_trunc_le w
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ1 := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := ExecLe.of (exec_marks (a := 4) (d := 8) (t := 3) (by decide) (by decide)
    (by decide) σ1 (by simp [σ1, he]))
  set σ2 := update σ1 8 (List.replicate (σ1 4).length true ++ σ1 8)
  have p3 := exec_trimC_word 4 w σ2 (by simp [σ2, σ1, he])
  set σ3 := update σ2 4 (((trunc w).flatMap ic).reverse)
  have p4 := ExecLe.of (exec_move (a := 4) (b := 1) (by decide) _ σ3 rfl)
  set σ4 := update (update σ3 4 []) 1 ((σ3 4).reverse ++ σ3 1)
  have l1 : (σ1 4).length = 2 * N := by
    simp only [σ1, update_self, List.length_append, List.length_reverse, length_flatMap_ic,
      he 4 (by decide), List.length_nil, Nat.add_zero]; rfl
  have h18 : σ1 8 = [] := by simp [σ1, he]
  have p5 := fpup_ex_half (a := 8) (d := 9) (by decide) true N σ4
    (by simp [σ4, σ3, σ2, l1, h18])
  set σ5 := update (update σ4 8 []) 9 (List.replicate N false ++ σ4 9)
  have p6 := fpup_ex_unL (a := 9) (d := 10) (by decide) _ σ5 rfl
  set σ6 := update (update σ5 9 []) 10 (rv (uRow (σ5 9).length) ++ σ5 10)
  have h6 : σ6 10 = rv (uRow N) := by simp [σ6, σ5, σ4, σ3, σ2, σ1, he]
  have h63 : σ6 3 = [] := by simp [σ6, σ5, σ4, σ3, σ2, σ1, he]
  have p7 := fpup_ex_cpN (a := 10) (d := 5) (by decide) (by decide) (by decide) 5 σ6 h63
  set σ7 := update σ6 5 ((List.replicate 5 (σ6 10)).flatten ++ σ6 5)
  have p8 := fpup_ex_cpN (a := 10) (d := 6) (by decide) (by decide) (by decide) 6 σ7
    (by simp [σ7, h63])
  set σ8 := update σ7 6 ((List.replicate 6 (σ7 10)).flatten ++ σ7 6)
  have p9 := fpup_ex_cpN (a := 10) (d := 7) (by decide) (by decide) (by decide) 21 σ8
    (by simp [σ8, σ7, h63])
  set σ9 := update σ8 7 ((List.replicate 21 (σ8 10)).flatten ++ σ8 7)
  have p10 := ExecLe.of (exec_drain 10 _ σ9 rfl)
  have e7 : σ7 10 = rv (uRow N) := by simp [σ7, h6]
  have e8 : σ8 10 = rv (uRow N) := by simp [σ8, e7]
  have e9 : σ9 10 = rv (uRow N) := by simp [σ9, e8]
  have h65 : σ6 5 = [] := by simp [σ6, σ5, σ4, σ3, σ2, σ1, he]
  have h66 : σ6 6 = [] := by simp [σ6, σ5, σ4, σ3, σ2, σ1, he]
  have h67 : σ6 7 = [] := by simp [σ6, σ5, σ4, σ3, σ2, σ1, he]
  have v5 : σ9 5 = rv (uRow (5 * N)) := by
    simp only [σ9, σ8, σ7, update_of_ne (show (5:ℕ) ≠ 7 by decide),
      update_of_ne (show (5:ℕ) ≠ 6 by decide), update_self, h6, h65, fpup_rv_uRow_mul,
      List.append_nil]
  have h76 : σ7 6 = [] := by simp only [σ7, update_of_ne (show (6:ℕ) ≠ 5 by decide), h66]
  have h87 : σ8 7 = [] := by
    simp only [σ8, σ7, update_of_ne (show (7:ℕ) ≠ 5 by decide),
      update_of_ne (show (7:ℕ) ≠ 6 by decide), h67]
  have v6 : σ9 6 = rv (uRow (6 * N)) := by
    simp only [σ9, σ8, update_of_ne (show (6:ℕ) ≠ 7 by decide), update_self, e7,
      h76, fpup_rv_uRow_mul, List.append_nil]
  have v7 : σ9 7 = rv (uRow (21 * N)) := by
    simp only [σ9, update_self, e8, update_of_ne (show (7:ℕ) ≠ 6 by decide),
      h87, fpup_rv_uRow_mul, List.append_nil]
  have hfin : update σ9 10 [] = fpup_ss N [] (fpup_code (clauses w)) [] [] := by
    funext j
    by_cases j5 : j = 5
    · subst j5; rw [update_of_ne (by decide), v5]; rfl
    by_cases j6 : j = 6
    · subst j6; rw [update_of_ne (by decide), v6]; rfl
    by_cases j7 : j = 7
    · subst j7; rw [update_of_ne (by decide), v7]; rfl
    by_cases hj : j < 11
    · interval_cases j <;> first | (exfalso; omega) |
        simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, he, fpup_st, h6, fpup_rv_uRow_mul,
          fpup_code, trunc]
    · simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, fpup_st, update_apply,
        he j (by omega), show j ≠ 0 by omega, show j ≠ 1 by omega, show j ≠ 2 by omega,
        show j ≠ 4 by omega, show j ≠ 5 by omega, show j ≠ 6 by omega, show j ≠ 7 by omega,
        show j ≠ 8 by omega, show j ≠ 9 by omega, show j ≠ 10 by omega]
  rw [hfin] at p10
  refine (p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm (p5.seq_norm (p6.seq_norm
    (p7.seq_norm (p8.seq_norm (p9.seq_norm p10))))))))).mono ?_
  have l3 : (σ3 4).length = 2 * (trunc w).length := by
    simp only [σ3, update_self, List.length_reverse, length_flatMap_ic]
  have l5 : (σ5 9).length = N := by simp [σ5, σ4, σ3, σ2, σ1, he]
  have l6 : (σ6 10).length = 2 * N := by rw [h6, fpup_len_rv_uRow]
  rw [e7, fpup_len_rv_uRow] at *
  rw [e8, fpup_len_rv_uRow] at *
  rw [e9, fpup_len_rv_uRow]
  rw [l1, l3, l5, l6]
  omega

theorem fpup_out_eq (w : List SatSym) :
    fpup_rowsO w.length (clauses w) ++
      fpup_filO w.length ((clauses w).dropLast.length / 3) ++
      (uRow (21 * w.length + ((clauses w).getLastD []).length) ++ [sep]) = fpuT w := by
  simp [fpuT, fpup_rowsO, fpup_filO, List.flatMap_append]

theorem fpup_exec_redCmd (x : Str) : ∃ σ', ExecLe fpup_redCmd (init [x]).stk (.norm σ')
    (1000 * (x.length + 2) ^ 2) ∧ σ' 0 = ((fpuT (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  set N := w.length
  set n := x.length
  have hwx : N ≤ n := FunBridge.length_dec2_le x
  have hLw : (trunc w).length ≤ w.length := length_trunc_le w
  have p1 := fpup_ex_pre x
  have hrows : ∀ r ∈ clauses w, sep ∉ r ∧ r.length ≤ n := fun r hr =>
    ⟨sep_not_mem_clauses w r hr, by
      have := tpp_len_le (clauses w) r hr
      have h2 : ((clauses w).flatMap (· ++ [sep])).length = (trunc w).length := rfl
      omega⟩
  have hcl : (clauses w).length ≤ n := by
    have := tpp_cnt_le (clauses w)
    have h2 : ((clauses w).flatMap (· ++ [sep])).length = (trunc w).length := rfl
    omega
  have p2 := fpup_ex_rowL N n hwx (clauses w) [] [] hrows
  simp only [List.append_nil, List.nil_append] at p2
  have p3 := fpup_ex_filL N [] (rv (uRow ((clauses w).getLastD []).length))
    (clauses w).dropLast.length (fpup_rowsO N (clauses w))
  set a := ((clauses w).getLastD []).length
  set k := (clauses w).dropLast.length
  obtain ⟨σ', p4, hσ'⟩ := fpup_ex_fin N a (fpup_rowsO N (clauses w) ++ fpup_filO N (k / 3)) [] []
  have ha : a ≤ n := by
    rcases (clauses w).eq_nil_or_concat with h | ⟨L, c, h⟩
    · simp [a, h]
    · have := (hrows c (by rw [h]; simp)).2
      simpa [a, h, List.getLastD_eq_getLast?] using this
  have hk : k ≤ n := by
    have : k ≤ (clauses w).length := by simp [k]
    omega
  refine ⟨σ', (p1.seq_norm (p2.seq_norm (p3.seq_norm p4))).mono ?_, ?_⟩
  · have hk3 : k / 3 ≤ n := le_trans (Nat.div_le_self _ _) hk
    have e1 : ((clauses w).length + 1) * (100 * n + 100) ≤ (n + 1) * (100 * n + 100) :=
      Nat.mul_le_mul_right _ (by omega)
    have e2 : (k / 3 + 1) * (60 * N + 20) ≤ (n + 1) * (60 * n + 20) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  · rw [hσ', ← fpup_out_eq w]
    rfl

theorem fpup_T_le (n : ℕ) : 1000 * (n + 2) ^ 2 ≤ tb 12 n := by
  unfold tb
  have hm : 2 ^ 10 ≤ (n + 2) ^ 10 := Nat.pow_le_pow_left (by omega) 10
  have e : (n + 2) ^ 12 = (n + 2) ^ 10 * (n + 2) ^ 2 := by ring
  rw [e]
  have : 1000 ≤ (n + 2) ^ 10 := le_trans (by norm_num) hm
  exact Nat.mul_le_mul_right _ this

/-- **`fpuT` is polynomial-time computable.** -/
theorem fpuT_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    fpuT) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    fpup_redCmd 0 12 (fun x => fpuT (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := fpup_exec_redCmd x
      exact ⟨σ', h1.mono (fpup_T_le _), h2⟩)
    fpuT (fun t => (congrArg fpuT (FunBridge.dec2_flatMap_ic t)).symm)

/-- **SAT ≤ₚ unary 4-PARTITION** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `FPUI`. -/
theorem sat_le_fpu_of (h : ∀ w, SATLang w ↔ FPULang (FPUI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang FPULang := by
  obtain ⟨hd⟩ := mg_computable 1 (by norm_num) DMI mg_DMI
  obtain ⟨ht⟩ := tpup_F_computable
  obtain ⟨hf⟩ := fpuT_computable
  refine ⟨fpuT ∘ (tpup_F ∘ DMI), Pnp.TM2Comp.comp (Pnp.TM2Comp.comp hd ht) hf, fun w => ?_⟩
  rw [Function.comp_apply, Function.comp_apply, tpup_F_DMI]
  exact h w

end Pnp.Karp.FourPartU
