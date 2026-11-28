import Pnp.Karp.SeqRDProgB

/-!
# The unary scheduling reduction program and SAT ≤ₚ unary SEQUENCING WITH RELEASE TIMES AND
DEADLINES

`srp_redCmd`, on the bit string `x` on stack `0`, prints `srdT u` (`u = dec2 x`,
`Pnp/Karp/SeqRD.lean`) on stack `0`.  With `rows = clauses u`, `B` the length of the last row,
`k` the number of the other rows, `m = k / 3`, `P = B + 1`, `D = m P - 1`:

1. `parseLoop`, `trimC 4`, `move 4 1`: stack `1` holds the code of the rows;
2. `srp_mid`: copy the input to stack `9`, count the rows (`srp_cntL`, last row `B` in the
   buffer), restore the input, `P` on stack `5`, `m` on stack `8` (`srp_div`), `D` on stack `6`
   (`srp_mul`, `srp_p2 6`), `P` on stack `7`, `m - 1` on stack `8`;
3. `srp_itL` prints the item tasks, `srp_sL` the separator tasks.

`srdT_computable` (time bound `tb 13`) follows from `FunBridge.computable_of_cmd_code`;
`sat_le_srd_of` composes it with the unary 3-PARTITION reduction `tpup_F ∘ DMI`.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.SeqRD

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.ThreePartU Pnp.Karp.ThreePart Pnp.Karp.FourPartU Pnp.Karp.ThreeDM

def srp_pre : Cmd := .seq parseLoop (.seq (trimC 4) (move 4 1))

def srp_mid : Cmd :=
  .seq (copyVia 1 9 3) (.seq srp_cntL (.seq (copyVia 9 1 3) (.seq (copyVia 2 5 3)
    (.seq (pushList 5 (rv [pos])) (.seq (drain 2) (.seq srp_div (.seq (copyVia 8 4 3)
    (.seq srp_mul (.seq (srp_p2 6) (.seq (copyVia 5 7 3) srp_p1))))))))))

/-- The reduction program. -/
def srp_redCmd : Cmd := .seq srp_pre (.seq srp_mid (.seq srp_itL srp_sL))

theorem srp_ex_pre (x : Str) :
    ExecLe srp_pre (init [x]).stk
      (.norm (srp_st [] (fpup_code (clauses (FunBridge.dec2 x))) [] [] [] [] [] [] []))
      (10 * x.length + 20) := by
  set w := FunBridge.dec2 x
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have hLw : (trunc w).length ≤ w.length := length_trunc_le w
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ1 := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := exec_trimC_word 4 w σ1 (by simp [σ1, he 4 (by decide)])
  set σ2 := update σ1 4 (((trunc w).flatMap ic).reverse)
  have hW : (σ2 4).length = 2 * (trunc w).length := by
    simp only [σ2, update_self, List.length_reverse, length_flatMap_ic]
  have m1 := exec_move (a := 4) (b := 1) (by decide) _ σ2 rfl
  have hfin : update (update σ2 4 []) 1 ((σ2 4).reverse ++ σ2 1) =
      srp_st [] (fpup_code (clauses w)) [] [] [] [] [] [] [] := by
    funext j
    by_cases hj : j < 10
    · interval_cases j <;> simp [σ2, σ1, he, srp_st, fpup_code, trunc]
    · simp [σ2, σ1, srp_st, update_apply, he j (by omega), show j ≠ 0 by omega,
        show j ≠ 1 by omega, show j ≠ 2 by omega, show j ≠ 4 by omega, show j ≠ 5 by omega,
        show j ≠ 6 by omega, show j ≠ 7 by omega, show j ≠ 8 by omega, show j ≠ 9 by omega]
  rw [hfin] at m1
  refine (p1.seq_norm (p2.seq_norm (ExecLe.of m1))).mono ?_
  rw [hW]; omega

theorem srp_out_eq (w : List SatSym) :
    srp_itO (((clauses w).dropLast.length / 3) * (((clauses w).getLastD []).length + 1) - 1)
        (clauses w) ++
      srp_sO (((clauses w).getLastD []).length + 1) 0 ((clauses w).dropLast.length / 3 - 1) =
      srdT w := by
  rw [srp_sO_eq]
  simp [srdT, srp_itO, List.flatMap_append]

theorem srp_len_code (w : List SatSym) :
    (fpup_code (clauses w)).length = 2 * (trunc w).length := by
  unfold fpup_code trunc; exact length_flatMap_ic _

set_option maxHeartbeats 2000000 in
theorem srp_exec_redCmd (x : Str) : ∃ σ', ExecLe srp_redCmd (init [x]).stk (.norm σ')
    (1000 * (x.length + 2) ^ 3) ∧ σ' 0 = ((srdT (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  set n := x.length
  have hwx : w.length ≤ n := FunBridge.length_dec2_le x
  have hLw : (trunc w).length ≤ w.length := length_trunc_le w
  have hrows : ∀ r ∈ clauses w, sep ∉ r ∧ r.length ≤ n := fun r hr =>
    ⟨sep_not_mem_clauses w r hr, by
      have := tpp_len_le (clauses w) r hr
      have h2 : ((clauses w).flatMap (· ++ [sep])).length = (trunc w).length := rfl
      omega⟩
  have hcl : (clauses w).length ≤ n := by
    have := tpp_cnt_le (clauses w)
    have h2 : ((clauses w).flatMap (· ++ [sep])).length = (trunc w).length := rfl
    omega
  have hcode : (fpup_code (clauses w)).length ≤ 2 * n := by
    have := srp_len_code w; omega
  set rows := clauses w with hrw
  set code := fpup_code rows
  set B := (rows.getLastD []).length
  set k := rows.dropLast.length
  set m := k / 3
  set P := B + 1
  set D := m * P - 1
  have hB : B ≤ n := by
    rcases rows.eq_nil_or_concat with h | ⟨L, c, h⟩
    · simp [B, h]
    · have := (hrows c (by rw [h]; simp)).2
      simpa [B, h, List.getLastD_eq_getLast?] using this
  have hk : k ≤ n := by
    have : k ≤ rows.length := by simp [k]
    omega
  have hm : m ≤ n := le_trans (Nat.div_le_self _ _) hk
  have hP : P ≤ n + 1 := by omega
  have hmP : m * P ≤ n * (n + 1) := Nat.mul_le_mul hm hP
  have hD : D ≤ n * (n + 1) := le_trans (Nat.sub_le _ _) hmP
  -- the phases
  have q0 := srp_ex_pre x
  have q1 := srp_ex_cp [] code [] [] [] [] [] [] [] (a := 1) (b := 9) (by decide) (by decide)
    (by decide)
  simp only [srp_u9, srp_st1, srp_st9, List.append_nil] at q1
  have q2 := srp_ex_cntL n [] [] [] [] [] code rows [] hrows
  simp only [List.append_nil] at q2
  have q3 := srp_ex_cp [] [] (rv (uRow B)) (List.replicate k false) [] [] [] [] code
    (a := 9) (b := 1) (by decide) (by decide) (by decide)
  simp only [srp_u1, srp_st1, srp_st9, List.append_nil] at q3
  have q4 := srp_ex_cp [] code (rv (uRow B)) (List.replicate k false) [] [] [] [] code
    (a := 2) (b := 5) (by decide) (by decide) (by decide)
  simp only [srp_u5, srp_st2, srp_st5, List.append_nil] at q4
  have q5 := (ExecLe.of (exec_pushList 5 (rv [pos])
    (srp_st [] code (rv (uRow B)) (List.replicate k false) (rv (uRow B)) [] [] [] code))).cast
    (by rw [srp_u5, srp_st5, ← fpup_rv_uRow_succ]) le_rfl
  have q6 := srp_ex_dr2 [] code (rv (uRow B)) (List.replicate k false) (rv (uRow P)) [] [] []
    code
  have q7 := srp_ex_div [] code [] (rv (uRow P)) [] [] code k []
  simp only [List.append_nil] at q7
  have q8 := srp_ex_cp [] code [] [] (rv (uRow P)) [] [] (List.replicate m false) code
    (a := 8) (b := 4) (by decide) (by decide) (by decide)
  simp only [srp_u4, srp_st8, srp_st4, List.append_nil] at q8
  have q9 := srp_ex_mul [] code [] (rv (uRow P)) [] (List.replicate m false) code m []
  simp only [List.append_nil, fpup_rv_uRow_mul] at q9
  have q10 := srp_ex_p2_uRow 6 (srp_st [] code [] [] (rv (uRow P)) (rv (uRow (m * P))) []
    (List.replicate m false) code) (m * P) rfl
  rw [srp_u6] at q10
  have q11 := srp_ex_cp [] code [] [] (rv (uRow P)) (rv (uRow D)) [] (List.replicate m false)
    code (a := 5) (b := 7) (by decide) (by decide) (by decide)
  simp only [srp_u7, srp_st5, srp_st7, List.append_nil] at q11
  have q12 := srp_ex_p1 [] code [] [] (rv (uRow P)) (rv (uRow D)) (rv (uRow P)) code m
  have q13 := srp_ex_itL D n [] (rv (uRow P)) (rv (uRow P)) (List.replicate (m - 1) false) code
    rows [] hrows
  simp only [rv_nil, List.nil_append] at q13
  have q14 := srp_ex_sL P ((n + 1) * (n + 1)) (by omega) [] (rv (uRow B)) [] (rv (uRow D)) code
    (m - 1) 0 (srp_itO D rows) (by
      have : 0 + (m - 1) + 1 ≤ n + 1 := by omega
      exact Nat.mul_le_mul this hP)
  simp only [Nat.zero_add, Nat.one_mul] at q14
  have hall := q0.seq_norm ((q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm (q5.seq_norm
    (q6.seq_norm (q7.seq_norm (q8.seq_norm (q9.seq_norm (q10.seq_norm (q11.seq_norm
    q12))))))))))).seq_norm (q13.seq_norm q14))
  refine ⟨_, hall.mono ?_, ?_⟩
  · simp only [srp_st1, srp_st2, srp_st4, srp_st5, srp_st8, srp_st9, fpup_len_rv_uRow,
      List.length_replicate, List.length_cons, List.length_nil, List.length_reverse,
      length_flatMap_ic, rv, uRow, List.length_replicate]
    have e1 : (rows.length + 1) * (10 * n + 20) ≤ (n + 1) * (10 * n + 20) :=
      Nat.mul_le_mul_right _ (by omega)
    have e2 : (rows.length + 1) * (30 * n + 10 * D + 40) ≤
        (n + 1) * (30 * n + 10 * (n * (n + 1)) + 40) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e3 : (m - 1) * (30 * ((n + 1) * (n + 1)) + 50) ≤ n * (30 * ((n + 1) * (n + 1)) + 50) :=
      Nat.mul_le_mul_right _ (by omega)
    have e4 : m * (5 * (2 * P) + 5) ≤ n * (5 * (2 * (n + 1)) + 5) :=
      Nat.mul_le_mul hm (by omega)
    nlinarith
  · rw [srp_st0, ← srp_out_eq w]
    rfl

theorem srp_T_le (n : ℕ) : 1000 * (n + 2) ^ 3 ≤ tb 13 n := by
  unfold tb
  have hm : 2 ^ 10 ≤ (n + 2) ^ 10 := Nat.pow_le_pow_left (by omega) 10
  have e : (n + 2) ^ 13 = (n + 2) ^ 10 * (n + 2) ^ 3 := by ring
  rw [e]
  have : 1000 ≤ (n + 2) ^ 10 := le_trans (by norm_num) hm
  exact Nat.mul_le_mul_right _ this

/-- **`srdT` is polynomial-time computable.** -/
theorem srdT_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    srdT) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    srp_redCmd 0 13 (fun x => srdT (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := srp_exec_redCmd x
      exact ⟨σ', h1.mono (srp_T_le _), h2⟩)
    srdT (fun t => (congrArg srdT (FunBridge.dec2_flatMap_ic t)).symm)

/-- **SAT ≤ₚ unary SEQUENCING WITH RELEASE TIMES AND DEADLINES** (official polynomial-time
many-one reducibility), given the correctness of the reduction instance `SRDI`. -/
theorem sat_le_srd_of (h : ∀ w, SATLang w ↔ SRDLang (SRDI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang SRDLang := by
  obtain ⟨hd⟩ := mg_computable 1 (by norm_num) DMI mg_DMI
  obtain ⟨ht⟩ := tpup_F_computable
  obtain ⟨hf⟩ := srdT_computable
  refine ⟨srdT ∘ (tpup_F ∘ DMI), Pnp.TM2Comp.comp (Pnp.TM2Comp.comp hd ht) hf, fun w => ?_⟩
  rw [Function.comp_apply, Function.comp_apply, tpup_F_DMI]
  exact h w

end Pnp.Karp.SeqRD
