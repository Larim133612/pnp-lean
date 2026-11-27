import Pnp.Karp.SetCover
import Pnp.Karp.ThreeDMProg

/-!
# The SET COVER reduction program and SAT ≤ₚ SET COVER

`sp_redCmd` is the X3C reduction program `mg_redCmd 3` (`Pnp/Karp/ThreeDMProg.lean`) with the
header phase `mg_hdC 3` followed by `mg_hdC 1`, which prints the budget row `zero^q` after the
header `zero^(3q)`.  It prints `SCI w` (`sp_exec_redCmd`) within `(n + 2)^22` steps, giving
`sat_le_sc_of`.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.SetCover

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM

/-- **The SET COVER instance as printed by the program.** -/
theorem sp_SCI_eq (w : List SatSym) : SCI w =
    List.replicate (3 * qB w) zero ++ [sep] ++ (List.replicate (1 * qB w) zero ++ [sep]) ++
      mg_ringP (qB w) (NV w) (mC w) ++ mg_clP (qB w) (NV w * mC w) (mC w) (clauses w) ++
      mg_garP (qB w) (NV w * mC w) (mC w) := by
  have h := mg_out_eq 3 w
  simp only [mg_out, List.flatMap_cons, List.append_assoc] at h
  simp only [SCI, List.flatMap_cons, List.append_assoc, one_mul]
  rw [List.append_cancel_left (List.append_cancel_left h)]

/-- The reduction program: `mg_redCmd 3` with the extra budget row `zero^q`. -/
def sp_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq (copyVia 2 4 11) (.seq (.push 5 true)
  (.seq sg_cntLoop (.seq mg_setC (.seq (.seq (mg_hdC 3) (mg_hdC 1))
    (.seq mg_ringC (.seq mg_clC mg_garC)))))))))

/-- Time bound of the program. -/
def sp_Tred (n : ℕ) : ℕ := mg_Tred n + (9 * mg_U n + 6) + 4

set_option maxHeartbeats 1600000 in
/-- The program prints `SCI` of the decoded input. -/
theorem sp_exec_redCmd (x : Str) : ∃ σ', ExecLe sp_redCmd
    (init [x]).stk (.norm σ') (sp_Tred x.length) ∧
    σ' 1 = ((SCI (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  set L := trunc w
  set W := L.flatMap ic
  set m := mC w
  set N := NV w
  set V := x.length + 1 with hVd
  set U := mg_U x.length with hUd
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have hLw : L.length ≤ w.length := length_trunc_le w
  have hmw : m ≤ w.length := length_clauses_le w
  have hW : W.length = 2 * L.length := length_flatMap_ic L
  have hN : N = L.length + 1 := rfl
  have hNV : N ≤ V := by omega
  have hmV : m ≤ V := by omega
  have hU : 2 * (N * m) + N + m ≤ U := by
    have h1 : N * m ≤ V * V := Nat.mul_le_mul hNV hmV
    have h2 : V ≤ V * V := Nat.le_mul_of_pos_left V (by omega)
    rw [hUd, mg_U, ← hVd]; omega
  have hcnt : (L.flatMap Clique.hg).length = m := by
    simp only [L, hg_trunc, List.length_replicate]; rfl
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ1 := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := exec_trimC_word 4 w σ1 (by simp [σ1, he 4 (by decide)])
  set σ2 := update σ1 4 ((L.flatMap ic).reverse)
  have p3 := exec_move (a := 4) (b := 2) (by decide) _ σ2 rfl
  have e3 : update (update σ2 4 []) 2 ((σ2 4).reverse ++ σ2 2) =
      Clique.st2 W [] [] (rv []) fun _ => 0 := by
    funext j
    simp only [σ2, σ1, Clique.st2, update_apply, rv_nil, W, L]
    split_ifs <;> simp_all
  rw [e3] at p3
  -- counting
  have q1 := ex_copyW (W := W) (O := []) (rv []) (fun _ : ℕ => (0 : ℕ)) rfl
  have q2 := ex_push_reg (W := W) (O := []) (Q := W) (r := 5) (by norm_num) (rv [])
    (fun _ : ℕ => (0 : ℕ))
  obtain ⟨v1, c1, c2, c3, q3⟩ := sg_ex_cnt W [] L []
    (update (fun _ : ℕ => (0 : ℕ)) 5 ((fun _ : ℕ => (0 : ℕ)) 5 + 1))
  have v1_5 : v1 5 = N := by rw [c2]; simp [hN]; omega
  have v1_9 : v1 9 = m := by rw [c3, hcnt]; simp
  have v1_o : ∀ r, r ≠ 5 → r ≠ 9 → v1 r = 0 := fun r a b => by rw [c1 r a b]; simp [a]
  -- the phases
  obtain ⟨v2, hG2, f2, q4⟩ := mg_ex_set N m U hU W [] [] [] v1 v1_5 v1_9 v1_o
  have q5 := ((mg_em_hd 3 hG2 (U := U) (by omega)).seq (mg_em_hd 1 hG2 (U := U) (by omega)))
    W [] [] []
  set E1 := [] ++ (List.replicate (3 * (2 * (N * m))) zero ++ [sep] ++
    (List.replicate (1 * (2 * (N * m))) zero ++ [sep]))
  obtain ⟨v3, f3, q6⟩ := mg_ex_ring N m U hU W [] [] E1 v2 hG2 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [f2 r (by omega) (by omega) (by omega) (by omega), v1_o r (by omega) (by omega)])
  set E2 := E1 ++ mg_ringP (2 * (N * m)) N m
  have hG3 : mg_G v3 N m := mg_G_out [15, 16, 17, 18, 19, 20] hG2 f3 (by decide)
  obtain ⟨v4, f4, q7⟩ := mg_ex_cl N m U hU W [] (clauses w)
    (fun c hc => by
      refine ⟨sep_not_mem_clauses w c hc, ?_⟩
      have := Ham.hg_len_le_flatMap hc
      simp only [N, NV, trunc] at this ⊢; omega)
    rfl rfl (by rw [hW, hN]; omega) E2 v3 hG3 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [f3 r (by simp; omega), f2 r (by omega) (by omega) (by omega) (by omega),
      v1_o r (by omega) (by omega)])
  set E3 := E2 ++ mg_clP (2 * (N * m)) (N * m) m (clauses w)
  have hG4 : mg_G v4 N m := mg_G_out [21, 22, 23, 24, 33] hG3 f4 (by decide)
  obtain ⟨v5, q8⟩ := mg_ex_gar N m U hU W [] [] E3 v4 hG4 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [f4 r (by simp; omega), f3 r (by simp; omega),
      f2 r (by omega) (by omega) (by omega) (by omega), v1_o r (by omega) (by omega)])
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm (q1.seq_norm (q2.seq_norm
    (q3.seq_norm (q4.seq_norm (q5.seq_norm (q6.seq_norm (q7.seq_norm q8)))))))))).cast rfl ?_, ?_⟩
  · have tσ : (σ2 4).length = W.length := by simp [σ2, W]
    rw [tσ, hW]
    unfold sp_Tred mg_Tred
    rw [← hUd, ← hVd]
    omega
  · simp only [st2_1, rv, E3, E2, E1]
    rw [sp_SCI_eq w, show qB w = 2 * (N * m) by unfold qB; ring]
    simp only [List.append_assoc, List.nil_append]
    rfl

/-- The polynomial time bound. -/
theorem sp_Tred_le (n : ℕ) : sp_Tred n ≤ tb 22 n := by
  unfold sp_Tred mg_Tred mg_U tb
  set V := n + 1
  set P := n + 2
  have e : 100 * V + 100 + mg_tS (4 * (V * V)) + 3 * (9 * (4 * (V * V)) + 6) + 4 +
      mg_tR (4 * (V * V)) + mg_tC (4 * (V * V)) + mg_tG (4 * (V * V)) + (9 * (4 * (V * V)) + 6) + 4 =
      42368 * V ^ 6 + 14720 * V ^ 4 + 1952 * V ^ 2 + 100 * V + 292 := by
    unfold mg_tS mg_tR mg_tRO mg_tC mg_tCO mg_tSy mg_tG mg_tGO mg_rowT mg_ohT; ring
  rw [e]
  have hVP : V ≤ P := by omega
  have h1 : 1 ≤ P := by omega
  have k6 : V ^ 6 ≤ P ^ 6 := Nat.pow_le_pow_left hVP 6
  have k4 : V ^ 4 ≤ P ^ 6 :=
    le_trans (Nat.pow_le_pow_left hVP 4) (Nat.pow_le_pow_right h1 (by norm_num))
  have k2 : V ^ 2 ≤ P ^ 6 :=
    le_trans (Nat.pow_le_pow_left hVP 2) (Nat.pow_le_pow_right h1 (by norm_num))
  have k1 : V ≤ P ^ 6 := le_trans hVP (by
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ 6 := Nat.pow_le_pow_right h1 (by norm_num))
  have k0 : 1 ≤ P ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 ^ 16 ≤ P ^ 16 := Nat.pow_le_pow_left (by omega) 16
  have h3 : 2 ^ 16 * P ^ 6 ≤ P ^ 16 * P ^ 6 := Nat.mul_le_mul h2 le_rfl
  have e2 : P ^ 22 = P ^ 16 * P ^ 6 := by ring
  rw [e2]
  norm_num at h3
  generalize P ^ 16 * P ^ 6 = A at *
  generalize P ^ 6 = B at *
  generalize V ^ 6 = a6 at *
  generalize V ^ 4 = a4 at *
  generalize V ^ 2 = a2 at *
  clear_value V P
  omega

/-! ## The reduction -/

theorem sp_computable :
    Nonempty (Turing.TM2ComputableInPolyTime (Millennium.fin_encoding_string SatSym).encode
      (Millennium.fin_encoding_string SatSym).encode SCI) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    sp_redCmd 1 22 (fun x => SCI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := sp_exec_redCmd x
      exact ⟨σ', h1.mono (sp_Tred_le _), h2⟩)
    SCI (fun t => (congrArg SCI (FunBridge.dec2_flatMap_ic t)).symm)

/-- **SAT ≤ₚ SET COVER** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `SCI`. -/
theorem sat_le_sc_of (h : ∀ w, SATLang w ↔ SCLang (SCI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang SCLang := by
  obtain ⟨hc⟩ := sp_computable
  exact ⟨SCI, hc, h⟩

end Pnp.Karp.SetCover
