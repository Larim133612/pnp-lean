import Pnp.Karp.MaxCutGen

/-!
# The MAX CUT reduction program, part 2: the whole program and SAT ≤ₚ MAX CUT

`mcp_redCmd` (layout and loops: `Pnp/Karp/MaxCutGen.lean`), on the bit string `x` on stack `0`:

1. `parseLoop`, `trimC 4`, `move 4 2` (as for CLIQUE): stack `2` holds the code `W` of
   `trunc w`, `w = dec2 x`;
2. copy `W` to stack `4`, run `mcp_kLoop` (five zeros per symbol), print `zero, sep`: the bound
   row `kRow w`; then print the rows `preRows` (`sep, pos, sep`);
3. copy `W` to stack `4`, run `mcp_litLoop`: the literal rows `litRows L`; afterwards register
   `5` holds `2L`; empty register `6`, copy register `5` into `8`;
4. copy `W` to stack `3`, run `mcp_gLoop`: the gadget rows `gadAll L 0 (annW w)`.

`mcp_exec_redCmd`: it terminates within `mcp_Tred |x| = O(|x|²)` steps with the reversed code of
`MCI (dec2 x)` on stack `1`, so `sat_le_mc_of` follows from `FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.MaxCut

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-- The end of the bound row and the rows `preRows`. -/
def mcp_hdr : List SatSym := [zero, sep, sep, pos, sep]

/-- The reduction program. -/
def mcp_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq (copyVia 2 4 11) (.seq mcp_kLoop
    (.seq (emL mcp_hdr) (.seq (copyVia 2 4 11) (.seq mcp_litLoop (.seq (drain 6)
    (.seq (copyVia 5 8 11) (.seq (copyVia 2 3 11) mcp_gLoop))))))))))

/-- `MCI w` as printed by the program. -/
theorem mcp_MCI_eq (w : List SatSym) : MCI w =
    List.replicate (5 * (trunc w).length) zero ++ mcp_hdr ++ mcp_litOut 0 (trunc w).length ++
    (gadAll (annW w).length 0 (ann (trunc w) 0 0)).flatMap (· ++ [sep]) := by
  have hL : (annW w).length = (trunc w).length := length_ann _ _ _
  rw [MCI, List.flatMap_cons, gRows, List.flatMap_append, List.flatMap_append,
    ← mcp_litOut_litRows, kRow, hL, List.replicate_succ']
  simp [mcp_hdr, preRows, annW, List.append_assoc]

/-- Time bound of the program. -/
def mcp_Tred (n : ℕ) : ℕ := 500 * n * n + 1000 * n + 1000

theorem mcp_exec_redCmd (x : Str) :
    ∃ σ', ExecLe mcp_redCmd (init [x]).stk (.norm σ') (mcp_Tred x.length) ∧
      σ' 1 = ((MCI (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  set L := trunc w
  set W := L.flatMap ic
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have hLw : L.length ≤ w.length := length_trunc_le w
  have hW : W.length = 2 * L.length := length_flatMap_ic L
  have hLc : (annW w).length = L.length := length_ann _ _ _
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
  have e3 : update (update σ2 4 []) 2 ((σ2 4).reverse ++ σ2 2) = mcp_S W [] [] [] 0 0 0 := by
    funext j
    simp only [σ2, σ1, mcp_S, Clique.st2, update_apply, rv_nil, W, L]
    split_ifs <;> simp_all [mcp_regs]
  rw [e3] at p3
  have q1 : ExecLe (copyVia 2 4 11) (mcp_S W [] [] [] 0 0 0) (.norm (mcp_S W [] W [] 0 0 0))
      (5 * W.length + 4) := ex_copyW _ _ (mcp_regs_11 0 0 0)
  have q2 : ExecLe mcp_kLoop (mcp_S W [] W [] 0 0 0)
      (.norm (mcp_S W [] [] ([] ++ List.replicate (5 * L.length) zero) 0 0 0))
      (13 * L.length + 2) := mcp_ex_kLoop W [] (mcp_regs 0 0 0) L []
  set E0 := [] ++ List.replicate (5 * L.length) zero
  have q3 := mcp_em_emL mcp_hdr 0 0 0 W [] [] E0
  have q4 : ExecLe (copyVia 2 4 11) (mcp_S W [] [] (E0 ++ mcp_hdr) 0 0 0)
      (.norm (mcp_S W [] W (E0 ++ mcp_hdr) 0 0 0)) (5 * W.length + 4) :=
    ex_copyW _ _ (mcp_regs_11 0 0 0)
  have q5 := mcp_ex_litLoop W [] L.length L 0 (E0 ++ mcp_hdr) (by omega)
  set E1 := E0 ++ mcp_hdr ++ mcp_litOut 0 L.length
  have q6 := mcp_ex_drain6 W [] [] E1 (2 * (0 + L.length)) (0 + L.length) 0
  have q7 := mcp_ex_copy58 W [] [] E1 (2 * (0 + L.length)) 0
  have q8 : ExecLe (copyVia 2 3 11) (mcp_S W [] [] E1 (2 * (0 + L.length)) 0 (2 * (0 + L.length)))
      (.norm (mcp_S W W [] E1 (2 * (0 + L.length)) 0 (2 * (0 + L.length)))) (5 * W.length + 4) := by
    refine (ExecLe.of (exec_copyVia (a := 2) (b := 3) (t := 11) (by decide) (by decide)
      (by decide) _ (by simp [mcp_S, st2_reg]))).cast ?_ (by simp [mcp_S])
    simp only [mcp_S, st2_2, st2_3, List.append_nil]; rw [upd2_3]
  obtain ⟨j', e', q9⟩ := mcp_ex_gLoop (annW w).length L.length W (by omega) L 0 0 0
    (2 * (0 + L.length)) (2 * (0 + L.length)) E1 le_rfl (by omega) (by omega) (by omega)
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm (q1.seq_norm (q2.seq_norm
    (q3.seq_norm (q4.seq_norm (q5.seq_norm (q6.seq_norm (q7.seq_norm (q8.seq_norm
    q9))))))))))).cast rfl ?_, ?_⟩
  · have ht : mcp_hdr.length = 5 := rfl
    simp only [σ2, update_self, List.length_reverse, hW, mcp_Tred, ht]
    have : L.length ≤ x.length := by omega
    have h1 : L.length * (18 * L.length + 42) ≤ x.length * (18 * x.length + 42) :=
      Nat.mul_le_mul this (by omega)
    have h2 : L.length * (400 * L.length + 400) ≤ x.length * (400 * x.length + 400) :=
      Nat.mul_le_mul this (by omega)
    nlinarith
  · simp only [mcp_S_1, rv, E1, E0]
    rw [mcp_MCI_eq w]
    simp only [List.nil_append]; rfl

theorem mcp_Tred_le (n : ℕ) : mcp_Tred n ≤ tb 11 n := by
  unfold mcp_Tred tb
  have h9 : 2 ^ 9 ≤ (n + 2) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have e : (n + 2) ^ 11 = (n + 2) ^ 2 * (n + 2) ^ 9 := by ring
  rw [e]; norm_num at h9
  nlinarith

/-! ## The reduction -/

/-- **SAT ≤ₚ MAX CUT** (official polynomial-time many-one reducibility), given the correctness
of the reduction instance `MCI`. -/
theorem sat_le_mc_of (h : ∀ w, SATLang w ↔ MCLang (MCI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang MCLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    mcp_redCmd 1 11 (fun x => MCI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := mcp_exec_redCmd x
      exact ⟨σ', h1.mono (mcp_Tred_le _), h2⟩)
    MCI (fun t => (congrArg MCI (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨MCI, hc, h⟩

end Pnp.Karp.MaxCut
