import Pnp.Karp.ColorGen

/-!
# The 3-COLORING reduction program, part 2: the whole program and SAT ≤ₚ 3-COLORING

`redCmd` (layout and loops: `Pnp/Karp/ColorGen.lean`), on the bit string `x` on stack `0`:

1. `parseLoop`, `trimC 4`, `move 4 2` (as for CLIQUE): stack `2` holds the code `W` of
   `trunc w`, `w = dec2 x`;
2. print the triangle rows `triRows`;
3. copy `W` to stack `4`, set register `5` to `1`, run `litLoop`: the literal rows
   `litRows L` (`L = |trunc w|`); afterwards register `5` holds `1 + 2L`; empty register `6`;
4. copy `W` to stack `3`, run `gLoop`: the gadget rows `gadAll L 0 (annW w)`.

`exec_redCmd`: it terminates within `Tred |x| = O(|x|²)` steps with the reversed code of
`G (dec2 x)` on stack `1`, so `sat_le_col_of` (given the correctness `SATLang w ↔ ColLang (G w)`)
follows from `FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.Color

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-- The triangle rows, each followed by `sep`. -/
def triOut : List SatSym := triRows.flatMap (· ++ [sep])

/-- The reduction program. -/
def redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq (emL triOut) (.seq (copyVia 2 4 11)
    (.seq (.push 5 true) (.seq litLoop (.seq (drain 6) (.seq (copyVia 2 3 11) gLoop))))))))

/-- `G w` as printed by the program. -/
theorem G_eq (w : List SatSym) : G w = triOut ++ litOut 0 (trunc w).length ++
    (gadAll (annW w).length 0 (ann (trunc w) 0 0)).flatMap (· ++ [sep]) := by
  rw [G, gRows, List.flatMap_append, List.flatMap_append, litOut_litRows, annW, length_ann]; rfl

/-- Time bound of the program. -/
def Tred (n : ℕ) : ℕ := 300 * n * n + 500 * n + 500

theorem exec_redCmd (x : Str) : ∃ σ', ExecLe redCmd (init [x]).stk (.norm σ') (Tred x.length) ∧
    σ' 1 = ((G (FunBridge.dec2 x)).flatMap ic).reverse := by
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
  have e3 : update (update σ2 4 []) 2 ((σ2 4).reverse ++ σ2 2) = S W [] [] [] 0 0 := by
    funext j
    simp only [σ2, σ1, S, Clique.st2, update_apply, rv_nil, W, L]
    split_ifs <;> simp_all [regs]
  rw [e3] at p3
  have q1 := em_emL triOut 0 0 W [] [] []
  have q2 : ExecLe (copyVia 2 4 11) (S W [] [] ([] ++ triOut) 0 0)
      (.norm (S W [] W ([] ++ triOut) 0 0)) (5 * W.length + 4) :=
    ex_copyW _ _ (regs_11 0 0)
  have q3 := ex_push5 W [] W ([] ++ triOut) 0 0
  have q4 := ex_litLoop W [] L.length L 0 ([] ++ triOut) (by omega)
  set E1 := [] ++ triOut ++ litOut 0 L.length
  have q5 := ex_drain6 W [] [] E1 (1 + 2 * (0 + L.length)) (0 + L.length)
  have eb : 1 + 2 * (0 + L.length) = 1 + 2 * (annW w).length + 3 * 0 := by rw [hLc]; ring
  replace q5 := q5.cast (by rw [eb]) le_rfl
  have q6 : ExecLe (copyVia 2 3 11) (S W [] [] E1 (1 + 2 * (annW w).length + 3 * 0) 0)
      (.norm (S W W [] E1 (1 + 2 * (annW w).length + 3 * 0) 0)) (5 * W.length + 4) := by
    refine (ExecLe.of (exec_copyVia (a := 2) (b := 3) (t := 11) (by decide) (by decide)
      (by decide) _ (by simp [S, st2_reg]))).cast ?_ (by simp [S])
    simp only [S, st2_2, st2_3, List.append_nil]; rw [upd2_3]
  obtain ⟨j', q7⟩ := ex_gLoop (annW w).length L.length W (by omega) L 0 0 0 E1 le_rfl (by omega)
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm (q1.seq_norm (q2.seq_norm
    (q3.seq_norm (q4.seq_norm (q5.seq_norm (q6.seq_norm q7))))))))).cast rfl ?_, ?_⟩
  · have ht : triOut.length = 9 := rfl
    simp only [σ2, update_self, List.length_reverse, hW, Tred, ht]
    have : L.length ≤ x.length := by omega
    have h1 : L.length * (18 * L.length + 42) ≤ x.length * (18 * x.length + 42) :=
      Nat.mul_le_mul this (by omega)
    have h2 : L.length * (200 * L.length + 200) ≤ x.length * (200 * x.length + 200) :=
      Nat.mul_le_mul this (by omega)
    nlinarith
  · simp only [S_1, rv, E1]
    rw [G_eq w]
    simp only [List.nil_append]; rfl

theorem Tred_le (n : ℕ) : Tred n ≤ tb 11 n := by
  unfold Tred tb
  have h9 : 2 ^ 9 ≤ (n + 2) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have e : (n + 2) ^ 11 = (n + 2) ^ 2 * (n + 2) ^ 9 := by ring
  rw [e]; norm_num at h9
  nlinarith

/-! ## The reduction -/

/-- **SAT ≤ₚ 3-COLORING** (official polynomial-time many-one reducibility), given the
correctness of the reduction graph `G`. -/
theorem sat_le_col_of (h : ∀ w, Pnp.CookLevin.SATLang w ↔ ColLang (G w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang ColLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    redCmd 1 11 (fun x => G (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := exec_redCmd x
      exact ⟨σ', h1.mono (Tred_le _), h2⟩)
    G (fun t => (congrArg G (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨G, hc, h⟩

end Pnp.Karp.Color
