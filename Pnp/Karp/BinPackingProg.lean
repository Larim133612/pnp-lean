import Pnp.Karp.BinPacking
import Pnp.Karp.PartProg

/-!
# The BIN PACKING reduction program, PARTITION ≤ₚ BIN PACKING

`bpp_redCmd`, on the bit string `x` on stack `0`, prints `BPI w` (`w = dec2 x`,
`Pnp/Karp/BinPacking.lean`) on stack `0`:

1. `parseLoop`, `trimC 4`, `move 4 3`: stack `3` holds the code of the rows of `w`;
2. `pp_loop` (`Pnp/Karp/PartProg.lean`): print every row while adding it to the accumulator
   (stack `5`);
3. pop the least significant bit of the accumulator, print the rest (`toRow`), then
   `sep zero zero sep`.

`part_le_bp_of` follows from `FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.BinPacking

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Partition

/-- The reduction program. -/
def bpp_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 3) (.seq pp_loop
    (.seq (.pop 5 .skip .skip .skip) (.seq (pp_pr 5) (pp_emL [sep, zero, zero, sep]))))))

theorem bpp_ex_drop (R : Str) (A : Str) :
    ExecLe (.pop 5 .skip .skip .skip) (sv_st R [] [] A [] false)
      (.norm (sv_st R [] [] A.tail [] false)) 2 := by
  rcases A with _ | ⟨b, A⟩
  · exact ExecLe.pop_nil rfl (ExecLe.skip _)
  · refine ExecLe.pop_cons (b := b) (s := A) rfl ?_
    rw [sv_u5]
    cases b <;> exact ExecLe.skip _

theorem bpp_out_eq (w : List SatSym) :
    [] ++ (clauses w).flatMap (· ++ [sep]) ++ toRow (accRows [] (clauses w)).tail ++
      [sep, zero, zero, sep] = BPI w := by
  simp [BPI, List.flatMap_append, toRow, List.map_tail]

set_option maxHeartbeats 800000 in
theorem bpp_exec_redCmd (x : Str) : ∃ σ', ExecLe bpp_redCmd (init [x]).stk (.norm σ')
    (16 * (x.length + 2) ^ 2) ∧ σ' 0 = ((BPI (FunBridge.dec2 x)).flatMap ic).reverse := by
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
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hsep := sep_not_mem_clauses w
  have hW : (σ2 4).length = 2 * (trunc w).length := by
    simp only [σ2, update_self, List.length_reverse, length_flatMap_ic]
  have m1 := exec_move (a := 4) (b := 3) (by decide) _ σ2 rfl
  have hσ : update (update σ2 4 []) 3 ((σ2 4).reverse ++ σ2 3) =
      sv_st (rv []) (enc (clauses w)) [] [] [] false := by
    funext j
    simp only [σ2, σ1, sv_st, update_apply, enc, trunc, CookLevin.fl, rv_nil]
    split_ifs <;> simp_all
  rw [hσ] at m1
  have m4 := pp_ex_rows (T := []) x.length (clauses w) [] [] hsep (by simp; omega)
  set E1 := [] ++ (clauses w).flatMap (· ++ [sep])
  set S := accRows [] (clauses w)
  have m5 := bpp_ex_drop (rv E1) S
  set σa := sv_st (rv E1) [] [] S.tail [] false
  have m6 := pp_ex_pr (k := 5) (by decide) S.tail σa E1 rfl rfl
  set σb := update (update σa 5 []) 0 (rv (E1 ++ toRow S.tail))
  have m7 := pp_ex_emL' [sep, zero, zero, sep] (E1 ++ toRow S.tail) σb (by simp [σb])
  have hall := p1.seq_norm (p2.seq_norm ((ExecLe.of m1).seq_norm (m4.seq_norm
    (m5.seq_norm (m6.seq_norm m7)))))
  refine ⟨_, hall.mono ?_, ?_⟩
  · rw [pp_Trows_eq]
    have hS := pp_accRows_length [] (clauses w)
    have hSt : S.tail.length ≤ S.length := by simp
    simp only [hW, List.length_nil, List.length_cons] at hS ⊢
    have h1 : (clauses w).length * (8 * x.length + 20) ≤ x.length * (8 * x.length + 20) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · simp only [update_self]
    rw [← bpp_out_eq w]
    rfl

/-- **PARTITION ≤ₚ BIN PACKING** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `BPI`. -/
theorem part_le_bp_of (h : ∀ w, PartLang w ↔ BPLang (BPI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) PartLang BPLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    bpp_redCmd 0 6 (fun x => BPI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := bpp_exec_redCmd x
      exact ⟨σ', h1.mono (pp_T_le _), h2⟩)
    BPI (fun t => (congrArg BPI (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨BPI, hc, h⟩

end Pnp.Karp.BinPacking
