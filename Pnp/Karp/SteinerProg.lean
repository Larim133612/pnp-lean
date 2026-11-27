import Pnp.Karp.Steiner
import Pnp.Karp.ThreeDMProg
import Pnp.Karp.IndSet

/-!
# The STEINER TREE reduction program and SAT ≤ₚ STEINER TREE

`STI w` is computed as a composition of two polynomial-time computable functions:

1. `stp_SRC`, computed by `stp_redCmd`: the X3C reduction program `mg_redCmd`
   (`Pnp/Karp/ThreeDMProg.lean`) with the header phase replaced by `stp_hdC`, which prints
   `zero^(4q) neg pos^(3q) pos neg neg^(3q) neg` (`q` in register `14`); the triple rows
   `triRows w` (each followed by `sep`) come after it, as for X3C;
2. the symbol homomorphism `stH` (`zero ↦ zero`, `pos ↦ pos`, `neg ↦ sep`,
   `sep ↦ pos sep`), which turns `stp_SRC w` into `STI w` (`stp_STI_eq`), since the triple
   rows contain only `zero` and `pos`.

`sat_le_st_of` (given the correctness `SATLang w ↔ STLang (STI w)`) follows with
`Pnp.TM2Comp.comp`.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.Steiner

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM

/-! ## The source word and the homomorphism -/

/-- The symbol homomorphism. -/
def stH : SatSym → List SatSym
  | zero => [zero]
  | pos => [pos]
  | neg => [sep]
  | sep => [pos, sep]

/-- The header printed by `stp_hdC`. -/
def stp_hdr (q : ℕ) : List SatSym :=
  List.replicate (4 * q) zero ++ [neg] ++ List.replicate (3 * q) pos ++ [pos, neg] ++
    List.replicate (3 * q) neg ++ [neg]

/-- The word printed by the program. -/
def stp_SRC (w : List SatSym) : List SatSym :=
  stp_hdr (qB w) ++ (triRows w).flatMap (· ++ [sep])

theorem stp_fm_rep {α : Type} (a : α) (f : α → List SatSym) :
    ∀ n, (List.replicate n a).flatMap f = (List.replicate n (f a)).flatten
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, stp_fm_rep a f n]

theorem stp_flat_rep1 (a : SatSym) : ∀ n, (List.replicate n [a]).flatten = List.replicate n a
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, stp_flat_rep1 a n]

theorem stp_flat_rep3 (a : SatSym) :
    ∀ n, (List.replicate n [a, a, a]).flatten = List.replicate (3 * n) a
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, stp_flat_rep3 a n,
      show 3 * (n + 1) = 3 + 3 * n by ring, ← List.replicate_append_replicate]
    rfl

theorem stp_fix : ∀ r : List SatSym, (∀ x ∈ r, x = zero ∨ x = pos) → r.flatMap stH = r
  | [], _ => rfl
  | x :: r, h => by
    rw [List.flatMap_cons, stp_fix r (fun y hy => h y (by simp [hy]))]
    rcases h x (by simp) with rfl | rfl <;> rfl

theorem stp_triRows_sym (w : List SatSym) :
    ∀ r ∈ triRows w, ∀ x ∈ r, x = zero ∨ x = pos := by
  intro r hr x hx
  simp only [triRows, List.mem_map] at hr
  obtain ⟨t, -, rfl⟩ := hr
  simp only [triRow, oh, List.mem_append, List.mem_map] at hx
  rcases hx with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩ <;> split_ifs <;> simp

/-- **`STI` is the homomorphic image of the source word.** -/
theorem stp_STI_eq (w : List SatSym) : STI w = (stp_SRC w).flatMap stH := by
  have hr : ((triRows w).flatMap (· ++ [sep])).flatMap stH =
      (triRows w).flatMap (fun r => r ++ ([pos] ++ [sep])) := by
    rw [List.flatMap_assoc]
    refine List.flatMap_congr fun r hr => ?_
    rw [List.flatMap_append, stp_fix r (stp_triRows_sym w r hr)]
    simp [stH]
  have e3 : ∀ n, (List.replicate n ([] : List SatSym)).flatMap (· ++ [sep]) =
      List.replicate n sep := fun n => by rw [stp_fm_rep]; exact stp_flat_rep1 sep n
  simp only [STI, STW, stRows, stp_SRC, stp_hdr, List.flatMap_cons, List.flatMap_append,
    List.flatMap_map, List.append_assoc, e3, hr]
  simp only [stp_fm_rep, stH, stp_flat_rep1, List.flatMap_nil, List.append_assoc,
    List.cons_append, List.nil_append, List.singleton_append, List.replicate_succ',
    List.flatMap_cons]

/-- The source word in the form printed by the program. -/
theorem stp_SRC_eq (w : List SatSym) : stp_SRC w =
    stp_hdr (qB w) ++ mg_ringP (qB w) (NV w) (mC w) ++ mg_clP (qB w) (NV w * mC w) (mC w) (clauses w) ++
      mg_garP (qB w) (NV w * mC w) (mC w) := by
  have h := mg_out_eq 3 w
  simp only [mg_out, List.flatMap_cons, List.append_assoc] at h
  simp only [stp_SRC, List.append_assoc]
  rw [List.append_cancel_left (List.append_cancel_left h)]

/-! ## The header phase -/

/-- Print `v 14` copies of `L` (counter `10`). -/
def stp_repC (L : List SatSym) : Cmd := sg_rep 14 10 (emL L)

/-- The header phase: `zero^(4q) neg pos^(3q) pos neg neg^(3q) neg`. -/
def stp_hdC : Cmd :=
  .seq (mg_zsL (List.replicate 4 14)) (.seq (emL [neg]) (.seq (stp_repC [pos, pos, pos])
    (.seq (emL [pos, neg]) (.seq (stp_repC [neg, neg, neg]) (emL [neg])))))

theorem stp_em_rep (a : SatSym) {v : ℕ → ℕ} {U : ℕ} (h10 : v 10 = 0) (h11 : v 11 = 0)
    (hU : v 14 ≤ U) :
    sg_Em (stp_repC [a, a, a]) v (List.replicate (3 * v 14) a) (13 * U + 6) :=
  (sg_em_rep (r := 14) (c := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h10 h11 (fun n => sg_em_emL [a, a, a] _)).cast (stp_flat_rep3 a _)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem stp_em_hd {v : ℕ → ℕ} {N m U : ℕ} (hG : mg_G v N m) (hU : 2 * (N * m) ≤ U)
    (h10 : v 10 = 0) :
    sg_Em stp_hdC v (stp_hdr (2 * (N * m))) (62 * U + 48) := by
  obtain ⟨-, -, -, -, h14, -, h7, h11, -⟩ := hG
  have a := mg_em_zsL U h7 h11 (List.replicate 4 14) (fun r hr => by
    rw [List.eq_of_mem_replicate hr]; exact ⟨by norm_num, by norm_num, by norm_num, by omega⟩)
  rw [mg_sum_rep, h14, List.length_replicate] at a
  have b := stp_em_rep pos h10 h11 (U := U) (by omega)
  have c := stp_em_rep neg h10 h11 (U := U) (by omega)
  rw [h14] at b c
  refine (a.seq ((sg_em_emL [neg] v).seq (b.seq ((sg_em_emL [pos, neg] v).seq
    (c.seq (sg_em_emL [neg] v)))))).cast ?_ ?_
  · simp only [stp_hdr, List.append_assoc]
  · simp only [List.length_cons, List.length_nil]; omega

/-! ## The whole program -/

/-- The reduction program: `mg_redCmd` with the header phase `stp_hdC`. -/
def stp_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq (copyVia 2 4 11) (.seq (.push 5 true)
  (.seq sg_cntLoop (.seq mg_setC (.seq stp_hdC
    (.seq mg_ringC (.seq mg_clC mg_garC)))))))))

/-- Time bound of the program. -/
def stp_Tred (n : ℕ) : ℕ := mg_Tred n + (62 * mg_U n + 48)

set_option maxHeartbeats 1600000 in
/-- The program prints `stp_SRC` of the decoded input. -/
theorem stp_exec_redCmd (x : Str) : ∃ σ', ExecLe stp_redCmd
    (init [x]).stk (.norm σ') (stp_Tred x.length) ∧
    σ' 1 = ((stp_SRC (FunBridge.dec2 x)).flatMap ic).reverse := by
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
  have q5 := stp_em_hd hG2 (U := U) (by omega)
    (by rw [f2 10 (by omega) (by omega) (by omega) (by omega), v1_o 10 (by omega) (by omega)])
    W [] [] []
  set E1 := [] ++ stp_hdr (2 * (N * m))
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
    unfold stp_Tred mg_Tred
    rw [← hUd, ← hVd]
    omega
  · simp only [st2_1, rv, E3, E2, E1]
    rw [stp_SRC_eq w, show qB w = 2 * (N * m) by unfold qB; ring]
    simp only [List.append_assoc, List.nil_append]
    rfl

/-- The polynomial time bound. -/
theorem stp_Tred_le (n : ℕ) : stp_Tred n ≤ tb 22 n := by
  unfold stp_Tred mg_Tred mg_U tb
  set V := n + 1
  set P := n + 2
  have e : 100 * V + 100 + mg_tS (4 * (V * V)) + 3 * (9 * (4 * (V * V)) + 6) + 4 +
      mg_tR (4 * (V * V)) + mg_tC (4 * (V * V)) + mg_tG (4 * (V * V)) + (62 * (4 * (V * V)) + 48) =
      42368 * V ^ 6 + 14720 * V ^ 4 + 2164 * V ^ 2 + 100 * V + 330 := by
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

/-- The source word is polynomial-time computable. -/
theorem stp_SRC_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    stp_SRC) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    stp_redCmd 1 22 (fun x => stp_SRC (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := stp_exec_redCmd x
      exact ⟨σ', h1.mono (stp_Tred_le _), h2⟩)
    stp_SRC (fun t => (congrArg stp_SRC (FunBridge.dec2_flatMap_ic t)).symm)

/-- The homomorphism `stH` is polynomial-time computable. -/
theorem stp_hom_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    (fun w : List SatSym => w.flatMap stH)) := by
  have e : FunBridge.dec2 ∘ (fun t => ((Millennium.fin_encoding_string SatSym).encode t).flatMap
      fun s => (stH s).flatMap ic) = fun w : List SatSym => w.flatMap stH := by
    funext t
    simp only [comp_apply, Millennium.fin_encoding_string_encode]
    rw [← FunBridge.dec2_flatMap_ic (t.flatMap stH), List.flatMap_assoc]
  rw [← e]
  exact ⟨Pnp.TM2Comp.comp (Pnp.TM2Hom.homComp _ _) FunBridge.computableB⟩

/-- **SAT ≤ₚ STEINER TREE** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `STI`. -/
theorem sat_le_st_of (h : ∀ w, SATLang w ↔ STLang (STI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang STLang := by
  obtain ⟨hS⟩ := stp_SRC_computable
  obtain ⟨hH⟩ := stp_hom_computable
  have e : (fun w : List SatSym => w.flatMap stH) ∘ stp_SRC = STI :=
    funext fun w => (stp_STI_eq w).symm
  exact ⟨_, e ▸ Pnp.TM2Comp.comp hS hH, h⟩

end Pnp.Karp.Steiner
