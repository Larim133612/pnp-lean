import Pnp.Karp.DomSet
import Pnp.Karp.ThreeDMProg

/-!
# The DOMINATING SET reduction program, SAT ≤ₚ DOMINATING SET (given the correctness of `DSI`)

`dsp_redCmd`, on the bit string `x` on stack `0`, prints `DSI (dec2 x)`
(`Pnp/Karp/DomSet.lean`), on the layout `st2` of `Pnp/Karp/CliqueGen.lean`, following
`Pnp/Karp/HittingSetProg.lean`:

1. parsing, trimming and counting as for SUBSET SUM: `N = |trunc w| + 1` (register `5`);
2. `dsp_hdC`: the budget row `zero^N sep`;
3. `dsp_triC`: for `i < N`, three times the triangle row
   `zero^(3i) ++ [pos, pos, pos] ++ zero^(3(N-1-i)) ++ [sep]`
   (`i` in `15`, `N - 1 - i` in `16`, counter `17`);
4. `dsp_mapC`: the symbolwise image of `trunc w` under `dsp_trpS` (`pos ↦ [pos, zero, zero]`,
   `neg ↦ [zero, pos, zero]`, `zero ↦ [zero, zero, zero]`, `sep ↦ [sep]`), which is the list of
   the clause rows, each followed by `sep`.

`dsp_DSI_eq` is the closed form of `DSI w` printed in this order; `sat_le_ds_of` follows from
`FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.DomSet

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM

/-! ## The closed form -/

/-- The symbolwise image used for the clause rows (`trp`, and `sep ↦ [sep]`). -/
def dsp_trpS : SatSym → List SatSym
  | pos => [pos, zero, zero]
  | neg => [zero, pos, zero]
  | zero => [zero, zero, zero]
  | sep => [sep]

/-- A printed triangle row of the triangle `i` (with its `sep`). -/
def dsp_triO (N i : ℕ) : List SatSym :=
  List.replicate (3 * i) zero ++ [pos, pos, pos] ++ List.replicate (3 * (N - 1 - i)) zero ++ [sep]

/-- The three printed rows of the triangle `i`. -/
def dsp_triO3 (N i : ℕ) : List SatSym := dsp_triO N i ++ (dsp_triO N i ++ dsp_triO N i)

theorem dsp_triRow (N u : ℕ) (h : u < 3 * N) :
    triRow N u = List.replicate (3 * (u / 3)) zero ++
      pos :: pos :: pos :: List.replicate (3 * (N - 1 - u / 3)) zero := by
  apply List.ext_getElem
  · simp [triRow]; omega
  · intro n h1 h2
    simp only [triRow, List.getElem_map, List.getElem_range, List.getElem_append,
      List.length_replicate, List.getElem_replicate, List.getElem_cons]
    by_cases h3 : n < 3 * (u / 3)
    · simp [h3, show n / 3 ≠ u / 3 by omega]
    · by_cases h4 : n - 3 * (u / 3) = 0
      · simp [h3, h4, show n / 3 = u / 3 by omega]
      · by_cases h5 : n - 3 * (u / 3) - 1 = 0
        · simp [h3, h4, h5, show n / 3 = u / 3 by omega]
        · by_cases h6 : n - 3 * (u / 3) - 1 - 1 = 0
          · simp [h3, h4, h5, h6, show n / 3 = u / 3 by omega]
          · simp [h3, h4, h5, h6, show n / 3 ≠ u / 3 by omega]

theorem dsp_triRow_eq (N u : ℕ) (h : u < 3 * N) : triRow N u ++ [sep] = dsp_triO N (u / 3) := by
  rw [dsp_triRow N u h, dsp_triO]; simp

theorem dsp_flatMap_range3 {α : Type} (f : ℕ → List α) : ∀ M : ℕ,
    (List.range (3 * M)).flatMap f =
      (List.range M).flatMap fun i => f (3 * i) ++ (f (3 * i + 1) ++ f (3 * i + 2))
  | 0 => by simp
  | M + 1 => by
    rw [show 3 * (M + 1) = 3 * M + 1 + 1 + 1 by ring, List.range_succ, List.range_succ,
      List.range_succ, List.range_succ, List.flatMap_append, List.flatMap_append,
      List.flatMap_append, List.flatMap_append, dsp_flatMap_range3 f M]
    simp [List.append_assoc]

theorem dsp_flatMap_trp (c : List SatSym) (hc : sep ∉ c) : c.flatMap dsp_trpS = c.flatMap trp :=
  List.flatMap_congr fun s hs => by
    cases s with
    | sep => exact absurd hs hc
    | _ => rfl

/-- **The instance in printing order.** -/
theorem dsp_DSI_eq (w : List SatSym) : DSI w =
    List.replicate (NV w) zero ++ [sep] ++
      (List.range' 0 (NV w)).flatMap (dsp_triO3 (NV w)) ++ (trunc w).flatMap dsp_trpS := by
  unfold DSI dsRows
  rw [List.flatMap_cons, List.flatMap_append, List.flatMap_map,
    List.flatMap_map, ← List.range_eq_range', trunc, List.flatMap_assoc]
  have e1 : (List.range (3 * NV w)).flatMap (fun u => triRow (NV w) u ++ [sep]) =
      (List.range (NV w)).flatMap (dsp_triO3 (NV w)) := by
    rw [dsp_flatMap_range3]
    refine List.flatMap_congr fun i hi => ?_
    have hi := List.mem_range.1 hi
    rw [dsp_triRow_eq _ _ (by omega), dsp_triRow_eq _ _ (by omega), dsp_triRow_eq _ _ (by omega),
      dsp_triO3, show 3 * i / 3 = i by omega, show (3 * i + 1) / 3 = i by omega,
      show (3 * i + 2) / 3 = i by omega]
  have e2 : (clauses w).flatMap (fun c => c.flatMap trp ++ [sep]) =
      (clauses w).flatMap (fun c => (c ++ [sep]).flatMap dsp_trpS) :=
    List.flatMap_congr fun c hc => by
      rw [List.flatMap_append, dsp_flatMap_trp c (sep_not_mem_clauses w c hc)]; rfl
  rw [e1, e2]
  simp only [List.append_assoc]

/-! ## The budget row -/

/-- Print `zero^N sep` (`N = v 5`). -/
def dsp_hdC : Cmd := .seq (mg_zsL [5]) (emL [sep])

theorem dsp_em_hd {v : ℕ → ℕ} {N U : ℕ} (h5 : v 5 = N) (hN : N ≤ U) (h7 : v 7 = 0)
    (h11 : v 11 = 0) :
    sg_Em dsp_hdC v (List.replicate N zero ++ [sep]) ((9 * U + 6) + 4) := by
  have b := mg_em_zsL U h7 h11 [5] (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact ⟨by norm_num, by norm_num, by norm_num, by omega⟩)
  refine (b.seq (sg_em_emL [sep] v)).cast ?_ ?_
  · simp [h5, mg_sum]
  · simp

/-! ## The triangle rows -/

/-- Print one triangle row `zero^(3 v15) ppp zero^(3 v16) sep`. -/
def dsp_rowC : Cmd :=
  .seq (mg_zsL [15, 15, 15]) (.seq (emL [pos, pos, pos]) (.seq (mg_zsL [16, 16, 16]) (emL [sep])))

def dsp_tB : Cmd :=
  .seq (.seq dsp_rowC (.seq dsp_rowC dsp_rowC)) (.seq (.push 15 true) (Ham.hg_dec 16))

def dsp_tL : Cmd := .loop (.pop 17 .brk dsp_tB dsp_tB)

def dsp_triC : Cmd :=
  .seq (copyVia 5 16 11) (.seq (Ham.hg_dec 16) (.seq (copyVia 5 17 11) dsp_tL))

/-- Time of one triangle (three rows). -/
def dsp_tTB (U : ℕ) : ℕ := 162 * U + 160

theorem dsp_em_row (N U i : ℕ) (hN : N ≤ U) (hi : i < N) (v : ℕ → ℕ) (h7 : v 7 = 0)
    (h11 : v 11 = 0) (h15 : v 15 = i) (h16 : v 16 = N - 1 - i) :
    sg_Em dsp_rowC v (dsp_triO N i) (54 * U + 48) := by
  have a := mg_em_zsL U h7 h11 [15, 15, 15] (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hr
    subst hr; exact ⟨by norm_num, by norm_num, by norm_num, by omega⟩)
  have b := mg_em_zsL U h7 h11 [16, 16, 16] (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hr
    subst hr; exact ⟨by norm_num, by norm_num, by norm_num, by omega⟩)
  refine (a.seq ((sg_em_emL [pos, pos, pos] v).seq (b.seq (sg_em_emL [sep] v)))).cast ?_ ?_
  · simp [dsp_triO, mg_sum, h15, h16]; ring_nf
  · simp; omega

theorem dsp_ex_tB (N U i : ℕ) (hN : N ≤ U) (hi : i < N) (W O Q : Str) (E : List SatSym)
    (v : ℕ → ℕ) (h7 : v 7 = 0) (h11 : v 11 = 0) (h15 : v 15 = i) (h16 : v 16 = N - 1 - i) :
    ExecLe dsp_tB (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ dsp_triO3 N i))
        (update (update v 15 (v 15 + 1)) 16 (update v 15 (v 15 + 1) 16 - 1)))) (dsp_tTB U) := by
  have r := dsp_em_row N U i hN hi v h7 h11 h15 h16
  have c := (r.seq (r.seq r)) W O Q E
  have p1 := ex_push_reg (W := W) (O := O) (Q := Q) (r := 15) (by norm_num)
    (rv (E ++ dsp_triO3 N i)) v
  have p2 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 16) (by norm_num)
    (rv (E ++ dsp_triO3 N i)) (update v 15 (v 15 + 1))
  refine (c.seq_norm (p1.seq_norm p2)).cast ?_ ?_
  · rfl
  · simp only [dsp_tTB]; omega

/-- Time of the triangle rows. -/
def dsp_tP (U : ℕ) : ℕ := U * (dsp_tTB U + 1) + 12 * U + 20

theorem dsp_ex_tri (N U : ℕ) (hN : N ≤ U) (W O Q : Str) (E : List SatSym) (v : ℕ → ℕ)
    (h5 : v 5 = N) (h7 : v 7 = 0) (h11 : v 11 = 0) (h15 : v 15 = 0) (h16 : v 16 = 0)
    (h17 : v 17 = 0) :
    ∃ v', v' 11 = 0 ∧ ExecLe dsp_triC (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ (List.range' 0 N).flatMap (dsp_triO3 N))) v')) (dsp_tP U) := by
  have p1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 5) (b := 16) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v h11
  rw [h5, h16, Nat.zero_add] at p1
  have p2 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 16) (by norm_num) (rv E)
    (update v 16 N)
  rw [update_idem, update_self] at p2
  set x1 := update v 16 (N - 1) with hx1
  have p3 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 5) (b := 17) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) x1 (by simp [hx1, h11])
  rw [show x1 17 + x1 5 = N by simp [hx1, h5, h17]] at p3
  set x2 := update x1 17 N with hx2
  obtain ⟨v', ⟨a1, a2, -⟩, -, p4⟩ := mg_loop (c := 17) (B := dsp_tB) (by norm_num) W Q
    (fun _ => O) (fun j u => u 7 = 0 ∧ u 11 = 0 ∧ u 15 = j ∧ u 16 = N - 1 - j)
    (dsp_triO3 N) (dsp_tTB U) N
    (fun j u x ⟨a, b, c, d⟩ => ⟨by simp [a], by simp [b], by simp [c], by simp [d]⟩)
    (fun j u E' hj ⟨a, b, c, d⟩ => ⟨_, ⟨by simp [a], by simp [b], by simp [c], by simp [c, d]; omega⟩,
      by simp, dsp_ex_tB N U j hN hj W O Q E' u a b c d⟩)
    N 0 E x2 (by omega) ⟨by simp [hx2, hx1, h7], by simp [hx2, hx1, h11], by simp [hx2, hx1, h15],
      by simp [hx2, hx1]⟩ (by simp [hx2])
  refine ⟨v', a2, (p1.seq_norm (p2.seq_norm (p3.seq_norm p4))).cast (by simp) ?_⟩
  have hn : N * (dsp_tTB U + 1) ≤ U * (dsp_tTB U + 1) := Nat.mul_le_mul_right _ hN
  simp only [hx1, update_of_ne (show (5 : ℕ) ≠ 16 by norm_num), h5]
  unfold dsp_tP
  omega

/-! ## The clause rows: a symbolwise map -/

/-- Print `dsp_trpS s` for every symbol `s` of stack `4`. -/
def dsp_mapL : Cmd := .loop (disp 4 fun s => emL (dsp_trpS s))

theorem dsp_len_trpS (s : SatSym) : (dsp_trpS s).length ≤ 3 := by cases s <;> simp [dsp_trpS]

theorem dsp_ex_mapL (W O : Str) (v : ℕ → ℕ) : ∀ (l E : List SatSym),
    ExecLe dsp_mapL (st2 W O (l.flatMap ic) (rv E) v)
      (.norm (st2 W O [] (rv (E ++ l.flatMap dsp_trpS)) v)) (9 * l.length + 2)
  | [], E => (ex_disp_nil rfl).cast (by simp) le_rfl
  | s :: l, E => by
    have ih := dsp_ex_mapL W O v l (E ++ dsp_trpS s)
    have hb := ex_disp (k := 4) (f := fun s => emL (dsp_trpS s)) (s := s) (Q' := l.flatMap ic)
      (σ := st2 W O ((s :: l).flatMap ic) (rv E) v) (by simp)
      (by rw [upd2_4]; exact ex_emL (dsp_trpS s) E v)
    refine (ExecLe.loop_norm hb ih).cast (by simp) ?_
    have := dsp_len_trpS s; simp; omega

def dsp_mapC : Cmd := .seq (copyVia 2 4 11) dsp_mapL

theorem dsp_ex_map (l : List SatSym) (O : Str) (E : List SatSym) (v : ℕ → ℕ) (h11 : v 11 = 0) :
    ExecLe dsp_mapC (st2 (l.flatMap ic) O [] (rv E) v)
      (.norm (st2 (l.flatMap ic) O [] (rv (E ++ l.flatMap dsp_trpS)) v)) (19 * l.length + 7) := by
  have p1 := ex_copyW (W := l.flatMap ic) (O := O) (rv E) v h11
  have p2 := dsp_ex_mapL (l.flatMap ic) O v l E
  refine (p1.seq_norm p2).cast rfl ?_
  rw [length_flatMap_ic]; omega

/-! ## The whole program -/

/-- The reduction program. -/
def dsp_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq (copyVia 2 4 11) (.seq (.push 5 true)
  (.seq sg_cntLoop (.seq dsp_hdC (.seq dsp_triC dsp_mapC)))))))

/-- Time bound of the program. -/
def dsp_Tred (n : ℕ) : ℕ :=
  100 * (n + 1) + 100 + (9 * (n + 1) + 6) + 4 + dsp_tP (n + 1)

set_option maxHeartbeats 1600000 in
theorem dsp_exec_redCmd (x : Str) : ∃ σ', ExecLe dsp_redCmd (init [x]).stk (.norm σ')
    (dsp_Tred x.length) ∧ σ' 1 = ((DSI (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  set L := trunc w
  set W := L.flatMap ic
  set N := NV w
  set V := x.length + 1 with hVd
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have hLw : L.length ≤ w.length := length_trunc_le w
  have hW : W.length = 2 * L.length := length_flatMap_ic L
  have hN : N = L.length + 1 := rfl
  have hNV : N ≤ V := by omega
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
  obtain ⟨v1, c1, c2, -, q3⟩ := sg_ex_cnt W [] L []
    (update (fun _ : ℕ => (0 : ℕ)) 5 ((fun _ : ℕ => (0 : ℕ)) 5 + 1))
  have v1_5 : v1 5 = N := by rw [c2]; simp [hN]; omega
  have v1_o : ∀ r, r ≠ 5 → r ≠ 9 → v1 r = 0 := fun r a b => by rw [c1 r a b]; simp [a]
  -- the phases
  have q4 := dsp_em_hd (U := V) v1_5 hNV (v1_o 7 (by norm_num) (by norm_num))
    (v1_o 11 (by norm_num) (by norm_num)) W [] [] []
  set E1 := [] ++ (List.replicate N zero ++ [sep])
  obtain ⟨v2, z2, q5⟩ := dsp_ex_tri N V hNV W [] [] E1 v1 v1_5
    (v1_o 7 (by norm_num) (by norm_num)) (v1_o 11 (by norm_num) (by norm_num))
    (v1_o 15 (by norm_num) (by norm_num)) (v1_o 16 (by norm_num) (by norm_num))
    (v1_o 17 (by norm_num) (by norm_num))
  set E2 := E1 ++ (List.range' 0 N).flatMap (dsp_triO3 N)
  have q6 := dsp_ex_map L [] E2 v2 z2
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm (q1.seq_norm (q2.seq_norm
    (q3.seq_norm (q4.seq_norm (q5.seq_norm q6)))))))).cast rfl ?_, ?_⟩
  · have tσ : (σ2 4).length = W.length := by simp [σ2, W]
    rw [tσ, hW]
    unfold dsp_Tred
    rw [← hVd]
    omega
  · simp only [st2_1, rv, E2, E1]
    rw [dsp_DSI_eq w]
    simp only [List.append_assoc, List.nil_append]
    rfl

theorem dsp_Tred_le (n : ℕ) : dsp_Tred n ≤ tb 11 n := by
  unfold dsp_Tred dsp_tP dsp_tTB tb
  set V := n + 1
  set P := n + 2
  have hVP : V ≤ P := by omega
  have h1 : 1 ≤ P := by omega
  have e : 100 * V + 100 + (9 * V + 6) + 4 + (V * (162 * V + 160 + 1) + 12 * V + 20) =
      162 * (V * V) + 282 * V + 130 := by ring
  rw [e]
  have k2 : V * V ≤ P * P := Nat.mul_le_mul hVP hVP
  have k1 : V ≤ P * P := le_trans hVP (Nat.le_mul_of_pos_left P (by omega))
  have k0 : 4 ≤ P * P := Nat.mul_le_mul (show 2 ≤ P by omega) (show 2 ≤ P by omega)
  have h2 : 2 ^ 9 ≤ P ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have h3 : 2 ^ 9 * (P * P) ≤ P ^ 9 * (P * P) := Nat.mul_le_mul h2 le_rfl
  have e2 : P ^ 11 = P ^ 9 * (P * P) := by ring
  rw [e2]
  norm_num at h3
  generalize P ^ 9 * (P * P) = A at *
  generalize P * P = B at *
  generalize V * V = a2 at *
  clear_value V P
  omega

/-! ## The reduction -/

theorem dsp_computable :
    Nonempty (Turing.TM2ComputableInPolyTime (Millennium.fin_encoding_string SatSym).encode
      (Millennium.fin_encoding_string SatSym).encode DSI) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    dsp_redCmd 1 11 (fun x => DSI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := dsp_exec_redCmd x
      exact ⟨σ', h1.mono (dsp_Tred_le _), h2⟩)
    DSI (fun t => (congrArg DSI (FunBridge.dec2_flatMap_ic t)).symm)

/-- **SAT ≤ₚ DOMINATING SET** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `DSI`. -/
theorem sat_le_ds_of (h : ∀ w, SATLang w ↔ DSLang (DSI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang DSLang := by
  obtain ⟨hc⟩ := dsp_computable
  exact ⟨DSI, hc, h⟩

end Pnp.Karp.DomSet
