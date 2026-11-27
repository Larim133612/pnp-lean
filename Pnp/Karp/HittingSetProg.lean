import Pnp.Karp.HittingSet
import Pnp.Karp.ThreeDMProg

/-!
# The HITTING SET reduction program, SAT ≤ₚ HITTING SET (given the correctness of `HSI`)

`hsp_redCmd`, on the bit string `x` on stack `0`, prints `HSI (dec2 x)`
(`Pnp/Karp/HittingSet.lean`), on the layout `st2` of `Pnp/Karp/CliqueGen.lean`:

1. parsing, trimming and counting as for SUBSET SUM: `N = |trunc w| + 1` (register `5`);
2. `hsp_hdC`: the header `zero^(2N) sep` and the budget `zero^N sep`;
3. `hsp_pairC`: the pair rows `zero^(2i) ++ [pos, pos] ++ zero^(2(N-1-i)) ++ [sep]` for `i < N`
   (`i` in `15`, `N - 1 - i` in `16`, counter `17`);
4. `hsp_mapC`: the symbolwise image of `trunc w` under `hsp_dblS` (`pos ↦ [pos, zero]`,
   `neg ↦ [zero, pos]`, `zero ↦ [zero, zero]`, `sep ↦ [sep]`), which is the list of the clause
   rows, each followed by `sep`.

`hsp_HSI_eq` is the closed form of `HSI w` printed in this order; `sat_le_hs_of` follows from
`FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.HittingSet

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM

/-! ## The closed form -/

/-- The symbolwise image used for the clause rows (`dbl`, and `sep ↦ [sep]`). -/
def hsp_dblS : SatSym → List SatSym
  | pos => [pos, zero]
  | neg => [zero, pos]
  | zero => [zero, zero]
  | sep => [sep]

/-- A printed pair row (with its `sep`). -/
def hsp_pairO (N i : ℕ) : List SatSym :=
  List.replicate (2 * i) zero ++ [pos, pos] ++ List.replicate (2 * (N - 1 - i)) zero ++ [sep]

theorem hsp_pairRow (N i : ℕ) (h : i < N) :
    pairRow N i = List.replicate (2 * i) zero ++ pos :: pos :: List.replicate (2 * (N - 1 - i)) zero := by
  apply List.ext_getElem
  · simp [pairRow]; omega
  · intro n h1 h2
    simp only [pairRow, List.getElem_map, List.getElem_range, List.getElem_append,
      List.length_replicate, List.getElem_replicate, List.getElem_cons]
    by_cases h3 : n < 2 * i
    · simp [h3, show n / 2 ≠ i by omega]
    · by_cases h4 : n - 2 * i = 0
      · simp [h3, h4, show n / 2 = i by omega]
      · by_cases h5 : n - 2 * i - 1 = 0
        · simp [h3, h4, h5, show n / 2 = i by omega]
        · simp [h3, h4, h5, show n / 2 ≠ i by omega]

theorem hsp_pairRow_eq (N i : ℕ) (h : i < N) : pairRow N i ++ [sep] = hsp_pairO N i := by
  rw [hsp_pairRow N i h, hsp_pairO]; simp

theorem hsp_flatMap_dbl (c : List SatSym) (hc : sep ∉ c) : c.flatMap hsp_dblS = c.flatMap dbl :=
  List.flatMap_congr fun s hs => by
    cases s with
    | sep => exact absurd hs hc
    | _ => rfl

/-- **The instance in printing order.** -/
theorem hsp_HSI_eq (w : List SatSym) : HSI w =
    List.replicate (2 * NV w) zero ++ [sep] ++ (List.replicate (NV w) zero ++ [sep]) ++
      (List.range' 0 (NV w)).flatMap (hsp_pairO (NV w)) ++ (trunc w).flatMap hsp_dblS := by
  unfold HSI hsRows
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_append, List.flatMap_map,
    List.flatMap_map, ← List.range_eq_range', trunc, List.flatMap_assoc]
  have e1 : (List.range (NV w)).flatMap (fun i => pairRow (NV w) i ++ [sep]) =
      (List.range (NV w)).flatMap (hsp_pairO (NV w)) :=
    List.flatMap_congr fun i hi => hsp_pairRow_eq _ _ (List.mem_range.1 hi)
  have e2 : (clauses w).flatMap (fun c => c.flatMap dbl ++ [sep]) =
      (clauses w).flatMap (fun c => (c ++ [sep]).flatMap hsp_dblS) :=
    List.flatMap_congr fun c hc => by
      rw [List.flatMap_append, hsp_flatMap_dbl c (sep_not_mem_clauses w c hc)]; rfl
  rw [e1, e2]
  simp only [List.append_assoc]

/-! ## Header and budget -/

/-- Print `zero^(2N) sep zero^N sep` (`N = v 5`). -/
def hsp_hdC : Cmd := .seq (mg_zsL [5, 5]) (.seq (emL [sep]) (.seq (mg_zsL [5]) (emL [sep])))

theorem hsp_em_hd {v : ℕ → ℕ} {N U : ℕ} (h5 : v 5 = N) (hN : N ≤ U) (h7 : v 7 = 0)
    (h11 : v 11 = 0) :
    sg_Em hsp_hdC v (List.replicate (2 * N) zero ++ [sep] ++ (List.replicate N zero ++ [sep]))
      (3 * (9 * U + 6) + 10) := by
  have a := mg_em_zsL U h7 h11 [5, 5] (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hr
    subst hr; exact ⟨by norm_num, by norm_num, by norm_num, by omega⟩)
  have b := mg_em_zsL U h7 h11 [5] (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact ⟨by norm_num, by norm_num, by norm_num, by omega⟩)
  refine (a.seq ((sg_em_emL [sep] v).seq (b.seq (sg_em_emL [sep] v)))).cast ?_ ?_
  · simp [h5, two_mul]
  · simp; omega

/-! ## The pair rows -/

def hsp_pB : Cmd :=
  .seq (.seq (mg_zsL [15, 15]) (.seq (emL [pos, pos]) (.seq (mg_zsL [16, 16]) (emL [sep]))))
    (.seq (.push 15 true) (Ham.hg_dec 16))

def hsp_pL : Cmd := .loop (.pop 17 .brk hsp_pB hsp_pB)

def hsp_pairC : Cmd :=
  .seq (copyVia 5 16 11) (.seq (Ham.hg_dec 16) (.seq (copyVia 5 17 11) hsp_pL))

/-- Time of one pair row. -/
def hsp_tPB (U : ℕ) : ℕ := 36 * U + 37

/-- The output of `hsp_pB`. -/
theorem hsp_pairO_eq (N i : ℕ) (v : ℕ → ℕ) (h15 : v 15 = i) (h16 : v 16 = N - 1 - i) :
    List.replicate (mg_sum v [15, 15]) zero ++ ([pos, pos] ++
      (List.replicate (mg_sum v [16, 16]) zero ++ [sep])) = hsp_pairO N i := by
  simp [hsp_pairO, mg_sum, h15, h16, two_mul]

theorem hsp_ex_pB (N U i : ℕ) (hN : N ≤ U) (hi : i < N) (W O Q : Str) (E : List SatSym)
    (v : ℕ → ℕ) (h7 : v 7 = 0) (h11 : v 11 = 0) (h15 : v 15 = i) (h16 : v 16 = N - 1 - i) :
    ExecLe hsp_pB (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ hsp_pairO N i))
        (update (update v 15 (v 15 + 1)) 16 (update v 15 (v 15 + 1) 16 - 1)))) (hsp_tPB U) := by
  have a := mg_em_zsL U h7 h11 [15, 15] (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hr
    subst hr; exact ⟨by norm_num, by norm_num, by norm_num, by omega⟩)
  have b := mg_em_zsL U h7 h11 [16, 16] (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hr
    subst hr; exact ⟨by norm_num, by norm_num, by norm_num, by omega⟩)
  have c := (a.seq ((sg_em_emL [pos, pos] v).seq (b.seq (sg_em_emL [sep] v)))) W O Q E
  rw [hsp_pairO_eq N i v h15 h16] at c
  have p1 := ex_push_reg (W := W) (O := O) (Q := Q) (r := 15) (by norm_num)
    (rv (E ++ hsp_pairO N i)) v
  have p2 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 16) (by norm_num)
    (rv (E ++ hsp_pairO N i)) (update v 15 (v 15 + 1))
  refine (c.seq_norm (p1.seq_norm p2)).cast ?_ ?_
  · rfl
  · simp only [List.length_cons, List.length_nil, hsp_tPB]; omega

/-- Time of the pair rows. -/
def hsp_tP (U : ℕ) : ℕ := U * (hsp_tPB U + 1) + 12 * U + 20

theorem hsp_ex_pair (N U : ℕ) (hN : N ≤ U) (W O Q : Str) (E : List SatSym) (v : ℕ → ℕ)
    (h5 : v 5 = N) (h7 : v 7 = 0) (h11 : v 11 = 0) (h15 : v 15 = 0) (h16 : v 16 = 0)
    (h17 : v 17 = 0) :
    ∃ v', v' 11 = 0 ∧ ExecLe hsp_pairC (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ (List.range' 0 N).flatMap (hsp_pairO N))) v')) (hsp_tP U) := by
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
  obtain ⟨v', ⟨a1, a2, -⟩, -, p4⟩ := mg_loop (c := 17) (B := hsp_pB) (by norm_num) W Q
    (fun _ => O) (fun j u => u 7 = 0 ∧ u 11 = 0 ∧ u 15 = j ∧ u 16 = N - 1 - j)
    (hsp_pairO N) (hsp_tPB U) N
    (fun j u x ⟨a, b, c, d⟩ => ⟨by simp [a], by simp [b], by simp [c], by simp [d]⟩)
    (fun j u E' hj ⟨a, b, c, d⟩ => ⟨_, ⟨by simp [a], by simp [b], by simp [c], by simp [c, d]; omega⟩,
      by simp, hsp_ex_pB N U j hN hj W O Q E' u a b c d⟩)
    N 0 E x2 (by omega) ⟨by simp [hx2, hx1, h7], by simp [hx2, hx1, h11], by simp [hx2, hx1, h15],
      by simp [hx2, hx1]⟩ (by simp [hx2])
  refine ⟨v', a2, (p1.seq_norm (p2.seq_norm (p3.seq_norm p4))).cast (by simp) ?_⟩
  have hn : N * (hsp_tPB U + 1) ≤ U * (hsp_tPB U + 1) := Nat.mul_le_mul_right _ hN
  simp only [hx1, update_of_ne (show (5 : ℕ) ≠ 16 by norm_num), h5]
  unfold hsp_tP
  omega

/-! ## The clause rows: a symbolwise map -/

/-- Print `hsp_dblS s` for every symbol `s` of stack `4`. -/
def hsp_mapL : Cmd := .loop (disp 4 fun s => emL (hsp_dblS s))

theorem hsp_len_dblS (s : SatSym) : (hsp_dblS s).length ≤ 2 := by cases s <;> simp [hsp_dblS]

theorem hsp_ex_mapL (W O : Str) (v : ℕ → ℕ) : ∀ (l E : List SatSym),
    ExecLe hsp_mapL (st2 W O (l.flatMap ic) (rv E) v)
      (.norm (st2 W O [] (rv (E ++ l.flatMap hsp_dblS)) v)) (7 * l.length + 2)
  | [], E => (ex_disp_nil rfl).cast (by simp) le_rfl
  | s :: l, E => by
    have ih := hsp_ex_mapL W O v l (E ++ hsp_dblS s)
    have hb := ex_disp (k := 4) (f := fun s => emL (hsp_dblS s)) (s := s) (Q' := l.flatMap ic)
      (σ := st2 W O ((s :: l).flatMap ic) (rv E) v) (by simp)
      (by rw [upd2_4]; exact ex_emL (hsp_dblS s) E v)
    refine (ExecLe.loop_norm hb ih).cast (by simp) ?_
    have := hsp_len_dblS s; simp; omega

def hsp_mapC : Cmd := .seq (copyVia 2 4 11) hsp_mapL

theorem hsp_ex_map (l : List SatSym) (O : Str) (E : List SatSym) (v : ℕ → ℕ) (h11 : v 11 = 0) :
    ExecLe hsp_mapC (st2 (l.flatMap ic) O [] (rv E) v)
      (.norm (st2 (l.flatMap ic) O [] (rv (E ++ l.flatMap hsp_dblS)) v)) (17 * l.length + 7) := by
  have p1 := ex_copyW (W := l.flatMap ic) (O := O) (rv E) v h11
  have p2 := hsp_ex_mapL (l.flatMap ic) O v l E
  refine (p1.seq_norm p2).cast rfl ?_
  rw [length_flatMap_ic]; omega

/-! ## The whole program -/

/-- The reduction program. -/
def hsp_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq (copyVia 2 4 11) (.seq (.push 5 true)
  (.seq sg_cntLoop (.seq hsp_hdC (.seq hsp_pairC hsp_mapC)))))))

/-- Time bound of the program. -/
def hsp_Tred (n : ℕ) : ℕ :=
  100 * (n + 1) + 100 + 3 * (9 * (n + 1) + 6) + 10 + hsp_tP (n + 1)

set_option maxHeartbeats 1600000 in
theorem hsp_exec_redCmd (x : Str) : ∃ σ', ExecLe hsp_redCmd (init [x]).stk (.norm σ')
    (hsp_Tred x.length) ∧ σ' 1 = ((HSI (FunBridge.dec2 x)).flatMap ic).reverse := by
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
  have q4 := hsp_em_hd (U := V) v1_5 hNV (v1_o 7 (by norm_num) (by norm_num))
    (v1_o 11 (by norm_num) (by norm_num)) W [] [] []
  set E1 := [] ++ (List.replicate (2 * N) zero ++ [sep] ++ (List.replicate N zero ++ [sep]))
  obtain ⟨v2, z2, q5⟩ := hsp_ex_pair N V hNV W [] [] E1 v1 v1_5
    (v1_o 7 (by norm_num) (by norm_num)) (v1_o 11 (by norm_num) (by norm_num))
    (v1_o 15 (by norm_num) (by norm_num)) (v1_o 16 (by norm_num) (by norm_num))
    (v1_o 17 (by norm_num) (by norm_num))
  set E2 := E1 ++ (List.range' 0 N).flatMap (hsp_pairO N)
  have q6 := hsp_ex_map L [] E2 v2 z2
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm (q1.seq_norm (q2.seq_norm
    (q3.seq_norm (q4.seq_norm (q5.seq_norm q6)))))))).cast rfl ?_, ?_⟩
  · have tσ : (σ2 4).length = W.length := by simp [σ2, W]
    rw [tσ, hW]
    unfold hsp_Tred
    rw [← hVd]
    omega
  · simp only [st2_1, rv, E2, E1]
    rw [hsp_HSI_eq w]
    simp only [List.append_assoc, List.nil_append]
    rfl

theorem hsp_Tred_le (n : ℕ) : hsp_Tred n ≤ tb 11 n := by
  unfold hsp_Tred hsp_tP hsp_tPB tb
  set V := n + 1
  set P := n + 2
  have hVP : V ≤ P := by omega
  have h1 : 1 ≤ P := by omega
  have e : 100 * V + 100 + 3 * (9 * V + 6) + 10 + (V * (36 * V + 37 + 1) + 12 * V + 20) =
      36 * (V * V) + 177 * V + 148 := by ring
  rw [e]
  have k2 : V * V ≤ P * P := Nat.mul_le_mul hVP hVP
  have k1 : V ≤ P * P := le_trans hVP (Nat.le_mul_of_pos_left P (by omega))
  have k0 : 1 ≤ P * P := Nat.one_le_iff_ne_zero.2 (by positivity)
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

theorem hsp_computable :
    Nonempty (Turing.TM2ComputableInPolyTime (Millennium.fin_encoding_string SatSym).encode
      (Millennium.fin_encoding_string SatSym).encode HSI) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    hsp_redCmd 1 11 (fun x => HSI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := hsp_exec_redCmd x
      exact ⟨σ', h1.mono (hsp_Tred_le _), h2⟩)
    HSI (fun t => (congrArg HSI (FunBridge.dec2_flatMap_ic t)).symm)

/-- **SAT ≤ₚ HITTING SET** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `HSI`. -/
theorem sat_le_hs_of (h : ∀ w, SATLang w ↔ HSLang (HSI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang HSLang := by
  obtain ⟨hc⟩ := hsp_computable
  exact ⟨HSI, hc, h⟩

end Pnp.Karp.HittingSet
