import Pnp.Karp.ILP
import Pnp.Karp.HittingSetProg

/-!
# The 0-1 INTEGER PROGRAMMING reduction program, SAT ≤ₚ ILP (given the correctness of `ILPI`)

`il_redCmd`, on the bit string `x` on stack `0`, prints `ILPI (dec2 x)` (`Pnp/Karp/ILP.lean`),
on the layout `st2` of `Pnp/Karp/CliqueGen.lean`:

1. parsing, trimming and counting as for SUBSET SUM: `N = |trunc w| + 1` (register `5`);
2. `il_pairC`: for `i < N` the two rows `posR (pairRow N i)`, `negR (pairRow N i)`, each followed
   by `sep` (`il_pairO`; runs of `neg` printed by `il_negsC` from the registers `15 = i` and
   `16 = N - 1 - i`, counter `17`);
3. `il_mapC`: the clause rows, a symbolwise map of `trunc w` with a one-bit state (register
   `18`, "at the start of a row"): a symbol `s` prints the row prefix `[neg, pos, neg]` if the
   flag is set, then `il_cS s` (`pos ↦ [pos, neg, neg, neg, neg]`,
   `neg ↦ [neg, neg, pos, neg, neg]`, `zero ↦ [neg, neg, neg, neg]`, `sep ↦ [sep]`), and sets
   the flag iff `s = sep` (`il_hm`).  Since `posR (c.flatMap dbl) = [neg, pos, neg] ++
   c.flatMap il_cS`, this prints the rows `posR (c.flatMap dbl)` of the clauses, each followed
   by `sep`.

`il_ILPI_eq` is the closed form of `ILPI w` printed in this order; `sat_le_ilp_of` follows from
`FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.ILP

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM Pnp.Karp.HittingSet

/-! ## The closed form -/

/-- The prefix of every `posR` row. -/
def il_P : List SatSym := [neg, pos, neg]

/-- The image of a clause symbol in its row (`sep ↦ [sep]`). -/
def il_cS : SatSym → List SatSym
  | pos => [pos, neg, neg, neg, neg]
  | neg => [neg, neg, pos, neg, neg]
  | zero => [neg, neg, neg, neg]
  | sep => [sep]

/-- The new value of the flag "at the start of a row" after the symbol `s`. -/
def il_nb : SatSym → Bool
  | sep => true
  | _ => false

/-- The stateful symbolwise map (flag `b`: at the start of a row). -/
def il_hm : Bool → List SatSym → List SatSym
  | _, [] => []
  | b, s :: l => ((if b then il_P else []) ++ il_cS s) ++ il_hm (il_nb s) l

/-- The two printed rows of the pair `i` (each with its `sep`). -/
def il_pairO (N i : ℕ) : List SatSym :=
  [neg, pos, neg] ++ (List.replicate (4 * i) neg ++ ([pos, neg, neg, pos, neg, neg] ++
    (List.replicate (4 * (N - 1 - i)) neg ++ ([sep, pos, neg, neg] ++
    (List.replicate (4 * i) neg ++ ([neg, pos, neg, neg, pos, neg] ++
    (List.replicate (4 * (N - 1 - i)) neg ++ [sep])))))))

theorem il_rep_zero_posR (k : ℕ) :
    (List.replicate k zero).flatMap (fun s => if s = pos then [pos, neg, neg] else [neg, neg]) =
      List.replicate (2 * k) neg := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, show 2 * (k + 1) = 2 + 2 * k by ring,
      List.replicate_add]
    rfl

theorem il_rep_zero_negR (k : ℕ) :
    (List.replicate k zero).flatMap (fun s => if s = pos then [neg, pos, neg] else [neg, neg]) =
      List.replicate (2 * k) neg := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, show 2 * (k + 1) = 2 + 2 * k by ring,
      List.replicate_add]
    rfl

theorem il_pairRow_eq (N i : ℕ) (h : i < N) :
    posR (pairRow N i) ++ [sep] ++ (negR (pairRow N i) ++ [sep]) = il_pairO N i := by
  rw [hsp_pairRow N i h]
  simp only [posR, negR, List.flatMap_append, List.flatMap_cons, il_rep_zero_posR,
    il_rep_zero_negR, il_pairO]
  have e : ∀ k : ℕ, 2 * (2 * k) = 4 * k := fun k => by ring
  simp [e]

theorem il_hm_row (b : Bool) (rest : List SatSym) :
    ∀ c : List SatSym, sep ∉ c → il_hm b (c ++ sep :: rest) =
      (if b then il_P else []) ++ c.flatMap il_cS ++ [sep] ++ il_hm true rest
  | [], _ => by simp [il_hm, il_cS, il_nb]
  | s :: c, hc => by
    have hs : s ≠ sep := fun e => hc (e ▸ List.mem_cons_self)
    have hc' : sep ∉ c := fun e => hc (List.mem_cons_of_mem _ e)
    have hn : il_nb s = false := by cases s <;> simp_all [il_nb]
    rw [List.cons_append, il_hm, hn, il_hm_row false rest c hc']
    simp

theorem il_hm_rows : ∀ cs : List (List SatSym), (∀ c ∈ cs, sep ∉ c) →
    il_hm true (cs.flatMap (· ++ [sep])) = cs.flatMap (fun c => il_P ++ c.flatMap il_cS ++ [sep])
  | [], _ => rfl
  | c :: cs, h => by
    rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, List.singleton_append,
      il_hm_row true _ c (h c List.mem_cons_self),
      il_hm_rows cs (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    simp

theorem il_posR_dbl (c : List SatSym) (hc : sep ∉ c) :
    posR (c.flatMap dbl) = il_P ++ c.flatMap il_cS := by
  rw [posR, List.flatMap_assoc]
  congr 1
  exact List.flatMap_congr fun s hs => by
    cases s with
    | sep => exact absurd hs hc
    | _ => rfl

/-- **The instance in printing order.** -/
theorem il_ILPI_eq (w : List SatSym) : ILPI w =
    (List.range' 0 (NV w)).flatMap (il_pairO (NV w)) ++ il_hm true (trunc w) := by
  unfold ILPI ilpRows
  rw [List.flatMap_append, List.flatMap_assoc, List.flatMap_map, List.flatMap_map,
    ← List.range_eq_range', trunc, il_hm_rows _ (sep_not_mem_clauses w)]
  congr 1
  · exact List.flatMap_congr fun i hi => by
      rw [← il_pairRow_eq _ _ (List.mem_range.1 hi)]
      simp
  · exact List.flatMap_congr fun c hc => by
      rw [il_posR_dbl c (sep_not_mem_clauses w c hc)]

/-! ## Runs of `neg` given by registers -/

/-- Print `[neg, neg, neg, neg]` once per mark of register `7` (emptying it). -/
def il_nLoop : Cmd := .loop (.pop 7 .brk (emL [neg, neg, neg, neg]) (emL [neg, neg, neg, neg]))

theorem il_ex_nLoop (W O Q : Str) : ∀ (n : ℕ) (E : List SatSym) (v : ℕ → ℕ), v 7 = n →
    ExecLe il_nLoop (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ List.replicate (4 * n) neg)) (update v 7 0))) (10 * n + 2)
  | 0, E, v, h => (ExecLe.loop_brk (ExecLe.pop_nil (by rw [st2_reg (by norm_num), h]; rfl)
      (ExecLe.brk _))).cast (by rw [Nat.mul_zero, List.replicate_zero, List.append_nil,
        update_eq_self_iff.2 h.symm]) (by omega)
  | n + 1, E, v, h => by
    have h1 : ExecLe (.pop 7 .brk (emL [neg, neg, neg, neg]) (emL [neg, neg, neg, neg]))
        (st2 W O Q (rv E) v)
        (.norm (st2 W O Q (rv (E ++ [neg, neg, neg, neg])) (update v 7 n))) 10 := by
      refine ExecLe.pop_same (b := true) (s := List.replicate n true)
        (by rw [st2_reg (by norm_num), h]; rfl) ?_
      rw [upd2_reg (by norm_num)]
      exact ex_emL [neg, neg, neg, neg] E _
    have ih := il_ex_nLoop W O Q n (E ++ [neg, neg, neg, neg]) (update v 7 n) (by simp)
    refine (ExecLe.loop_norm h1 ih).cast ?_ (by omega)
    rw [update_idem, List.append_assoc, show 4 * (n + 1) = 4 + 4 * n by ring,
      List.replicate_add]
    rfl

/-- Print `4 · v a` negs. -/
def il_negsC (a : ℕ) : Cmd := .seq (copyVia a 7 11) il_nLoop

theorem il_em_negs {a : ℕ} (ha : 5 ≤ a) (ha7 : a ≠ 7) (ha11 : a ≠ 11) {v : ℕ → ℕ}
    (h7 : v 7 = 0) (h11 : v 11 = 0) :
    sg_Em (il_negsC a) v (List.replicate (4 * v a) neg) (15 * v a + 6) := by
  intro W O Q E
  have h1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := a) (b := 7) ha (by norm_num) ha7 ha11
    (by norm_num) (rv E) v h11
  have h2 := il_ex_nLoop W O Q (v a) E (update v 7 (v 7 + v a)) (by simp [h7])
  refine (h1.seq_norm h2).cast ?_ (by omega)
  rw [update_idem, ← h7, update_eq_self]

/-! ## The pair rows -/

def il_pB : Cmd :=
  .seq (.seq (emL [neg, pos, neg]) (.seq (il_negsC 15) (.seq (emL [pos, neg, neg, pos, neg, neg])
    (.seq (il_negsC 16) (.seq (emL [sep, pos, neg, neg]) (.seq (il_negsC 15)
    (.seq (emL [neg, pos, neg, neg, pos, neg]) (.seq (il_negsC 16) (emL [sep])))))))))
    (.seq (.push 15 true) (Ham.hg_dec 16))

def il_pL : Cmd := .loop (.pop 17 .brk il_pB il_pB)

def il_pairC : Cmd :=
  .seq (copyVia 5 16 11) (.seq (Ham.hg_dec 16) (.seq (copyVia 5 17 11) il_pL))

/-- Time of one pair row. -/
def il_tPB (U : ℕ) : ℕ := 60 * U + 80

theorem il_ex_pB (N U i : ℕ) (hN : N ≤ U) (hi : i < N) (W O Q : Str) (E : List SatSym)
    (v : ℕ → ℕ) (h7 : v 7 = 0) (h11 : v 11 = 0) (h15 : v 15 = i) (h16 : v 16 = N - 1 - i) :
    ExecLe il_pB (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ il_pairO N i))
        (update (update v 15 (v 15 + 1)) 16 (update v 15 (v 15 + 1) 16 - 1)))) (il_tPB U) := by
  have a := il_em_negs (a := 15) (by norm_num) (by norm_num) (by norm_num) h7 h11
  have b := il_em_negs (a := 16) (by norm_num) (by norm_num) (by norm_num) h7 h11
  have c := ((sg_em_emL [neg, pos, neg] v).seq (a.seq
    ((sg_em_emL [pos, neg, neg, pos, neg, neg] v).seq (b.seq
    ((sg_em_emL [sep, pos, neg, neg] v).seq (a.seq
    ((sg_em_emL [neg, pos, neg, neg, pos, neg] v).seq (b.seq
    (sg_em_emL [sep] v))))))))) W O Q E
  rw [h15, h16] at c
  replace c : ExecLe _ _ (.norm (st2 W O Q (rv (E ++ il_pairO N i)) v)) _ := c
  have p1 := ex_push_reg (W := W) (O := O) (Q := Q) (r := 15) (by norm_num)
    (rv (E ++ il_pairO N i)) v
  have p2 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 16) (by norm_num)
    (rv (E ++ il_pairO N i)) (update v 15 (v 15 + 1))
  refine (c.seq_norm (p1.seq_norm p2)).cast ?_ ?_
  · rfl
  · simp only [List.length_cons, List.length_nil, il_tPB]; omega

/-- Time of the pair rows. -/
def il_tP (U : ℕ) : ℕ := U * (il_tPB U + 1) + 12 * U + 20

theorem il_ex_pair (N U : ℕ) (hN : N ≤ U) (W O Q : Str) (E : List SatSym) (v : ℕ → ℕ)
    (h5 : v 5 = N) (h7 : v 7 = 0) (h11 : v 11 = 0) (h15 : v 15 = 0) (h16 : v 16 = 0)
    (h17 : v 17 = 0) (h18 : v 18 = 0) :
    ∃ v', v' 11 = 0 ∧ v' 18 = 0 ∧ ExecLe il_pairC (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ (List.range' 0 N).flatMap (il_pairO N))) v')) (il_tP U) := by
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
  obtain ⟨v', ⟨-, a2, -, -, a5⟩, -, p4⟩ := mg_loop (c := 17) (B := il_pB) (by norm_num) W Q
    (fun _ => O) (fun j u => u 7 = 0 ∧ u 11 = 0 ∧ u 15 = j ∧ u 16 = N - 1 - j ∧ u 18 = 0)
    (il_pairO N) (il_tPB U) N
    (fun j u x ⟨a, b, c, d, e⟩ => ⟨by simp [a], by simp [b], by simp [c], by simp [d],
      by simp [e]⟩)
    (fun j u E' hj ⟨a, b, c, d, e⟩ => ⟨_, ⟨by simp [a], by simp [b], by simp [c],
      by simp [c, d]; omega, by simp [e]⟩, by simp, il_ex_pB N U j hN hj W O Q E' u a b c d⟩)
    N 0 E x2 (by omega) ⟨by simp [hx2, hx1, h7], by simp [hx2, hx1, h11],
      by simp [hx2, hx1, h15], by simp [hx2, hx1], by simp [hx2, hx1, h18]⟩ (by simp [hx2])
  refine ⟨v', a2, a5, (p1.seq_norm (p2.seq_norm (p3.seq_norm p4))).cast (by simp) ?_⟩
  have hn : N * (il_tPB U + 1) ≤ U * (il_tPB U + 1) := Nat.mul_le_mul_right _ hN
  simp only [hx1, update_of_ne (show (5 : ℕ) ≠ 16 by norm_num), h5]
  unfold il_tP
  omega

/-! ## The clause rows: a stateful symbolwise map -/

/-- Set the flag (register `18`) after `sep`. -/
def il_flC : SatSym → Cmd
  | sep => .push 18 true
  | _ => .skip

/-- The body for the symbol `s`: the prefix if the flag is set (clearing it), `il_cS s`, the
new flag. -/
def il_mB (s : SatSym) : Cmd :=
  .seq (.pop 18 .skip (emL il_P) (emL il_P)) (.seq (emL (il_cS s)) (il_flC s))

def il_mapL : Cmd := .loop (disp 4 il_mB)

theorem il_len_cS (s : SatSym) : (il_cS s).length ≤ 5 := by cases s <;> simp [il_cS]

theorem il_ex_mB (W O Q : Str) (E : List SatSym) (s : SatSym) (b : Bool) (v : ℕ → ℕ)
    (h : v 18 = if b then 1 else 0) :
    ExecLe (il_mB s) (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ (((if b then il_P else []) ++ il_cS s))))
        (update v 18 (if il_nb s then 1 else 0)))) 20 := by
  have p1 : ExecLe (.pop 18 .skip (emL il_P) (emL il_P)) (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ (if b then il_P else []))) (update v 18 0))) 8 := by
    cases b with
    | true =>
      have q := ExecLe.pop_same (cn := .skip) (b := true) (s := List.replicate 0 true)
        (k := 18) (σ := st2 W O Q (rv E) v) (by rw [st2_reg (by norm_num), h]; rfl)
        (by rw [upd2_reg (by norm_num)]; exact ex_emL il_P E _)
      exact q.cast (by simp) (by simp [il_P])
    | false =>
      refine (ExecLe.pop_nil (by rw [st2_reg (by norm_num), h]; rfl) (ExecLe.skip _)).cast ?_
        (by omega)
      simp only [Bool.false_eq_true, if_false, List.append_nil]
      rw [update_eq_self_iff.2 (by simpa using h.symm)]
  have p2 := ex_emL (W := W) (O := O) (Q := Q) (il_cS s) (E ++ (if b then il_P else []))
    (update v 18 0)
  have p3 : ExecLe (il_flC s) (st2 W O Q (rv (E ++ (if b then il_P else []) ++ il_cS s))
      (update v 18 0))
      (.norm (st2 W O Q (rv (E ++ (if b then il_P else []) ++ il_cS s))
        (update v 18 (if il_nb s then 1 else 0)))) 1 := by
    cases s with
    | sep =>
      refine (ex_push_reg (by norm_num) _ _).cast ?_ le_rfl
      simp [il_nb]
    | _ => exact (ExecLe.skip _).cast (by simp [il_nb]) le_rfl
  refine (p1.seq_norm (p2.seq_norm p3)).cast (by simp) ?_
  have := il_len_cS s; omega

theorem il_ex_mapL (W O : Str) : ∀ (l E : List SatSym) (b : Bool) (v : ℕ → ℕ),
    v 18 = (if b then 1 else 0) → ∃ v',
    ExecLe il_mapL (st2 W O (l.flatMap ic) (rv E) v)
      (.norm (st2 W O [] (rv (E ++ il_hm b l)) v')) (22 * l.length + 2)
  | [], E, _, v, _ => ⟨v, (ex_disp_nil rfl).cast (by simp [il_hm]) le_rfl⟩
  | s :: l, E, b, v, h => by
    obtain ⟨v', ih⟩ := il_ex_mapL W O l (E ++ ((if b then il_P else []) ++ il_cS s)) (il_nb s)
      (update v 18 (if il_nb s then 1 else 0)) (by simp)
    have hb := ex_disp (k := 4) (f := il_mB) (s := s) (Q' := l.flatMap ic)
      (σ := st2 W O ((s :: l).flatMap ic) (rv E) v) (by simp)
      (by rw [upd2_4]; exact il_ex_mB W O _ E s b v h)
    refine ⟨v', (ExecLe.loop_norm hb ih).cast (by simp [il_hm]) ?_⟩
    simp; omega

def il_mapC : Cmd := .seq (copyVia 2 4 11) (.seq (.push 18 true) il_mapL)

theorem il_ex_map (l : List SatSym) (O : Str) (E : List SatSym) (v : ℕ → ℕ) (h11 : v 11 = 0)
    (h18 : v 18 = 0) : ∃ v',
    ExecLe il_mapC (st2 (l.flatMap ic) O [] (rv E) v)
      (.norm (st2 (l.flatMap ic) O [] (rv (E ++ il_hm true l)) v')) (32 * l.length + 8) := by
  have p1 := ex_copyW (W := l.flatMap ic) (O := O) (rv E) v h11
  have p2 := ex_push_reg (W := l.flatMap ic) (O := O) (Q := l.flatMap ic) (r := 18)
    (by norm_num) (rv E) v
  obtain ⟨v', p3⟩ := il_ex_mapL (l.flatMap ic) O l E true (update v 18 (v 18 + 1))
    (by simp [h18])
  refine ⟨v', (p1.seq_norm (p2.seq_norm p3)).cast rfl ?_⟩
  rw [length_flatMap_ic]; omega

/-! ## The whole program -/

/-- The reduction program. -/
def il_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq (copyVia 2 4 11) (.seq (.push 5 true)
  (.seq sg_cntLoop (.seq il_pairC il_mapC))))))

/-- Time bound of the program. -/
def il_Tred (n : ℕ) : ℕ := 100 * (n + 1) + 100 + il_tP (n + 1)

set_option maxHeartbeats 1600000 in
theorem il_exec_redCmd (x : Str) : ∃ σ', ExecLe il_redCmd (init [x]).stk (.norm σ')
    (il_Tred x.length) ∧ σ' 1 = ((ILPI (FunBridge.dec2 x)).flatMap ic).reverse := by
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
  obtain ⟨v2, z2, z2', q5⟩ := il_ex_pair N V hNV W [] [] [] v1 v1_5
    (v1_o 7 (by norm_num) (by norm_num)) (v1_o 11 (by norm_num) (by norm_num))
    (v1_o 15 (by norm_num) (by norm_num)) (v1_o 16 (by norm_num) (by norm_num))
    (v1_o 17 (by norm_num) (by norm_num)) (v1_o 18 (by norm_num) (by norm_num))
  set E2 := [] ++ (List.range' 0 N).flatMap (il_pairO N)
  obtain ⟨v3, q6⟩ := il_ex_map L [] E2 v2 z2 z2'
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm (q1.seq_norm (q2.seq_norm
    (q3.seq_norm (q5.seq_norm q6))))))).cast rfl ?_, ?_⟩
  · have tσ : (σ2 4).length = W.length := by simp [σ2, W]
    rw [tσ, hW]
    unfold il_Tred
    rw [← hVd]
    omega
  · simp only [st2_1, rv, E2]
    rw [il_ILPI_eq w]
    simp only [List.nil_append]
    rfl

theorem il_Tred_le (n : ℕ) : il_Tred n ≤ tb 11 n := by
  unfold il_Tred il_tP il_tPB tb
  set V := n + 1
  set P := n + 2
  have hVP : V ≤ P := by omega
  have e : 100 * V + 100 + (V * (60 * V + 80 + 1) + 12 * V + 20) =
      60 * (V * V) + 193 * V + 120 := by ring
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

theorem il_computable :
    Nonempty (Turing.TM2ComputableInPolyTime (Millennium.fin_encoding_string SatSym).encode
      (Millennium.fin_encoding_string SatSym).encode ILPI) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    il_redCmd 1 11 (fun x => ILPI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := il_exec_redCmd x
      exact ⟨σ', h1.mono (il_Tred_le _), h2⟩)
    ILPI (fun t => (congrArg ILPI (FunBridge.dec2_flatMap_ic t)).symm)

/-- **SAT ≤ₚ 0-1 INTEGER PROGRAMMING** (official polynomial-time many-one reducibility), given
the correctness of the reduction instance `ILPI`. -/
theorem sat_le_ilp_of (h : ∀ w, SATLang w ↔ ILPLang (ILPI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang ILPLang := by
  obtain ⟨hc⟩ := il_computable
  exact ⟨ILPI, hc, h⟩

end Pnp.Karp.ILP
