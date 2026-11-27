import Pnp.Karp.Partition
import Pnp.Karp.CliqueProg

/-!
# The PARTITION reduction program, SUBSET SUM ≤ₚ PARTITION

`pp_redCmd`, on the bit string `x` on stack `0`, prints `PI w` (`w = dec2 x`,
`Pnp/Karp/Partition.lean`) on stack `0`:

1. `parseLoop`, `trimC 4` (as for CLIQUE): stack `4` holds the reversed code of `trunc w`;
   if it is empty (no rows), print `pos sep` and stop;
2. otherwise (`pp_main`): `move 4 3`; `sv_frLoop`, `move 8 4` (as in the SUBSET SUM verifier):
   the bits of the first row `t` on stack `4`;
3. `pp_loop`: for every further row, symbol by symbol, print the symbol and do one
   ripple-carry step of the addition of the row to the accumulator (stack `5`, layout `sv_st`
   of `Pnp/Karp/SubVer.lean` with the output in place of the certificate);
4. print `toRow` of the accumulator (`accRows [] as`), `sep zero`, `toRow (sv_bits t)`, `sep`.

`pp_exec_redCmd` shows that the program prints `PI w` within `tb 6 |x|` steps, and
`ss_le_part_of` follows from `FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.Partition

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

/-! ## Printing on stack `0` -/

/-- Print the symbols `L` on stack `0`. -/
def pp_emL (L : List SatSym) : Cmd := pushList 0 (rv L)

theorem pp_ex_emL' (L E : List SatSym) (σ : ℕ → Str) (h0 : σ 0 = rv E) :
    ExecLe (pp_emL L) σ (.norm (update σ 0 (rv (E ++ L)))) (2 * L.length + 1) := by
  refine (ExecLe.of (exec_pushList 0 _ _)).cast ?_
    (by simp only [rv, List.length_reverse, length_flatMap_ic]; omega)
  rw [h0, rv_append]

theorem pp_ex_emL {Q T A S : Str} {c : Bool} (L E : List SatSym) :
    ExecLe (pp_emL L) (sv_st (rv E) Q T A S c) (.norm (sv_st (rv (E ++ L)) Q T A S c))
      (2 * L.length + 1) :=
  (pp_ex_emL' L E _ rfl).cast (by rw [sv_u0]) le_rfl

/-- Print a bit stack `k` as a row (`true ↦ pos`, `false ↦ zero`). -/
def pp_prB (k : ℕ) : Cmd := .pop k .brk (pp_emL [zero]) (pp_emL [pos])

def pp_pr (k : ℕ) : Cmd := .loop (pp_prB k)

theorem pp_ex_pr {k : ℕ} (hk : k ≠ 0) : ∀ (A : Str) (σ : ℕ → Str) (E : List SatSym),
    σ k = A → σ 0 = rv E →
    ExecLe (pp_pr k) σ (.norm (update (update σ k []) 0 (rv (E ++ toRow A)))) (5 * A.length + 2)
  | [], σ, E, h, h0 => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk _))).cast
      (by
        congr 1; funext j; simp only [update_apply]
        split_ifs with h1 h2 <;> subst_vars <;> simp_all [toRow])
      (by simp)
  | a :: A, σ, E, h, h0 => by
    set s : SatSym := if a then pos else zero
    have ih := pp_ex_pr hk A (update (update σ k A) 0 (rv (E ++ [s]))) (E ++ [s])
      (by simp [hk]) (by simp)
    have hb : ExecLe (pp_prB k) σ (.norm (update (update σ k A) 0 (rv (E ++ [s])))) 4 := by
      refine ExecLe.pop_cons h ?_
      have h0' : update σ k A 0 = rv E := by simp [Ne.symm hk, h0]
      cases a
      · exact pp_ex_emL' [zero] E _ h0'
      · exact pp_ex_emL' [pos] E _ h0'
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    have e : E ++ [s] ++ toRow A = E ++ toRow (a :: A) := by simp [toRow, s]
    rw [e]
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all

/-! ## Copying and adding the rows -/

/-- Per-symbol action: print the symbol; add its bit (at `sep`: finish the addition). -/
def pp_act : SatSym → Cmd
  | sep => .seq (pp_emL [sep]) (.seq sv_prop (move 6 5))
  | zero => .seq (pp_emL [zero]) (sv_addStep false)
  | pos => .seq (pp_emL [pos]) (sv_addStep true)
  | neg => .seq (pp_emL [neg]) (sv_addStep false)

def pp_B : Cmd :=
  .pop 3 .brk (.pop 3 .brk (pp_act sep) (pp_act zero)) (.pop 3 .brk (pp_act pos) (pp_act neg))

def pp_loop : Cmd := .loop pp_B

theorem pp_ex_row {T : Str} (N : ℕ) (Q' : Str) {res : Res} {T0 : ℕ} :
    ∀ (r E : List SatSym) (A S : Str) (c : Bool),
    sep ∉ r → A.length + S.length + r.length ≤ N →
    ExecLe pp_loop (sv_st (rv (E ++ r ++ [sep])) Q' T (S.reverse ++ sv_addL c A (sv_bits r)) []
      false) res T0 →
    ExecLe pp_loop (sv_st (rv E) (r.flatMap ic ++ false :: false :: Q') T A S c) res
      (9 * r.length + 8 * N + 20 + T0)
  | [], E, A, S, c, _, hN, h => by
    have h0 := pp_ex_emL (Q := Q') (T := T) (A := A) (S := S) (c := c) [sep] E
    have h1 := sv_ex_prop (R := rv (E ++ [sep])) (Q := Q') (T := T) A S c
    have h2 := sv_ex_move65 (R := rv (E ++ [sep])) (Q := Q') (T := T)
      ((sv_propL c A).reverse ++ S)
    have hb := sv_pop2 (cE := .brk) (cX := .brk) (cS := pp_act sep) (cZ := pp_act zero)
      (cP := pp_act pos) (cN := pp_act neg) (R := rv E) (Q := Q') (T := T) (A := A)
      (S := S) (c := c) sep (r := .norm _) (h0.seq_norm (h1.seq_norm h2))
    have hl := sv_propL_length c A
    have e : sv_st (rv (E ++ [sep])) Q' T ((sv_propL c A).reverse ++ S).reverse [] false =
        sv_st (rv (E ++ [] ++ [sep])) Q' T (S.reverse ++ sv_addL c A (sv_bits [])) [] false := by
      simp [sv_addL, sv_bits]
    rw [← e] at h
    refine (ExecLe.loop_norm (c := pp_B)
      (σ := sv_st (rv E) (([] : List SatSym).flatMap ic ++ false :: false :: Q') T A S c)
      hb h).cast rfl ?_
    simp at hN ⊢; omega
  | s :: r, E, A, S, c, hr, hN, h => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have hA : A.tail.length ≤ A.length := by simp
    simp only [List.length_cons] at hN
    have e : sv_st (rv (E ++ [s] ++ r ++ [sep])) Q' T
        ((sv_x3 (A.headD false) (isPos s) c :: S).reverse ++
          sv_addL (sv_maj (A.headD false) (isPos s) c) A.tail (sv_bits r)) [] false =
        sv_st (rv (E ++ s :: r ++ [sep])) Q' T (S.reverse ++ sv_addL c A (sv_bits (s :: r))) []
          false := by
      simp [sv_addL, sv_bits]
    rw [← e] at h
    have ih := pp_ex_row N Q' r (E ++ [s]) A.tail (sv_x3 (A.headD false) (isPos s) c :: S)
      (sv_maj (A.headD false) (isPos s) c) hr' (by simp; omega) h
    have hst := sv_ex_addStep (R := rv (E ++ [s])) (Q := r.flatMap ic ++ false :: false :: Q')
      (T := T) (A := A) (S := S) (isPos s) c
    have h0 := pp_ex_emL (Q := r.flatMap ic ++ false :: false :: Q') (T := T) (A := A) (S := S)
      (c := c) [s] E
    have es : sv_sel s (pp_act sep) (pp_act zero) (pp_act pos) (pp_act neg) =
        .seq (pp_emL [s]) (sv_addStep (isPos s)) := by
      cases s <;> simp_all [sv_sel, pp_act, isPos]
    have hb := sv_pop2 (cE := .brk) (cX := .brk) (cS := pp_act sep) (cZ := pp_act zero)
      (cP := pp_act pos) (cN := pp_act neg) s (r := .norm _) (T' := 3 + 4)
      (by rw [es]; exact h0.seq_norm hst)
    simp only [List.flatMap_cons, List.append_assoc]
    refine (ExecLe.loop_norm (c := pp_B) hb ih).cast rfl (by simp; omega)

/-- Cost of the row phase. -/
def pp_Trows (N : ℕ) : List (List SatSym) → ℕ
  | [] => 3
  | r :: rows => 9 * r.length + 8 * N + 20 + pp_Trows N rows

theorem pp_Trows_eq (N : ℕ) : ∀ rows : List (List SatSym),
    pp_Trows N rows = 9 * (rows.map List.length).sum + rows.length * (8 * N + 20) + 3
  | [] => by simp [pp_Trows]
  | r :: rows => by simp only [pp_Trows, pp_Trows_eq N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem pp_accRows_length : ∀ (A : Str) (rows : List (List SatSym)),
    (accRows A rows).length ≤ A.length + (rows.map List.length).sum + rows.length
  | A, [] => by simp [accRows]
  | A, r :: rows => by
    have h1 := sv_addL_length false A (sv_bits r)
    have h2 := pp_accRows_length (sv_addL false A (sv_bits r)) rows
    simp only [sv_bits, List.length_map] at h1 h2
    simp only [accRows, List.map_cons, List.sum_cons, List.length_cons]
    simp only [sv_bits] at h2 ⊢
    omega

theorem pp_ex_rows {T : Str} (N : ℕ) : ∀ (rows : List (List SatSym)) (E : List SatSym) (A : Str),
    (∀ r ∈ rows, sep ∉ r) → A.length + (rows.map List.length).sum + rows.length ≤ N →
    ExecLe pp_loop (sv_st (rv E) (enc rows) T A [] false)
      (.norm (sv_st (rv (E ++ rows.flatMap (· ++ [sep]))) [] T (accRows A rows) [] false))
      (pp_Trows N rows)
  | [], E, A, _, _ => (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [accRows, enc]) (by simp [pp_Trows])
  | r :: rows, E, A, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hN
    have hl := sv_addL_length false A (sv_bits r)
    simp only [sv_bits, List.length_map] at hl
    have ih := pp_ex_rows (T := T) N rows (E ++ r ++ [sep]) (sv_addL false A (sv_bits r)) hrs
      (by simp only [sv_bits] at *; omega)
    have ih' : ExecLe pp_loop (sv_st (rv (E ++ r ++ [sep])) (enc rows) T
        (([] : Str).reverse ++ sv_addL false A (sv_bits r)) [] false)
        (.norm (sv_st (rv (E ++ (r :: rows).flatMap (· ++ [sep]))) [] T (accRows A (r :: rows))
          [] false)) (pp_Trows N rows) := by
      simpa [accRows, List.append_assoc] using ih
    rw [enc_cons]
    exact (pp_ex_row N (enc rows) r E A [] false hr (by simp; omega) ih').cast rfl
      (by simp [pp_Trows])

/-! ## The whole program -/

/-- The main phase (there is a row). -/
def pp_main : Cmd :=
  .seq (move 4 3) (.seq sv_frLoop (.seq (move 8 4) (.seq pp_loop (.seq (pp_pr 5)
    (.seq (pp_emL [sep, zero]) (.seq (pp_pr 4) (pp_emL [sep])))))))

/-- The reduction program. -/
def pp_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.pop 4 (pp_emL [pos, sep]) (.seq (.push 4 false) pp_main)
    (.seq (.push 4 true) pp_main)))

theorem pp_out_eq (w : List SatSym) (t : List SatSym) (as : List (List SatSym))
    (h : clauses w = t :: as) :
    [] ++ as.flatMap (· ++ [sep]) ++ toRow (accRows [] as) ++ [sep, zero] ++
      toRow (sv_bits t) ++ [sep] = PI w := by
  simp [PI, h, List.flatMap_append]

set_option maxHeartbeats 800000 in
theorem pp_exec_redCmd (x : Str) : ∃ σ', ExecLe pp_redCmd (init [x]).stk (.norm σ')
    (16 * (x.length + 2) ^ 2) ∧ σ' 0 = ((PI (FunBridge.dec2 x)).flatMap ic).reverse := by
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
  have hpre : ∀ (c : Cmd) (σ' : ℕ → Str) (T : ℕ), ExecLe c σ2 (.norm σ') T →
      ExecLe (.seq parseLoop (.seq (trimC 4) c)) (init [x]).stk (.norm σ')
        (2 * x.length + 3 + (4 * w.length + 6 + T)) :=
    fun c σ' T h => p1.seq_norm (p2.seq_norm h)
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨t, as⟩
  · -- no rows
    have h4 : σ2 4 = [] := by simp [σ2, trunc, hcw]
    have q := pp_ex_emL' [pos, sep] [] σ2 (by simp [σ2, σ1])
    refine ⟨_, ((hpre _ _ _ (ExecLe.pop_nil h4 q)).mono ?_), ?_⟩
    · have : 2 * x.length + 3 + (4 * w.length + 6 + (2 * [pos, sep].length + 1 + 1)) ≤
          16 * (x.length + 2) ^ 2 := by simp; nlinarith
      exact this
    · simp [PI, hcw, rv]
  · rw [hcw] at hsum hsep
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hW : (σ2 4).length = 2 * (trunc w).length := by
      simp only [σ2, update_self, List.length_reverse, length_flatMap_ic]
    obtain ⟨b, s, hbs⟩ : ∃ b s, σ2 4 = b :: s := by
      rcases h : σ2 4 with _ | ⟨b, s⟩
      · rw [h] at hW; simp only [List.length_nil] at hW; omega
      · exact ⟨b, s, rfl⟩
    -- the first row
    have m1 := exec_move (a := 4) (b := 3) (by decide) _ σ2 rfl
    have hσ : update (update σ2 4 []) 3 ((σ2 4).reverse ++ σ2 3) = sv_st0 [] (enc (t :: as)) [] := by
      funext j
      simp only [σ2, σ1, sv_st0, update_apply, enc, trunc, hcw]
      split_ifs <;> simp_all
    rw [hσ] at m1
    rw [enc_cons] at m1
    have m2 := sv_ex_fr [] (enc as) t [] (hsep t (by simp))
    rw [List.append_nil] at m2
    have m3 := sv_ex_move84 [] (enc as) (sv_bits t)
    have m4 := pp_ex_rows (T := sv_bits t) x.length as [] [] (fun r hr => hsep r (by simp [hr]))
      (by simp; omega)
    set E1 := [] ++ as.flatMap (· ++ [sep])
    set S := accRows [] as
    set σa := sv_st (rv E1) [] (sv_bits t) S [] false
    have m5 := pp_ex_pr (k := 5) (by decide) S σa E1 rfl rfl
    set σb := update (update σa 5 []) 0 (rv (E1 ++ toRow S))
    have m6 := pp_ex_emL' [sep, zero] (E1 ++ toRow S) σb (by simp [σb])
    set σc := update σb 0 (rv (E1 ++ toRow S ++ [sep, zero]))
    have m7 := pp_ex_pr (k := 4) (by decide) (sv_bits t) σc (E1 ++ toRow S ++ [sep, zero])
      (by simp [σc, σb, σa]) (by simp [σc])
    set σd := update (update σc 4 []) 0 (rv (E1 ++ toRow S ++ [sep, zero] ++ toRow (sv_bits t)))
    have m8 := pp_ex_emL' [sep] (E1 ++ toRow S ++ [sep, zero] ++ toRow (sv_bits t)) σd
      (by simp [σd])
    have hmain := (ExecLe.of m1).seq_norm (m2.seq_norm (m3.seq_norm (m4.seq_norm (m5.seq_norm
      (m6.seq_norm (m7.seq_norm m8))))))
    have hp : ExecLe (.push 4 b) (update σ2 4 s) (.norm σ2) 1 :=
      (ExecLe.push 4 b _).cast (by rw [update_idem, update_self, ← hbs, update_eq_self]) le_rfl
    have hbr := (show ExecLe (if b then .seq (.push 4 true) pp_main else .seq (.push 4 false) pp_main)
        (update σ2 4 s) (.norm _) _ by
      have e : (if b then Cmd.seq (.push 4 true) pp_main else .seq (.push 4 false) pp_main) =
          .seq (.push 4 b) pp_main := by cases b <;> rfl
      rw [e]; exact hp.seq_norm hmain)
    refine ⟨_, (hpre _ _ _ (ExecLe.pop_cons hbs hbr)).mono ?_, ?_⟩
    · rw [pp_Trows_eq]
      have hS := pp_accRows_length [] as
      simp only [hW, sv_bits, List.length_map, List.length_nil, List.length_cons] at hS ⊢
      have h1 : as.length * (8 * x.length + 20) ≤ x.length * (8 * x.length + 20) :=
        Nat.mul_le_mul_right _ (by omega)
      nlinarith
    · simp only [σd, update_self]
      rw [pp_out_eq w t as hcw]
      rfl

theorem pp_T_le (n : ℕ) : 16 * (n + 2) ^ 2 ≤ tb 6 n := by
  unfold tb
  have hm : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  norm_num at hm
  have e : (n + 2) ^ 6 = (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by ring
  rw [e]; nlinarith

/-! ## The reduction -/

/-- **SUBSET SUM ≤ₚ PARTITION** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `PI`. -/
theorem ss_le_part_of (h : ∀ w, SSLang w ↔ PartLang (PI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SSLang PartLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    pp_redCmd 0 6 (fun x => PI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := pp_exec_redCmd x
      exact ⟨σ', h1.mono (pp_T_le _), h2⟩)
    PI (fun t => (congrArg PI (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨PI, hc, h⟩

end Pnp.Karp.Partition
