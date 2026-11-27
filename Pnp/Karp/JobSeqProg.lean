import Pnp.Karp.JobSeq
import Pnp.Karp.PartProg

/-!
# The JOB SEQUENCING reduction program, SUBSET SUM ≤ₚ JOB SEQUENCING

`jsp_redCmd`, on the bit string `x` on stack `0`, prints `JI w` (`w = dec2 x`,
`Pnp/Karp/JobSeq.lean`) on stack `0`.  Stacks (layout `jsp_st`): `0` the output (reversed
code), `3` the input rows, `4` the reversed code of the first row `t`, `8` a row buffer,
`9` a temporary.

1. `parseLoop`, `trimC 4` (as for CLIQUE): stack `4` holds the reversed code of `trunc w`;
   if it is empty (no rows), print `[sep, pos, sep, sep, pos, sep]` and stop;
2. otherwise (`jsp_main`): `move 4 3`; `jsp_frLoop` copies the first row `t` symbol by symbol
   onto stack `4` (reversed code `rv t`);
3. `pp_loop` (the PARTITION program): copies the remaining rows `as` onto stack `0` and
   accumulates their sum `accRows [] as` on stack `5`; `move 0 3` puts the rows back as input;
4. print `toRow (accRows [] as)` and `sep` (`pp_pr 5`);
5. `jsp_loop`: for every row `a`, print `a` (keeping a copy in the buffer `8`), then at its
   `sep`: print `sep`, `t` (`copyVia 4 0 9`), `sep`, the buffer, `sep`;
6. print `pos sep sep`, `t`, `sep`.

`jsp_exec_redCmd` shows that the program prints `JI w` within `tb 7 |x|` steps, and
`ss_le_js_of` follows from `FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.JobSeq

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Partition

/-! ## Layout -/

/-- The stacks: output `R`, input `Q`, first row `T`, buffer `B`. -/
def jsp_st (R Q T B : Str) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 4 then T else if j = 8 then B else []

local macro "jsp_stx" : tactic =>
  `(tactic| (funext j; simp only [jsp_st, sv_st, update_apply, CookLevin.fl]; split_ifs <;> simp_all))

section St
variable {R Q T B : Str}
@[simp] theorem jsp_st_0 : jsp_st R Q T B 0 = R := rfl
@[simp] theorem jsp_st_3 : jsp_st R Q T B 3 = Q := rfl
@[simp] theorem jsp_st_4 : jsp_st R Q T B 4 = T := rfl
@[simp] theorem jsp_st_8 : jsp_st R Q T B 8 = B := rfl
@[simp] theorem jsp_st_9 : jsp_st R Q T B 9 = [] := rfl
theorem jsp_u0 (R' : Str) : update (jsp_st R Q T B) 0 R' = jsp_st R' Q T B := by jsp_stx
theorem jsp_u3 (Q' : Str) : update (jsp_st R Q T B) 3 Q' = jsp_st R Q' T B := by jsp_stx
theorem jsp_u4 (T' : Str) : update (jsp_st R Q T B) 4 T' = jsp_st R Q T' B := by jsp_stx
theorem jsp_u8 (B' : Str) : update (jsp_st R Q T B) 8 B' = jsp_st R Q T B' := by jsp_stx
theorem jsp_eq_sv : sv_st R Q T [] [] false = jsp_st R Q T [] := by jsp_stx
end St

/-! ## Primitives -/

theorem jsp_ex_emL {Q T B : Str} (L E : List SatSym) :
    ExecLe (pp_emL L) (jsp_st (rv E) Q T B) (.norm (jsp_st (rv (E ++ L)) Q T B))
      (2 * L.length + 1) :=
  (pp_ex_emL' L E _ rfl).cast (by rw [jsp_u0]) le_rfl

theorem jsp_ex_push4 {R Q B : Str} (s : SatSym) (P : List SatSym) :
    ExecLe (pushList 4 (rv [s])) (jsp_st R Q (rv P) B) (.norm (jsp_st R Q (rv (P ++ [s])) B))
      3 := by
  refine (ExecLe.of (exec_pushList 4 _ _)).cast ?_ (by cases s <;> rfl)
  rw [jsp_st_4, jsp_u4, rv_append]

theorem jsp_ex_push8 {R Q T : Str} (s : SatSym) (P : List SatSym) :
    ExecLe (pushList 8 (rv [s])) (jsp_st R Q T (rv P)) (.norm (jsp_st R Q T (rv (P ++ [s]))))
      3 := by
  refine (ExecLe.of (exec_pushList 8 _ _)).cast ?_ (by cases s <;> rfl)
  rw [jsp_st_8, jsp_u8, rv_append]

/-- Print the first row `t` (kept on stack `4`). -/
theorem jsp_ex_prT {Q B : Str} (t E : List SatSym) :
    ExecLe (copyVia 4 0 9) (jsp_st (rv E) Q (rv t) B) (.norm (jsp_st (rv (E ++ t)) Q (rv t) B))
      (10 * t.length + 4) := by
  refine (ExecLe.of (exec_copyVia (by decide) (by decide) (by decide) _ rfl)).cast ?_ ?_
  · rw [jsp_st_4, jsp_st_0, jsp_u0, rv_append]
  · simp only [jsp_st_4, rv, List.length_reverse, length_flatMap_ic]; omega

/-- Print the buffer (and empty it). -/
theorem jsp_ex_prB {Q T : Str} (P E : List SatSym) :
    ExecLe (.seq (move 8 9) (move 9 0)) (jsp_st (rv E) Q T (rv P))
      (.norm (jsp_st (rv (E ++ P)) Q T [])) (8 * P.length + 4) := by
  have h1 := exec_move (a := 8) (b := 9) (by decide) _ (jsp_st (rv E) Q T (rv P)) rfl
  set σ1 := update (update (jsp_st (rv E) Q T (rv P)) 8 []) 9
    ((rv P).reverse ++ jsp_st (rv E) Q T (rv P) 9)
  have h2 := exec_move (a := 9) (b := 0) (by decide) _ σ1 rfl
  refine ((ExecLe.of h1).seq_norm (ExecLe.of h2)).cast ?_ ?_
  · congr 1
    simp only [σ1, rv_append]
    funext j; simp only [jsp_st, update_apply, rv, List.reverse_reverse]
    split_ifs <;> simp_all
  · simp only [σ1, jsp_st_8, rv, List.length_reverse, length_flatMap_ic, update_self,
      List.length_append, jsp_st_9, List.length_nil]; omega

/-! ## The first row -/

/-- Per-symbol action of the first-row copy. -/
def jsp_frB : SatSym → Cmd
  | sep => .brk
  | s => pushList 4 (rv [s])

def jsp_frLoop : Cmd := .loop (disp 3 jsp_frB)

theorem jsp_ex_fr (R Q' : Str) : ∀ (t P : List SatSym), sep ∉ t →
    ExecLe jsp_frLoop (jsp_st R (t.flatMap ic ++ false :: false :: Q') (rv P) [])
      (.norm (jsp_st R Q' (rv (P ++ t)) [])) (5 * t.length + 3)
  | [], P, _ => by
    have h := ex_disp (k := 3) (f := jsp_frB) (s := sep) (Q' := Q')
      (σ := jsp_st R (([] : List SatSym).flatMap ic ++ false :: false :: Q') (rv P) [])
      (r := .brk _) rfl (ExecLe.brk _)
    exact (ExecLe.loop_brk h).cast (by rw [jsp_u3, List.append_nil]) (by simp)
  | s :: t, P, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := jsp_ex_fr R Q' t (P ++ [s]) (fun e => hr (List.mem_cons_of_mem _ e))
    have hb : jsp_frB s = pushList 4 (rv [s]) := by cases s <;> simp_all [jsp_frB]
    have h := ex_disp (k := 3) (f := jsp_frB) (s := s)
      (Q' := t.flatMap ic ++ false :: false :: Q')
      (σ := jsp_st R ((s :: t).flatMap ic ++ false :: false :: Q') (rv P) [])
      (by simp)
      (by rw [jsp_u3, hb]; exact jsp_ex_push4 s P)
    refine (ExecLe.loop_norm h ih).cast (by simp) (by simp; omega)

/-! ## The item triples -/

/-- Per-symbol action of the triple pass. -/
def jsp_symB : SatSym → Cmd
  | sep => .seq (pp_emL [sep]) (.seq (copyVia 4 0 9) (.seq (pp_emL [sep])
      (.seq (.seq (move 8 9) (move 9 0)) (pp_emL [sep]))))
  | s => .seq (pp_emL [s]) (pushList 8 (rv [s]))

def jsp_loop : Cmd := .loop (disp 3 jsp_symB)

theorem jsp_ex_sep (t P E : List SatSym) (Q : Str) :
    ExecLe (jsp_symB sep) (jsp_st (rv E) Q (rv t) (rv P))
      (.norm (jsp_st (rv (E ++ sep :: t ++ sep :: P ++ [sep])) Q (rv t) []))
      (10 * t.length + 8 * P.length + 17) := by
  have q1 := jsp_ex_emL (Q := Q) (T := rv t) (B := rv P) [sep] E
  have q2 := jsp_ex_prT (Q := Q) (B := rv P) t (E ++ [sep])
  have q3 := jsp_ex_emL (Q := Q) (T := rv t) (B := rv P) [sep] (E ++ [sep] ++ t)
  have q4 := jsp_ex_prB (Q := Q) (T := rv t) P (E ++ [sep] ++ t ++ [sep])
  have q5 := jsp_ex_emL (Q := Q) (T := rv t) (B := []) [sep] (E ++ [sep] ++ t ++ [sep] ++ P)
  refine (q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm q5)))).cast (by simp) ?_
  simp; omega

theorem jsp_ex_row (t : List SatSym) (Q' : Str) {res : Res} {T0 : ℕ} :
    ∀ (r P E : List SatSym), sep ∉ r →
    ExecLe jsp_loop (jsp_st (rv (E ++ r ++ sep :: t ++ sep :: (P ++ r) ++ [sep])) Q' (rv t) [])
      res T0 →
    ExecLe jsp_loop (jsp_st (rv E) (r.flatMap ic ++ false :: false :: Q') (rv t) (rv P)) res
      (16 * r.length + 8 * P.length + 10 * t.length + 19 + T0)
  | [], P, E, _, h => by
    have hb := ex_disp (k := 3) (f := jsp_symB) (s := sep) (Q' := Q')
      (σ := jsp_st (rv E) (([] : List SatSym).flatMap ic ++ false :: false :: Q') (rv t) (rv P))
      rfl (by rw [jsp_u3]; exact jsp_ex_sep t P E Q')
    simp only [List.append_nil] at h
    refine (ExecLe.loop_norm hb h).cast rfl (by simp; omega)
  | s :: r, P, E, hr, h => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have ih := jsp_ex_row t Q' r (P ++ [s]) (E ++ [s]) hr' (by simpa using h)
    have hb : jsp_symB s = .seq (pp_emL [s]) (pushList 8 (rv [s])) := by
      cases s <;> simp_all [jsp_symB]
    have q := (jsp_ex_emL (Q := r.flatMap ic ++ false :: false :: Q') (T := rv t) (B := rv P)
      [s] E).seq_norm (jsp_ex_push8 (R := rv (E ++ [s]))
        (Q := r.flatMap ic ++ false :: false :: Q') (T := rv t) s P)
    have hd := ex_disp (k := 3) (f := jsp_symB) (s := s)
      (Q' := r.flatMap ic ++ false :: false :: Q')
      (σ := jsp_st (rv E) ((s :: r).flatMap ic ++ false :: false :: Q') (rv t) (rv P))
      (by simp) (by rw [jsp_u3, hb]; exact q)
    refine (ExecLe.loop_norm hd ih).cast rfl (by simp; omega)

/-- What the triple pass prints for the rows. -/
def jsp_trip (t : List SatSym) (rows : List (List SatSym)) : List SatSym :=
  rows.flatMap fun a => a ++ sep :: t ++ sep :: a ++ [sep]

/-- Cost of the triple pass. -/
def jsp_Trows (m : ℕ) : List (List SatSym) → ℕ
  | [] => 2
  | r :: rows => 16 * r.length + m + jsp_Trows m rows

theorem jsp_Trows_eq (m : ℕ) : ∀ rows : List (List SatSym),
    jsp_Trows m rows = 16 * (rows.map List.length).sum + rows.length * m + 2
  | [] => by simp [jsp_Trows]
  | r :: rows => by simp only [jsp_Trows, jsp_Trows_eq m rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem jsp_ex_rows (t : List SatSym) : ∀ (rows : List (List SatSym)) (E : List SatSym),
    (∀ r ∈ rows, sep ∉ r) →
    ExecLe jsp_loop (jsp_st (rv E) (enc rows) (rv t) [])
      (.norm (jsp_st (rv (E ++ jsp_trip t rows)) [] (rv t) []))
      (jsp_Trows (10 * t.length + 19) rows)
  | [], E, _ => (ex_disp_nil rfl).cast (by simp [jsp_trip, enc]) (by simp [jsp_Trows])
  | r :: rows, E, hrows => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    have ih := jsp_ex_rows t rows (E ++ r ++ sep :: t ++ sep :: ([] ++ r) ++ [sep]) hrs
    have h := jsp_ex_row t (enc rows) r [] E hr ih
    rw [enc_cons]
    refine h.cast (by simp [jsp_trip]) (by simp [jsp_Trows]; omega)

/-! ## The whole program -/

/-- The main phase (there is a row). -/
def jsp_main : Cmd :=
  .seq (move 4 3) (.seq jsp_frLoop (.seq pp_loop (.seq (move 0 3) (.seq (pp_pr 5)
    (.seq (pp_emL [sep]) (.seq jsp_loop (.seq (pp_emL [pos, sep, sep])
      (.seq (copyVia 4 0 9) (pp_emL [sep])))))))))

/-- The reduction program. -/
def jsp_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.pop 4 (pp_emL [sep, pos, sep, sep, pos, sep])
    (.seq (.push 4 false) jsp_main) (.seq (.push 4 true) jsp_main)))

theorem jsp_out_eq (w : List SatSym) (t : List SatSym) (as : List (List SatSym))
    (h : clauses w = t :: as) :
    toRow (accRows [] as) ++ [sep] ++ jsp_trip t as ++ [pos, sep, sep] ++ t ++ [sep] = JI w := by
  simp [JI, h, jsp_trip, List.flatMap_append, List.flatMap_assoc]

set_option maxHeartbeats 800000 in
theorem jsp_exec_redCmd (x : Str) : ∃ σ', ExecLe jsp_redCmd (init [x]).stk (.norm σ')
    (32 * (x.length + 2) ^ 2) ∧ σ' 0 = ((JI (FunBridge.dec2 x)).flatMap ic).reverse := by
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
    have q := pp_ex_emL' [sep, pos, sep, sep, pos, sep] [] σ2 (by simp [σ2, σ1])
    refine ⟨_, ((hpre _ _ _ (ExecLe.pop_nil h4 q)).mono ?_), ?_⟩
    · have : 2 * x.length + 3 + (4 * w.length + 6 +
          (2 * [sep, pos, sep, sep, pos, sep].length + 1 + 1)) ≤
          32 * (x.length + 2) ^ 2 := by simp; nlinarith
      exact this
    · simp [JI, hcw, rv]
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
    have hσ : update (update σ2 4 []) 3 ((σ2 4).reverse ++ σ2 3) =
        jsp_st [] (enc (t :: as)) (rv []) [] := by
      funext j
      simp only [σ2, σ1, jsp_st, update_apply, enc, trunc, hcw, rv_nil]
      split_ifs <;> simp_all
    rw [hσ, enc_cons] at m1
    have m2 := (jsp_ex_fr [] (enc as) t [] (hsep t (by simp))).cast
      (r' := .norm (sv_st [] (enc as) (rv t) [] [] false)) (by rw [jsp_eq_sv, List.nil_append])
      le_rfl
    have m3 := pp_ex_rows (T := rv t) x.length as [] [] (fun r hr => hsep r (by simp [hr]))
      (by simp; omega)
    set E1 := [] ++ as.flatMap (· ++ [sep])
    set S := accRows [] as
    have m4 := exec_move (a := 0) (b := 3) (by decide) _ (sv_st (rv E1) [] (rv t) S [] false)
      rfl
    have e4 : update (update (sv_st (rv E1) [] (rv t) S [] false) 0 []) 3
        ((rv E1).reverse ++ []) = sv_st [] (enc as) (rv t) S [] false := by
      have : (rv E1).reverse = enc as := by simp [E1, rv, enc]
      funext j; simp only [sv_st, update_apply, this, List.append_nil]
      split_ifs <;> simp_all
    simp only [sv_st_0, sv_st_3] at m4
    rw [e4] at m4
    have m5 := pp_ex_pr (k := 5) (by decide) S (sv_st [] (enc as) (rv t) S [] false) [] rfl rfl
    have e5 : update (update (sv_st [] (enc as) (rv t) S [] false) 5 []) 0 (rv ([] ++ toRow S)) =
        jsp_st (rv (toRow S)) (enc as) (rv t) [] := by
      funext j; simp only [sv_st, jsp_st, update_apply, List.nil_append, CookLevin.fl]
      split_ifs <;> simp_all
    rw [e5] at m5
    have m6 := jsp_ex_emL (Q := enc as) (T := rv t) (B := []) [sep] (toRow S)
    have m7 := jsp_ex_rows t as (toRow S ++ [sep]) (fun r hr => hsep r (by simp [hr]))
    have m8 := jsp_ex_emL (Q := []) (T := rv t) (B := []) [pos, sep, sep]
      (toRow S ++ [sep] ++ jsp_trip t as)
    have m9 := jsp_ex_prT (Q := []) (B := []) t (toRow S ++ [sep] ++ jsp_trip t as ++
      [pos, sep, sep])
    have m10 := jsp_ex_emL (Q := []) (T := rv t) (B := []) [sep]
      (toRow S ++ [sep] ++ jsp_trip t as ++ [pos, sep, sep] ++ t)
    have hmain := (ExecLe.of m1).seq_norm (m2.seq_norm (m3.seq_norm ((ExecLe.of m4).seq_norm
      (m5.seq_norm (m6.seq_norm (m7.seq_norm (m8.seq_norm (m9.seq_norm m10))))))))
    have hp : ExecLe (.push 4 b) (update σ2 4 s) (.norm σ2) 1 :=
      (ExecLe.push 4 b _).cast (by rw [update_idem, update_self, ← hbs, update_eq_self]) le_rfl
    have hbr := (show ExecLe (if b then .seq (.push 4 true) jsp_main
        else .seq (.push 4 false) jsp_main) (update σ2 4 s) (.norm _) _ by
      have e : (if b then Cmd.seq (.push 4 true) jsp_main else .seq (.push 4 false) jsp_main) =
          .seq (.push 4 b) jsp_main := by cases b <;> rfl
      rw [e]; exact hp.seq_norm hmain)
    refine ⟨_, (hpre _ _ _ (ExecLe.pop_cons hbs hbr)).mono ?_, ?_⟩
    · rw [pp_Trows_eq, jsp_Trows_eq]
      have hS := pp_accRows_length [] as
      have hE1 : (rv E1).length = 2 * ((as.map List.length).sum + as.length) := by
        simp only [E1, rv, List.length_reverse, length_flatMap_ic, List.nil_append,
          ← sum_length_le]
      simp only [hW, hE1, List.length_nil, List.length_cons] at hS ⊢
      have h1 : as.length * (8 * x.length + 20) ≤ x.length * (8 * x.length + 20) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : as.length * (10 * t.length + 19) ≤ x.length * (10 * x.length + 19) :=
        Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    · simp only [jsp_st_0]
      rw [jsp_out_eq w t as hcw]
      rfl

theorem jsp_T_le (n : ℕ) : 32 * (n + 2) ^ 2 ≤ tb 7 n := by
  unfold tb
  have hm : 2 ^ 5 ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  norm_num at hm
  have e : (n + 2) ^ 7 = (n + 2) ^ 5 * (n + 2) ^ 2 := by ring
  rw [e]; exact Nat.mul_le_mul_right _ hm

/-! ## The reduction -/

/-- **SUBSET SUM ≤ₚ JOB SEQUENCING** (official polynomial-time many-one reducibility), given
the correctness of the reduction instance `JI`. -/
theorem ss_le_js_of (h : ∀ w, SSLang w ↔ JSLang (JI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SSLang JSLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    jsp_redCmd 0 7 (fun x => JI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := jsp_exec_redCmd x
      exact ⟨σ', h1.mono (jsp_T_le _), h2⟩)
    JI (fun t => (congrArg JI (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨JI, hc, h⟩

end Pnp.Karp.JobSeq
