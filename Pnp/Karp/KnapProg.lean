import Pnp.Karp.Knapsack
import Pnp.Karp.SubProg

/-!
# The KNAPSACK reduction program: SUBSET SUM ≤ₚ KNAPSACK

`kp_redCmd`, on the bit string `x` on stack `0` (layout `st2` of `Pnp/Karp/CliqueGen.lean`, all
registers `0`):

1. `parseLoop`, `trimC 4`, `move 4 2` (as for CLIQUE): stack `2` holds the code of `trunc w`,
   `w = dec2 x`;
2. `kp_test`: if stack `2` is empty (no rows), print `[sep, pos, sep]`;
3. `kp_loop` (scanning stack `2` symbol by symbol): a non-`sep` symbol is printed and pushed onto
   the buffer stack `3` (the reversed code of the row so far); at a `sep`, print `sep`, then the
   buffer (`move 3 4`, `move 4 1`, which undoes the reversal), then `sep` again.

So every row is printed twice (`kp_out_trunc`), which is `KI w` (`kp_KI_eq`).  `kp_exec_redCmd`
bounds the run by `26 n + 21 ≤ tb 6 n`, and `ss_le_knap_of` follows from
`FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.Knapsack

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

/-! ## The output -/

/-- What the scan prints on the rest `l` of `trunc w`, with the current row prefix `P`. -/
def kp_out : List SatSym → List SatSym → List SatSym
  | _, [] => []
  | P, s :: l => if s = sep then sep :: (P ++ sep :: kp_out [] l) else s :: kp_out (P ++ [s]) l

theorem kp_out_row (l : List SatSym) : ∀ (r P : List SatSym), sep ∉ r →
    kp_out P (r ++ sep :: l) = r ++ sep :: (P ++ r ++ sep :: kp_out [] l)
  | [], P, _ => by simp [kp_out]
  | s :: r, P, h => by
    have hs : s ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have hr : sep ∉ r := fun e => h (List.mem_cons_of_mem _ e)
    simp only [List.cons_append, kp_out, if_neg hs, kp_out_row l r (P ++ [s]) hr]
    simp

theorem kp_out_rows : ∀ cs : List (List SatSym), (∀ c ∈ cs, sep ∉ c) →
    kp_out [] (cs.flatMap (· ++ [sep])) = cs.flatMap fun r => r ++ sep :: (r ++ [sep])
  | [], _ => rfl
  | c :: cs, h => by
    rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, List.singleton_append,
      kp_out_row _ c [] (h c (by simp)), kp_out_rows cs (fun c' hc => h c' (by simp [hc]))]
    simp

theorem kp_KI_eq (w : List SatSym) :
    KI w = (if trunc w = [] then [sep, pos, sep] else []) ++ kp_out [] (trunc w) := by
  rw [trunc, kp_out_rows _ (sep_not_mem_clauses w), KI]
  rcases h : clauses w with _ | ⟨t, as⟩
  · simp
  · simp only [List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append,
      List.flatMap_assoc]
    simp

/-! ## The program -/

section Prog
variable {W O Q : Str}

theorem kp_upd2 (W' : Str) {o : Str} {v : ℕ → ℕ} :
    update (st2 W O Q o v) 2 W' = st2 W' O Q o v := by
  funext j; unfold Clique.st2; simp only [update_apply]; split_ifs <;> simp_all

/-- Per-symbol action of the scan. -/
def kp_symB : SatSym → Cmd
  | sep => .seq (emL [sep]) (.seq (move 3 4) (.seq (move 4 1) (emL [sep])))
  | s => .seq (emL [s]) (pushList 3 (rv [s]))

/-- The scan of stack `2`. -/
def kp_loop : Cmd := .loop (disp 2 kp_symB)

theorem kp_ex_sep (P E : List SatSym) (v : ℕ → ℕ) :
    ExecLe (kp_symB sep) (st2 W (rv P) [] (rv E) v)
      (.norm (st2 W [] [] (rv (E ++ sep :: (P ++ [sep]))) v)) (8 * P.length + 10) := by
  have q1 := ex_emL (W := W) (O := rv P) (Q := []) [sep] E v
  have q2 := exec_move (a := 3) (b := 4) (by decide) (rv P) (st2 W (rv P) [] (rv (E ++ [sep])) v)
    rfl
  have e2 : update (update (st2 W (rv P) [] (rv (E ++ [sep])) v) 3 []) 4
      ((rv P).reverse ++ (st2 W (rv P) [] (rv (E ++ [sep])) v) 4) =
      st2 W [] (P.flatMap ic) (rv (E ++ [sep])) v := by
    rw [upd2_3, st2_4, upd2_4, rv, List.reverse_reverse, List.append_nil]
  rw [e2] at q2
  have q3 := exec_move (a := 4) (b := 1) (by decide) (P.flatMap ic)
    (st2 W [] (P.flatMap ic) (rv (E ++ [sep])) v) rfl
  have e3 : update (update (st2 W [] (P.flatMap ic) (rv (E ++ [sep])) v) 4 []) 1
      ((P.flatMap ic).reverse ++ (st2 W [] (P.flatMap ic) (rv (E ++ [sep])) v) 1) =
      st2 W [] [] (rv (E ++ [sep] ++ P)) v := by
    rw [upd2_4, st2_1, upd2_1, rv_append _ P]; rfl
  rw [e3] at q3
  have q4 := ex_emL (W := W) (O := []) (Q := []) [sep] (E ++ [sep] ++ P) v
  refine (q1.seq_norm ((ExecLe.of q2).seq_norm ((ExecLe.of q3).seq_norm q4))).cast
    (by simp) ?_
  have hP := length_flatMap_ic P
  simp [rv] at hP ⊢
  omega

theorem kp_ex_sym (s : SatSym) (hs : s ≠ sep) (P E : List SatSym) (v : ℕ → ℕ) :
    ExecLe (kp_symB s) (st2 W (rv P) [] (rv E) v)
      (.norm (st2 W (rv (P ++ [s])) [] (rv (E ++ [s])) v)) 6 := by
  have hb : kp_symB s = .seq (emL [s]) (pushList 3 (rv [s])) := by
    cases s <;> simp_all [kp_symB]
  rw [hb]
  have q1 := ex_emL (W := W) (O := rv P) (Q := []) [s] E v
  have q2 := exec_pushList 3 (rv [s]) (st2 W (rv P) [] (rv (E ++ [s])) v)
  rw [st2_3, upd2_3, ← rv_append] at q2
  refine (q1.seq_norm (ExecLe.of q2)).cast rfl ?_
  have hP := length_flatMap_ic [s]
  simp [rv] at hP ⊢; omega

theorem kp_ex_loop (v : ℕ → ℕ) : ∀ (l P E : List SatSym), ∃ P',
    ExecLe kp_loop (st2 (l.flatMap ic) (rv P) [] (rv E) v)
      (.norm (st2 [] (rv P') [] (rv (E ++ kp_out P l)) v)) (16 * l.length + 8 * P.length + 2)
  | [], P, E => ⟨P, (ex_disp_nil rfl).cast (by simp [kp_out]) (by omega)⟩
  | s :: l, P, E => by
    by_cases hs : s = sep
    · subst hs
      obtain ⟨P', ih⟩ := kp_ex_loop v l [] (E ++ sep :: (P ++ [sep]))
      refine ⟨P', ?_⟩
      have hb := ex_disp (k := 2) (f := kp_symB) (s := sep) (Q' := l.flatMap ic)
        (σ := st2 ((sep :: l).flatMap ic) (rv P) [] (rv E) v) (by simp)
        (by rw [kp_upd2]; exact kp_ex_sep (W := l.flatMap ic) P E v)
      refine (ExecLe.loop_norm hb ih).cast (by simp [kp_out]) ?_
      simp; omega
    · obtain ⟨P', ih⟩ := kp_ex_loop v l (P ++ [s]) (E ++ [s])
      refine ⟨P', ?_⟩
      have hb := ex_disp (k := 2) (f := kp_symB) (s := s) (Q' := l.flatMap ic)
        (σ := st2 ((s :: l).flatMap ic) (rv P) [] (rv E) v) (by simp)
        (by rw [kp_upd2]; exact kp_ex_sym (W := l.flatMap ic) s hs P E v)
      refine (ExecLe.loop_norm hb ih).cast (by simp [kp_out, hs]) ?_
      simp; omega

/-- Print `[sep, pos, sep]` iff stack `2` is empty. -/
def kp_test : Cmd := .pop 2 (emL [sep, pos, sep]) (.push 2 false) (.push 2 true)

theorem kp_ex_test (v : ℕ → ℕ) :
    ExecLe kp_test (st2 W [] [] (rv []) v)
      (.norm (st2 W [] [] (rv (if W = [] then [sep, pos, sep] else [])) v)) 8 := by
  rcases W with _ | ⟨b, W'⟩
  · exact (ExecLe.pop_nil rfl (ex_emL (W := []) (O := []) (Q := []) [sep, pos, sep] [] v)).cast
      (by simp) (by simp)
  · refine (ExecLe.pop_cons (r := .norm (st2 (b :: W') [] [] (rv []) v)) (b := b) (s := W') rfl
      ?_).cast (by simp) (show 1 + 1 ≤ 8 by omega)
    rw [kp_upd2]
    cases b
    · exact (ExecLe.push 2 false _).cast (by rw [st2_2, kp_upd2]) le_rfl
    · exact (ExecLe.push 2 true _).cast (by rw [st2_2, kp_upd2]) le_rfl

end Prog

/-- The reduction program. -/
def kp_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq kp_test kp_loop)))

theorem kp_exec_redCmd (x : Str) : ∃ σ', ExecLe kp_redCmd (init [x]).stk (.norm σ')
    (26 * x.length + 21) ∧ σ' 1 = ((KI (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  set L := trunc w
  set W := L.flatMap ic
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have hLw : L.length ≤ w.length := length_trunc_le w
  have hW : W.length = 2 * L.length := length_flatMap_ic L
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
      st2 W [] [] (rv []) fun _ => 0 := by
    funext j
    simp only [σ2, σ1, Clique.st2, update_apply, rv_nil, W, L]
    split_ifs <;> simp_all
  rw [e3] at p3
  have p4 := kp_ex_test (W := W) (fun _ => 0)
  have hWL : (W = []) ↔ (L = []) := by
    rw [← List.length_eq_zero_iff, hW, ← List.length_eq_zero_iff (l := L)]; omega
  obtain ⟨P', p5⟩ := kp_ex_loop (fun _ => 0) L []
    (if W = [] then [sep, pos, sep] else [])
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm (p4.seq_norm p5)))).cast rfl ?_,
    ?_⟩
  · simp only [σ2, update_self, List.length_reverse, List.length_nil]
    have := length_flatMap_ic L
    omega
  · simp only [st2_1, rv]
    rw [kp_KI_eq w]
    simp only [W, L] at hWL ⊢
    rw [if_congr hWL rfl rfl]

theorem kp_T_le (n : ℕ) : 26 * n + 21 ≤ tb 6 n := by
  unfold tb
  have h : 2 ^ 5 * (n + 2) ≤ (n + 2) ^ 5 * (n + 2) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 5) le_rfl
  rw [pow_succ]
  generalize (n + 2) ^ 5 * (n + 2) = A at *
  omega

/-! ## The reduction -/

/-- **SUBSET SUM ≤ₚ KNAPSACK** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `KI`. -/
theorem ss_le_knap_of (h : ∀ w, SSLang w ↔ KnapLang (KI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SSLang KnapLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    kp_redCmd 1 6 (fun x => KI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := kp_exec_redCmd x
      exact ⟨σ', h1.mono (kp_T_le _), h2⟩)
    KI (fun t => (congrArg KI (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨KI, hc, h⟩

end Pnp.Karp.Knapsack
