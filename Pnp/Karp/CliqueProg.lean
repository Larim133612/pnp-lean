import Pnp.Karp.CliqueGen
import Pnp.CookLevin.FunBridge

/-!
# The reduction program, part 2: the whole program and the reduction SAT ≤ₚ CLIQUE

`redCmd` (layout: `Pnp/Karp/CliqueGen.lean`), on the bit string `x` on stack `0`:

1. `parseLoop`: decode `x` two bits at a time (`FunBridge.dec2`) onto stack `4` (reversed);
   `trimC 4`: drop the unfinished tail; `move 4 2`: stack `2` holds the code `W` of `trunc w`;
2. `hdrC`: print one `zero` per `sep` of `trunc w`, then `zero, sep` (the row `k = m + 1`);
3. `uRowC`: print the row of the universal vertex;
4. `initO`, `outerLoop`: for every position of `trunc w` (stack `3`), print its row: all `zero`
   for a non-literal (`scanZ`), the scan `scanL sg` for a literal of sign `sg`; the registers
   `5`, `6` track the clause index (plus one) and the index inside the clause.

`exec_redCmd`: it terminates within `Tred |x|` steps with `rv (G (dec2 x))` on stack `1`, so
`sat_le_clique : SATLang ≤ₚ CliqueLang` follows from `FunBridge.computable_of_cmd_code` and
`sat_iff_clique`.
-/

namespace Pnp.Karp.Clique

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

/-! ## Facts about annotations -/

theorem ann_fst : ∀ (l : List SatSym) (t j : ℕ), (ann l t j).map Prod.fst = l
  | [], _, _ => rfl
  | s :: l, t, j => by rw [ann_cons, List.map_cons, ann_fst l]

theorem length_ann (l : List SatSym) (t j : ℕ) : (ann l t j).length = l.length := by
  have := congrArg List.length (ann_fst l t j); simpa using this

theorem flatMap_zero : ∀ L : List SatSym, (L.flatMap fun _ => [zero]) = List.replicate L.length zero
  | [] => rfl
  | _ :: L => by simp [flatMap_zero L, List.replicate_succ]

theorem flatMap_single {α β : Type} (f : α → β) : ∀ l : List α, (l.flatMap fun a => [f a]) = l.map f
  | [] => rfl
  | _ :: l => by simp [flatMap_single f l]

/-! ## The outer loop -/

/-- The scan of a non-literal row: all `zero`. -/
def scanZ : Cmd := .seq (copyVia 2 4 11) (mapLoop fun _ => [zero])

/-- Per-symbol action of the outer loop. -/
def outerBr : SatSym → Cmd
  | sep => .seq (emL [zero]) (.seq scanZ (.seq (emL [sep]) (.seq (.push 5 true) (drain 6))))
  | zero => .seq (emL [zero]) (.seq scanZ (.seq (emL [sep]) (.push 6 true)))
  | pos => .seq (emL [pos]) (.seq (scanL false) (.seq (emL [sep]) (.push 6 true)))
  | neg => .seq (emL [pos]) (.seq (scanL true) (.seq (emL [sep]) (.push 6 true)))

def outerLoop : Cmd := .loop (disp 3 outerBr)

/-- Cost of one row. -/
def rowT (n : ℕ) : ℕ := 7 * n * n + 80 * n + 100

section Outer

variable (L : List SatSym)

theorem ex_scanZ (O : Str) (E : List SatSym) (v : ℕ → ℕ) (h11 : v 11 = 0) :
    ExecLe scanZ (st2 (L.flatMap ic) O [] (rv E) v)
      (.norm (st2 (L.flatMap ic) O [] (rv (E ++ L.flatMap fun _ => [zero])) v))
      (15 * L.length + 6) := by
  refine ((ex_copyW (rv E) v h11).seq_norm (ex_mapLoop _ O v _ (fun _ => by simp) L E)).cast
    rfl ?_
  rw [length_flatMap_ic]; omega

theorem row_nonlit (A : List (SatSym × ℕ × ℕ)) (hA : A.length = L.length) (a : SatSym × ℕ × ℕ)
    (ha : isLit a.1 = false) :
    vRow A a = zero :: L.flatMap fun _ => [zero] := by
  unfold vRow
  rw [ha]
  have : ∀ b ∈ A, ent (adjB a b) = zero := fun b _ => by simp [adjB, ha, ent]
  rw [List.map_congr_left this, List.map_const', hA, flatMap_zero]
  simp [ent]

theorem ex_outer (A : List (SatSym × ℕ × ℕ)) (hA : A = ann L 0 0) :
    ∀ (l : List SatSym) (cp jp : ℕ) (E : List SatSym) (v : ℕ → ℕ), RowInv v cp jp →
    cp + jp + l.length ≤ L.length →
    ∃ v', ExecLe outerLoop (st2 (L.flatMap ic) (l.flatMap ic) [] (rv E) v)
      (.norm (st2 (L.flatMap ic) [] [] (rv (E ++ (ann l cp jp).flatMap fun a => vRow A a ++ [sep]))
        v')) (l.length * (rowT L.length + 2) + 2)
  | [], cp, jp, E, v, _, _ => ⟨v, (ex_disp_nil rfl).cast (by simp [ann]) (by simp)⟩
  | s :: l, cp, jp, E, v, hv, hl => by
    have hlen : A.length = L.length := by rw [hA, length_ann]
    obtain ⟨h5, h6, h7, h8, h9, h10, h11⟩ := hv
    simp only [List.length_cons] at hl
    set W := L.flatMap ic
    set R := vRow A (s, cp, jp) ++ [sep]
    have hW : W.length = 2 * L.length := length_flatMap_ic L
    -- the row and the register update
    have hrow : ∃ v1, RowInv v1 (nxT s cp) (nxJ s jp) ∧
        ExecLe (outerBr s) (st2 W (l.flatMap ic) [] (rv E) v)
          (.norm (st2 W (l.flatMap ic) [] (rv (E ++ R)) v1)) (rowT L.length) := by
      cases s with
      | sep =>
        have q1 := ex_emL (W := W) (O := l.flatMap ic) (Q := []) [zero] E v
        have q2 := ex_scanZ L (l.flatMap ic) (E ++ [zero]) v h11
        have q3 := ex_emL (W := W) (O := l.flatMap ic) (Q := []) [sep]
          (E ++ [zero] ++ L.flatMap fun _ => [zero]) v
        have q4 := ex_push_reg (W := W) (O := l.flatMap ic) (Q := []) (r := 5) (by norm_num)
          (rv (E ++ [zero] ++ (L.flatMap fun _ => [zero]) ++ [sep])) v
        have q5 := ex_drain_reg (W := W) (O := l.flatMap ic) (Q := []) (r := 6) (by norm_num)
          (rv (E ++ [zero] ++ (L.flatMap fun _ => [zero]) ++ [sep])) (update v 5 (v 5 + 1))
        refine ⟨update (update v 5 (v 5 + 1)) 6 0, ?_,
          (q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm q5)))).cast ?_ ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [nxT, nxJ, h5, h7, h8, h9, h10, h11]
        · congr 2; simp only [R]; rw [row_nonlit L A hlen (sep, cp, jp) rfl]; simp
        · simp only [update_apply, h6, rowT]; simp; nlinarith
      | zero =>
        have q1 := ex_emL (W := W) (O := l.flatMap ic) (Q := []) [zero] E v
        have q2 := ex_scanZ L (l.flatMap ic) (E ++ [zero]) v h11
        have q3 := ex_emL (W := W) (O := l.flatMap ic) (Q := []) [sep]
          (E ++ [zero] ++ L.flatMap fun _ => [zero]) v
        have q4 := ex_push_reg (W := W) (O := l.flatMap ic) (Q := []) (r := 6) (by norm_num)
          (rv (E ++ [zero] ++ (L.flatMap fun _ => [zero]) ++ [sep])) v
        refine ⟨update v 6 (v 6 + 1), ?_, (q1.seq_norm (q2.seq_norm (q3.seq_norm q4))).cast ?_ ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [nxT, nxJ, h5, h6, h7, h8, h9, h10, h11]
        · congr 2; simp only [R]; rw [row_nonlit L A hlen (zero, cp, jp) rfl]; simp
        · simp only [rowT]; simp; nlinarith
      | pos =>
        have q1 := ex_emL (W := W) (O := l.flatMap ic) (Q := []) [pos] E v
        have q2 := ex_scanL false W (l.flatMap ic) (E ++ [pos]) cp jp v
          ⟨h5, h6, h7, h8, h9, h10, h11⟩ L rfl
        have q3 := ex_emL (W := W) (O := l.flatMap ic) (Q := []) [sep]
          (E ++ [pos] ++ (ann L 0 0).map (entP false cp jp)) v
        have q4 := ex_push_reg (W := W) (O := l.flatMap ic) (Q := []) (r := 6) (by norm_num)
          (rv (E ++ [pos] ++ (ann L 0 0).map (entP false cp jp) ++ [sep])) v
        refine ⟨update v 6 (v 6 + 1), ?_, (q1.seq_norm (q2.seq_norm (q3.seq_norm q4))).cast ?_ ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [nxT, nxJ, h5, h6, h7, h8, h9, h10, h11]
        · have hm : (ann L 0 0).map (entP false cp jp) = A.map (fun b => ent (adjB (pos, cp, jp) b)) := by
            rw [hA]; exact List.map_congr_left (fun b _ => entP_eq false cp jp b)
          congr 2
          simp only [R, vRow, hm, List.append_assoc, List.cons_append]; rfl
        · simp only [rowT, hW]
          have : jp ≤ L.length := by omega
          have : cp ≤ L.length := by omega
          simp; nlinarith
      | neg =>
        have q1 := ex_emL (W := W) (O := l.flatMap ic) (Q := []) [pos] E v
        have q2 := ex_scanL true W (l.flatMap ic) (E ++ [pos]) cp jp v
          ⟨h5, h6, h7, h8, h9, h10, h11⟩ L rfl
        have q3 := ex_emL (W := W) (O := l.flatMap ic) (Q := []) [sep]
          (E ++ [pos] ++ (ann L 0 0).map (entP true cp jp)) v
        have q4 := ex_push_reg (W := W) (O := l.flatMap ic) (Q := []) (r := 6) (by norm_num)
          (rv (E ++ [pos] ++ (ann L 0 0).map (entP true cp jp) ++ [sep])) v
        refine ⟨update v 6 (v 6 + 1), ?_, (q1.seq_norm (q2.seq_norm (q3.seq_norm q4))).cast ?_ ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [nxT, nxJ, h5, h6, h7, h8, h9, h10, h11]
        · have hm : (ann L 0 0).map (entP true cp jp) = A.map (fun b => ent (adjB (neg, cp, jp) b)) := by
            rw [hA]; exact List.map_congr_left (fun b _ => entP_eq true cp jp b)
          congr 2
          simp only [R, vRow, hm, List.append_assoc, List.cons_append]; rfl
        · simp only [rowT, hW]
          have : jp ≤ L.length := by omega
          have : cp ≤ L.length := by omega
          simp; nlinarith
    obtain ⟨v1, hv1, h1⟩ := hrow
    have hnx : nxT s cp + nxJ s jp + l.length ≤ L.length := by
      cases s <;> simp only [nxT, nxJ] <;> omega
    obtain ⟨v', h2⟩ := ex_outer A hA l (nxT s cp) (nxJ s jp) (E ++ R) v1 hv1 hnx
    refine ⟨v', ?_⟩
    have hb := ex_disp (k := 3) (f := outerBr) (s := s) (Q' := l.flatMap ic)
      (σ := st2 W ((s :: l).flatMap ic) [] (rv E) v) (by simp) (by rw [upd2_3]; exact h1)
    refine (ExecLe.loop_norm hb h2).cast (by simp [ann_cons, R, W]) ?_
    simp only [List.length_cons]; nlinarith

end Outer

/-! ## Parsing -/

def parseB : Cmd :=
  .pop 0 .brk (.pop 0 .brk (.seq (.push 4 false) (.push 4 false))
    (.seq (.push 4 false) (.push 4 true)))
    (.pop 0 .brk (.seq (.push 4 true) (.push 4 false)) (.seq (.push 4 true) (.push 4 true)))

def parseLoop : Cmd := .loop parseB

theorem ic_sym (a b : Bool) : ic (FunBridge.sym a b) = [a, b] := by
  cases a <;> cases b <;> rfl

theorem ex_parseLoop : ∀ (x : Str) (σ : ℕ → Str), σ 0 = x →
    ExecLe parseLoop σ
      (.norm (update (update σ 0 []) 4 (((FunBridge.dec2 x).flatMap ic).reverse ++ σ 4)))
      (2 * x.length + 3)
  | [], σ, h => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk _))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [FunBridge.dec2])
      (by simp)
  | [a], σ, h => by
    cases a <;> exact (ExecLe.loop_brk (ExecLe.pop_cons (s := []) h
      (ExecLe.pop_nil (by simp) (ExecLe.brk _)))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [FunBridge.dec2])
      (by simp)
  | a :: b :: r, σ, h => by
    have hb : ExecLe parseB σ (.norm (update (update σ 0 r) 4 (b :: a :: σ 4))) 4 := by
      have e : ∀ c d : Bool, ExecLe (.seq (.push 4 c) (.push 4 d)) (update σ 0 r)
          (.norm (update (update σ 0 r) 4 (d :: c :: σ 4))) 2 := fun c d =>
        ((ExecLe.push 4 c _).seq_norm (ExecLe.push 4 d _)).cast (by simp [update_idem]) le_rfl
      refine ExecLe.pop_cons (b := a) (s := b :: r) h ?_
      have h2 : update σ 0 (b :: r) 0 = b :: r := by simp
      cases a <;> cases b <;> exact (ExecLe.pop_cons h2 (by rw [update_idem]; exact e _ _)).cast
        rfl le_rfl
    have ih := ex_parseLoop r (update (update σ 0 r) 4 (b :: a :: σ 4)) (by simp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all [FunBridge.dec2, ic_sym]

/-! ## The whole program -/

/-- Header symbols: one `zero` per `sep`. -/
def hg (s : SatSym) : List SatSym := if s = sep then [zero] else []

def hdrC : Cmd := .seq (copyVia 2 4 11) (.seq (mapLoop hg) (emL [zero, sep]))

def uRowC : Cmd :=
  .seq (emL [zero]) (.seq (copyVia 2 4 11) (.seq (mapLoop fun s => [ent (isLit s)]) (emL [sep])))

def initO : Cmd := .seq (copyVia 2 3 11) (.push 5 true)

def redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq hdrC (.seq uRowC (.seq initO outerLoop)))))

theorem hg_nil : ∀ c : List SatSym, sep ∉ c → c.flatMap hg = []
  | [], _ => rfl
  | s :: c, h => by
    have hs : s ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    simp [hg, hs, hg_nil c (fun e => h (List.mem_cons_of_mem _ e))]

theorem hg_rows : ∀ L : List (List SatSym), (∀ c ∈ L, sep ∉ c) →
    (L.flatMap (· ++ [sep])).flatMap hg = List.replicate L.length zero
  | [], _ => rfl
  | c :: L, h => by
    simp only [List.flatMap_cons, List.flatMap_append, hg_nil c (h c (by simp)), List.nil_append,
      List.length_cons, List.replicate_succ, hg_rows L (fun c' hc' => h c' (by simp [hc']))]
    simp [hg]

theorem hg_trunc (w : List SatSym) : (trunc w).flatMap hg = List.replicate (clauses w).length zero :=
  hg_rows _ (sep_not_mem_clauses w)

/-- The output of the program equals `G w`. -/
theorem out_eq (w : List SatSym) :
    [] ++ ((trunc w).flatMap hg ++ [zero, sep]) ++ ([zero] ++ (trunc w).flatMap
      (fun s => [ent (isLit s)]) ++ [sep]) ++
      (ann (trunc w) 0 0).flatMap (fun a => vRow (annW w) a ++ [sep]) = G w := by
  simp only [G, gRows, kRow, litRow, annW, List.flatMap_cons, hg_trunc, List.nil_append,
    List.replicate_succ', List.append_assoc]
  congr 1
  simp only [List.cons_append, List.cons.injEq, true_and]
  have e : (trunc w).flatMap (fun s => [ent (isLit s)]) =
      (ann (trunc w) 0 0).map fun b => ent (isLit b.1) := by
    conv_lhs => rw [← ann_fst (trunc w) 0 0]
    rw [List.flatMap_map, flatMap_single]
  rw [← List.append_assoc, e]
  congr 1
  simp [List.flatMap_map]

/-- Time bound of the program. -/
def Tred (n : ℕ) : ℕ := 7 * n * n * n + 80 * n * n + 200 * n + 60

theorem exec_redCmd (x : Str) : ∃ σ', ExecLe redCmd (init [x]).stk (.norm σ') (Tred x.length) ∧
    σ' 1 = ((G (FunBridge.dec2 x)).flatMap ic).reverse := by
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
  have e3 : update (update σ2 4 []) 2 ((σ2 4).reverse ++ σ2 2) = st2 W [] [] (rv []) fun _ => 0 := by
    funext j
    simp only [σ2, σ1, st2, update_apply, rv_nil, W, L]
    split_ifs <;> simp_all
  rw [e3] at p3
  -- header
  have q1 := ex_copyW (W := W) (O := []) (rv []) (fun _ => 0) rfl
  have q2 := ex_mapLoop W [] (fun _ => 0) hg (fun s => by unfold hg; split_ifs <;> simp) L []
  have q3 := ex_emL (W := W) (O := []) (Q := []) [zero, sep] ([] ++ L.flatMap hg) (fun _ => 0)
  set E1 := [] ++ L.flatMap hg ++ [zero, sep]
  -- universal row
  have r1 := ex_emL (W := W) (O := []) (Q := []) [zero] E1 (fun _ => 0)
  have r2 := ex_copyW (W := W) (O := []) (rv (E1 ++ [zero])) (fun _ => 0) rfl
  have r3 := ex_mapLoop W [] (fun _ => 0) (fun s => [ent (isLit s)]) (fun s => by simp) L
    (E1 ++ [zero])
  have r4 := ex_emL (W := W) (O := []) (Q := []) [sep]
    (E1 ++ [zero] ++ L.flatMap fun s => [ent (isLit s)]) (fun _ => 0)
  set E2 := E1 ++ [zero] ++ (L.flatMap fun s => [ent (isLit s)]) ++ [sep]
  -- outer loop
  have i1 : ExecLe (copyVia 2 3 11) (st2 W [] [] (rv E2) fun _ => 0)
      (.norm (st2 W W [] (rv E2) fun _ => 0)) (5 * W.length + 4) := by
    refine (ExecLe.of (exec_copyVia (a := 2) (b := 3) (t := 11) (by decide) (by decide)
      (by decide) _ (by rw [st2_reg (by norm_num)]; rfl))).cast ?_ (by simp)
    rw [st2_2, st2_3, List.append_nil, upd2_3]
  have i2 := ex_push_reg (W := W) (O := W) (Q := []) (r := 5) (by norm_num) (rv E2) (fun _ => 0)
  obtain ⟨v', o1⟩ := ex_outer L (annW w) rfl L 0 0 E2
    (update (fun _ : ℕ => (0 : ℕ)) 5 ((fun _ : ℕ => (0 : ℕ)) 5 + 1))
    ⟨by simp, by simp, by simp, by simp,
      by simp, by simp, by simp⟩ (by omega)
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm ((q1.seq_norm (q2.seq_norm q3)).seq_norm
    ((r1.seq_norm (r2.seq_norm (r3.seq_norm r4))).seq_norm ((i1.seq_norm i2).seq_norm o1)))))).cast
    rfl ?_, ?_⟩
  · simp only [σ2, update_self, List.length_reverse, hW, Tred, List.length_cons, List.length_nil,
      rowT]
    have : L.length ≤ x.length := by omega
    have h1 : L.length * (7 * L.length * L.length + 80 * L.length + 100) ≤
        x.length * (7 * x.length * x.length + 80 * x.length + 100) :=
      Nat.mul_le_mul this (by nlinarith)
    nlinarith
  · simp only [st2_1, rv]
    congr 2
    simp only [E2, E1, List.append_assoc]
    rw [← out_eq w]
    simp only [List.append_assoc, List.nil_append]
    rfl

theorem Tred_le (n : ℕ) : Tred n ≤ tb 10 n := by
  unfold Tred tb
  have h7 : 2 ^ 7 ≤ (n + 2) ^ 7 := Nat.pow_le_pow_left (by omega) 7
  have e : (n + 2) ^ 10 = (n + 2) ^ 3 * (n + 2) ^ 7 := by ring
  have e3 : (n + 2) ^ 3 = n * n * n + 6 * (n * n) + 12 * n + 8 := by ring
  have : 7 * n * n * n + 80 * n * n + 200 * n + 60 ≤ 128 * (n + 2) ^ 3 := by
    rw [e3]; nlinarith
  rw [e]; norm_num at h7
  nlinarith

/-! ## The reduction -/

/-- **SAT ≤ₚ CLIQUE** (official polynomial-time many-one reducibility). -/
theorem sat_le_clique :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang CliqueLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    redCmd 1 10 (fun x => G (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := exec_redCmd x
      exact ⟨σ', h1.mono (Tred_le _), h2⟩)
    G (fun t => (congrArg G (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨G, hc, sat_iff_clique⟩

end Pnp.Karp.Clique
