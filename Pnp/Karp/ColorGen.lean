import Pnp.Karp.Color
import Pnp.Karp.CliqueProg

/-!
# The 3-COLORING reduction program, part 1: primitives, the literal and gadget loops

A stack program printing `G w` (`Pnp/Karp/Color.lean`), on the layout `st2` of
`Pnp/Karp/CliqueGen.lean`: stack `1` the (reversed code of the) output, `2` the code `W` of
`trunc w`, `3` the rest of `trunc w` for the gadget loop, `4` the rest for the literal loop.
Unary registers: `5` holds `b` (the gadget base minus `2`, i.e. `1 + 2L + 3p`; during the
literal loop `1 + 2j`), `6` holds `j` (the index inside the clause; during the literal loop the
variable index), `7` is the countdown of a run of `zero`s, `11` the copy temporary; all other
registers are `0` (`regs b j`).

* `Em c b j out T`: `c` prints `out` within `T` steps without touching the registers;
* `zs1 5` prints `b` zeros, `zs2 6` prints `2j` zeros (copy into `7`, then `zLoop`);
* `litLoop`: the literal rows `vpRow j`, `vnRow` (`ex_litLoop`);
* `gLoop`: the three gadget rows of every annotated position (`ex_gLoop`).
-/

namespace Pnp.Karp.Color

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Registers and states -/

/-- The registers: `5 ↦ b`, `6 ↦ j`, all others `0`. -/
def regs (b j : ℕ) : ℕ → ℕ := fun r => if r = 5 then b else if r = 6 then j else 0

@[simp] theorem regs_5 (b j : ℕ) : regs b j 5 = b := by simp [regs]
@[simp] theorem regs_6 (b j : ℕ) : regs b j 6 = j := by simp [regs]
@[simp] theorem regs_7 (b j : ℕ) : regs b j 7 = 0 := by simp [regs]
@[simp] theorem regs_11 (b j : ℕ) : regs b j 11 = 0 := by simp [regs]

theorem upd_regs5 (b j k : ℕ) : update (regs b j) 5 k = regs k j := by
  funext r; simp only [regs, update_apply]; split_ifs <;> simp_all

theorem upd_regs6 (b j k : ℕ) : update (regs b j) 6 k = regs b k := by
  funext r; simp only [regs, update_apply]; split_ifs <;> simp_all

theorem upd_regs7 (b j n : ℕ) : update (update (regs b j) 7 n) 7 0 = regs b j := by
  rw [update_idem, update_eq_self_iff, regs_7]

theorem regs_zero : (fun _ : ℕ => (0 : ℕ)) = regs 0 0 := by
  funext r; simp only [regs]; split_ifs <;> rfl

/-- The states. -/
def S (W O Q : Str) (E : List SatSym) (b j : ℕ) : ℕ → Str := st2 W O Q (rv E) (regs b j)

@[simp] theorem S_1 (W O Q : Str) (E : List SatSym) (b j : ℕ) : S W O Q E b j 1 = rv E := rfl
@[simp] theorem S_3 (W O Q : Str) (E : List SatSym) (b j : ℕ) : S W O Q E b j 3 = O := rfl
@[simp] theorem S_4 (W O Q : Str) (E : List SatSym) (b j : ℕ) : S W O Q E b j 4 = Q := rfl

theorem upd_S3 (W O Q O' : Str) (E : List SatSym) (b j : ℕ) :
    update (S W O Q E b j) 3 O' = S W O' Q E b j := upd2_3 O'

theorem upd_S4 (W O Q Q' : Str) (E : List SatSym) (b j : ℕ) :
    update (S W O Q E b j) 4 Q' = S W O Q' E b j := upd2_4 Q'

/-! ## Register steps -/

theorem ex_push5 (W O Q : Str) (E : List SatSym) (b j : ℕ) :
    ExecLe (.push 5 true) (S W O Q E b j) (.norm (S W O Q E (b + 1) j)) 1 :=
  (ex_push_reg (W := W) (O := O) (Q := Q) (by norm_num) (rv E) (regs b j)).cast
    (by rw [regs_5, upd_regs5]; rfl) le_rfl

theorem ex_push6 (W O Q : Str) (E : List SatSym) (b j : ℕ) :
    ExecLe (.push 6 true) (S W O Q E b j) (.norm (S W O Q E b (j + 1))) 1 :=
  (ex_push_reg (W := W) (O := O) (Q := Q) (by norm_num) (rv E) (regs b j)).cast
    (by rw [regs_6, upd_regs6]; rfl) le_rfl

theorem ex_drain6 (W O Q : Str) (E : List SatSym) (b j : ℕ) :
    ExecLe (drain 6) (S W O Q E b j) (.norm (S W O Q E b 0)) (2 * j + 2) :=
  (ex_drain_reg (W := W) (O := O) (Q := Q) (r := 6) (by norm_num) (rv E) (regs b j)).cast
    (by rw [upd_regs6]; rfl) (by rw [regs_6])

/-! ## Printing -/

/-- `c` prints `out` within `T` steps, leaving everything else unchanged. -/
def Em (c : Cmd) (b j : ℕ) (out : List SatSym) (T : ℕ) : Prop :=
  ∀ W O Q E, ExecLe c (S W O Q E b j) (.norm (S W O Q (E ++ out) b j)) T

theorem Em.seq {c d : Cmd} {b j : ℕ} {o₁ o₂ : List SatSym} {T₁ T₂ : ℕ} (h1 : Em c b j o₁ T₁)
    (h2 : Em d b j o₂ T₂) : Em (.seq c d) b j (o₁ ++ o₂) (T₁ + T₂) := fun W O Q E =>
  ((h1 W O Q E).seq_norm (h2 W O Q (E ++ o₁))).cast (by rw [List.append_assoc]) le_rfl

theorem Em.cast {c : Cmd} {b j : ℕ} {o o' : List SatSym} {T T' : ℕ} (h : Em c b j o T)
    (ho : o = o') (hT : T ≤ T') : Em c b j o' T' := fun W O Q E =>
  (h W O Q E).cast (by rw [ho]) hT

theorem em_emL (L : List SatSym) (b j : ℕ) : Em (emL L) b j L (2 * L.length + 1) :=
  fun _ _ _ E => ex_emL L E _

/-- Print `zero` once per mark of register `7` (emptying it). -/
def zLoop : Cmd := .loop (.pop 7 .brk (emL [zero]) (emL [zero]))

theorem ex_zLoop (W O Q : Str) : ∀ (n : ℕ) (E : List SatSym) (v : ℕ → ℕ), v 7 = n →
    ExecLe zLoop (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ List.replicate n zero)) (update v 7 0))) (4 * n + 2)
  | 0, E, v, h => (ExecLe.loop_brk (ExecLe.pop_nil (by rw [st2_reg (by norm_num), h]; rfl)
      (ExecLe.brk _))).cast (by rw [List.replicate_zero, List.append_nil, update_eq_self_iff.2 h.symm])
      (by omega)
  | n + 1, E, v, h => by
    have h1 : ExecLe (.pop 7 .brk (emL [zero]) (emL [zero])) (st2 W O Q (rv E) v)
        (.norm (st2 W O Q (rv (E ++ [zero])) (update v 7 n))) 4 := by
      refine ExecLe.pop_same (b := true) (s := List.replicate n true)
        (by rw [st2_reg (by norm_num), h]; rfl) ?_
      rw [upd2_reg (by norm_num)]
      exact ex_emL [zero] E _
    have ih := ex_zLoop W O Q n (E ++ [zero]) (update v 7 n) (by simp)
    refine (ExecLe.loop_norm h1 ih).cast ?_ (by omega)
    rw [update_idem, List.append_assoc, List.singleton_append, ← List.replicate_succ]

/-- Print `b` zeros (register `a = 5`) / `2j` zeros (register `a = 6`). -/
def zs1 (a : ℕ) : Cmd := .seq (copyVia a 7 11) zLoop
def zs2 (a : ℕ) : Cmd := .seq (copyVia a 7 11) (.seq (copyVia a 7 11) zLoop)

theorem em_zs1 (b j : ℕ) : Em (zs1 5) b j (List.replicate b zero) (9 * b + 6) := by
  intro W O Q E
  have h1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 5) (b := 7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (rv E) (regs b j) (regs_11 b j)
  have h2 := ex_zLoop W O Q b E (update (regs b j) 7 (regs b j 7 + regs b j 5)) (by simp)
  refine (h1.seq_norm h2).cast (by rw [upd_regs7]; rfl) (by simp; omega)

theorem em_zs2 (b j : ℕ) : Em (zs2 6) b j (List.replicate (j + j) zero) (18 * j + 10) := by
  intro W O Q E
  have h1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 6) (b := 7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (rv E) (regs b j) (regs_11 b j)
  set u := update (regs b j) 7 (regs b j 7 + regs b j 6)
  have h2 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 6) (b := 7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (rv E) u (by simp [u])
  have h3 := ex_zLoop W O Q (j + j) E (update u 7 (u 7 + u 6)) (by simp [u])
  refine (h1.seq_norm (h2.seq_norm h3)).cast (by rw [update_idem, upd_regs7]; rfl) ?_
  simp [u]; omega

/-- Run `c` if `j = 0`, otherwise `d` (register `6` is restored). -/
def ifJ0 (c d : Cmd) : Cmd := .pop 6 c (.seq (.push 6 true) d) (.seq (.push 6 true) d)

theorem em_ifJ0 {c d : Cmd} {b j : ℕ} {o o' : List SatSym} {T T' : ℕ} (hc : j = 0 → Em c b j o T)
    (hd : j ≠ 0 → Em d b j o' T') : Em (ifJ0 c d) b j (if j = 0 then o else o') (T + T' + 2) := by
  intro W O Q E
  rcases j with _ | j
  · exact (ExecLe.pop_nil (by simp [S, st2_reg]) (hc rfl W O Q E)).cast (by simp) (by omega)
  · have e : update (S W O Q E b (j + 1)) 6 (List.replicate j true) = S W O Q E b j := by
      unfold S; rw [upd2_reg (by norm_num), upd_regs6]
    have h := (ex_push6 W O Q E b j).seq_norm (hd (by omega) W O Q E)
    rw [← e] at h
    exact (ExecLe.pop_same (b := true) (s := List.replicate j true)
      (by simp [S, st2_reg, List.replicate_succ]) h).cast (by simp) (by omega)

/-! ## The gadget rows -/

/-- Row `x` (with `b = base - 2`). -/
def xC : Cmd :=
  ifJ0 (.seq (emL [zero, pos]) (.seq (zs1 5) (emL [zero, pos, pos, sep])))
    (.seq (zs1 5) (emL [zero, pos, zero, pos, pos, sep]))

theorem em_xC (b j : ℕ) : Em xC b j (xRow (b + 2) j ++ [sep]) (18 * b + 45) := by
  refine (em_ifJ0 (fun _ => (em_emL _ b j).seq ((em_zs1 b j).seq (em_emL _ b j)))
    (fun _ => (em_zs1 b j).seq (em_emL _ b j))).cast ?_ (by simp; omega)
  unfold xRow
  split_ifs <;> simp [List.replicate_succ']

/-- Row `y`. -/
def yC : SatSym → Cmd
  | pos => .seq (emL [zero, zero, zero]) (.seq (zs2 6) (emL [pos, sep]))
  | neg => .seq (emL [zero, zero, zero, zero]) (.seq (zs2 6) (emL [pos, sep]))
  | _ => emL [zero, pos, sep]

theorem rep_add (n m : ℕ) : List.replicate (n + m) zero = List.replicate n zero ++ List.replicate m zero :=
  List.replicate_add n m zero

theorem em_yC (s : SatSym) (b j : ℕ) : Em (yC s) b j (yRow s j ++ [sep]) (18 * j + 30) := by
  cases s with
  | pos =>
    refine ((em_emL _ b j).seq ((em_zs2 b j).seq (em_emL _ b j))).cast ?_ (by simp; omega)
    rw [yRow, litCol, show 3 + 2 * j = 3 + (j + j) by omega, List.replicate_add 3 (j + j)]; simp
  | neg =>
    refine ((em_emL _ b j).seq ((em_zs2 b j).seq (em_emL _ b j))).cast ?_ (by simp; omega)
    rw [yRow, litCol, show 4 + 2 * j = 4 + (j + j) by omega, List.replicate_add 4 (j + j)]; simp
  | sep => exact (em_emL _ b j).cast (by simp [yRow, litCol]) (by simp)
  | zero => exact (em_emL _ b j).cast (by simp [yRow, litCol]) (by simp)

/-- Row `o`. -/
def oC (s : SatSym) : Cmd :=
  .seq (emL [zero, if s = sep then pos else zero, pos]) (.seq (zs1 5) (emL [pos, sep]))

theorem em_oC (s : SatSym) (b j : ℕ) : Em (oC s) b j (oRow s (b + 2) ++ [sep]) (9 * b + 20) :=
  ((em_emL _ b j).seq ((em_zs1 b j).seq (em_emL _ b j))).cast (by simp [oRow]) (by simp; omega)

/-- Register update after a position. -/
def updC (s : SatSym) : Cmd :=
  .seq (.push 5 true) (.seq (.push 5 true) (.seq (.push 5 true)
    (if s = sep then drain 6 else .push 6 true)))

theorem ex_updC (s : SatSym) (W O Q : Str) (E : List SatSym) (b j : ℕ) :
    ExecLe (updC s) (S W O Q E b j) (.norm (S W O Q E (b + 3) (nxJ s j))) (2 * j + 5) := by
  have h1 := ex_push5 W O Q E b j
  have h2 := ex_push5 W O Q E (b + 1) j
  have h3 := ex_push5 W O Q E (b + 1 + 1) j
  have h4 : ExecLe (if s = sep then drain 6 else .push 6 true) (S W O Q E (b + 3) j)
      (.norm (S W O Q E (b + 3) (nxJ s j))) (2 * j + 2) := by
    by_cases hs : s = sep
    · subst hs; rw [if_pos rfl]; exact ex_drain6 W O Q E _ j
    · rw [if_neg hs]
      have : nxJ s j = j + 1 := by cases s <;> simp_all [nxJ]
      rw [this]; exact (ex_push6 W O Q E _ j).cast rfl (by omega)
  exact (h1.seq_norm (h2.seq_norm (h3.seq_norm h4))).cast rfl (by omega)

/-- The gadget of one position. -/
def gBr (s : SatSym) : Cmd := .seq (.seq xC (.seq (yC s) (oC s))) (updC s)

theorem ex_gBr (L p t : ℕ) (s : SatSym) (W O Q : Str) (E : List SatSym) (b j : ℕ)
    (hb : b + 2 = base L p) :
    ExecLe (gBr s) (S W O Q E b j)
      (.norm (S W O Q (E ++ (gadRows L p (s, t, j)).flatMap (· ++ [sep])) (b + 3) (nxJ s j)))
      (27 * b + 20 * j + 100) := by
  have h := ((em_xC b j).seq ((em_yC s b j).seq (em_oC s b j))) W O Q E
  have h2 := h.seq_norm (ex_updC s W O Q _ b j)
  refine h2.cast ?_ ?_
  · simp [gadRows, ← hb, List.append_assoc]
  · omega

/-! ## The gadget loop -/

def gLoop : Cmd := .loop (disp 3 gBr)

theorem ex_gLoop (L N : ℕ) (W : Str) (hL : L ≤ N) : ∀ (l : List SatSym) (p t j : ℕ)
    (E : List SatSym), j ≤ p → p + l.length ≤ N →
    ∃ j', ExecLe gLoop (S W (l.flatMap ic) [] E (1 + 2 * L + 3 * p) j)
      (.norm (S W [] [] (E ++ (gadAll L p (ann l t j)).flatMap (· ++ [sep]))
        (1 + 2 * L + 3 * (p + l.length)) j')) (l.length * (200 * N + 200) + 2)
  | [], p, t, j, E, _, _ => ⟨j, (ex_disp_nil rfl).cast (by simp [ann, gadAll]) (by simp)⟩
  | s :: l, p, t, j, E, hj, hl => by
    simp only [List.length_cons] at hl
    have h1 := ex_gBr L p t s W (l.flatMap ic) [] E (1 + 2 * L + 3 * p) j
      (by simp [base]; omega)
    have e : 1 + 2 * L + 3 * p + 3 = 1 + 2 * L + 3 * (p + 1) := by ring
    rw [e] at h1
    obtain ⟨j', h2⟩ := ex_gLoop L N W hL l (p + 1) (nxT s t) (nxJ s j)
      (E ++ (gadRows L p (s, t, j)).flatMap (· ++ [sep]))
      (by cases s <;> simp [nxJ] <;> omega) (by omega)
    refine ⟨j', ?_⟩
    have hb := ex_disp (k := 3) (f := gBr) (s := s) (Q' := l.flatMap ic)
      (σ := S W ((s :: l).flatMap ic) [] E (1 + 2 * L + 3 * p) j) (by simp)
      (by rw [upd_S3]; exact h1)
    refine (ExecLe.loop_norm hb h2).cast ?_ ?_
    · rw [show p + 1 + l.length = p + (l.length + 1) by omega]
      simp [ann_cons, gadAll, List.append_assoc]
    · simp only [List.length_cons]; nlinarith

/-! ## The literal loop -/

/-- The rows `vpRow j, vnRow` (each followed by `sep`). -/
def litB : Cmd :=
  .seq (.seq (emL [zero, zero, pos]) (.seq (zs2 6) (emL [zero, pos, sep, zero, zero, pos, sep])))
    (.seq (.push 6 true) (.seq (.push 5 true) (.push 5 true)))

def litLoop : Cmd := .loop (disp 4 fun _ => litB)

/-- The literal rows printed from variable `j` on, `n` variables. -/
def litOut : ℕ → ℕ → List SatSym
  | _, 0 => []
  | j, n + 1 => vpRow j ++ [sep] ++ (vnRow ++ [sep]) ++ litOut (j + 1) n

theorem litOut_eq : ∀ (n j : ℕ),
    litOut j n = ((List.range' j n).flatMap fun j => [vpRow j, vnRow]).flatMap (· ++ [sep])
  | 0, j => rfl
  | n + 1, j => by
    rw [litOut, litOut_eq n (j + 1), List.range'_succ]
    simp [List.append_assoc]

theorem litOut_litRows (n : ℕ) : litOut 0 n = (litRows n).flatMap (· ++ [sep]) := by
  rw [litOut_eq, litRows, List.range_eq_range']

theorem ex_litB (W O Q : Str) (E : List SatSym) (j : ℕ) :
    ExecLe litB (S W O Q E (1 + 2 * j) j)
      (.norm (S W O Q (E ++ (vpRow j ++ [sep] ++ (vnRow ++ [sep]))) (1 + 2 * (j + 1)) (j + 1)))
      (18 * j + 40) := by
  have h := ((em_emL [zero, zero, pos] (1 + 2 * j) j).seq ((em_zs2 (1 + 2 * j) j).seq
    (em_emL [zero, pos, sep, zero, zero, pos, sep] (1 + 2 * j) j))) W O Q E
  have h4 := ex_push6 W O Q (E ++ ([zero, zero, pos] ++ (List.replicate (j + j) zero ++
    [zero, pos, sep, zero, zero, pos, sep]))) (1 + 2 * j) j
  have h5 := ex_push5 W O Q (E ++ ([zero, zero, pos] ++ (List.replicate (j + j) zero ++
    [zero, pos, sep, zero, zero, pos, sep]))) (1 + 2 * j) (j + 1)
  have h6 := ex_push5 W O Q (E ++ ([zero, zero, pos] ++ (List.replicate (j + j) zero ++
    [zero, pos, sep, zero, zero, pos, sep]))) (1 + 2 * j + 1) (j + 1)
  have h7 := h.seq_norm (h4.seq_norm (h5.seq_norm h6))
  refine h7.cast ?_ (by simp; omega)
  have e : 1 + 2 * j + 1 + 1 = 1 + 2 * (j + 1) := by ring
  rw [e]
  congr 3
  rw [vpRow, show 2 * j + 1 = j + j + 1 by omega, List.replicate_succ']
  simp [vnRow]

theorem ex_litLoop (W O : Str) (N : ℕ) : ∀ (l : List SatSym) (j : ℕ) (E : List SatSym),
    j + l.length ≤ N →
    ExecLe litLoop (S W O (l.flatMap ic) E (1 + 2 * j) j)
      (.norm (S W O [] (E ++ litOut j l.length) (1 + 2 * (j + l.length)) (j + l.length)))
      (l.length * (18 * N + 42) + 2)
  | [], j, E, _ => (ex_disp_nil rfl).cast (by simp [litOut]) (by simp)
  | s :: l, j, E, hl => by
    simp only [List.length_cons] at hl
    have h1 := ex_litB W O (l.flatMap ic) E j
    have h2 := ex_litLoop W O N l (j + 1) (E ++ (vpRow j ++ [sep] ++ (vnRow ++ [sep]))) (by omega)
    have hb := ex_disp (k := 4) (f := fun _ => litB) (s := s) (Q' := l.flatMap ic)
      (σ := S W O ((s :: l).flatMap ic) E (1 + 2 * j) j) (by simp)
      (by rw [upd_S4]; exact h1)
    refine (ExecLe.loop_norm hb h2).cast ?_ ?_
    · rw [show j + 1 + l.length = j + (l.length + 1) by omega]
      simp [litOut, List.append_assoc]
    · simp only [List.length_cons]; nlinarith

end Pnp.Karp.Color
