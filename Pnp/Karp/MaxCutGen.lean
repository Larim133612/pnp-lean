import Pnp.Karp.MaxCut
import Pnp.Karp.ColorGen

/-!
# The MAX CUT reduction program, part 1: primitives, the header, literal and gadget loops

A stack program printing `MCI w` (`Pnp/Karp/MaxCut.lean`), on the layout `st2` of
`Pnp/Karp/CliqueGen.lean` (as for 3-COLORING, `Pnp/Karp/ColorGen.lean`): stack `1` the
(reversed code of the) output, `2` the code `W` of `trunc w`, `3` the rest of `trunc w` for the
gadget loop, `4` the rest for the literal loop / the header loop.  Unary registers: `5` holds
`r = base - 2 = 2L + 3p` (during the literal loop `2j`), `6` holds `j` (the index inside the
clause; during the literal loop the variable index), `8` holds `e = r - 2j`, `7` is the countdown
of a run of `zero`s, `11` the copy temporary; all other registers are `0` (`mcp_regs r j e`).

* `mcp_zs a k` prints `v a - k` zeros (copy into `7`, pop `k` times, `Color.zLoop`);
* `mcp_kLoop`: five zeros per symbol of `trunc w` (the bound row);
* `mcp_litLoop`: the literal rows `[]`, `xpRow j`;
* `mcp_gLoop`: the three gadget rows `lRow`, `cRow`, `bRow` of every annotated position.
-/

namespace Pnp.Karp.MaxCut

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Registers and states -/

/-- The registers: `5 ↦ r`, `6 ↦ j`, `8 ↦ e`, all others `0`. -/
def mcp_regs (r j e : ℕ) : ℕ → ℕ := fun x =>
  if x = 5 then r else if x = 6 then j else if x = 8 then e else 0

@[simp] theorem mcp_regs_5 (r j e : ℕ) : mcp_regs r j e 5 = r := by simp [mcp_regs]
@[simp] theorem mcp_regs_6 (r j e : ℕ) : mcp_regs r j e 6 = j := by simp [mcp_regs]
@[simp] theorem mcp_regs_7 (r j e : ℕ) : mcp_regs r j e 7 = 0 := by simp [mcp_regs]
@[simp] theorem mcp_regs_8 (r j e : ℕ) : mcp_regs r j e 8 = e := by simp [mcp_regs]
@[simp] theorem mcp_regs_11 (r j e : ℕ) : mcp_regs r j e 11 = 0 := by simp [mcp_regs]

theorem mcp_upd_regs5 (r j e k : ℕ) : update (mcp_regs r j e) 5 k = mcp_regs k j e := by
  funext x; simp only [mcp_regs, update_apply]; split_ifs <;> simp_all

theorem mcp_upd_regs6 (r j e k : ℕ) : update (mcp_regs r j e) 6 k = mcp_regs r k e := by
  funext x; simp only [mcp_regs, update_apply]; split_ifs <;> simp_all

theorem mcp_upd_regs8 (r j e k : ℕ) : update (mcp_regs r j e) 8 k = mcp_regs r j k := by
  funext x; simp only [mcp_regs, update_apply]; split_ifs <;> simp_all

theorem mcp_regs_zero : (fun _ : ℕ => (0 : ℕ)) = mcp_regs 0 0 0 := by
  funext x; simp only [mcp_regs]; split_ifs <;> rfl

/-- The states. -/
def mcp_S (W O Q : Str) (E : List SatSym) (r j e : ℕ) : ℕ → Str := st2 W O Q (rv E) (mcp_regs r j e)

@[simp] theorem mcp_S_1 (W O Q : Str) (E : List SatSym) (r j e : ℕ) :
    mcp_S W O Q E r j e 1 = rv E := rfl
@[simp] theorem mcp_S_3 (W O Q : Str) (E : List SatSym) (r j e : ℕ) :
    mcp_S W O Q E r j e 3 = O := rfl
@[simp] theorem mcp_S_4 (W O Q : Str) (E : List SatSym) (r j e : ℕ) :
    mcp_S W O Q E r j e 4 = Q := rfl

theorem mcp_upd_S3 (W O Q O' : Str) (E : List SatSym) (r j e : ℕ) :
    update (mcp_S W O Q E r j e) 3 O' = mcp_S W O' Q E r j e := upd2_3 O'

theorem mcp_upd_S4 (W O Q Q' : Str) (E : List SatSym) (r j e : ℕ) :
    update (mcp_S W O Q E r j e) 4 Q' = mcp_S W O Q' E r j e := upd2_4 Q'

/-! ## Register steps -/

theorem mcp_ex_push5 (W O Q : Str) (E : List SatSym) (r j e : ℕ) :
    ExecLe (.push 5 true) (mcp_S W O Q E r j e) (.norm (mcp_S W O Q E (r + 1) j e)) 1 :=
  (ex_push_reg (W := W) (O := O) (Q := Q) (by norm_num) (rv E) (mcp_regs r j e)).cast
    (by rw [mcp_regs_5, mcp_upd_regs5]; rfl) le_rfl

theorem mcp_ex_push6 (W O Q : Str) (E : List SatSym) (r j e : ℕ) :
    ExecLe (.push 6 true) (mcp_S W O Q E r j e) (.norm (mcp_S W O Q E r (j + 1) e)) 1 :=
  (ex_push_reg (W := W) (O := O) (Q := Q) (by norm_num) (rv E) (mcp_regs r j e)).cast
    (by rw [mcp_regs_6, mcp_upd_regs6]; rfl) le_rfl

theorem mcp_ex_push8 (W O Q : Str) (E : List SatSym) (r j e : ℕ) :
    ExecLe (.push 8 true) (mcp_S W O Q E r j e) (.norm (mcp_S W O Q E r j (e + 1))) 1 :=
  (ex_push_reg (W := W) (O := O) (Q := Q) (by norm_num) (rv E) (mcp_regs r j e)).cast
    (by rw [mcp_regs_8, mcp_upd_regs8]; rfl) le_rfl

theorem mcp_ex_drain6 (W O Q : Str) (E : List SatSym) (r j e : ℕ) :
    ExecLe (drain 6) (mcp_S W O Q E r j e) (.norm (mcp_S W O Q E r 0 e)) (2 * j + 2) :=
  (ex_drain_reg (W := W) (O := O) (Q := Q) (r := 6) (by norm_num) (rv E) (mcp_regs r j e)).cast
    (by rw [mcp_upd_regs6]; rfl) (by rw [mcp_regs_6])

theorem mcp_ex_drain8 (W O Q : Str) (E : List SatSym) (r j e : ℕ) :
    ExecLe (drain 8) (mcp_S W O Q E r j e) (.norm (mcp_S W O Q E r j 0)) (2 * e + 2) :=
  (ex_drain_reg (W := W) (O := O) (Q := Q) (r := 8) (by norm_num) (rv E) (mcp_regs r j e)).cast
    (by rw [mcp_upd_regs8]; rfl) (by rw [mcp_regs_8])

/-- Copy register `5` into the empty register `8`. -/
theorem mcp_ex_copy58 (W O Q : Str) (E : List SatSym) (r j : ℕ) :
    ExecLe (copyVia 5 8 11) (mcp_S W O Q E r j 0) (.norm (mcp_S W O Q E r j r)) (5 * r + 4) :=
  (ex_copy_reg (W := W) (O := O) (Q := Q) (a := 5) (b := 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (rv E) (mcp_regs r j 0) (mcp_regs_11 r j 0)).cast
    (by rw [mcp_regs_8, mcp_regs_5, Nat.zero_add, mcp_upd_regs8]; rfl) (by rw [mcp_regs_5])

/-! ## Printing -/

/-- `c` prints `out` within `T` steps, leaving everything else unchanged. -/
def mcp_Em (c : Cmd) (r j e : ℕ) (out : List SatSym) (T : ℕ) : Prop :=
  ∀ W O Q E, ExecLe c (mcp_S W O Q E r j e) (.norm (mcp_S W O Q (E ++ out) r j e)) T

theorem mcp_Em.seq {c d : Cmd} {r j e : ℕ} {o₁ o₂ : List SatSym} {T₁ T₂ : ℕ}
    (h1 : mcp_Em c r j e o₁ T₁) (h2 : mcp_Em d r j e o₂ T₂) :
    mcp_Em (.seq c d) r j e (o₁ ++ o₂) (T₁ + T₂) := fun W O Q E =>
  ((h1 W O Q E).seq_norm (h2 W O Q (E ++ o₁))).cast (by rw [List.append_assoc]) le_rfl

theorem mcp_Em.cast {c : Cmd} {r j e : ℕ} {o o' : List SatSym} {T T' : ℕ}
    (h : mcp_Em c r j e o T) (ho : o = o') (hT : T ≤ T') : mcp_Em c r j e o' T' :=
  fun W O Q E => (h W O Q E).cast (by rw [ho]) hT

theorem mcp_em_emL (L : List SatSym) (r j e : ℕ) : mcp_Em (emL L) r j e L (2 * L.length + 1) :=
  fun _ _ _ E => ex_emL L E _

/-- Pop register `7` `k` times (skipping when it is empty). -/
def mcp_decs : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (.pop 7 .skip .skip .skip) (mcp_decs k)

theorem mcp_ex_decs (W O Q o : Str) : ∀ (k : ℕ) (v : ℕ → ℕ),
    ExecLe (mcp_decs k) (st2 W O Q o v) (.norm (st2 W O Q o (update v 7 (v 7 - k)))) (2 * k + 1)
  | 0, v => (ExecLe.skip _).cast (by rw [Nat.sub_zero, update_eq_self]) le_rfl
  | k + 1, v => by
    rcases h : v 7 with _ | n
    · have h1 : ExecLe (.pop 7 .skip .skip .skip) (st2 W O Q o v) (.norm (st2 W O Q o v)) 2 :=
        ExecLe.pop_nil (by rw [st2_reg (by norm_num), h]; rfl) (ExecLe.skip _)
      have ih := mcp_ex_decs W O Q o k v
      refine (h1.seq_norm ih).cast (by rw [h]; simp) (by omega)
    · have h1 : ExecLe (.pop 7 .skip .skip .skip) (st2 W O Q o v)
          (.norm (st2 W O Q o (update v 7 n))) 2 := by
        refine ExecLe.pop_same (b := true) (s := List.replicate n true)
          (by rw [st2_reg (by norm_num), h]; rfl) ?_
        rw [upd2_reg (by norm_num)]
        exact ExecLe.skip _
      have ih := mcp_ex_decs W O Q o k (update v 7 n)
      refine (h1.seq_norm ih).cast ?_ (by omega)
      rw [update_idem, update_self, show n + 1 - (k + 1) = n - k by omega]

/-- Print `v a - k` zeros. -/
def mcp_zs (a k : ℕ) : Cmd := .seq (copyVia a 7 11) (.seq (mcp_decs k) Color.zLoop)

theorem mcp_ex_zs {a : ℕ} (ha : 5 ≤ a) (ha7 : a ≠ 7) (ha11 : a ≠ 11) (k : ℕ) (W O Q : Str)
    (E : List SatSym) (v : ℕ → ℕ) (h7 : v 7 = 0) (h11 : v 11 = 0) :
    ExecLe (mcp_zs a k) (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ List.replicate (v a - k) zero)) v)) (9 * v a + 2 * k + 8) := by
  have h1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := a) (b := 7) ha (by norm_num) ha7 ha11
    (by norm_num) (rv E) v h11
  have h2 := mcp_ex_decs W O Q (rv E) k (update v 7 (v 7 + v a))
  have h3 := Color.ex_zLoop W O Q (v a - k) E
    (update (update v 7 (v 7 + v a)) 7 ((update v 7 (v 7 + v a)) 7 - k)) (by simp [h7])
  refine (h1.seq_norm (h2.seq_norm h3)).cast ?_ (by omega)
  rw [update_idem, update_idem, ← h7, update_eq_self]

theorem mcp_em_zs5 (k r j e : ℕ) :
    mcp_Em (mcp_zs 5 k) r j e (List.replicate (r - k) zero) (9 * r + 2 * k + 8) :=
  fun W O Q E => (mcp_ex_zs (a := 5) (by norm_num) (by norm_num) (by norm_num) k W O Q E
    (mcp_regs r j e) (by simp) (by simp)).cast (by rw [mcp_regs_5]; rfl) (by rw [mcp_regs_5])

theorem mcp_em_zs6 (k r j e : ℕ) :
    mcp_Em (mcp_zs 6 k) r j e (List.replicate (j - k) zero) (9 * j + 2 * k + 8) :=
  fun W O Q E => (mcp_ex_zs (a := 6) (by norm_num) (by norm_num) (by norm_num) k W O Q E
    (mcp_regs r j e) (by simp) (by simp)).cast (by rw [mcp_regs_6]; rfl) (by rw [mcp_regs_6])

theorem mcp_em_zs8 (k r j e : ℕ) :
    mcp_Em (mcp_zs 8 k) r j e (List.replicate (e - k) zero) (9 * e + 2 * k + 8) :=
  fun W O Q E => (mcp_ex_zs (a := 8) (by norm_num) (by norm_num) (by norm_num) k W O Q E
    (mcp_regs r j e) (by simp) (by simp)).cast (by rw [mcp_regs_8]; rfl) (by rw [mcp_regs_8])

/-- Print `2j` zeros. -/
def mcp_zs2 : Cmd := .seq (mcp_zs 6 0) (mcp_zs 6 0)

theorem mcp_em_zs2 (r j e : ℕ) :
    mcp_Em mcp_zs2 r j e (List.replicate (2 * j) zero) (18 * j + 16) :=
  ((mcp_em_zs6 0 r j e).seq (mcp_em_zs6 0 r j e)).cast
    (by rw [Nat.sub_zero, ← List.replicate_add, two_mul]) (by omega)

/-- Run `c` if `j = 0`, otherwise `d` (register `6` is restored). -/
def mcp_ifJ0 (c d : Cmd) : Cmd := .pop 6 c (.seq (.push 6 true) d) (.seq (.push 6 true) d)

theorem mcp_em_ifJ0 {c d : Cmd} {r j e : ℕ} {o o' : List SatSym} {T T' : ℕ}
    (hc : j = 0 → mcp_Em c r j e o T) (hd : j ≠ 0 → mcp_Em d r j e o' T') :
    mcp_Em (mcp_ifJ0 c d) r j e (if j = 0 then o else o') (T + T' + 2) := by
  intro W O Q E
  rcases j with _ | j
  · exact (ExecLe.pop_nil (by simp [mcp_S, st2_reg]) (hc rfl W O Q E)).cast (by simp) (by omega)
  · have h0 : update (mcp_S W O Q E r (j + 1) e) 6 (List.replicate j true) = mcp_S W O Q E r j e := by
      unfold mcp_S; rw [upd2_reg (by norm_num), mcp_upd_regs6]
    have h := (mcp_ex_push6 W O Q E r j e).seq_norm (hd (by omega) W O Q E)
    rw [← h0] at h
    exact (ExecLe.pop_same (b := true) (s := List.replicate j true)
      (by simp [mcp_S, st2_reg, List.replicate_succ]) h).cast (by simp) (by omega)

/-! ## The header row -/

/-- Print five zeros per symbol of stack `4`. -/
def mcp_kLoop : Cmd := .loop (disp 4 fun _ => emL [zero, zero, zero, zero, zero])

theorem mcp_ex_kLoop (W O : Str) (v : ℕ → ℕ) : ∀ (l E : List SatSym),
    ExecLe mcp_kLoop (st2 W O (l.flatMap ic) (rv E) v)
      (.norm (st2 W O [] (rv (E ++ List.replicate (5 * l.length) zero)) v)) (13 * l.length + 2)
  | [], E => (ex_disp_nil rfl).cast (by simp) le_rfl
  | s :: l, E => by
    have ih := mcp_ex_kLoop W O v l (E ++ [zero, zero, zero, zero, zero])
    have hb := ex_disp (k := 4) (f := fun _ => emL [zero, zero, zero, zero, zero]) (s := s)
      (Q' := l.flatMap ic) (σ := st2 W O ((s :: l).flatMap ic) (rv E) v) (by simp)
      (by rw [upd2_4]; exact ex_emL [zero, zero, zero, zero, zero] E v)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    rw [List.append_assoc, List.length_cons, show 5 * (l.length + 1) = 5 + 5 * l.length by ring,
      List.replicate_add]
    rfl

/-! ## The gadget rows -/

/-- Row `Lₚ` for `j ≠ 0`. -/
def mcp_lNz : SatSym → Cmd
  | pos => .seq (emL [zero, zero, zero]) (.seq mcp_zs2 (.seq (emL [pos])
      (.seq (mcp_zs 8 3) (emL [pos, sep]))))
  | neg => .seq (emL [zero, zero]) (.seq mcp_zs2 (.seq (emL [pos])
      (.seq (mcp_zs 8 2) (emL [pos, sep]))))
  | _ => .seq (emL [zero, pos]) (.seq (mcp_zs 5 1) (emL [pos, sep]))

/-- Row `Lₚ` (with `r = base - 2`). -/
def mcp_lC (s : SatSym) : Cmd := mcp_ifJ0 (emL (tw 0 (nlCol s 0) ++ [sep])) (mcp_lNz s)

theorem mcp_em_lNz (s : SatSym) (r j e : ℕ) (hj : j ≠ 0) (he : e = r - 2 * j) :
    mcp_Em (mcp_lNz s) r j e (lRow s (r + 2) j ++ [sep]) (9 * r + 18 * j + 9 * e + 60) := by
  cases s with
  | pos =>
    refine ((mcp_em_emL _ r j e).seq ((mcp_em_zs2 r j e).seq ((mcp_em_emL _ r j e).seq
      ((mcp_em_zs8 3 r j e).seq (mcp_em_emL _ r j e))))).cast ?_ (by simp; omega)
    rw [lRow, if_neg hj, tw, nlCol, show r + 2 - 1 - (3 + 2 * j) - 1 = e - 3 by omega,
      List.replicate_add]
    simp
  | neg =>
    refine ((mcp_em_emL _ r j e).seq ((mcp_em_zs2 r j e).seq ((mcp_em_emL _ r j e).seq
      ((mcp_em_zs8 2 r j e).seq (mcp_em_emL _ r j e))))).cast ?_ (by simp; omega)
    rw [lRow, if_neg hj, tw, nlCol, show r + 2 - 1 - (2 + 2 * j) - 1 = e - 2 by omega,
      List.replicate_add]
    simp
  | zero =>
    refine ((mcp_em_emL _ r j e).seq ((mcp_em_zs5 1 r j e).seq (mcp_em_emL _ r j e))).cast ?_
      (by simp; omega)
    rw [lRow, if_neg hj, tw, show nlCol zero j = 1 from rfl, show r + 2 - 1 - 1 - 1 = r - 1 by omega]
    simp
  | sep =>
    refine ((mcp_em_emL _ r j e).seq ((mcp_em_zs5 1 r j e).seq (mcp_em_emL _ r j e))).cast ?_
      (by simp; omega)
    rw [lRow, if_neg hj, tw, show nlCol sep j = 1 from rfl, show r + 2 - 1 - 1 - 1 = r - 1 by omega]
    simp

theorem mcp_em_lC (s : SatSym) (r j e : ℕ) (he : e = r - 2 * j) :
    mcp_Em (mcp_lC s) r j e (lRow s (r + 2) j ++ [sep]) (9 * r + 18 * j + 9 * e + 80) := by
  have h0 : (tw 0 (nlCol s 0) ++ [sep]).length ≤ 5 := by
    cases s <;> simp [tw, nlCol]
  refine (mcp_em_ifJ0 (o := tw 0 (nlCol s 0) ++ [sep]) (fun _ => mcp_em_emL _ r j e)
    (fun hj => mcp_em_lNz s r j e hj he)).cast ?_ (by omega)
  split_ifs with hj
  · subst hj; simp [lRow]
  · rfl

/-- Row `Cₚ`. -/
def mcp_cC (s : SatSym) : Cmd :=
  if s = sep then
    mcp_ifJ0 (.seq (emL [pos, pos]) (.seq (mcp_zs 5 0) (emL [pos, sep])))
      (.seq (emL [zero, pos]) (.seq (mcp_zs 5 1) (emL [pos, pos, sep])))
  else
    mcp_ifJ0 (.seq (emL [pos, zero]) (.seq (mcp_zs 5 0) (emL [pos, sep])))
      (.seq (emL [zero]) (.seq (mcp_zs 5 0) (emL [pos, pos, sep])))

theorem mcp_em_cC (s : SatSym) (r j e : ℕ) :
    mcp_Em (mcp_cC s) r j e (cRow s (r + 2) j ++ [sep]) (18 * r + 60) := by
  unfold mcp_cC
  by_cases hs : s = sep
  · rw [if_pos hs]
    refine (mcp_em_ifJ0 (fun _ => (mcp_em_emL _ r j e).seq ((mcp_em_zs5 0 r j e).seq
      (mcp_em_emL _ r j e))) (fun _ => (mcp_em_emL _ r j e).seq ((mcp_em_zs5 1 r j e).seq
      (mcp_em_emL _ r j e)))).cast ?_ (by simp; omega)
    unfold cRow
    split_ifs with hj
    · simp [show r + 2 - 2 = r by omega]
    · simp [show r + 2 - 3 = r - 1 by omega]
  · rw [if_neg hs]
    refine (mcp_em_ifJ0 (fun _ => (mcp_em_emL _ r j e).seq ((mcp_em_zs5 0 r j e).seq
      (mcp_em_emL _ r j e))) (fun _ => (mcp_em_emL _ r j e).seq ((mcp_em_zs5 0 r j e).seq
      (mcp_em_emL _ r j e)))).cast ?_ (by simp; omega)
    unfold cRow
    split_ifs with hj
    · simp [tw, List.replicate_succ]
    · simp [show r + 2 - 1 = r + 1 by omega, List.replicate_succ]

/-- Row `Bₚ`. -/
def mcp_bC (s : SatSym) : Cmd :=
  if s = sep then emL [sep]
  else .seq (emL [zero, zero, zero]) (.seq (mcp_zs 5 0) (emL [pos, sep]))

theorem mcp_em_bC (s : SatSym) (r j e : ℕ) :
    mcp_Em (mcp_bC s) r j e (bRow s (r + 2) ++ [sep]) (9 * r + 20) := by
  unfold mcp_bC
  by_cases hs : s = sep
  · rw [if_pos hs]
    exact (mcp_em_emL _ r j e).cast (by simp [bRow, hs]) (by simp)
  · rw [if_neg hs]
    refine ((mcp_em_emL _ r j e).seq ((mcp_em_zs5 0 r j e).seq (mcp_em_emL _ r j e))).cast ?_
      (by simp; omega)
    rw [bRow, if_neg hs, show r + 2 + 1 = 3 + r by omega, List.replicate_add]
    simp

/-- Register update after a position. -/
def mcp_updC (s : SatSym) : Cmd :=
  .seq (.push 5 true) (.seq (.push 5 true) (.seq (.push 5 true)
    (if s = sep then .seq (drain 6) (.seq (drain 8) (copyVia 5 8 11))
     else .seq (.push 6 true) (.push 8 true))))

theorem mcp_ex_updC (s : SatSym) (W O Q : Str) (E : List SatSym) (r j e : ℕ) :
    ExecLe (mcp_updC s) (mcp_S W O Q E r j e)
      (.norm (mcp_S W O Q E (r + 3) (nxJ s j) (if s = sep then r + 3 else e + 1)))
      (2 * j + 2 * e + 5 * r + 30) := by
  have h1 := mcp_ex_push5 W O Q E r j e
  have h2 := mcp_ex_push5 W O Q E (r + 1) j e
  have h3 := mcp_ex_push5 W O Q E (r + 1 + 1) j e
  have h4 : ExecLe (if s = sep then .seq (drain 6) (.seq (drain 8) (copyVia 5 8 11))
      else .seq (.push 6 true) (.push 8 true)) (mcp_S W O Q E (r + 3) j e)
      (.norm (mcp_S W O Q E (r + 3) (nxJ s j) (if s = sep then r + 3 else e + 1)))
      (2 * j + 2 * e + 5 * r + 25) := by
    by_cases hs : s = sep
    · subst hs; rw [if_pos rfl, if_pos rfl]
      exact ((mcp_ex_drain6 W O Q E _ j e).seq_norm ((mcp_ex_drain8 W O Q E _ 0 e).seq_norm
        (mcp_ex_copy58 W O Q E (r + 3) 0))).cast rfl (by omega)
    · rw [if_neg hs, if_neg hs]
      have : nxJ s j = j + 1 := by cases s <;> simp_all [nxJ]
      rw [this]
      exact ((mcp_ex_push6 W O Q E _ j e).seq_norm (mcp_ex_push8 W O Q E _ (j + 1) e)).cast rfl
        (by omega)
  exact (h1.seq_norm (h2.seq_norm (h3.seq_norm h4))).cast rfl (by omega)

/-- The gadget of one position. -/
def mcp_gBr (s : SatSym) : Cmd := .seq (.seq (mcp_lC s) (.seq (mcp_cC s) (mcp_bC s))) (mcp_updC s)

theorem mcp_ex_gBr (L p t : ℕ) (s : SatSym) (W O Q : Str) (E : List SatSym) (r j e : ℕ)
    (hb : r + 2 = base L p) (he : e = r - 2 * j) :
    ExecLe (mcp_gBr s) (mcp_S W O Q E r j e)
      (.norm (mcp_S W O Q (E ++ (gadRows L p (s, t, j)).flatMap (· ++ [sep])) (r + 3) (nxJ s j)
        (if s = sep then r + 3 else e + 1)))
      (50 * r + 20 * j + 20 * e + 200) := by
  have h := ((mcp_em_lC s r j e he).seq ((mcp_em_cC s r j e).seq (mcp_em_bC s r j e))) W O Q E
  have h2 := h.seq_norm (mcp_ex_updC s W O Q _ r j e)
  refine h2.cast ?_ ?_
  · simp [gadRows, ← hb, List.append_assoc]
  · omega

/-! ## The gadget loop -/

def mcp_gLoop : Cmd := .loop (disp 3 mcp_gBr)

theorem mcp_ex_gLoop (L N : ℕ) (W : Str) (hL : L ≤ N) : ∀ (l : List SatSym) (p t j r e : ℕ)
    (E : List SatSym), j ≤ p → p + l.length ≤ N → r = 2 * L + 3 * p → e = r - 2 * j →
    ∃ j' e', ExecLe mcp_gLoop (mcp_S W (l.flatMap ic) [] E r j e)
      (.norm (mcp_S W [] [] (E ++ (gadAll L p (ann l t j)).flatMap (· ++ [sep]))
        (2 * L + 3 * (p + l.length)) j' e')) (l.length * (400 * N + 400) + 2)
  | [], p, t, j, r, e, E, _, _, hr, _ =>
    ⟨j, e, (ex_disp_nil rfl).cast (by simp [ann, gadAll, hr]) (by simp)⟩
  | s :: l, p, t, j, r, e, E, hj, hl, hr, he => by
    simp only [List.length_cons] at hl
    have h1 := mcp_ex_gBr L p t s W (l.flatMap ic) [] E r j e (by simp [base]; omega) he
    obtain ⟨j', e', h2⟩ := mcp_ex_gLoop L N W hL l (p + 1) (nxT s t) (nxJ s j) (r + 3)
      (if s = sep then r + 3 else e + 1)
      (E ++ (gadRows L p (s, t, j)).flatMap (· ++ [sep]))
      (by cases s <;> simp [nxJ] <;> omega) (by omega) (by omega)
      (by cases s <;> simp [nxJ] <;> omega)
    refine ⟨j', e', ?_⟩
    have hb := ex_disp (k := 3) (f := mcp_gBr) (s := s) (Q' := l.flatMap ic)
      (σ := mcp_S W ((s :: l).flatMap ic) [] E r j e) (by simp)
      (by rw [mcp_upd_S3]; exact h1)
    refine (ExecLe.loop_norm hb h2).cast ?_ ?_
    · rw [show p + 1 + l.length = p + (l.length + 1) by omega]
      simp [ann_cons, gadAll, List.append_assoc]
    · simp only [List.length_cons]
      have : e ≤ r := by omega
      nlinarith

/-! ## The literal loop -/

/-- The rows `[]`, `xpRow j` (each followed by `sep`). -/
def mcp_litB : Cmd :=
  .seq (.seq (emL [sep, zero, zero]) (.seq mcp_zs2 (emL [pos, sep])))
    (.seq (.push 6 true) (.seq (.push 5 true) (.push 5 true)))

def mcp_litLoop : Cmd := .loop (disp 4 fun _ => mcp_litB)

/-- The literal rows printed from variable `j` on, `n` variables. -/
def mcp_litOut : ℕ → ℕ → List SatSym
  | _, 0 => []
  | j, n + 1 => [sep] ++ (xpRow j ++ [sep]) ++ mcp_litOut (j + 1) n

theorem mcp_litOut_eq : ∀ (n j : ℕ),
    mcp_litOut j n = ((List.range' j n).flatMap fun j => [[], xpRow j]).flatMap (· ++ [sep])
  | 0, j => rfl
  | n + 1, j => by
    rw [mcp_litOut, mcp_litOut_eq n (j + 1), List.range'_succ]
    simp [List.append_assoc]

theorem mcp_litOut_litRows (n : ℕ) : mcp_litOut 0 n = (litRows n).flatMap (· ++ [sep]) := by
  rw [mcp_litOut_eq, litRows, List.range_eq_range']

theorem mcp_ex_litB (W O Q : Str) (E : List SatSym) (j : ℕ) :
    ExecLe mcp_litB (mcp_S W O Q E (2 * j) j 0)
      (.norm (mcp_S W O Q (E ++ ([sep] ++ (xpRow j ++ [sep]))) (2 * (j + 1)) (j + 1) 0))
      (18 * j + 40) := by
  have h := ((mcp_em_emL [sep, zero, zero] (2 * j) j 0).seq ((mcp_em_zs2 (2 * j) j 0).seq
    (mcp_em_emL [pos, sep] (2 * j) j 0))) W O Q E
  set E' := E ++ ([sep, zero, zero] ++ (List.replicate (2 * j) zero ++ [pos, sep]))
  have h4 := mcp_ex_push6 W O Q E' (2 * j) j 0
  have h5 := mcp_ex_push5 W O Q E' (2 * j) (j + 1) 0
  have h6 := mcp_ex_push5 W O Q E' (2 * j + 1) (j + 1) 0
  have h7 := h.seq_norm (h4.seq_norm (h5.seq_norm h6))
  refine h7.cast ?_ (by simp; omega)
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
  congr 2
  simp [E', xpRow, List.replicate_add, List.append_assoc]

theorem mcp_ex_litLoop (W O : Str) (N : ℕ) : ∀ (l : List SatSym) (j : ℕ) (E : List SatSym),
    j + l.length ≤ N →
    ExecLe mcp_litLoop (mcp_S W O (l.flatMap ic) E (2 * j) j 0)
      (.norm (mcp_S W O [] (E ++ mcp_litOut j l.length) (2 * (j + l.length)) (j + l.length) 0))
      (l.length * (18 * N + 42) + 2)
  | [], j, E, _ => (ex_disp_nil rfl).cast (by simp [mcp_litOut]) (by simp)
  | s :: l, j, E, hl => by
    simp only [List.length_cons] at hl
    have h1 := mcp_ex_litB W O (l.flatMap ic) E j
    have h2 := mcp_ex_litLoop W O N l (j + 1) (E ++ ([sep] ++ (xpRow j ++ [sep]))) (by omega)
    have hb := ex_disp (k := 4) (f := fun _ => mcp_litB) (s := s) (Q' := l.flatMap ic)
      (σ := mcp_S W O ((s :: l).flatMap ic) E (2 * j) j 0) (by simp)
      (by rw [mcp_upd_S4]; exact h1)
    refine (ExecLe.loop_norm hb h2).cast ?_ ?_
    · rw [show j + 1 + l.length = j + (l.length + 1) by omega]
      simp [mcp_litOut, List.append_assoc]
    · simp only [List.length_cons]; nlinarith

end Pnp.Karp.MaxCut
