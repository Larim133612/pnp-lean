import Pnp.Karp.DomSet
import Pnp.Karp.HittingSetVer

/-!
# DOMINATING SET ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/DomSet.lean`, rows `kr :: rows`, `n = |rows|`) and a certificate `y : List Bool`
(bit `u` says whether the vertex `u < n` is in the dominating set; missing bits are `false`).
Let `V = hsv_pad y n` be the indicator vector.  A vertex `v` is dominated iff
`V_v`, or the row `v` has `pos` at a position of `V` (`hsv_hit`, as for HITTING SET), or some
row `u` with `V_u` has `pos` at position `v` (the *column* `v`).  The column condition is
computed in one pass as the vector `Dm = ⋁_{u, V_u} row u` (`dsv_dm`).  Stack layout:

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the indicator vector `V`;  `5`: `V` reversed (pass 1) / the scanned part of `V` (pass 2);
* `6`: the unary budget counter;  `7`: the code of the scanned rows (reversed, pass 1);
* `8`: the vector `Dm`;  `9`: the updated prefix of `Dm` (pass 1) / a second copy of `V`
  (pass 2);  `10`: `V` reversed (pass 1) / the domination flag (pass 2).

Program (`dsv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3`: parse the code of `w`, drop the unfinished tail;
2. `dsv_bL`: read the budget row `kr`, pushing a `true` onto stack `6` per symbol (halt `false`
   if there is no row);
3. `dsv_aL` (pass 1): per row `r` (detected by peeking at stack `3`), pop a certificate bit `b`,
   push it onto stacks `5` and `10`; if `b`, pop the budget counter (halt `false` if empty) and
   or the `pos` entries of `r` into `Dm` (`dsv_cL true`, then `move 9 8`); the code of `r` is
   copied onto stack `7`;
4. `move 7 3`, `move 5 4`, `move 10 9`: restore the rows, put `V` on stacks `4` and `9`;
5. `dsv_mL` (pass 2): per row `v`, set the flag to `Dm_v || V_v` (popping stacks `8` and `9`),
   then scan the row in parallel with `V` as in `hsv_rL`, setting the flag on a hit; at the `sep`
   the flag must be set (halt `false` otherwise).  At the end of the input accept.

`dsv_exec_ver`: the program halts with `dsv_vres (dec z).1 (dec z).2` on every input `z`,
within `dsv_Tver |z|` steps.
-/

namespace Pnp.Karp.DomSet

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.HittingSet

/-! ## Semantics -/

/-- The first `|r|` bits of `D`, or'ed with the `pos` entries of `r`. -/
def dsv_orP : List SatSym → Str → Str
  | [], _ => []
  | s :: r, D => (D.headD false || decide (s = pos)) :: dsv_orP r D.tail

/-- `D` or'ed with the `pos` entries of `r`. -/
def dsv_or (r : List SatSym) (D : Str) : Str := dsv_orP r D ++ D.drop r.length

/-- The column vector: `D` or'ed with every row whose certificate bit is set. -/
def dsv_dm : List (List SatSym) → Str → Str → Str
  | [], _, D => D
  | r :: rows, R, D => dsv_dm rows R.tail (if R.headD false then dsv_or r D else D)

/-- What the second pass computes. -/
def dsv_go (V : Str) : List (List SatSym) → Str → Str → Bool
  | [], _, _ => true
  | r :: rows, D, E =>
      (D.headD false || E.headD false || hsv_hit r V) && dsv_go V rows D.tail E.tail

/-- The answer of the verifier on `(w, y)`. -/
def dsv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | kr :: rows => decide ((hsv_pad y rows.length).count true ≤ kr.length) &&
      dsv_go (hsv_pad y rows.length) rows (dsv_dm rows y []) (hsv_pad y rows.length)

theorem dsv_orP_length : ∀ (r : List SatSym) (D : Str), (dsv_orP r D).length = r.length
  | [], _ => rfl
  | _ :: r, D => by simp [dsv_orP, dsv_orP_length r D.tail]

theorem dsv_enc_length : ∀ rows : List (List SatSym),
    (enc rows).length = 2 * ((rows.map List.length).sum + rows.length)
  | [] => rfl
  | r :: rows => by
    rw [enc_cons]
    simp only [List.length_append, length_flatMap_ic, List.length_cons, dsv_enc_length rows,
      List.map_cons, List.sum_cons]
    ring

/-! ## Stack layout -/

/-- The stacks of the verifier. -/
def dsv_st (R Q V W K C D E F : Str) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 4 then V else if j = 5 then W else
  if j = 6 then K else if j = 7 then C else if j = 8 then D else if j = 9 then E else
  if j = 10 then F else []

local macro "dsv_stx" : tactic =>
  `(tactic| (funext j; simp only [dsv_st, update_apply]; split_ifs <;> simp_all))

section St
variable {R Q V W K C D E F : Str}
@[simp] theorem dsv_st_0 : dsv_st R Q V W K C D E F 0 = R := rfl
@[simp] theorem dsv_st_3 : dsv_st R Q V W K C D E F 3 = Q := rfl
@[simp] theorem dsv_st_4 : dsv_st R Q V W K C D E F 4 = V := rfl
@[simp] theorem dsv_st_5 : dsv_st R Q V W K C D E F 5 = W := rfl
@[simp] theorem dsv_st_6 : dsv_st R Q V W K C D E F 6 = K := rfl
@[simp] theorem dsv_st_7 : dsv_st R Q V W K C D E F 7 = C := rfl
@[simp] theorem dsv_st_8 : dsv_st R Q V W K C D E F 8 = D := rfl
@[simp] theorem dsv_st_9 : dsv_st R Q V W K C D E F 9 = E := rfl
@[simp] theorem dsv_st_10 : dsv_st R Q V W K C D E F 10 = F := rfl
@[simp] theorem dsv_u0 (X : Str) :
    update (dsv_st R Q V W K C D E F) 0 X = dsv_st X Q V W K C D E F := by dsv_stx
@[simp] theorem dsv_u3 (X : Str) :
    update (dsv_st R Q V W K C D E F) 3 X = dsv_st R X V W K C D E F := by dsv_stx
@[simp] theorem dsv_u4 (X : Str) :
    update (dsv_st R Q V W K C D E F) 4 X = dsv_st R Q X W K C D E F := by dsv_stx
@[simp] theorem dsv_u5 (X : Str) :
    update (dsv_st R Q V W K C D E F) 5 X = dsv_st R Q V X K C D E F := by dsv_stx
@[simp] theorem dsv_u6 (X : Str) :
    update (dsv_st R Q V W K C D E F) 6 X = dsv_st R Q V W X C D E F := by dsv_stx
@[simp] theorem dsv_u7 (X : Str) :
    update (dsv_st R Q V W K C D E F) 7 X = dsv_st R Q V W K X D E F := by dsv_stx
@[simp] theorem dsv_u8 (X : Str) :
    update (dsv_st R Q V W K C D E F) 8 X = dsv_st R Q V W K C X E F := by dsv_stx
@[simp] theorem dsv_u9 (X : Str) :
    update (dsv_st R Q V W K C D E F) 9 X = dsv_st R Q V W K C D X F := by dsv_stx
@[simp] theorem dsv_u10 (X : Str) :
    update (dsv_st R Q V W K C D E F) 10 X = dsv_st R Q V W K C D E X := by dsv_stx
end St

/-- The two-bit dispatch on stack `3` (generic stacks). -/
theorem dsv_pop2 {σ : ℕ → Str} {Q : Str} {cE cX cS cZ cP cN : Cmd} (s : SatSym) {r : Res}
    {T : ℕ} (hq : σ 3 = ic s ++ Q) (h : ExecLe (hsv_sel s cS cZ cP cN) (update σ 3 Q) r T) :
    ExecLe (.pop 3 cE (.pop 3 cX cS cZ) (.pop 3 cX cP cN)) σ r (T + 2) := by
  cases s with
  | sep => exact ExecLe.pop_cons (b := false) hq (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [hsv_sel, update_idem] using h))
  | zero => exact ExecLe.pop_cons (b := false) hq (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [hsv_sel, update_idem] using h))
  | pos => exact ExecLe.pop_cons (b := true) hq (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [hsv_sel, update_idem] using h))
  | neg => exact ExecLe.pop_cons (b := true) hq (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [hsv_sel, update_idem] using h))

/-- Peeking at stack `3`: pop a bit and push it back. -/
theorem dsv_peek {c : Cmd} {σ : ℕ → Str} {b : Bool} {s : Str} {r : Res} {T : ℕ}
    (hk : σ 3 = b :: s) (h : ExecLe c σ r T) :
    ExecLe (.pop 3 .brk (.seq (.push 3 false) c) (.seq (.push 3 true) c)) σ r (T + 2) := by
  have e : update (update σ 3 s) 3 (b :: update σ 3 s 3) = σ := by
    rw [update_self, update_idem, ← hk, update_eq_self]
  refine ExecLe.pop_cons hk ?_
  cases b
  · exact ((ExecLe.push 3 false _).seq_norm (by rw [e]; exact h)).cast rfl (by omega)
  · exact ((ExecLe.push 3 true _).seq_norm (by rw [e]; exact h)).cast rfl (by omega)

/-! ## The budget row -/

def dsv_bB : Cmd :=
  .pop 3 (.halt false) (.pop 3 (.halt false) .brk (.push 6 true))
    (.pop 3 (.halt false) (.push 6 true) (.push 6 true))

def dsv_bL : Cmd := .loop dsv_bB

theorem dsv_ex_bd (R Q' V W C D E F : Str) : ∀ (t : List SatSym) (c : ℕ), sep ∉ t →
    ExecLe dsv_bL
      (dsv_st R (t.flatMap ic ++ false :: false :: Q') V W (List.replicate c true) C D E F)
      (.norm (dsv_st R Q' V W (List.replicate (t.length + c) true) C D E F))
      (4 * t.length + 3)
  | [], c, _ => by
    have hb := dsv_pop2 (cE := .halt false) (cX := .halt false) (cZ := .push 6 true)
      (cP := .push 6 true) (cN := .push 6 true) (cS := .brk) (Q := Q') sep
      (σ := dsv_st R (false :: false :: Q') V W (List.replicate c true) C D E F) rfl
      (ExecLe.brk _)
    exact (ExecLe.loop_brk hb).cast (by simp) (by simp)
  | s :: t, c, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := dsv_ex_bd R Q' V W C D E F t (c + 1) (fun e => hr (List.mem_cons_of_mem _ e))
    have hp : ExecLe (hsv_sel s .brk (.push 6 true) (.push 6 true) (.push 6 true))
        (dsv_st R (t.flatMap ic ++ false :: false :: Q') V W (List.replicate c true) C D E F)
        (.norm (dsv_st R (t.flatMap ic ++ false :: false :: Q') V W
          (List.replicate (c + 1) true) C D E F)) 1 := by
      have := ExecLe.push 6 true
        (dsv_st R (t.flatMap ic ++ false :: false :: Q') V W (List.replicate c true) C D E F)
      rw [dsv_st_6, dsv_u6, ← List.replicate_succ] at this
      cases s with
      | sep => exact absurd rfl hs
      | _ => exact this
    have hb := dsv_pop2 (cE := .halt false) (cX := .halt false) s
      (Q := t.flatMap ic ++ false :: false :: Q')
      (σ := dsv_st R ((s :: t).flatMap ic ++ false :: false :: Q') V W
        (List.replicate c true) C D E F) (by simp) (by rw [dsv_u3]; exact hp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp only [List.length_cons]
    congr 3; omega

theorem dsv_ex_bdEnd (R V W K C D E F : Str) :
    ExecLe dsv_bL (dsv_st R [] V W K C D E F) (.halt false) 2 :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt false _))

/-! ## Pass 1: scanning a row -/

/-- Update one bit of `Dm` (`p`: the symbol is `pos`). -/
def dsv_dU (p : Bool) : Cmd := .pop 8 (.push 9 p) (.push 9 p) (.push 9 true)

/-- The `Dm` update, if the row is selected. -/
def dsv_sU : Bool → Bool → Cmd
  | false, _ => .skip
  | true, p => dsv_dU p

/-- Copy the two code bits of a symbol onto stack `7`, then continue. -/
def dsv_cpy (a b : Bool) (c : Cmd) : Cmd := .seq (.push 7 a) (.seq (.push 7 b) c)

def dsv_cB (u : Bool) : Cmd :=
  .pop 3 (.halt false)
    (.pop 3 (.halt false) (dsv_cpy false false .brk) (dsv_cpy false true (dsv_sU u false)))
    (.pop 3 (.halt false) (dsv_cpy true false (dsv_sU u true))
      (dsv_cpy true true (dsv_sU u false)))

def dsv_cL (u : Bool) : Cmd := .loop (dsv_cB u)

theorem dsv_ex_cpy (a b : Bool) {c : Cmd} {R Q V W K C D E F : Str} {r : Res} {T : ℕ}
    (h : ExecLe c (dsv_st R Q V W K (b :: a :: C) D E F) r T) :
    ExecLe (dsv_cpy a b c) (dsv_st R Q V W K C D E F) r (T + 2) := by
  have h1 := ExecLe.push 7 a (dsv_st R Q V W K C D E F)
  rw [dsv_st_7, dsv_u7] at h1
  have h2 := ExecLe.push 7 b (dsv_st R Q V W K (a :: C) D E F)
  rw [dsv_st_7, dsv_u7] at h2
  exact (h1.seq_norm (h2.seq_norm h)).cast rfl (by omega)

theorem dsv_ex_dU (p : Bool) (R Q V W K C D E F : Str) :
    ExecLe (dsv_dU p) (dsv_st R Q V W K C D E F)
      (.norm (dsv_st R Q V W K C D.tail ((D.headD false || p) :: E) F)) 2 := by
  rcases D with _ | ⟨_ | _, D⟩
  · have := ExecLe.push 9 p (dsv_st R Q V W K C [] E F)
    rw [dsv_st_9, dsv_u9] at this
    exact (ExecLe.pop_nil rfl this).cast (by simp) le_rfl
  · have := ExecLe.push 9 p (dsv_st R Q V W K C D E F)
    rw [dsv_st_9, dsv_u9] at this
    exact (ExecLe.pop_cons (b := false) (s := D) rfl (by rw [dsv_u8]; exact this)).cast
      (by simp) le_rfl
  · have := ExecLe.push 9 true (dsv_st R Q V W K C D E F)
    rw [dsv_st_9, dsv_u9] at this
    exact (ExecLe.pop_cons (b := true) (s := D) rfl (by rw [dsv_u8]; exact this)).cast
      (by simp) le_rfl

theorem dsv_ex_sU (u p : Bool) (R Q V W K C D E F : Str) :
    ExecLe (dsv_sU u p) (dsv_st R Q V W K C D E F)
      (.norm (dsv_st R Q V W K C (if u then D.tail else D)
        (if u then (D.headD false || p) :: E else E) F)) 2 := by
  cases u
  · exact (ExecLe.skip _).cast (by simp) (by omega)
  · exact (dsv_ex_dU p _ _ _ _ _ _ _ _ _).cast (by simp) le_rfl

theorem dsv_ex_csym (u : Bool) (R Q V W K C D E F : Str) {s : SatSym} (hs : s ≠ sep) :
    ExecLe (hsv_sel s (dsv_cpy false false .brk) (dsv_cpy false true (dsv_sU u false))
        (dsv_cpy true false (dsv_sU u true)) (dsv_cpy true true (dsv_sU u false)))
      (dsv_st R Q V W K C D E F)
      (.norm (dsv_st R Q V W K ((ic s).reverse ++ C) (if u then D.tail else D)
        (if u then (D.headD false || decide (s = pos)) :: E else E) F)) 4 := by
  cases s with
  | sep => exact absurd rfl hs
  | zero =>
    exact (dsv_ex_cpy false true (dsv_ex_sU u false _ _ _ _ _ _ _ _ _)).cast (by simp [ic]) le_rfl
  | pos =>
    exact (dsv_ex_cpy true false (dsv_ex_sU u true _ _ _ _ _ _ _ _ _)).cast (by simp [ic]) le_rfl
  | neg =>
    exact (dsv_ex_cpy true true (dsv_ex_sU u false _ _ _ _ _ _ _ _ _)).cast (by simp [ic]) le_rfl

theorem dsv_ex_cl (u : Bool) (R Q' V W K F : Str) :
    ∀ (t : List SatSym) (C D E : Str), sep ∉ t →
    ExecLe (dsv_cL u) (dsv_st R (t.flatMap ic ++ false :: false :: Q') V W K C D E F)
      (.norm (dsv_st R Q' V W K ((t.flatMap ic ++ [false, false]).reverse ++ C)
        (if u then D.drop t.length else D) (if u then (dsv_orP t D).reverse ++ E else E) F))
      (6 * t.length + 5)
  | [], C, D, E, _ => by
    have hb := dsv_pop2 (cE := .halt false) (cX := .halt false)
      (cZ := dsv_cpy false true (dsv_sU u false)) (cP := dsv_cpy true false (dsv_sU u true))
      (cN := dsv_cpy true true (dsv_sU u false)) (cS := dsv_cpy false false .brk) (Q := Q') sep
      (σ := dsv_st R (false :: false :: Q') V W K C D E F) rfl
      (by rw [dsv_u3]; exact dsv_ex_cpy false false (ExecLe.brk _))
    refine (ExecLe.loop_brk hb).cast ?_ (by simp)
    cases u <;> simp [dsv_orP]
  | s :: t, C, D, E, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := dsv_ex_cl u R Q' V W K F t ((ic s).reverse ++ C) (if u then D.tail else D)
      (if u then (D.headD false || decide (s = pos)) :: E else E)
      (fun e => hr (List.mem_cons_of_mem _ e))
    have hb := dsv_pop2 (cE := .halt false) (cX := .halt false) s
      (Q := t.flatMap ic ++ false :: false :: Q')
      (σ := dsv_st R ((s :: t).flatMap ic ++ false :: false :: Q') V W K C D E F) (by simp)
      (by rw [dsv_u3]; exact dsv_ex_csym u R _ V W K C D E F hs)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    cases u <;> simp [dsv_orP, List.drop_tail]

/-! ## Pass 1: one row -/

def dsv_aDec : Cmd := .pop 6 (.halt false) .skip .skip

def dsv_aT : Bool → Cmd
  | false => dsv_cL false
  | true => .seq dsv_aDec (.seq (dsv_cL true) (move 9 8))

def dsv_aRow (b : Bool) : Cmd := .seq (.push 5 b) (.seq (.push 10 b) (dsv_aT b))

def dsv_aR : Cmd := .pop 0 (dsv_aRow false) (dsv_aRow false) (dsv_aRow true)

def dsv_aB : Cmd := .pop 3 .brk (.seq (.push 3 false) dsv_aR) (.seq (.push 3 true) dsv_aR)

def dsv_aL : Cmd := .loop dsv_aB

theorem dsv_ex_push510 (b : Bool) {c : Cmd} {R Q V W K C D E F : Str} {r : Res} {T : ℕ}
    (h : ExecLe c (dsv_st R Q V (b :: W) K C D E (b :: F)) r T) :
    ExecLe (.seq (.push 5 b) (.seq (.push 10 b) c)) (dsv_st R Q V W K C D E F) r (T + 2) := by
  have h1 := ExecLe.push 5 b (dsv_st R Q V W K C D E F)
  rw [dsv_st_5, dsv_u5] at h1
  have h2 := ExecLe.push 10 b (dsv_st R Q V (b :: W) K C D E F)
  rw [dsv_st_10, dsv_u10] at h2
  exact (h1.seq_norm (h2.seq_norm h)).cast rfl (by omega)

section Row
variable (R Q' W C D F : Str) (r : List SatSym) (hr : sep ∉ r)
include hr

theorem dsv_ex_aRowF (K : Str) :
    ExecLe (dsv_aRow false) (dsv_st R (r.flatMap ic ++ false :: false :: Q') [] W K C D [] F)
      (.norm (dsv_st R Q' [] (false :: W) K ((r.flatMap ic ++ [false, false]).reverse ++ C) D []
        (false :: F))) (6 * r.length + 7) :=
  (dsv_ex_push510 false (dsv_ex_cl false R Q' [] (false :: W) K (false :: F) r C D [] hr)).cast
    (by simp) le_rfl

theorem dsv_ex_aRowT (c : ℕ) :
    ExecLe (dsv_aRow true)
      (dsv_st R (r.flatMap ic ++ false :: false :: Q') [] W (List.replicate (c + 1) true) C D []
        F)
      (.norm (dsv_st R Q' [] (true :: W) (List.replicate c true)
        ((r.flatMap ic ++ [false, false]).reverse ++ C) (dsv_or r D) [] (true :: F)))
      (8 * r.length + 11) := by
  have hD : ExecLe dsv_aDec
      (dsv_st R (r.flatMap ic ++ false :: false :: Q') [] (true :: W)
        (List.replicate (c + 1) true) C D [] (true :: F))
      (.norm (dsv_st R (r.flatMap ic ++ false :: false :: Q') [] (true :: W)
        (List.replicate c true) C D [] (true :: F))) 2 :=
    (ExecLe.pop_cons (b := true) (s := List.replicate c true) rfl
      (by rw [dsv_u6]; exact ExecLe.skip _)).cast rfl le_rfl
  have hC := dsv_ex_cl true R Q' [] (true :: W) (List.replicate c true) (true :: F) r C D [] hr
  simp only [if_true, List.append_nil] at hC
  have hM := exec_move (a := 9) (b := 8) (by decide) _ _ (dsv_st_9 (R := R) (Q := Q')
    (V := []) (W := true :: W) (K := List.replicate c true)
    (C := (r.flatMap ic ++ [false, false]).reverse ++ C) (D := D.drop r.length)
    (E := (dsv_orP r D).reverse) (F := true :: F))
  simp only [dsv_u9, dsv_u8, dsv_st_8, List.reverse_reverse] at hM
  refine (dsv_ex_push510 true (hD.seq_norm (hC.seq_norm (ExecLe.of hM)))).cast rfl ?_
  simp only [List.length_reverse, dsv_orP_length]; omega

omit hr in
theorem dsv_ex_aRowT0 (K : Str) (hK : K = []) :
    ExecLe (dsv_aRow true) (dsv_st R (r.flatMap ic ++ false :: false :: Q') [] W K C D [] F)
      (.halt false) 4 := by
  subst hK
  exact dsv_ex_push510 true (ExecLe.seq_halt (ExecLe.pop_nil rfl (ExecLe.halt false _)))

end Row

/-! ## Pass 1: the loop -/

theorem dsv_ex_pass1 : ∀ (rows : List (List SatSym)) (R W C D F : Str) (c : ℕ),
    (∀ r ∈ rows, sep ∉ r) →
    ExecLe dsv_aL (dsv_st R (enc rows) [] W (List.replicate c true) C D [] F)
      (if (hsv_pad R rows.length).count true ≤ c then
        .norm (dsv_st (R.drop rows.length) [] [] ((hsv_pad R rows.length).reverse ++ W)
          (List.replicate (c - (hsv_pad R rows.length).count true) true)
          ((enc rows).reverse ++ C) (dsv_dm rows R D) [] ((hsv_pad R rows.length).reverse ++ F))
      else .halt false)
      (8 * (rows.map List.length).sum + 16 * rows.length + 2)
  | [], R, W, C, D, F, c, _ => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast ?_ (by simp)
    simp [hsv_pad, dsv_dm, enc]
  | r :: rows, R, W, C, D, F, c, hrows => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r' ∈ rows, sep ∉ r' := fun r' h => hrows r' (by simp [h])
    obtain ⟨b0, s0, hbs⟩ : ∃ b s, r.flatMap ic ++ false :: false :: enc rows = b :: s :=
      List.exists_cons_of_ne_nil (by simp)
    have hT : 8 * ((r :: rows).map List.length).sum + 16 * (r :: rows).length + 2 =
        (8 * r.length + 14) + (8 * (rows.map List.length).sum + 16 * rows.length + 2) + 2 := by
      simp; ring
    rw [hT]
    have key : ∀ (b : Bool) (R' : Str) (res : Res) (T : ℕ), R.headD false = b →
        R.tail = R' →
        (R = [] ∨ R = b :: R') →
        ExecLe (dsv_aRow b) (dsv_st R' (enc (r :: rows)) [] W (List.replicate c true) C D [] F)
          res T →
        ExecLe dsv_aB (dsv_st R (enc (r :: rows)) [] W (List.replicate c true) C D [] F) res
          (T + 2 + 1) := by
      intro b R' res T _ _ hR h
      refine dsv_peek (by rw [dsv_st_3, enc_cons]; exact hbs) ?_
      rcases hR with rfl | rfl
      · subst b; subst R'
        exact (ExecLe.pop_nil rfl h).cast rfl (by omega)
      · cases b
        · exact (ExecLe.pop_cons (b := false) (s := R') rfl (by rw [dsv_u0]; exact h)).cast rfl
            (by omega)
        · exact (ExecLe.pop_cons (b := true) (s := R') rfl (by rw [dsv_u0]; exact h)).cast rfl
            (by omega)
    have hRc : R = [] ∨ R = R.headD false :: R.tail := by
      rcases R with _ | ⟨x, R⟩ <;> simp
    have hpad : hsv_pad R (r :: rows).length = R.headD false :: hsv_pad R.tail rows.length := rfl
    rw [hpad]
    cases hb : R.headD false
    · rw [hb] at hRc
      have ih := dsv_ex_pass1 rows R.tail (false :: W)
        ((r.flatMap ic ++ [false, false]).reverse ++ C) D (false :: F) c hrs
      have h1 := dsv_ex_aRowF R.tail (enc rows) W C D F r hr (List.replicate c true)
      rw [← enc_cons] at h1
      have := ExecLe.loop_norm (key false R.tail _ _ hb rfl hRc h1) ih
      refine this.cast ?_ (by omega)
      have hdm : dsv_dm (r :: rows) R D = dsv_dm rows R.tail D := by
        simp only [dsv_dm, hb, Bool.false_eq_true, if_false]
      rw [hdm]
      by_cases hc : (hsv_pad R.tail rows.length).count true ≤ c
      · rw [if_pos hc, if_pos (by simpa using hc)]
        simp [List.drop_tail, enc_cons]
      · rw [if_neg hc, if_neg (by simpa using hc)]
    · rw [hb] at hRc
      rcases c with _ | c
      · have h1 := dsv_ex_aRowT0 R.tail (enc rows) W C D F r (List.replicate 0 true) rfl
        rw [← enc_cons] at h1
        refine (ExecLe.loop_halt (key true R.tail _ _ hb rfl hRc h1)).cast ?_ (by omega)
        simp
      · have ih := dsv_ex_pass1 rows R.tail (true :: W)
          ((r.flatMap ic ++ [false, false]).reverse ++ C) (dsv_or r D) (true :: F) c hrs
        have h1 := dsv_ex_aRowT R.tail (enc rows) W C D F r hr c
        rw [← enc_cons] at h1
        have := ExecLe.loop_norm (key true R.tail _ _ hb rfl hRc h1) ih
        refine this.cast ?_ (by omega)
        have hdm : dsv_dm (r :: rows) R D = dsv_dm rows R.tail (dsv_or r D) := by
          simp only [dsv_dm, hb, if_true]
        rw [hdm]
        simp only [List.count_cons_self, List.length_cons]
        by_cases hc : (hsv_pad R.tail rows.length).count true ≤ c
        · rw [if_pos hc, if_pos (by omega)]
          simp [List.drop_tail, enc_cons]
        · rw [if_neg hc, if_neg (by omega)]

/-! ## Pass 2: the domination flag -/

def dsv_setF : Cmd := .pop 10 (.push 10 true) (.push 10 true) (.push 10 true)

def dsv_fD : Cmd := .pop 8 .skip .skip dsv_setF

def dsv_fE : Cmd := .pop 9 .skip .skip dsv_setF

theorem dsv_ex_setF (R Q V W K C D E : Str) (f : Bool) :
    ExecLe dsv_setF (dsv_st R Q V W K C D E (hsv_F f))
      (.norm (dsv_st R Q V W K C D E (hsv_F true))) 2 := by
  cases f
  · exact (ExecLe.pop_nil rfl (ExecLe.push 10 true _)).cast (by simp [hsv_F]) le_rfl
  · exact (ExecLe.pop_cons (b := true) (s := []) rfl
      (by rw [dsv_u10]; exact ExecLe.push 10 true _)).cast (by simp [hsv_F]) le_rfl

theorem dsv_ex_fD (R Q V W K C D E : Str) (f : Bool) :
    ExecLe dsv_fD (dsv_st R Q V W K C D E (hsv_F f))
      (.norm (dsv_st R Q V W K C D.tail E (hsv_F (f || D.headD false)))) 3 := by
  rcases D with _ | ⟨_ | _, D⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp) (by omega)
  · exact (ExecLe.pop_cons (b := false) (s := D) rfl
      (by rw [dsv_u8]; exact ExecLe.skip _)).cast (by simp) (by omega)
  · exact (ExecLe.pop_cons (b := true) (s := D) rfl
      (by rw [dsv_u8]; exact dsv_ex_setF _ _ _ _ _ _ _ _ f)).cast (by simp) le_rfl

theorem dsv_ex_fE (R Q V W K C D E : Str) (f : Bool) :
    ExecLe dsv_fE (dsv_st R Q V W K C D E (hsv_F f))
      (.norm (dsv_st R Q V W K C D E.tail (hsv_F (f || E.headD false)))) 3 := by
  rcases E with _ | ⟨_ | _, E⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp) (by omega)
  · exact (ExecLe.pop_cons (b := false) (s := E) rfl
      (by rw [dsv_u9]; exact ExecLe.skip _)).cast (by simp) (by omega)
  · exact (ExecLe.pop_cons (b := true) (s := E) rfl
      (by rw [dsv_u9]; exact dsv_ex_setF _ _ _ _ _ _ _ _ f)).cast (by simp) le_rfl

/-! ## Pass 2: scanning a row -/

def dsv_rZ : Cmd := .pop 4 .skip (.push 5 false) (.push 5 true)

def dsv_rP : Cmd := .pop 4 .skip (.push 5 false) (.seq (.push 5 true) dsv_setF)

def dsv_rS : Cmd := .pop 10 (.halt false) .brk .brk

def dsv_rB : Cmd :=
  .pop 3 (.halt true) (.pop 3 (.halt false) dsv_rS dsv_rZ) (.pop 3 (.halt false) dsv_rP dsv_rZ)

def dsv_rL : Cmd := .loop dsv_rB

theorem dsv_ex_sym_nil (R Q W K C D E F : Str) {s : SatSym} (hs : s ≠ sep) :
    ExecLe (hsv_sel s dsv_rS dsv_rZ dsv_rP dsv_rZ) (dsv_st R Q [] W K C D E F)
      (.norm (dsv_st R Q [] W K C D E F)) 2 := by
  cases s with
  | sep => exact absurd rfl hs
  | _ => exact ExecLe.pop_nil rfl (ExecLe.skip _)

theorem dsv_ex_sym (R Q W K C D E : Str) (v : Bool) (V : Str) (f : Bool) {s : SatSym}
    (hs : s ≠ sep) :
    ExecLe (hsv_sel s dsv_rS dsv_rZ dsv_rP dsv_rZ) (dsv_st R Q (v :: V) W K C D E (hsv_F f))
      (.norm (dsv_st R Q V (v :: W) K C D E (hsv_F (f || (v && decide (s = pos)))))) 4 := by
  have hZ : ExecLe dsv_rZ (dsv_st R Q (v :: V) W K C D E (hsv_F f))
      (.norm (dsv_st R Q V (v :: W) K C D E (hsv_F f))) 2 := by
    refine ExecLe.pop_cons (b := v) (s := V) rfl ?_
    cases v
    · exact (ExecLe.push 5 false _).cast (by simp) le_rfl
    · exact (ExecLe.push 5 true _).cast (by simp) le_rfl
  cases s with
  | sep => exact absurd rfl hs
  | pos =>
    refine ExecLe.pop_cons (b := v) (s := V) rfl ?_
    cases v
    · exact (ExecLe.push 5 false _).cast (by simp) (show 1 ≤ 3 by omega)
    · refine ((ExecLe.push 5 true _).seq_norm ?_).cast rfl (show 1 + 2 ≤ 3 by omega)
      simp only [dsv_u4, dsv_st_5, dsv_u5]
      exact (dsv_ex_setF _ _ _ _ _ _ _ _ f).cast (by simp) le_rfl
  | zero => exact (hZ.cast (by simp) (by omega))
  | neg => exact (hZ.cast (by simp) (by omega))

theorem dsv_ex_row (R Q' K C D E : Str) :
    ∀ (r : List SatSym) (V W : Str) (f : Bool), sep ∉ r →
    ExecLe dsv_rL (dsv_st R (r.flatMap ic ++ false :: false :: Q') V W K C D E (hsv_F f))
      (if (f || hsv_hit r V) = true then
        .norm (dsv_st R Q' (V.drop r.length) ((V.take r.length).reverse ++ W) K C D E [])
      else .halt false)
      (6 * r.length + 4)
  | [], V, W, false, _ => by
    have hb := dsv_pop2 (cE := .halt true) (cX := .halt false) (cZ := dsv_rZ) (cP := dsv_rP)
      (cN := dsv_rZ) (cS := dsv_rS) (Q := Q') sep
      (σ := dsv_st R (false :: false :: Q') V W K C D E []) rfl
      (by rw [dsv_u3]; exact ExecLe.pop_nil rfl (ExecLe.halt false _))
    exact (ExecLe.loop_halt hb).cast (by cases V <;> simp [hsv_hit]) (by simp)
  | [], V, W, true, _ => by
    have hb := dsv_pop2 (cE := .halt true) (cX := .halt false) (cZ := dsv_rZ) (cP := dsv_rP)
      (cN := dsv_rZ) (cS := dsv_rS) (Q := Q') sep
      (σ := dsv_st R (false :: false :: Q') V W K C D E [true]) rfl
      (by rw [dsv_u3]; exact ExecLe.pop_cons (b := true) (s := []) rfl (ExecLe.brk _))
    exact (ExecLe.loop_brk hb).cast (by simp) (by simp)
  | s :: r, [], W, f, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := dsv_ex_row R Q' K C D E r [] W f (fun e => hr (List.mem_cons_of_mem _ e))
    have hb := dsv_pop2 (cE := .halt true) (cX := .halt false) s
      (Q := r.flatMap ic ++ false :: false :: Q')
      (σ := dsv_st R ((s :: r).flatMap ic ++ false :: false :: Q') [] W K C D E (hsv_F f))
      (by simp) (by rw [dsv_u3]; exact dsv_ex_sym_nil R _ W K C D E (hsv_F f) hs)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp
  | s :: r, v :: V, W, f, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := dsv_ex_row R Q' K C D E r V (v :: W) (f || (v && decide (s = pos)))
      (fun e => hr (List.mem_cons_of_mem _ e))
    have hb := dsv_pop2 (cE := .halt true) (cX := .halt false) s
      (Q := r.flatMap ic ++ false :: false :: Q')
      (σ := dsv_st R ((s :: r).flatMap ic ++ false :: false :: Q') (v :: V) W K C D E
        (hsv_F f)) (by simp) (by rw [dsv_u3]; exact dsv_ex_sym R _ W K C D E v V f hs)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp only [hsv_hit, Bool.or_assoc, List.length_cons, List.drop_succ_cons,
      List.take_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem dsv_ex_rowEnd (R V W K C D E F : Str) :
    ExecLe dsv_rL (dsv_st R [] V W K C D E F) (.halt true) 2 :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt true _))

/-! ## Pass 2: the loop -/

def dsv_mB : Cmd := .seq dsv_fD (.seq dsv_fE (.seq dsv_rL (move 5 4)))

def dsv_mL : Cmd := .loop dsv_mB

theorem dsv_ex_main (R V K : Str) : ∀ (rows : List (List SatSym)) (D E : Str),
    (∀ r ∈ rows, sep ∉ r) →
    ExecLe dsv_mL (dsv_st R (enc rows) V [] K [] D E []) (.halt (dsv_go V rows D E))
      (8 * (rows.map List.length).sum + 12 * rows.length + 8)
  | [], D, E, _ => by
    have h1 := dsv_ex_fD R [] V [] K [] D E false
    have h2 := dsv_ex_fE R [] V [] K [] D.tail E (false || D.headD false)
    exact (ExecLe.loop_halt (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt
      (dsv_ex_rowEnd _ _ _ _ _ _ _ _))))).cast (by simp [dsv_go]) (by simp)
  | r :: rows, D, E, hrows => by
    have hr : sep ∉ r := hrows r (by simp)
    have ih := dsv_ex_main R V K rows D.tail E.tail fun r' h => hrows r' (by simp [h])
    have h1 := dsv_ex_fD R (enc (r :: rows)) V [] K [] D E false
    have h2 := dsv_ex_fE R (enc (r :: rows)) V [] K [] D.tail E (false || D.headD false)
    rw [enc_cons] at h1 h2
    have h3 := dsv_ex_row R (enc rows) K [] D.tail E.tail r V []
      ((false || D.headD false) || E.headD false) hr
    simp only [Bool.false_or, Bool.or_assoc, List.append_nil] at h1 h2 h3
    rw [enc_cons]
    by_cases hh : (D.headD false || (E.headD false || hsv_hit r V)) = true
    · rw [if_pos hh] at h3
      have hM := exec_move (a := 5) (b := 4) (by decide) ((V.take r.length).reverse)
        (dsv_st R (enc rows) (V.drop r.length) ((V.take r.length).reverse) K [] D.tail
          E.tail []) rfl
      simp only [dsv_u5, dsv_u4, dsv_st_4, List.reverse_reverse,
        List.take_append_drop] at hM
      have hb := h1.seq_norm (h2.seq_norm (h3.seq_norm (ExecLe.of hM)))
      refine (ExecLe.loop_norm hb ih).cast (by rw [dsv_go, Bool.or_assoc, hh, Bool.true_and]) ?_
      have : (V.take r.length).length ≤ r.length := by simp
      simp only [List.length_reverse, List.map_cons, List.sum_cons,
        List.length_cons]
      omega
    · rw [if_neg hh] at h3
      refine (ExecLe.loop_halt (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3)))).cast
        (by rw [dsv_go, Bool.or_assoc, Bool.eq_false_iff.mpr hh, Bool.false_and]) (by simp; omega)

/-! ## The whole verifier -/

def dsv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq dsv_bL (.seq dsv_aL
    (.seq (move 7 3) (.seq (move 5 4) (.seq (move 10 9) dsv_mL)))))))

/-- Time bound of the verifier. -/
def dsv_Tver (n : ℕ) : ℕ := 50 * n + 40

theorem dsv_exec_ver (z : Str) :
    ExecLe dsv_ver (init [z]).stk (.halt (dsv_vres (dec z).1 (dec z).2))
      (dsv_Tver z.length) := by
  have hl := dec_length z
  set w := (dec z).1
  set y := (dec z).2
  have h0 : (init [z]).stk 0 = z := rfl
  have he : ∀ j, j ≠ 0 → (init [z]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have hA := exec_phaseA z (init [z]).stk h0
  set σ₁ := update (update (init [z]).stk 0 y) 2 ((w.flatMap ic).reverse ++ (init [z]).stk 2)
  have hT := exec_trimC_word 2 w σ₁ (by simp [σ₁, he 2 (by decide)])
  set σ₂ := update σ₁ 2 (((trunc w).flatMap ic).reverse)
  have hM := exec_move (a := 2) (b := 3) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 2 []) 3 ((σ₂ 2).reverse ++ σ₂ 3) =
      dsv_st y (enc (clauses w)) [] [] [] [] [] [] [] := by
    funext j
    simp only [σ₂, σ₁, dsv_st, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ),
      ExecLe c (dsv_st y (enc (clauses w)) [] [] [] [] [] [] []) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold dsv_vres dsv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · rw [hcw] at hpre
    refine (hpre _ _ _ (ExecLe.seq_halt (dsv_ex_bdEnd y [] [] [] [] [] [] []))).cast rfl ?_
    simp only [htl, dsv_Tver]; omega
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    have hB := dsv_ex_bd y (enc rows) [] [] [] [] [] [] kr 0 (hsep kr (by simp))
    simp only [List.replicate_zero, Nat.add_zero] at hB
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r hr => hsep r (by simp [hr])
    have h1 := dsv_ex_pass1 rows y [] [] [] [] kr.length hrs
    simp only [List.append_nil] at h1
    set P := hsv_pad y rows.length
    have hPl : P.length = rows.length := hsv_pad_length _ _
    have hEl := dsv_enc_length rows
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    by_cases hc : P.count true ≤ kr.length
    · rw [if_pos hc] at h1
      set σ₃ := dsv_st (y.drop rows.length) [] [] P.reverse
        (List.replicate (kr.length - P.count true) true) (enc rows).reverse
        (dsv_dm rows y []) [] P.reverse
      have hM1 := exec_move (a := 7) (b := 3) (by decide) _ σ₃ rfl
      simp only [σ₃, dsv_u7, dsv_u3, dsv_st_3, dsv_st_7, List.reverse_reverse,
        List.append_nil] at hM1
      have hM2 := exec_move (a := 5) (b := 4) (by decide) _ _ (dsv_st_5 (R := y.drop rows.length)
        (Q := enc rows) (V := []) (W := P.reverse)
        (K := List.replicate (kr.length - P.count true) true) (C := []) (D := dsv_dm rows y [])
        (E := []) (F := P.reverse))
      simp only [dsv_u5, dsv_u4, dsv_st_4, List.reverse_reverse, List.append_nil] at hM2
      have hM3 := exec_move (a := 10) (b := 9) (by decide) _ _ (dsv_st_10
        (R := y.drop rows.length) (Q := enc rows) (V := P) (W := [])
        (K := List.replicate (kr.length - P.count true) true) (C := []) (D := dsv_dm rows y [])
        (E := []) (F := P.reverse))
      simp only [dsv_u10, dsv_u9, dsv_st_9, List.reverse_reverse, List.append_nil] at hM3
      have hR := dsv_ex_main (y.drop rows.length) P
        (List.replicate (kr.length - P.count true) true) rows (dsv_dm rows y []) P hrs
      have := hB.seq_norm (h1.seq_norm ((ExecLe.of hM1).seq_norm ((ExecLe.of hM2).seq_norm
        ((ExecLe.of hM3).seq_norm hR))))
      refine (hpre _ _ _ this).cast (by simp only [P] at hc ⊢; simp [hc]) ?_
      simp only [htl, dsv_Tver, List.length_reverse, hPl, hEl]
      omega
    · rw [if_neg hc] at h1
      have := hB.seq_norm (ExecLe.seq_halt
        (d := (move 7 3).seq ((move 5 4).seq ((move 10 9).seq dsv_mL))) h1)
      refine (hpre _ _ _ this).cast (by simp only [P] at hc ⊢; simp [hc]) ?_
      simp only [htl, dsv_Tver]
      omega

theorem dsv_Tver_le (n : ℕ) : dsv_Tver n ≤ tb 7 n := by
  unfold dsv_Tver tb
  have hm : 2 ^ 5 ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  norm_num at hm
  have e : (n + 2) ^ 7 = (n + 2) ^ 5 * (n + 2) ^ 2 := by ring
  have : 32 * (n + 2) ^ 2 ≤ (n + 2) ^ 5 * (n + 2) ^ 2 := Nat.mul_le_mul_right _ hm
  nlinarith

end Pnp.Karp.DomSet
