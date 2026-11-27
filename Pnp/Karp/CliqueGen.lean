import Pnp.Karp.CliqueRed

/-!
# The reduction program, part 1: layout, primitives, the column scan

A stack program printing `G w` (`Pnp/Karp/CliqueRed.lean`).  Main-phase stack layout (`st2`):

* `1`: the output (the reversed internal code `rv E` of the symbols `E` printed so far);
* `2`: the code `W` of `trunc w`;  `3`: the code of the rest of `trunc w` for the outer loop
  (rows);  `4`: the code of the rest of `trunc w` for an inner scan (columns);
* `j ≥ 5`: unary registers `v j`: `5`: `cp + 1` (clause index of the row vertex, plus one),
  `6`: `jp` (index of the row vertex inside its clause), `7`/`8`: countdown and flag
  "same clause", `9`/`10`: countdown and flag "same index", `11`: temporary.

All loops read one symbol (two bits) per iteration (`disp`).  This file: the primitives, the
generic "map" loop `mapLoop` (print `g s` for each symbol `s`), the flag update `adv`, the entry
test `entC`, and the column scan of a literal row (`scanL`, `ex_scanL`), which prints the
entries `entP sg cp jp b` (`= ent (adjB a b)`, `entP_eq`) for all annotated positions `b`.
-/

namespace Pnp.Karp.Clique

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

/-! ## Layout -/

/-- Reversed internal code of a list of symbols. -/
def rv (L : List SatSym) : Str := (L.flatMap ic).reverse

@[simp] theorem rv_nil : rv [] = [] := rfl

theorem rv_append (L₁ L₂ : List SatSym) : rv (L₁ ++ L₂) = rv L₂ ++ rv L₁ := by
  simp [rv]

/-- Stacks of the main phase. -/
def st2 (W O Q o : Str) (v : ℕ → ℕ) : ℕ → Str := fun j =>
  if j = 0 then [] else if j = 1 then o else if j = 2 then W else if j = 3 then O else
  if j = 4 then Q else List.replicate (v j) true

section St
variable {W O Q o : Str} {v : ℕ → ℕ}
@[simp] theorem st2_0 : st2 W O Q o v 0 = [] := rfl
@[simp] theorem st2_1 : st2 W O Q o v 1 = o := rfl
@[simp] theorem st2_2 : st2 W O Q o v 2 = W := rfl
@[simp] theorem st2_3 : st2 W O Q o v 3 = O := rfl
@[simp] theorem st2_4 : st2 W O Q o v 4 = Q := rfl

theorem st2_reg {r : ℕ} (h : 5 ≤ r) : st2 W O Q o v r = List.replicate (v r) true := by
  unfold st2; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

theorem upd2_reg {r : ℕ} (h : 5 ≤ r) (k : ℕ) :
    update (st2 W O Q o v) r (List.replicate k true) = st2 W O Q o (update v r k) := by
  funext j; unfold st2; simp only [update_apply]
  by_cases hj : j = r
  · subst hj; rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos rfl]
  · rw [if_neg hj, if_neg hj]

theorem upd2_1 (o' : Str) : update (st2 W O Q o v) 1 o' = st2 W O Q o' v := by
  funext j; unfold st2; simp only [update_apply]; split_ifs <;> simp_all

theorem upd2_3 (O' : Str) : update (st2 W O Q o v) 3 O' = st2 W O' Q o v := by
  funext j; unfold st2; simp only [update_apply]; split_ifs <;> simp_all

theorem upd2_4 (Q' : Str) : update (st2 W O Q o v) 4 Q' = st2 W O Q' o v := by
  funext j; unfold st2; simp only [update_apply]; split_ifs <;> simp_all

theorem st2_congr {v v' : ℕ → ℕ} (h : ∀ j, 5 ≤ j → v j = v' j) :
    st2 W O Q o v = st2 W O Q o v' := by
  funext j; unfold st2; split_ifs <;> try rfl
  rw [h j (by omega)]
end St

/-! ## Primitives -/

section Prim
variable {W O Q : Str}

/-- Print the symbols `L`. -/
def emL (L : List SatSym) : Cmd := pushList 1 (rv L)

theorem ex_emL (L E : List SatSym) (v : ℕ → ℕ) :
    ExecLe (emL L) (st2 W O Q (rv E) v) (.norm (st2 W O Q (rv (E ++ L)) v)) (2 * L.length + 1) := by
  refine (ExecLe.of (exec_pushList 1 _ _)).cast ?_
    (by simp only [rv, List.length_reverse, length_flatMap_ic]; omega)
  rw [st2_1, upd2_1, rv_append]

theorem ex_push_reg {r : ℕ} (hr : 5 ≤ r) (o : Str) (v : ℕ → ℕ) :
    ExecLe (.push r true) (st2 W O Q o v) (.norm (st2 W O Q o (update v r (v r + 1)))) 1 := by
  refine (ExecLe.push r true _).cast ?_ le_rfl
  rw [st2_reg hr, ← List.replicate_succ, upd2_reg hr]

theorem ex_drain_reg {r : ℕ} (hr : 5 ≤ r) (o : Str) (v : ℕ → ℕ) :
    ExecLe (drain r) (st2 W O Q o v) (.norm (st2 W O Q o (update v r 0))) (2 * v r + 2) := by
  refine (ExecLe.of (exec_drain r _ _ (st2_reg hr))).cast ?_ (by simp)
  rw [show ([] : Str) = List.replicate 0 true from rfl, upd2_reg hr]

theorem ex_copy_reg {a b : ℕ} (ha : 5 ≤ a) (hb : 5 ≤ b) (hab : a ≠ b) (ha11 : a ≠ 11)
    (hb11 : b ≠ 11) (o : Str) (v : ℕ → ℕ) (hv : v 11 = 0) :
    ExecLe (copyVia a b 11) (st2 W O Q o v) (.norm (st2 W O Q o (update v b (v b + v a))))
      (5 * v a + 4) := by
  refine (ExecLe.of (exec_copyVia hab ha11 hb11 _ (by rw [st2_reg (by norm_num), hv]; rfl))).cast
    ?_ (by rw [st2_reg ha]; simp)
  rw [st2_reg ha, st2_reg hb, ← List.replicate_add, Nat.add_comm, upd2_reg hb]

theorem ex_copyW (o : Str) (v : ℕ → ℕ) (hv : v 11 = 0) :
    ExecLe (copyVia 2 4 11) (st2 W O [] o v) (.norm (st2 W O W o v)) (5 * W.length + 4) := by
  refine (ExecLe.of (exec_copyVia (by decide) (by decide) (by decide) _
    (by rw [st2_reg (by norm_num), hv]; rfl))).cast ?_ (by simp)
  rw [st2_2, st2_4, List.append_nil, upd2_4]

end Prim

/-! ## Reading one symbol -/

/-- Read one symbol from stack `k` and run `f` on it (`brk` at the end of the stack). -/
def disp (k : ℕ) (f : SatSym → Cmd) : Cmd :=
  .pop k .brk (.pop k .brk (f sep) (f zero)) (.pop k .brk (f pos) (f neg))

theorem ex_disp {k : ℕ} {f : SatSym → Cmd} {σ : ℕ → Str} {s : SatSym} {Q' : Str} {r : Res}
    {T : ℕ} (hk : σ k = ic s ++ Q') (h : ExecLe (f s) (update σ k Q') r T) :
    ExecLe (disp k f) σ r (T + 2) := by
  have e : ∀ s' : Str, update (update σ k s') k Q' = update σ k Q' := fun _ => update_idem _ _ _
  cases s with
  | sep =>
    refine ExecLe.pop_cons (b := false) (s := false :: Q') hk ?_
    exact ExecLe.pop_cons (b := false) (s := Q') (by simp) (by rw [e]; exact h)
  | zero =>
    refine ExecLe.pop_cons (b := false) (s := true :: Q') hk ?_
    exact ExecLe.pop_cons (b := true) (s := Q') (by simp) (by rw [e]; exact h)
  | pos =>
    refine ExecLe.pop_cons (b := true) (s := false :: Q') hk ?_
    exact ExecLe.pop_cons (b := false) (s := Q') (by simp) (by rw [e]; exact h)
  | neg =>
    refine ExecLe.pop_cons (b := true) (s := true :: Q') hk ?_
    exact ExecLe.pop_cons (b := true) (s := Q') (by simp) (by rw [e]; exact h)

theorem ex_disp_nil {k : ℕ} {f : SatSym → Cmd} {σ : ℕ → Str} (hk : σ k = []) :
    ExecLe (.loop (disp k f)) σ (.norm σ) 2 :=
  ExecLe.loop_brk (ExecLe.pop_nil hk (ExecLe.brk _))

/-! ## Map loops -/

/-- Print `g s` for every symbol `s` of stack `4`. -/
def mapLoop (g : SatSym → List SatSym) : Cmd := .loop (disp 4 fun s => emL (g s))

theorem ex_mapLoop (W O : Str) (v : ℕ → ℕ) (g : SatSym → List SatSym) (hg : ∀ s, (g s).length ≤ 1) :
    ∀ (l E : List SatSym), ExecLe (mapLoop g) (st2 W O (l.flatMap ic) (rv E) v)
      (.norm (st2 W O [] (rv (E ++ l.flatMap g)) v)) (5 * l.length + 2)
  | [], E => (ex_disp_nil rfl).cast (by simp) le_rfl
  | s :: l, E => by
    have ih := ex_mapLoop W O v g hg l (E ++ g s)
    have hb := ex_disp (k := 4) (f := fun s => emL (g s)) (s := s) (Q' := l.flatMap ic)
      (σ := st2 W O ((s :: l).flatMap ic) (rv E) v) (by simp)
      (by rw [upd2_4]; exact ex_emL (g s) E v)
    refine (ExecLe.loop_norm hb ih).cast (by simp) ?_
    have := hg s; simp; omega

/-! ## Flags -/

/-- Countdown step: with `n` marks on `C`, leave `n - 1` and set flag `F` iff `n = 1`. -/
def adv (C F : ℕ) : Cmd :=
  .seq (drain F) (.pop C .skip (.pop C (.push F true) (.push C true) (.push C true))
    (.pop C (.push F true) (.push C true) (.push C true)))

theorem ex_adv {C F : ℕ} (hC : 5 ≤ C) (hF : 5 ≤ F) (hCF : C ≠ F) (W O Q o : Str) (v : ℕ → ℕ)
    (hv : v F ≤ 1) :
    ExecLe (adv C F) (st2 W O Q o v)
      (.norm (st2 W O Q o (update (update v F (if v C = 1 then 1 else 0)) C (v C - 1)))) 10 := by
  have h1 := ex_drain_reg (W := W) (O := O) (Q := Q) hF o v
  set v1 := update v F 0
  refine (h1.seq_norm (T₂ := 6) ?_).cast rfl (by omega)
  rcases hn : v C with _ | _ | n
  · refine (ExecLe.pop_nil (by rw [st2_reg hC]; simp [v1, hCF, hn]) (ExecLe.skip _)).cast ?_
      (by omega)
    congr 1; apply st2_congr; intro j _; simp only [v1, update_apply]; split_ifs <;> simp_all
  · have e1 : st2 W O Q o v1 C = true :: [] := by rw [st2_reg hC]; simp [v1, hCF, hn]
    refine ExecLe.pop_cons e1 ?_
    simp only [if_true]
    refine (ExecLe.pop_nil (by simp) ?_).cast rfl (show 1 + 1 ≤ 5 by omega)
    rw [show ([] : Str) = List.replicate 0 true from rfl, upd2_reg hC]
    refine (ex_push_reg hF o _).cast ?_ le_rfl
    congr 1; apply st2_congr; intro j _; simp only [v1, update_apply]; split_ifs <;> simp_all
  · have e1 : st2 W O Q o v1 C = true :: List.replicate (n + 1) true := by
      rw [st2_reg hC]; simp [v1, hCF, hn, List.replicate_succ]
    refine ExecLe.pop_cons e1 ?_
    simp only [if_true]
    refine (ExecLe.pop_cons (b := true) (s := List.replicate n true) (by simp [List.replicate_succ])
      ?_).cast rfl (show 1 + 1 ≤ 5 by omega)
    simp only [if_true]
    rw [update_idem, upd2_reg hC]
    refine (ex_push_reg hC o _).cast ?_ le_rfl
    congr 1; apply st2_congr; intro j _; simp only [v1, update_apply]; split_ifs <;> simp_all

/-- The entry of a literal column: `zero` in the same clause; at the same index, `pos` iff the
signs agree (`same`); otherwise `pos`.  Flags: `8` (same clause), `10` (same index). -/
def entC (same : Bool) : Cmd :=
  .pop 8 (.pop 10 (emL [pos]) (.seq (.push 10 true) (emL [if same then pos else zero]))
      (.seq (.push 10 true) (emL [if same then pos else zero])))
    (.seq (.push 8 true) (emL [zero])) (.seq (.push 8 true) (emL [zero]))

theorem ex_entC (same : Bool) (W O Q : Str) (E : List SatSym) (v : ℕ → ℕ) (h8 : v 8 ≤ 1)
    (h10 : v 10 ≤ 1) :
    ExecLe (entC same) (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ [if v 8 = 1 then zero else if v 10 = 1 then
        (if same then pos else zero) else pos])) v)) 6 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h8 with h8 | h8
  · have e8 : st2 W O Q (rv E) v 8 = [] := by rw [st2_reg (by norm_num), h8]; rfl
    refine ExecLe.pop_nil e8 ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h10 with h10 | h10
    · refine ExecLe.pop_nil (by rw [st2_reg (by norm_num), h10]; rfl) ?_
      exact (ex_emL _ E v).cast (by simp [h8, h10]) (by simp)
    · refine ExecLe.pop_cons (b := true) (s := [])
        (by rw [st2_reg (by norm_num), h10]; rfl) ?_
      simp only [if_true]
      rw [show ([] : Str) = List.replicate 0 true from rfl, upd2_reg (by norm_num)]
      have hs : (if v 8 = 1 then zero else if v 10 = 1 then (if same then pos else zero) else pos)
          = (if same then pos else zero) := by simp [h8, h10]
      have hst : ∀ E', st2 W O Q E' (update (update v 10 0) 10 (update v 10 0 10 + 1)) =
          st2 W O Q E' v := fun E' => by
        apply st2_congr; intro j _; simp only [update_apply]; split_ifs <;> simp_all
      refine ((ex_push_reg (by norm_num) _ _).seq_norm (ex_emL _ E _)).cast
        (by rw [hs, hst]) (by simp)
  · refine ExecLe.pop_cons (b := true) (s := []) (by rw [st2_reg (by norm_num), h8]; rfl) ?_
    rw [ite_self, show ([] : Str) = List.replicate 0 true from rfl, upd2_reg (by norm_num)]
    have hs : (if v 8 = 1 then zero else if v 10 = 1 then (if same then pos else zero) else pos)
        = zero := by simp [h8]
    have hst : ∀ E', st2 W O Q E' (update (update v 8 0) 8 (update v 8 0 8 + 1)) =
        st2 W O Q E' v := fun E' => by
      apply st2_congr; intro j _; simp only [update_apply]; split_ifs <;> simp_all
    refine ((ex_push_reg (by norm_num) _ _).seq_norm (ex_emL _ E _)).cast
      (by rw [hs, hst]) (by simp)

/-! ## The column scan of a literal row -/

/-- The entry printed by the scan of the row of a literal `(sign sg, cp, jp)` (`sg = true`:
`neg`) for the column `b`. -/
def entP (sg : Bool) (cp jp : ℕ) (b : SatSym × ℕ × ℕ) : SatSym :=
  match b.1 with
  | pos => if cp = b.2.1 then zero else if jp = b.2.2 then (if sg then zero else pos) else pos
  | neg => if cp = b.2.1 then zero else if jp = b.2.2 then (if sg then pos else zero) else pos
  | _ => zero

/-- The sign symbol. -/
def sgSym (sg : Bool) : SatSym := if sg then neg else pos

theorem entP_eq (sg : Bool) (cp jp : ℕ) (b : SatSym × ℕ × ℕ) :
    entP sg cp jp b = ent (adjB (sgSym sg, cp, jp) b) := by
  obtain ⟨s, t, j⟩ := b
  cases sg <;> cases s <;> simp only [entP, sgSym, adjB, isLit] <;>
    by_cases h1 : cp = t <;> by_cases h2 : jp = j <;> simp [h1, h2, ent]

/-- Next clause index / next index inside the clause. -/
def nxT : SatSym → ℕ → ℕ
  | sep, t => t + 1
  | _, t => t

def nxJ : SatSym → ℕ → ℕ
  | sep, _ => 0
  | _, j => j + 1

theorem ann_cons (s : SatSym) (l : List SatSym) (t j : ℕ) :
    ann (s :: l) t j = (s, t, j) :: ann l (nxT s t) (nxJ s j) := by
  cases s <;> rfl

/-- The scan registers at column `(t, jq)`. -/
def setInv (v : ℕ → ℕ) (cp jp t jq : ℕ) : ℕ → ℕ := fun j =>
  if j = 7 then cp - t else if j = 8 then (if cp = t then 1 else 0) else
  if j = 9 then jp - jq else if j = 10 then (if jp = jq then 1 else 0) else v j

/-- Register invariant of the scan. -/
def Inv (v : ℕ → ℕ) (cp jp : ℕ) : Prop := v 5 = cp + 1 ∧ v 6 = jp ∧ v 11 = 0

theorem setInv_setInv (v : ℕ → ℕ) (cp jp t jq t' jq' : ℕ) :
    setInv (setInv v cp jp t jq) cp jp t' jq' = setInv v cp jp t' jq' := by
  funext j; simp only [setInv]; split_ifs <;> rfl

theorem setInv_apply {v : ℕ → ℕ} {cp jp t jq j : ℕ} (h : j < 7 ∨ 10 < j) :
    setInv v cp jp t jq j = v j := by
  simp only [setInv]; split_ifs <;> omega

theorem regs_eq {f g : ℕ → ℕ} (h7 : f 7 = g 7) (h8 : f 8 = g 8) (h9 : f 9 = g 9)
    (h10 : f 10 = g 10) (ho : ∀ j, (j < 7 ∨ 10 < j) → f j = g j) : ∀ j, 5 ≤ j → f j = g j := by
  intro j _
  rcases (show j < 7 ∨ 10 < j ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 by omega) with h | h | h | h | h | h
  · exact ho j (Or.inl h)
  · exact ho j (Or.inr h)
  all_goals (subst h; assumption)

/-- Per-symbol action of the scan. -/
def lBr (sg : Bool) : SatSym → Cmd
  | sep => .seq (emL [zero]) (.seq (adv 7 8) (.seq (drain 9) (.seq (copyVia 6 9 11)
      (.seq (.push 9 true) (adv 9 10)))))
  | zero => .seq (emL [zero]) (adv 9 10)
  | pos => .seq (entC !sg) (adv 9 10)
  | neg => .seq (entC sg) (adv 9 10)

theorem ex_lBr (sg : Bool) (W O Q : Str) (E : List SatSym) (cp jp t jq : ℕ) (s : SatSym)
    (v : ℕ → ℕ) (hv : Inv v cp jp) :
    ExecLe (lBr sg s) (st2 W O Q (rv E) (setInv v cp jp t jq))
      (.norm (st2 W O Q (rv (E ++ [entP sg cp jp (s, t, jq)]))
        (setInv v cp jp (nxT s t) (nxJ s jq)))) (7 * jp + 38) := by
  obtain ⟨h5, h6, h11⟩ := hv
  set u := setInv v cp jp t jq
  have f8 : u 8 ≤ 1 := by simp only [u, setInv]; split_ifs <;> omega
  have f10 : u 10 ≤ 1 := by simp only [u, setInv]; split_ifs <;> omega
  have e8 : u 8 = if cp = t then 1 else 0 := by simp [u, setInv]
  have e10 : u 10 = if jp = jq then 1 else 0 := by simp [u, setInv]
  -- the index step
  have hJ : ∀ (E' : List SatSym),
      ExecLe (adv 9 10) (st2 W O Q (rv E') u) (.norm (st2 W O Q (rv E')
        (setInv v cp jp t (jq + 1)))) 10 := by
    intro E'
    refine (ex_adv (by norm_num) (by norm_num) (by norm_num) W O Q _ u f10).cast ?_ le_rfl
    congr 1; apply st2_congr; intro j _; simp only [u, setInv, update_apply]
    split_ifs <;> omega
  cases s with
  | zero =>
    exact ((ex_emL [zero] E u).seq_norm (hJ _)).cast (by simp [entP, nxT, nxJ]) (by simp)
  | pos =>
    have hE := ex_entC (!sg) W O Q E u f8 f10
    refine (hE.seq_norm (hJ _)).cast ?_ (by omega)
    simp only [entP, e8, e10, nxT, nxJ]
    by_cases a1 : cp = t <;> by_cases a2 : jp = jq <;> cases sg <;> simp [a1, a2]
  | neg =>
    have hE := ex_entC sg W O Q E u f8 f10
    refine (hE.seq_norm (hJ _)).cast ?_ (by omega)
    simp only [entP, e8, e10, nxT, nxJ]
    by_cases a1 : cp = t <;> by_cases a2 : jp = jq <;> cases sg <;> simp [a1, a2]
  | sep =>
    have q1 := ex_emL (W := W) (O := O) (Q := Q) [zero] E u
    have q2 := ex_adv (C := 7) (F := 8) (by norm_num) (by norm_num) (by norm_num) W O Q
      (rv (E ++ [zero])) u f8
    set u1 := update (update u 8 (if u 7 = 1 then 1 else 0)) 7 (u 7 - 1)
    have q3 := ex_drain_reg (W := W) (O := O) (Q := Q) (r := 9) (by norm_num) (rv (E ++ [zero])) u1
    set u2 := update u1 9 0
    have q4 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 6) (b := 9) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (rv (E ++ [zero])) u2
      (by simp [u2, u1, u, setInv, h11])
    set u3 := update u2 9 (u2 9 + u2 6)
    have q5 := ex_push_reg (W := W) (O := O) (Q := Q) (r := 9) (by norm_num) (rv (E ++ [zero])) u3
    set u4 := update u3 9 (u3 9 + 1)
    have q6 := ex_adv (C := 9) (F := 10) (by norm_num) (by norm_num) (by norm_num) W O Q
      (rv (E ++ [zero])) u4 (by simp [u4, u3, u2, u1, f10])
    have e6 : u2 6 = jp := by simp [u2, u1, u, setInv, h6]
    have e9 : u1 9 = jp - jq := by simp [u1, u, setInv]
    have hfin : st2 W O Q (rv (E ++ [zero]))
        (update (update u4 10 (if u4 9 = 1 then 1 else 0)) 9 (u4 9 - 1)) =
        st2 W O Q (rv (E ++ [zero])) (setInv v cp jp (t + 1) 0) := by
      apply st2_congr
      refine regs_eq ?_ ?_ ?_ ?_ ?_
      · simp [u4, u3, u2, u1, u, setInv]; omega
      · simp [u4, u3, u2, u1, u, setInv]; split_ifs <;> omega
      · simp [u4, u3, u2, u1, u, setInv, h6]
      · simp [u4, u3, u2, u1, u, setInv, h6]
      · intro j hj
        have hne : j ≠ 7 ∧ j ≠ 8 ∧ j ≠ 9 ∧ j ≠ 10 := by omega
        simp [u4, u3, u2, u1, u, setInv, hne]
    refine (q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm (q5.seq_norm q6))))).cast
      (by rw [hfin]; simp [entP, nxT, nxJ]) ?_
    rw [e6, e9]; simp; omega

/-- The scan loop of a literal row. -/
def scanLoop (sg : Bool) : Cmd := .loop (disp 4 (lBr sg))

theorem ex_scanLoop (sg : Bool) (W O : Str) (cp jp : ℕ) (v : ℕ → ℕ) (hv : Inv v cp jp) :
    ∀ (l : List SatSym) (t jq : ℕ) (E : List SatSym), ∃ t' jq',
      ExecLe (scanLoop sg) (st2 W O (l.flatMap ic) (rv E) (setInv v cp jp t jq))
        (.norm (st2 W O [] (rv (E ++ (ann l t jq).map (entP sg cp jp))) (setInv v cp jp t' jq')))
        (l.length * (7 * jp + 40) + 2)
  | [], t, jq, E => ⟨t, jq, (ex_disp_nil rfl).cast (by simp [ann]) (by simp)⟩
  | s :: l, t, jq, E => by
    have h1 := ex_lBr sg W O (l.flatMap ic) E cp jp t jq s v hv
    obtain ⟨t', jq', h2⟩ :=
      ex_scanLoop sg W O cp jp v hv l (nxT s t) (nxJ s jq) (E ++ [entP sg cp jp (s, t, jq)])
    refine ⟨t', jq', ?_⟩
    have hb := ex_disp (k := 4) (f := lBr sg) (s := s) (Q' := l.flatMap ic)
      (σ := st2 W O ((s :: l).flatMap ic) (rv E) (setInv v cp jp t jq)) (by simp)
      (by rw [upd2_4]; exact h1)
    refine (ExecLe.loop_norm hb h2).cast (by simp [ann_cons]) ?_
    simp only [List.length_cons]; nlinarith

/-- The whole row scan of a literal row (registers `7 … 11` empty before and after). -/
def scanL (sg : Bool) : Cmd :=
  .seq (copyVia 2 4 11) (.seq (copyVia 5 7 11) (.seq (adv 7 8) (.seq (copyVia 6 9 11)
    (.seq (.push 9 true) (.seq (adv 9 10) (.seq (scanLoop sg) (.seq (drain 7) (.seq (drain 8)
    (.seq (drain 9) (drain 10))))))))))

/-- Registers at the start of a row. -/
def RowInv (v : ℕ → ℕ) (cp jp : ℕ) : Prop :=
  v 5 = cp + 1 ∧ v 6 = jp ∧ v 7 = 0 ∧ v 8 = 0 ∧ v 9 = 0 ∧ v 10 = 0 ∧ v 11 = 0

theorem ex_scanL (sg : Bool) (W O : Str) (E : List SatSym) (cp jp : ℕ) (v : ℕ → ℕ)
    (hv : RowInv v cp jp) (l : List SatSym) (hW : W = l.flatMap ic) :
    ExecLe (scanL sg) (st2 W O [] (rv E) v)
      (.norm (st2 W O [] (rv (E ++ (ann l 0 0).map (entP sg cp jp))) v))
      (5 * W.length + l.length * (7 * jp + 40) + 7 * cp + 9 * jp + 80) := by
  obtain ⟨h5, h6, h7, h8, h9, h10, h11⟩ := hv
  have q1 := ex_copyW (W := W) (O := O) (rv E) v h11
  have q2 := ex_copy_reg (W := W) (O := O) (Q := W) (a := 5) (b := 7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (rv E) v h11
  set u1 := update v 7 (v 7 + v 5)
  have q3 := ex_adv (C := 7) (F := 8) (by norm_num) (by norm_num) (by norm_num) W O W (rv E) u1
    (by simp [u1, h8])
  set u2 := update (update u1 8 (if u1 7 = 1 then 1 else 0)) 7 (u1 7 - 1)
  have q4 := ex_copy_reg (W := W) (O := O) (Q := W) (a := 6) (b := 9) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (rv E) u2 (by simp [u2, u1, h11])
  set u3 := update u2 9 (u2 9 + u2 6)
  have q5 := ex_push_reg (W := W) (O := O) (Q := W) (r := 9) (by norm_num) (rv E) u3
  set u4 := update u3 9 (u3 9 + 1)
  have q6 := ex_adv (C := 9) (F := 10) (by norm_num) (by norm_num) (by norm_num) W O W (rv E) u4
    (by simp [u4, u3, u2, u1, h10])
  have hinv : Inv v cp jp := ⟨h5, h6, h11⟩
  have e6 : st2 W O W (rv E) (update (update u4 10 (if u4 9 = 1 then 1 else 0)) 9 (u4 9 - 1)) =
      st2 W O W (rv E) (setInv v cp jp 0 0) := by
    apply st2_congr
    refine regs_eq ?_ ?_ ?_ ?_ ?_
    · simp [u4, u3, u2, u1, setInv, h5, h7]
    · simp [u4, u3, u2, u1, setInv, h5, h7]
    · simp [u4, u3, u2, u1, setInv, h6, h9]
    · simp [u4, u3, u2, u1, setInv, h6, h9]
    · intro j hj
      have hne : j ≠ 7 ∧ j ≠ 8 ∧ j ≠ 9 ∧ j ≠ 10 := by omega
      simp [u4, u3, u2, u1, setInv, hne]
  rw [e6] at q6
  obtain ⟨t', jq', q7⟩ := ex_scanLoop sg W O cp jp v hinv l 0 0 E
  rw [← hW] at q7
  set E' := E ++ (ann l 0 0).map (entP sg cp jp)
  set v' := setInv v cp jp t' jq'
  have d7 := ex_drain_reg (W := W) (O := O) (Q := []) (r := 7) (by norm_num) (rv E') v'
  have d8 := ex_drain_reg (W := W) (O := O) (Q := []) (r := 8) (by norm_num) (rv E') (update v' 7 0)
  have d9 := ex_drain_reg (W := W) (O := O) (Q := []) (r := 9) (by norm_num) (rv E')
    (update (update v' 7 0) 8 0)
  have d10 := ex_drain_reg (W := W) (O := O) (Q := []) (r := 10) (by norm_num) (rv E')
    (update (update (update v' 7 0) 8 0) 9 0)
  have hfin : st2 W O [] (rv E') (update (update (update (update v' 7 0) 8 0) 9 0) 10 0) =
      st2 W O [] (rv E') v := by
    apply st2_congr
    refine regs_eq (by simp [h7]) (by simp [h8]) (by simp [h9]) (by simp [h10]) ?_
    intro j hj
    have hne : j ≠ 7 ∧ j ≠ 8 ∧ j ≠ 9 ∧ j ≠ 10 := by omega
    simp [v', setInv, hne]
  refine (q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm (q5.seq_norm (q6.seq_norm
    (q7.seq_norm (d7.seq_norm (d8.seq_norm (d9.seq_norm d10)))))))))).cast (by rw [hfin]) ?_
  have c5 : st2 W O [] (rv E) v 5 = List.replicate (cp + 1) true := by rw [st2_reg (by norm_num), h5]
  have c6 : u2 6 = jp := by simp [u2, u1, h6]
  have c7 : v' 7 ≤ cp := by simp [v', setInv]
  have c8 : update v' 7 0 8 ≤ 1 := by simp [v', setInv]; split_ifs <;> omega
  have c9 : update (update v' 7 0) 8 0 9 ≤ jp := by simp [v', setInv]
  have c10 : update (update (update v' 7 0) 8 0) 9 0 10 ≤ 1 := by
    simp [v', setInv]; split_ifs <;> omega
  simp only [h5, c6]
  nlinarith

end Pnp.Karp.Clique
