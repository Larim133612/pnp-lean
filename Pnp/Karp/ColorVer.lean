import Pnp.Karp.Color
import Pnp.Karp.CliqueVer

/-!
# 3-COLORING ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/Color.lean`) and a certificate `y : List Bool`: the color of vertex `v` is
`toCol (y.getD (2v) false) (y.getD (2v + 1) false)` (missing bits are `false`).  Stack layout:

* `0`: the unread certificate bits `R` (two bits per row: the color of the current row);
* `1`: a full copy of the certificate `y`;  `3`: the internal code of the remaining rows `Q`;
* `4`, `5`, `6`: the color flags of the current row (stack `4 + m` is `[true]` iff the row has
  color `m`);  `7`: the column bits `Y` of the current row;  `8`: a temporary.

Program (`verC`):
1. `phaseA`: parse the code of `w`; `trimC 2`: drop the unfinished tail; `move 2 3`;
   `copyVia 0 1 8`: copy the certificate;
2. `srRow` ("start row"): the column bits become a copy of `y`; pop two bits of `R`, set the
   flag of the row color;
3. `mainLoop`: one symbol per iteration; every symbol pops two column bits (the column color),
   and at `pos` the column color must differ from the row color; at `sep` the column bits and
   the flags are cleared (`endRow`) and the next row is started; at the end of the input, accept.

`exec_verC`: the program halts with `vresC (dec z).1 (dec z).2` on every input `z`, within
`TverC |z|` steps.
-/

namespace Pnp.Karp.Color

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics -/

/-- The color of two bits. -/
def toCol (b0 b1 : Bool) : Fin 3 := if b0 then 2 else if b1 then 1 else 0

/-- The color given by the first two bits. -/
def hdC (Y : Str) : Fin 3 := toCol (Y.getD 0 false) (Y.getD 1 false)

/-- Check a row of color `k` against the column bits `Y`. -/
def rowOk (k : Fin 3) : List SatSym → Str → Bool
  | [], _ => true
  | s :: r, Y => !(isPos s && decide (k = hdC Y)) && rowOk k r (Y.drop 2)

/-- What the main loop computes (`R`: the unread row color bits). -/
def goC (y : Str) : List (List SatSym) → Str → Bool
  | [], _ => true
  | r :: rows, R => rowOk (hdC R) r y && goC y rows (R.drop 2)

/-- The answer of the verifier on `(w, y)`. -/
def vresC (w : List SatSym) (y : Str) : Bool := goC y (clauses w) y

/-! ## Stack layout -/

/-- The flag stack of color `m`. -/
def fk (f : Option (Fin 3)) (m : Fin 3) : Str := if f = some m then [true] else []

theorem fk_tail (f : Option (Fin 3)) (m : Fin 3) : (fk f m).tail = [] := by
  unfold fk; split <;> rfl

/-- The stacks of the main phase. -/
def stC (y R Q Y : Str) (f : Option (Fin 3)) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 1 then y else if j = 3 then Q else if j = 4 then fk f 0 else
  if j = 5 then fk f 1 else if j = 6 then fk f 2 else if j = 7 then Y else []

/-- Equality of stack assignments. -/
local macro "stCx" : tactic =>
  `(tactic| (funext j; simp only [stC, update_apply]; split_ifs <;> simp_all))

section St
variable {y R Q Y : Str} {f : Option (Fin 3)}
@[simp] theorem stC_0 : stC y R Q Y f 0 = R := rfl
@[simp] theorem stC_1 : stC y R Q Y f 1 = y := rfl
@[simp] theorem stC_3 : stC y R Q Y f 3 = Q := rfl
@[simp] theorem stC_4 : stC y R Q Y f 4 = fk f 0 := rfl
@[simp] theorem stC_5 : stC y R Q Y f 5 = fk f 1 := rfl
@[simp] theorem stC_6 : stC y R Q Y f 6 = fk f 2 := rfl
@[simp] theorem stC_7 : stC y R Q Y f 7 = Y := rfl
@[simp] theorem stC_8 : stC y R Q Y f 8 = [] := rfl
theorem v0 (R' : Str) : update (stC y R Q Y f) 0 R' = stC y R' Q Y f := by stCx
theorem v1 (y' : Str) : update (stC y R Q Y f) 1 y' = stC y' R Q Y f := by stCx
theorem v3 (Q' : Str) : update (stC y R Q Y f) 3 Q' = stC y R Q' Y f := by stCx
theorem v7 (Y' : Str) : update (stC y R Q Y f) 7 Y' = stC y R Q Y' f := by stCx
end St

theorem stC_flag (y R Q Y : Str) (f : Option (Fin 3)) (m : Fin 3) :
    stC y R Q Y f (4 + m.val) = fk f m := by
  fin_cases m <;> rfl

/-! ## Commands -/

/-- A pop with three identical branches. -/
theorem ExecLe.pop3 {k : ℕ} {c : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ}
    (h : ExecLe c (update σ k (σ k).tail) r T) : ExecLe (.pop k c c c) σ r (T + 1) := by
  cases hk : σ k with
  | nil =>
    rw [hk, List.tail_nil, ← hk, update_eq_self] at h
    exact ExecLe.pop_nil hk h
  | cons b s =>
    rw [hk, List.tail_cons] at h
    exact ExecLe.pop_same hk h

/-- Pop the row color bits of `R` and set its flag. -/
def srBits : Cmd :=
  .pop 0 (.push 4 true) (.pop 0 (.push 4 true) (.push 4 true) (.push 5 true))
    (.pop 0 (.push 6 true) (.push 6 true) (.push 6 true))

theorem ex_push4 (y R Q Y : Str) :
    ExecLe (.push 4 true) (stC y R Q Y none) (.norm (stC y R Q Y (some 0))) 1 :=
  (ExecLe.push _ _ _).cast (by
    congr 1; funext j; simp only [stC, fk, update_apply]; split_ifs <;> simp_all) le_rfl

theorem ex_pushV5 (y R Q Y : Str) :
    ExecLe (.push 5 true) (stC y R Q Y none) (.norm (stC y R Q Y (some 1))) 1 :=
  (ExecLe.push _ _ _).cast (by
    congr 1; funext j; simp only [stC, fk, update_apply]; split_ifs <;> simp_all) le_rfl

theorem ex_pushV6 (y R Q Y : Str) :
    ExecLe (.push 6 true) (stC y R Q Y none) (.norm (stC y R Q Y (some 2))) 1 :=
  (ExecLe.push _ _ _).cast (by
    congr 1; funext j; simp only [stC, fk, update_apply]; split_ifs <;> simp_all) le_rfl

theorem ex_srBits (y R Q Y : Str) :
    ExecLe srBits (stC y R Q Y none) (.norm (stC y (R.drop 2) Q Y (some (hdC R)))) 3 := by
  rcases R with _ | ⟨_ | _, R'⟩
  · exact (ExecLe.pop_nil rfl (ex_push4 y [] Q Y)).cast (by simp [hdC, toCol]) (by omega)
  · rcases R' with _ | ⟨_ | _, R''⟩
    · exact (ExecLe.pop_cons (b := false) rfl (by
        rw [v0]; exact ExecLe.pop_nil rfl (ex_push4 y [] Q Y))).cast
        (by simp [hdC, toCol]) (by omega)
    · exact (ExecLe.pop_cons (b := false) rfl (by
        rw [v0]; exact ExecLe.pop_cons (b := false) (s := R'') rfl
          (by rw [v0]; exact ex_push4 y R'' Q Y))).cast
        (by simp [hdC, toCol]) (by omega)
    · exact (ExecLe.pop_cons (b := false) rfl (by
        rw [v0]; exact ExecLe.pop_cons (b := true) (s := R'') rfl
          (by rw [v0]; exact ex_pushV5 y R'' Q Y))).cast
        (by simp [hdC, toCol]) (by omega)
  · refine (ExecLe.pop_cons (b := true) rfl (by
      rw [v0]; exact ExecLe.pop3 (by rw [stC_0, v0]; exact ex_pushV6 y R'.tail Q Y))).cast ?_
      (by omega)
    rcases R' with _ | ⟨_, _⟩ <;> simp [hdC, toCol]

/-- Start a row: column bits `y`, the row color from `R`. -/
def srRow : Cmd := .seq (copyVia 1 7 8) srBits

theorem ex_srRow (y R Q : Str) :
    ExecLe srRow (stC y R Q [] none) (.norm (stC y (R.drop 2) Q y (some (hdC R))))
      (5 * y.length + 7) := by
  have h1 := exec_copyVia (a := 1) (b := 7) (t := 8) (by decide) (by decide) (by decide)
    (stC y R Q [] none) rfl
  rw [stC_1, stC_7, List.append_nil, v7] at h1
  exact ((ExecLe.of h1).seq_norm (ex_srBits y R Q y)).cast rfl (by simp)

/-- Halt `false` if the row has color `m` (when `ok`). -/
def chk (ok : Bool) (m : ℕ) : Cmd :=
  if ok then .pop (4 + m) .skip (.halt false) (.halt false) else .skip

theorem ex_chk (ok : Bool) (m : Fin 3) (y R Q Y : Str) (k : Fin 3) :
    ExecLe (chk ok m.val) (stC y R Q Y (some k))
      (if ok && decide (k = m) then .halt false else .norm (stC y R Q Y (some k))) 2 := by
  cases ok
  · exact (ExecLe.skip _).cast (by simp) (by omega)
  · by_cases hkm : k = m
    · subst hkm
      have h4 : stC y R Q Y (some k) (4 + k.val) = true :: [] := by rw [stC_flag]; simp [fk]
      exact (ExecLe.pop_cons h4 (ExecLe.halt false _)).cast (by simp) (by omega)
    · have h4 : stC y R Q Y (some k) (4 + m.val) = [] := by
        rw [stC_flag]; simp [fk, hkm]
      exact (ExecLe.pop_nil h4 (ExecLe.skip _)).cast (by simp [hkm]) (by omega)

/-- One column of a row (`ok`: the symbol is `pos`). -/
def colStep (ok : Bool) : Cmd :=
  .pop 7 (chk ok 0) (.pop 7 (chk ok 0) (chk ok 0) (chk ok 1))
    (.pop 7 (chk ok 2) (chk ok 2) (chk ok 2))

theorem ex_colStep (ok : Bool) (y R Q Y : Str) (k : Fin 3) :
    ExecLe (colStep ok) (stC y R Q Y (some k))
      (if ok && decide (k = hdC Y) then .halt false else .norm (stC y R Q (Y.drop 2) (some k)))
      4 := by
  rcases Y with _ | ⟨_ | _, Y'⟩
  · exact (ExecLe.pop_nil rfl (ex_chk ok 0 y R Q [] k)).cast (by simp [hdC, toCol]) (by omega)
  · rcases Y' with _ | ⟨_ | _, Y''⟩
    · exact (ExecLe.pop_cons (b := false) rfl (ExecLe.pop_nil (by simp)
        (by rw [v7]; exact ex_chk ok 0 y R Q [] k))).cast (by simp [hdC, toCol]) (by omega)
    · exact (ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Y'')
        (by simp) (by rw [v7, v7]; exact ex_chk ok 0 y R Q Y'' k))).cast
        (by simp [hdC, toCol]) (by omega)
    · exact (ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Y'')
        (by simp) (by rw [v7, v7]; exact ex_chk ok 1 y R Q Y'' k))).cast
        (by simp [hdC, toCol]) (by omega)
  · refine (ExecLe.pop_cons (b := true) rfl (ExecLe.pop3 (by
      rw [v7, stC_7, v7]; exact ex_chk ok 2 y R Q Y'.tail k))).cast ?_ (by omega)
    rcases Y' with _ | ⟨_, _⟩ <;> simp [hdC, toCol]

/-- Clear a flag stack. -/
def popF (j : ℕ) : Cmd := .pop j .skip .skip .skip

theorem ex_popF (j : ℕ) (σ : ℕ → Str) :
    ExecLe (popF j) σ (.norm (update σ j (σ j).tail)) 2 := ExecLe.pop3 (ExecLe.skip _)

/-- End of a row: clear the column bits and the flags. -/
def endRow : Cmd := .seq (drain 7) (.seq (popF 4) (.seq (popF 5) (popF 6)))

theorem ex_endRow (y R Q Y : Str) (k : Fin 3) :
    ExecLe endRow (stC y R Q Y (some k)) (.norm (stC y R Q [] none)) (2 * Y.length + 8) := by
  have h1 := exec_drain 7 Y (stC y R Q Y (some k)) rfl
  rw [v7] at h1
  refine ((ExecLe.of h1).seq_norm ((ex_popF 4 _).seq_norm ((ex_popF 5 _).seq_norm
    (ex_popF 6 _)))).cast ?_ (by omega)
  congr 1; funext j
  simp only [stC, update_apply]
  split_ifs <;> (try simp only [fk_tail]) <;> simp_all [fk]

/-- Loop body of the main phase. -/
def mainB : Cmd :=
  .pop 3 (.halt true) (.pop 3 (.halt false) (.seq endRow srRow) (colStep false))
    (.pop 3 (.halt false) (colStep true) (colStep false))

def mainLoop : Cmd := .loop mainB

section Main

variable {y R Y Q : Str} {f : Option (Fin 3)}

theorem mainB_sym {s : SatSym} (hs : s ≠ sep) {r : Res} {T : ℕ}
    (h : ExecLe (colStep (isPos s)) (stC y R Q Y f) r T) :
    ExecLe mainB (stC y R (ic s ++ Q) Y f) r (T + 2) := by
  cases s with
  | sep => exact absurd rfl hs
  | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [v3, isPos] using h))
  | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [v3, isPos] using h))
  | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [v3, isPos] using h))

theorem mainB_sep {r : Res} {T : ℕ}
    (h : ExecLe (.seq endRow srRow) (stC y R Q Y f) r T) :
    ExecLe mainB (stC y R (false :: false :: Q) Y f) r (T + 2) :=
  ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [v3] using h))

/-- One row. -/
theorem ex_row (N : ℕ) (hy : y.length ≤ N) (k : Fin 3) (Q' : Str) : ∀ (r : List SatSym) (Y : Str),
    sep ∉ r → Y.length ≤ N → ∀ (res : Res) (T' : ℕ),
    ExecLe mainLoop (stC y (R.drop 2) Q' y (some (hdC R))) res T' →
    ExecLe mainLoop (stC y R (r.flatMap ic ++ false :: false :: Q') Y (some k))
      (if rowOk k r Y then res else .halt false) (T' + (6 * r.length + 7 * N + 17))
  | [], Y, _, hY, res, T', h => by
    have hb := mainB_sep ((ex_endRow y R Q' Y k).seq_norm (ex_srRow y R Q'))
    exact (ExecLe.loop_norm hb h).cast (by simp [rowOk]) (by simp; omega)
  | s :: r, Y, hr, hY, res, T', h => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have hcs := ex_colStep (isPos s) y R (r.flatMap ic ++ false :: false :: Q') Y k
    have hb := mainB_sym (Q := r.flatMap ic ++ false :: false :: Q') hs hcs
    simp only [List.flatMap_cons, List.append_assoc]
    cases hc : (isPos s && decide (k = hdC Y))
    · rw [hc] at hb; simp only [Bool.false_eq_true, if_false] at hb
      have ih := ex_row N hy k Q' r (Y.drop 2) hr' (by simp; omega) res T' h
      exact (ExecLe.loop_norm hb ih).cast (by simp [rowOk, hc]) (by simp; omega)
    · rw [hc] at hb; simp only [if_true] at hb
      exact (ExecLe.loop_halt hb).cast (by simp [rowOk, hc]) (by omega)

/-- Cost of the main phase. -/
def TrowsC (N : ℕ) : List (List SatSym) → ℕ
  | [] => 2
  | r :: rows => 6 * r.length + 7 * N + 17 + TrowsC N rows

theorem ex_rows (N : ℕ) (hy : y.length ≤ N) : ∀ (rows : List (List SatSym)) (R : Str),
    (∀ r ∈ rows, sep ∉ r) →
    ExecLe mainLoop (stC y (R.drop 2) (enc rows) y (some (hdC R))) (.halt (goC y rows R))
      (TrowsC N rows)
  | [], R, _ => (ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt true _))).cast
      (by simp [goC]) (by simp [TrowsC])
  | r :: rows, R, hrows => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    have ih := ex_rows N hy rows (R.drop 2) hrs
    rw [enc_cons]
    have := ex_row (R := R.drop 2) N hy (hdC R) (enc rows) r y hr hy _ _ ih
    refine this.cast ?_ (by simp [TrowsC]; omega)
    simp only [goC]
    cases rowOk (hdC R) r y <;> rfl

end Main

/-! ## The whole verifier -/

def verC : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq (copyVia 0 1 8) (.seq srRow mainLoop))))

/-- Time bound of the verifier. -/
def TverC (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (5 * n + 4) + (5 * n + 7) +
  (6 * n + n * (7 * n + 17) + 2)

theorem TrowsC_eq (N : ℕ) : ∀ rows : List (List SatSym),
    TrowsC N rows = 6 * (rows.map List.length).sum + rows.length * (7 * N + 17) + 2
  | [] => by simp [TrowsC]
  | r :: rows => by simp only [TrowsC, TrowsC_eq N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem exec_verC (z : Str) :
    ExecLe verC (init [z]).stk (.halt (vresC (dec z).1 (dec z).2)) (TverC z.length) := by
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
      stC [] y (enc (clauses w)) [] none := by
    funext j
    simp only [σ₂, σ₁, stC, fk, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hC := exec_copyVia (a := 0) (b := 1) (t := 8) (by decide) (by decide) (by decide)
    (stC [] y (enc (clauses w)) [] none) rfl
  rw [stC_0, stC_1, List.append_nil, v1] at hC
  have hS := ex_srRow y y (enc (clauses w))
  have hcl := length_clauses_le w
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hR := ex_rows (y := y) z.length (by omega) (clauses w) y (sep_not_mem_clauses w)
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  refine (hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm ((ExecLe.of hC).seq_norm
    (hS.seq_norm hR))))).cast rfl ?_
  rw [TrowsC_eq]
  simp only [htl, TverC]
  have h1 : (clauses w).length * (7 * z.length + 17) ≤ z.length * (7 * z.length + 17) :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem TverC_le (n : ℕ) : TverC n ≤ tb 6 n := by
  unfold TverC tb
  have hm : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  norm_num at hm
  have e : (n + 2) ^ 6 = (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by ring
  have : 16 * (n + 2) ^ 2 ≤ (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by nlinarith
  nlinarith

end Pnp.Karp.Color
