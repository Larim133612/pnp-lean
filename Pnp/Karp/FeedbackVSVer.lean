import Pnp.Karp.FeedbackVS
import Pnp.Karp.DomSetVer

/-!
# FEEDBACK VERTEX SET ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/FeedbackVS.lean`, rows `kr :: rows`) and a certificate `y : List Bool`, read as a
sequence of *blocks*, one per vertex: the block of a vertex is `f :: true^ρ ++ [false]`
(`f`: the vertex is in `F`; `ρ`: its rank).  The block of vertex `v` starts at
`fvv_nx^[v] y` (`fvv_nx` skips one block; missing bits end the certificate).  A vertex is
*checked* iff its block starts with `false` (a missing block counts as a vertex of `F`); every
unchecked vertex `v < n` consumes one unit of the budget `|kr|`, and for every `pos` entry
`(i, j)` with `i ≠ j` and both `i`, `j` checked the rank of `i` must be smaller than the rank of
`j`.  Stack layout (`fvv_st`):

* `0`: the unread certificate `R` (the block of the current row);  `1`: a copy of `y`;
* `3`: the internal code of the remaining rows `Q`;  `4`: the rank of the current row (unary);
* `5`: a temporary for the rank;  `6`: the remaining budget (unary);
* `7`: the column blocks `Y` (the current column's block on top);  `9`: the row index (unary);
* `10`: the diagonal counter `D = true^(i - j) ++ [false]` (dropped by the column `j`).

Program (`fvv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3`, `copyVia 0 1 8`: parse, copy the certificate;
2. `dsv_bL`: read the budget row (one mark per symbol onto stack `6`);
3. `fvv_oL`: per row (peeking at stack `3`; accept at the end): `Y := y`, `D := I ++ [false]`;
   pop the row's flag; if it is `false` read the rank into stack `4` and scan the row
   (`fvv_kL`): every symbol pops `D` and the column block; at a non-diagonal `pos` entry whose
   column block starts with `false` the column rank must exceed the row rank (`fvv_cL`, halt
   `false` otherwise); otherwise pop the budget (halt `false` if empty), skip the rank and the
   row (`fvv_sL`); clean up and push a mark onto the row index.

`fvv_exec_ver`: the program halts with `fvv_vres (dec z).1 (dec z).2` on every input `z`,
within `fvv_Tver |z|` steps.
-/

namespace Pnp.Karp.FeedbackVS

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.HittingSet Pnp.Karp.DomSet

/-! ## Semantics -/

/-- Read a unary number terminated by `false` (or by the end). -/
def fvv_units : Str → ℕ × Str
  | [] => (0, [])
  | false :: s => (0, s)
  | true :: s => ((fvv_units s).1 + 1, (fvv_units s).2)

/-- Skip one block. -/
def fvv_nx : Str → Str
  | [] => []
  | _ :: s => (fvv_units s).2

/-- The rank of the block on top. -/
def fvv_rk (Y : Str) : ℕ := (fvv_units Y.tail).1

/-- A violation at a column: `pos`, not diagonal, the column checked, rank not larger. -/
def fvv_bad (a : ℕ) (s : SatSym) (Y D : Str) : Bool :=
  decide (s = pos ∧ D.head? ≠ some false ∧ Y.head? = some false ∧ ¬ a < fvv_rk Y)

/-- Check a row of rank `a` (`Y`: the column blocks, `D`: the diagonal counter). -/
def fvv_rowOk (a : ℕ) : List SatSym → Str → Str → Bool
  | [], _, _ => true
  | s :: r, Y, D => !fvv_bad a s Y D && fvv_rowOk a r (fvv_nx Y) D.tail

/-- What the row loop computes (`R`: the block of row `i`, `c`: the remaining budget). -/
def fvv_go (y : Str) : List (List SatSym) → Str → ℕ → ℕ → Bool
  | [], _, _, _ => true
  | r :: rows, R, c, i =>
    if R.head? = some false then
      fvv_rowOk (fvv_rk R) r y (List.replicate i true ++ [false]) &&
        fvv_go y rows (fvv_nx R) c (i + 1)
    else decide (0 < c) && fvv_go y rows (fvv_nx R) (c - 1) (i + 1)

/-- The answer of the verifier on `(w, y)`. -/
def fvv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | kr :: rows => fvv_go y rows y kr.length 0

theorem fvv_units_length : ∀ Y : Str, (fvv_units Y).1 + (fvv_units Y).2.length ≤ Y.length
  | [] => by simp [fvv_units]
  | false :: s => by simp [fvv_units]
  | true :: s => by have := fvv_units_length s; simp [fvv_units]; omega

theorem fvv_nx_length (Y : Str) : (fvv_nx Y).length ≤ Y.length := by
  rcases Y with _ | ⟨b, s⟩
  · simp [fvv_nx]
  · have := fvv_units_length s; simp [fvv_nx]; omega

theorem fvv_rk_le (Y : Str) : fvv_rk Y ≤ Y.length := by
  rcases Y with _ | ⟨b, s⟩
  · simp [fvv_rk, fvv_units]
  · have := fvv_units_length s; simp [fvv_rk]; omega

theorem fvv_nx_iter_length : ∀ (k : ℕ) (Y : Str), (fvv_nx^[k] Y).length ≤ Y.length
  | 0, _ => le_rfl
  | k + 1, Y => by
    rw [iterate_succ_apply]
    exact (fvv_nx_iter_length k _).trans (fvv_nx_length Y)

/-! ## Stack layout -/

/-- The stacks of the verifier. -/
def fvv_st (R y Q K T Y I D C : Str) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 1 then y else if j = 3 then Q else if j = 4 then K else
  if j = 5 then T else if j = 6 then C else if j = 7 then Y else if j = 9 then I else
  if j = 10 then D else []

local macro "fvv_stx" : tactic =>
  `(tactic| (funext j; simp only [fvv_st, update_apply]; split_ifs <;> simp_all))

section St
variable {R y Q K T Y I D C : Str}
@[simp] theorem fvv_st_0 : fvv_st R y Q K T Y I D C 0 = R := rfl
@[simp] theorem fvv_st_1 : fvv_st R y Q K T Y I D C 1 = y := rfl
@[simp] theorem fvv_st_2 : fvv_st R y Q K T Y I D C 2 = [] := rfl
@[simp] theorem fvv_st_3 : fvv_st R y Q K T Y I D C 3 = Q := rfl
@[simp] theorem fvv_st_4 : fvv_st R y Q K T Y I D C 4 = K := rfl
@[simp] theorem fvv_st_5 : fvv_st R y Q K T Y I D C 5 = T := rfl
@[simp] theorem fvv_st_6 : fvv_st R y Q K T Y I D C 6 = C := rfl
@[simp] theorem fvv_st_7 : fvv_st R y Q K T Y I D C 7 = Y := rfl
@[simp] theorem fvv_st_8 : fvv_st R y Q K T Y I D C 8 = [] := rfl
@[simp] theorem fvv_st_9 : fvv_st R y Q K T Y I D C 9 = I := rfl
@[simp] theorem fvv_st_10 : fvv_st R y Q K T Y I D C 10 = D := rfl
@[simp] theorem fvv_u0 (X : Str) :
    update (fvv_st R y Q K T Y I D C) 0 X = fvv_st X y Q K T Y I D C := by fvv_stx
@[simp] theorem fvv_u1 (X : Str) :
    update (fvv_st R y Q K T Y I D C) 1 X = fvv_st R X Q K T Y I D C := by fvv_stx
@[simp] theorem fvv_u3 (X : Str) :
    update (fvv_st R y Q K T Y I D C) 3 X = fvv_st R y X K T Y I D C := by fvv_stx
@[simp] theorem fvv_u4 (X : Str) :
    update (fvv_st R y Q K T Y I D C) 4 X = fvv_st R y Q X T Y I D C := by fvv_stx
@[simp] theorem fvv_u5 (X : Str) :
    update (fvv_st R y Q K T Y I D C) 5 X = fvv_st R y Q K X Y I D C := by fvv_stx
@[simp] theorem fvv_u6 (X : Str) :
    update (fvv_st R y Q K T Y I D C) 6 X = fvv_st R y Q K T Y I D X := by fvv_stx
@[simp] theorem fvv_u7 (X : Str) :
    update (fvv_st R y Q K T Y I D C) 7 X = fvv_st R y Q K T X I D C := by fvv_stx
@[simp] theorem fvv_u8 :
    update (fvv_st R y Q K T Y I D C) 8 [] = fvv_st R y Q K T Y I D C := by fvv_stx
@[simp] theorem fvv_u9 (X : Str) :
    update (fvv_st R y Q K T Y I D C) 9 X = fvv_st R y Q K T Y X D C := by fvv_stx
@[simp] theorem fvv_u10 (X : Str) :
    update (fvv_st R y Q K T Y I D C) 10 X = fvv_st R y Q K T Y I X C := by fvv_stx
end St

/-- A pop with three identical branches. -/
theorem fvv_pop3 {k : ℕ} {c : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ}
    (h : ExecLe c (update σ k (σ k).tail) r T) : ExecLe (.pop k c c c) σ r (T + 1) := by
  cases hk : σ k with
  | nil =>
    rw [hk, List.tail_nil, ← hk, update_eq_self] at h
    exact ExecLe.pop_nil hk h
  | cons b s =>
    rw [hk, List.tail_cons] at h
    exact ExecLe.pop_same hk h

/-- Peeking at stack `3`. -/
theorem fvv_peek {c cn : Cmd} {σ : ℕ → Str} {b : Bool} {s : Str} {r : Res} {T : ℕ}
    (hk : σ 3 = b :: s) (h : ExecLe c σ r T) :
    ExecLe (.pop 3 cn (.seq (.push 3 false) c) (.seq (.push 3 true) c)) σ r (T + 2) := by
  have e : update (update σ 3 s) 3 (b :: update σ 3 s 3) = σ := by
    rw [update_self, update_idem, ← hk, update_eq_self]
  refine ExecLe.pop_cons hk ?_
  cases b
  · exact ((ExecLe.push 3 false _).seq_norm (by rw [e]; exact h)).cast rfl (by omega)
  · exact ((ExecLe.push 3 true _).seq_norm (by rw [e]; exact h)).cast rfl (by omega)

/-! ## Skipping blocks -/

/-- Skip the units of the column block (up to and including the terminating `false`). -/
def fvv_su : Cmd := .loop (.pop 7 .brk .brk .skip)

theorem fvv_ex_su (R y Q K T I D C : Str) : ∀ Y : Str,
    ExecLe fvv_su (fvv_st R y Q K T Y I D C)
      (.norm (fvv_st R y Q K T (fvv_units Y).2 I D C)) (2 * Y.length + 2)
  | [] => (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast (by simp [fvv_units])
      (by simp)
  | false :: s => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := s) rfl
      (by rw [fvv_u7]; exact ExecLe.brk _))).cast (by simp [fvv_units]) (by simp)
  | true :: s => by
    have ih := fvv_ex_su R y Q K T I D C s
    have hb : ExecLe (.pop 7 .brk .brk .skip) (fvv_st R y Q K T (true :: s) I D C)
        (.norm (fvv_st R y Q K T s I D C)) 2 :=
      ExecLe.pop_cons (b := true) (s := s) rfl (by rw [fvv_u7]; exact ExecLe.skip _)
    exact (ExecLe.loop_norm hb ih).cast (by simp [fvv_units]) (by simp; omega)

/-- Skip the column block. -/
def fvv_sb : Cmd := .pop 7 .skip fvv_su fvv_su

theorem fvv_ex_sb (R y Q K T I D C Y : Str) :
    ExecLe fvv_sb (fvv_st R y Q K T Y I D C) (.norm (fvv_st R y Q K T (fvv_nx Y) I D C))
      (2 * Y.length + 3) := by
  rcases Y with _ | ⟨b, s⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [fvv_nx]) (by simp)
  · exact (ExecLe.pop_same (b := b) (s := s) rfl
      (by rw [fvv_u7]; exact fvv_ex_su R y Q K T I D C s)).cast (by simp [fvv_nx])
      (by simp only [List.length_cons]; omega)

/-! ## Comparing ranks -/

def fvv_cB : Cmd :=
  .pop 7 (.halt false) (.halt false) (.pop 4 (.seq fvv_su .brk) (.push 5 true) (.push 5 true))

def fvv_cL : Cmd := .loop fvv_cB

theorem fvv_ex_cL (R y Q I D C : Str) : ∀ (Y : Str) (a b : ℕ),
    ExecLe fvv_cL (fvv_st R y Q (List.replicate a true) (List.replicate b true) Y I D C)
      (if a < (fvv_units Y).1 then
        .norm (fvv_st R y Q [] (List.replicate (a + b) true) (fvv_units Y).2 I D C)
      else .halt false)
      (3 * Y.length + 5)
  | [], a, b => (ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt false _))).cast
      (by simp [fvv_units]) (by omega)
  | false :: s, a, b => (ExecLe.loop_halt (ExecLe.pop_cons (b := false) (s := s) rfl
      (by rw [fvv_u7]; exact ExecLe.halt false _))).cast (by simp [fvv_units]) (by simp)
  | true :: s, 0, b => by
    have h1 := fvv_ex_su R y Q [] (List.replicate b true) I D C s
    have hb : ExecLe fvv_cB (fvv_st R y Q [] (List.replicate b true) (true :: s) I D C)
        (.brk (fvv_st R y Q [] (List.replicate b true) (fvv_units s).2 I D C))
        (2 * s.length + 5) :=
      ExecLe.pop_cons (b := true) (s := s) rfl (by
        rw [fvv_u7]
        exact (ExecLe.pop_nil rfl (h1.seq_norm (ExecLe.brk _))).cast rfl (by omega))
    exact (ExecLe.loop_brk hb).cast (by simp [fvv_units]) (by simp; omega)
  | true :: s, a + 1, b => by
    have ih := fvv_ex_cL R y Q I D C s a (b + 1)
    have hb : ExecLe fvv_cB
        (fvv_st R y Q (List.replicate (a + 1) true) (List.replicate b true) (true :: s) I D C)
        (.norm (fvv_st R y Q (List.replicate a true) (List.replicate (b + 1) true) s I D C))
        3 := by
      refine ExecLe.pop_cons (b := true) (s := s) rfl ?_
      rw [fvv_u7]
      refine ExecLe.pop_cons (b := true) (s := List.replicate a true)
        (by simp [List.replicate_succ]) ?_
      rw [fvv_u4]
      exact (ExecLe.push 5 true _).cast (by simp [List.replicate_succ]) le_rfl
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp only [fvv_units]
    by_cases h : a < (fvv_units s).1
    · rw [if_pos h, if_pos (by omega), show a + (b + 1) = a + 1 + b by omega]
    · rw [if_neg h, if_neg (by omega)]

/-- Check a column (the block on stack `7`) against the row rank. -/
def fvv_chk : Cmd := .pop 7 .skip (.seq fvv_cL (move 5 4)) fvv_su

theorem fvv_ex_chk (R y Q I D C Y : Str) (a : ℕ) :
    ExecLe fvv_chk (fvv_st R y Q (List.replicate a true) [] Y I D C)
      (if Y.head? = some false ∧ ¬ a < fvv_rk Y then .halt false
        else .norm (fvv_st R y Q (List.replicate a true) [] (fvv_nx Y) I D C))
      (3 * Y.length + 2 * a + 12) := by
  rcases Y with _ | ⟨_ | _, s⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [fvv_nx]) (by omega)
  · have h1 := fvv_ex_cL R y Q I D C s a 0
    rw [List.replicate_zero, Nat.add_zero] at h1
    by_cases ha : a < (fvv_units s).1
    · rw [if_pos ha] at h1
      have hM := exec_move (a := 5) (b := 4) (by decide) (List.replicate a true)
        (fvv_st R y Q [] (List.replicate a true) (fvv_units s).2 I D C) rfl
      rw [fvv_u5, fvv_u4, fvv_st_4, List.reverse_replicate, List.append_nil] at hM
      refine (ExecLe.pop_cons (b := false) (s := s) rfl (by
        rw [fvv_u7]; exact h1.seq_norm (ExecLe.of hM))).cast ?_ ?_
      · simp [fvv_rk, fvv_nx, ha]
      · simp; omega
    · rw [if_neg ha] at h1
      refine (ExecLe.pop_cons (b := false) (s := s) rfl (by
        rw [fvv_u7]; exact ExecLe.seq_halt h1)).cast ?_ ?_
      · simp [fvv_rk, ha]
      · simp; omega
  · refine (ExecLe.pop_cons (b := true) (s := s) rfl (by
      rw [fvv_u7]; exact fvv_ex_su R y Q _ [] I D C s)).cast ?_ ?_
    · simp [fvv_nx]
    · simp; omega

/-! ## One column -/

def fvv_colS : Cmd := .seq (.pop 10 .skip .skip .skip) fvv_sb

def fvv_colP : Cmd := .pop 10 fvv_chk fvv_sb fvv_chk

theorem fvv_ex_col (R y Q I C Y D : Str) (a : ℕ) {s : SatSym} (hs : s ≠ sep) :
    ExecLe (hsv_sel s .brk fvv_colS fvv_colP fvv_colS)
      (fvv_st R y Q (List.replicate a true) [] Y I D C)
      (if fvv_bad a s Y D then .halt false
        else .norm (fvv_st R y Q (List.replicate a true) [] (fvv_nx Y) I D.tail C))
      (3 * Y.length + 2 * a + 14) := by
  have hS : ExecLe fvv_colS (fvv_st R y Q (List.replicate a true) [] Y I D C)
      (.norm (fvv_st R y Q (List.replicate a true) [] (fvv_nx Y) I D.tail C))
      (3 * Y.length + 2 * a + 14) := by
    have h1 : ExecLe (.pop 10 .skip .skip .skip) (fvv_st R y Q (List.replicate a true) [] Y I D C)
        (.norm (fvv_st R y Q (List.replicate a true) [] Y I D.tail C)) 2 :=
      fvv_pop3 (by rw [fvv_st_10, fvv_u10]; exact ExecLe.skip _)
    exact (h1.seq_norm (fvv_ex_sb _ _ _ _ _ _ _ _ _)).cast rfl (by omega)
  cases s with
  | sep => exact absurd rfl hs
  | zero => exact hS.cast (by simp [fvv_bad]) le_rfl
  | neg => exact hS.cast (by simp [fvv_bad]) le_rfl
  | pos =>
    show ExecLe fvv_colP _ _ _
    rcases D with _ | ⟨_ | _, d⟩
    · exact (ExecLe.pop_nil rfl (fvv_ex_chk R y Q I [] C Y a)).cast
        (by simp [fvv_bad]) (by omega)
    · exact (ExecLe.pop_cons (b := false) (s := d) rfl (by
        rw [fvv_u10]; exact fvv_ex_sb _ _ _ _ _ _ _ _ _)).cast (by simp [fvv_bad]) (by omega)
    · exact (ExecLe.pop_cons (b := true) (s := d) rfl (by
        rw [fvv_u10]; exact fvv_ex_chk R y Q I d C Y a)).cast (by simp [fvv_bad]) (by omega)

/-! ## The row loops -/

def fvv_kB : Cmd :=
  .pop 3 (.halt true) (.pop 3 (.halt true) .brk fvv_colS) (.pop 3 (.halt true) fvv_colP fvv_colS)

def fvv_kL : Cmd := .loop fvv_kB

theorem fvv_ex_kL (R y Q' I C : Str) (a N : ℕ) (ha : a ≤ N) : ∀ (r : List SatSym) (Y D : Str),
    sep ∉ r → Y.length ≤ N →
    ExecLe fvv_kL
      (fvv_st R y (r.flatMap ic ++ false :: false :: Q') (List.replicate a true) [] Y I D C)
      (if fvv_rowOk a r Y D then
        .norm (fvv_st R y Q' (List.replicate a true) [] (fvv_nx^[r.length] Y) I
          (D.drop r.length) C)
      else .halt false)
      (r.length * (5 * N + 16) + 3)
  | [], Y, D, _, _ => by
    have hb := dsv_pop2 (cE := .halt true) (cX := .halt true) (cS := .brk) (cZ := fvv_colS)
      (cP := fvv_colP) (cN := fvv_colS) (Q := Q') sep
      (σ := fvv_st R y (false :: false :: Q') (List.replicate a true) [] Y I D C) rfl
      (ExecLe.brk _)
    exact (ExecLe.loop_brk hb).cast (by simp [fvv_rowOk]) (by simp)
  | s :: r, Y, D, hr, hY => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hc := fvv_ex_col R y (r.flatMap ic ++ false :: false :: Q') I C Y D a hs
    have hb := dsv_pop2 (cE := .halt true) (cX := .halt true) s
      (Q := r.flatMap ic ++ false :: false :: Q')
      (σ := fvv_st R y ((s :: r).flatMap ic ++ false :: false :: Q') (List.replicate a true) []
        Y I D C) (by simp) (by rw [fvv_u3]; exact hc)
    simp only [List.flatMap_cons, List.append_assoc] at hb ⊢
    by_cases hbad : fvv_bad a s Y D = true
    · rw [if_pos hbad] at hb
      exact (ExecLe.loop_halt hb).cast (by simp [fvv_rowOk, hbad]) (by simp; nlinarith)
    · rw [if_neg hbad] at hb
      have ih := fvv_ex_kL R y Q' I C a N ha r (fvv_nx Y) D.tail
        (fun e => hr (List.mem_cons_of_mem _ e)) ((fvv_nx_length Y).trans hY)
      refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; nlinarith)
      simp only [fvv_rowOk, hbad, Bool.not_false, Bool.true_and, List.length_cons,
        iterate_succ_apply]
      cases D <;> simp

def fvv_sB : Cmd :=
  .pop 3 (.halt true) (.pop 3 (.halt true) .brk .skip) (.pop 3 (.halt true) .skip .skip)

def fvv_sL : Cmd := .loop fvv_sB

theorem fvv_ex_sL (R y Q' K T Y I D C : Str) : ∀ r : List SatSym, sep ∉ r →
    ExecLe fvv_sL (fvv_st R y (r.flatMap ic ++ false :: false :: Q') K T Y I D C)
      (.norm (fvv_st R y Q' K T Y I D C)) (3 * r.length + 3)
  | [], _ => by
    have hb := dsv_pop2 (cE := .halt true) (cX := .halt true) (cS := .brk) (cZ := .skip)
      (cP := .skip) (cN := .skip) (Q := Q') sep
      (σ := fvv_st R y (false :: false :: Q') K T Y I D C) rfl (ExecLe.brk _)
    exact (ExecLe.loop_brk hb).cast (by simp) (by simp)
  | s :: r, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := fvv_ex_sL R y Q' K T Y I D C r (fun e => hr (List.mem_cons_of_mem _ e))
    have hp : ExecLe (hsv_sel s .brk .skip .skip .skip)
        (fvv_st R y (r.flatMap ic ++ false :: false :: Q') K T Y I D C)
        (.norm (fvv_st R y (r.flatMap ic ++ false :: false :: Q') K T Y I D C)) 1 := by
      cases s with
      | sep => exact absurd rfl hs
      | _ => exact ExecLe.skip _
    have hb := dsv_pop2 (cE := .halt true) (cX := .halt true) s
      (Q := r.flatMap ic ++ false :: false :: Q')
      (σ := fvv_st R y ((s :: r).flatMap ic ++ false :: false :: Q') K T Y I D C) (by simp)
      (by rw [fvv_u3]; exact hp)
    simp only [List.flatMap_cons, List.append_assoc] at hb ⊢
    exact (ExecLe.loop_norm hb ih).cast rfl (by simp; omega)

/-! ## Starting a row -/

/-- Read the rank of the row block into stack `4`. -/
def fvv_rdK : Cmd := .loop (.pop 0 .brk .brk (.push 4 true))

theorem fvv_ex_rdK (y Q T Y I D C : Str) : ∀ (R : Str) (k : ℕ),
    ExecLe fvv_rdK (fvv_st R y Q (List.replicate k true) T Y I D C)
      (.norm (fvv_st (fvv_units R).2 y Q (List.replicate ((fvv_units R).1 + k) true) T Y I D C))
      (2 * R.length + 2)
  | [], k => (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [fvv_units]) (by simp)
  | false :: s, k => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := s) rfl
      (by rw [fvv_u0]; exact ExecLe.brk _))).cast (by simp [fvv_units]) (by simp)
  | true :: s, k => by
    have ih := fvv_ex_rdK y Q T Y I D C s (k + 1)
    have hb : ExecLe (.pop 0 .brk .brk (.push 4 true))
        (fvv_st (true :: s) y Q (List.replicate k true) T Y I D C)
        (.norm (fvv_st s y Q (List.replicate (k + 1) true) T Y I D C)) 2 :=
      ExecLe.pop_cons (b := true) (s := s) rfl (by
        rw [fvv_u0]; exact (ExecLe.push 4 true _).cast (by simp [List.replicate_succ]) (by omega))
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp only [fvv_units]
    congr 3; omega

/-- Pop the budget. -/
def fvv_bud : Cmd := .pop 6 (.halt false) .skip .skip

/-- A row of a vertex of `F`. -/
def fvv_skR : Cmd := .seq fvv_bud (.seq fvv_rdK fvv_sL)

def fvv_mode : Cmd := .pop 0 fvv_skR (.seq fvv_rdK fvv_kL) fvv_skR

/-- Clean up after a row. -/
def fvv_end : Cmd := .seq (drain 7) (.seq (drain 10) (.seq (drain 4) (.push 9 true)))

theorem fvv_ex_end (R y Q K Y I D C : Str) :
    ExecLe fvv_end (fvv_st R y Q K [] Y I D C) (.norm (fvv_st R y Q [] [] [] (true :: I) [] C))
      (2 * Y.length + 2 * D.length + 2 * K.length + 7) := by
  have h1 := exec_drain 7 Y (fvv_st R y Q K [] Y I D C) rfl
  rw [fvv_u7] at h1
  have h2 := exec_drain 10 D (fvv_st R y Q K [] [] I D C) rfl
  rw [fvv_u10] at h2
  have h3 := exec_drain 4 K (fvv_st R y Q K [] [] I [] C) rfl
  rw [fvv_u4] at h3
  have h4 := ExecLe.push 9 true (fvv_st R y Q [] [] [] I [] C)
  rw [fvv_st_9, fvv_u9] at h4
  exact ((ExecLe.of h1).seq_norm ((ExecLe.of h2).seq_norm ((ExecLe.of h3).seq_norm h4))).cast
    rfl (by omega)

def fvv_row : Cmd :=
  .seq (copyVia 1 7 8) (.seq (.push 10 false) (.seq (copyVia 9 10 8) (.seq fvv_mode fvv_end)))

/-- Result of a row. -/
def fvv_rres (y R : Str) (r : List SatSym) (c i : ℕ) : Res :=
  if R.head? = some false then
    (if fvv_rowOk (fvv_rk R) r y (List.replicate i true ++ [false]) then
      .norm (fvv_st (fvv_nx R) y [] [] [] [] [] [] []) else .halt false)
  else (if 0 < c then .norm (fvv_st (fvv_nx R) y [] [] [] [] [] [] []) else .halt false)

theorem fvv_ex_row (y Q' R : Str) (r : List SatSym) (c i N : ℕ) (hr : sep ∉ r)
    (hy : y.length ≤ N) (hR : R.length ≤ N) (hi : i + 1 ≤ N) :
    ExecLe fvv_row
      (fvv_st R y (r.flatMap ic ++ false :: false :: Q') [] [] [] (List.replicate i true) []
        (List.replicate c true))
      (if R.head? = some false then
        (if fvv_rowOk (fvv_rk R) r y (List.replicate i true ++ [false]) then
          .norm (fvv_st (fvv_nx R) y Q' [] [] [] (List.replicate (i + 1) true) []
            (List.replicate c true)) else .halt false)
      else (if 0 < c then
          .norm (fvv_st (fvv_nx R) y Q' [] [] [] (List.replicate (i + 1) true) []
            (List.replicate (c - 1) true)) else .halt false))
      (r.length * (5 * N + 16) + 20 * N + 30) := by
  set Q := r.flatMap ic ++ false :: false :: Q'
  set dg := List.replicate i true ++ [false]
  have hC1 := exec_copyVia (a := 1) (b := 7) (t := 8) (by decide) (by decide) (by decide)
    (fvv_st R y Q [] [] [] (List.replicate i true) [] (List.replicate c true)) rfl
  rw [fvv_st_1, fvv_st_7, List.append_nil, fvv_u7] at hC1
  have hP := ExecLe.push 10 false (fvv_st R y Q [] [] y (List.replicate i true) []
    (List.replicate c true))
  rw [fvv_st_10, fvv_u10] at hP
  have hC2 := exec_copyVia (a := 9) (b := 10) (t := 8) (by decide) (by decide) (by decide)
    (fvv_st R y Q [] [] y (List.replicate i true) [false] (List.replicate c true)) rfl
  rw [fvv_st_9, fvv_st_10, fvv_u10] at hC2
  have hpre : ∀ (res : Res) (T : ℕ),
      ExecLe (.seq fvv_mode fvv_end)
        (fvv_st R y Q [] [] y (List.replicate i true) dg (List.replicate c true)) res T →
      ExecLe fvv_row
        (fvv_st R y Q [] [] [] (List.replicate i true) [] (List.replicate c true)) res
        (5 * y.length + 4 + (1 + (5 * i + 4 + T))) := by
    intro res T h
    have hl : (List.replicate i true).length = i := List.length_replicate
    have := (ExecLe.of hC1).seq_norm (hP.seq_norm ((ExecLe.of hC2).seq_norm h))
    rw [hl] at this
    exact this
  have hrep : ∀ k, (List.replicate k true).length = k := fun k => List.length_replicate
  have hdg : dg.length = i + 1 := by simp [dg]
  have hrk := fvv_rk_le R
  -- the skip branch
  have hskip : ∀ R₀ : Str, R₀.length ≤ N → (fvv_units R₀).2 = fvv_nx R →
      (fvv_units R₀).1 = fvv_rk R →
      ExecLe fvv_skR (fvv_st R₀ y Q [] [] y (List.replicate i true) dg (List.replicate c true))
        (if 0 < c then .norm (fvv_st (fvv_nx R) y Q' (List.replicate (fvv_rk R) true) [] y
          (List.replicate i true) dg (List.replicate (c - 1) true)) else .halt false)
        (3 * r.length + 2 * N + 8) := by
    intro R₀ hR₀ e2 e1
    rcases c with _ | c
    · exact (ExecLe.seq_halt (ExecLe.pop_nil rfl (ExecLe.halt false _))).cast (by simp)
        (by omega)
    · have hb : ExecLe fvv_bud
          (fvv_st R₀ y Q [] [] y (List.replicate i true) dg (List.replicate (c + 1) true))
          (.norm (fvv_st R₀ y Q [] [] y (List.replicate i true) dg (List.replicate c true))) 2 :=
        ExecLe.pop_cons (b := true) (s := List.replicate c true) (by simp [List.replicate_succ])
          (by rw [fvv_u6]; exact ExecLe.skip _)
      have hk := fvv_ex_rdK y Q [] y (List.replicate i true) dg (List.replicate c true) R₀ 0
      rw [List.replicate_zero, Nat.add_zero, e1, e2] at hk
      have hs := fvv_ex_sL (fvv_nx R) y Q' (List.replicate (fvv_rk R) true) [] y
        (List.replicate i true) dg (List.replicate c true) r hr
      exact (hb.seq_norm (hk.seq_norm hs)).cast (by simp) (by omega)
  have hpost : ∀ (K Y' D' : Str) (C' : Str), K.length ≤ N → Y'.length ≤ N → D'.length ≤ N →
      ExecLe fvv_end (fvv_st (fvv_nx R) y Q' K [] Y' (List.replicate i true) D' C')
        (.norm (fvv_st (fvv_nx R) y Q' [] [] [] (List.replicate (i + 1) true) [] C'))
        (6 * N + 7) := by
    intro K Y' D' C' hK hY hD
    exact (fvv_ex_end _ _ _ _ _ _ _ _).cast (by simp [List.replicate_succ]) (by omega)
  have h3r : 3 * r.length ≤ r.length * (5 * N + 16) := by nlinarith
  refine (hpre _ (r.length * (5 * N + 16) + 10 * N + 21) ?_).mono (by omega)
  rcases R with _ | ⟨_ | _, s⟩
  · -- missing block
    have hm := hskip [] (by simp) (by simp [fvv_nx, fvv_units]) (by simp [fvv_rk, fvv_units])
    have hmode : ExecLe fvv_mode
        (fvv_st [] y Q [] [] y (List.replicate i true) dg (List.replicate c true)) _ _ :=
      ExecLe.pop_nil rfl hm
    rcases c with _ | c
    · exact (ExecLe.seq_halt hmode).cast (by simp) (by omega)
    · simp only [Nat.lt_add_one_iff, zero_le, if_true] at hmode
      refine (hmode.seq_norm (hpost _ _ _ _ ?_ ?_ ?_)).cast (by simp) ?_
      · simp only [List.length_replicate]; exact hrk.trans hR
      · omega
      · omega
      · omega
  · -- a checked vertex
    have hk := fvv_ex_rdK y Q [] y (List.replicate i true) dg (List.replicate c true) s 0
    rw [List.replicate_zero, Nat.add_zero] at hk
    have hrs : (fvv_units s).1 ≤ N := by
      have := fvv_units_length s; simp at hR; omega
    have hkl := fvv_ex_kL (fvv_units s).2 y Q' (List.replicate i true) (List.replicate c true)
      (fvv_units s).1 N hrs r y dg hr hy
    have hmode := ExecLe.pop_cons (cn := fvv_skR) (ct := fvv_skR) (b := false) (s := s)
      (show fvv_st (false :: s) y Q [] [] y (List.replicate i true) dg (List.replicate c true) 0
        = false :: s from rfl) (by rw [fvv_u0]; exact hk.seq_norm hkl)
    by_cases hok : fvv_rowOk (fvv_units s).1 r y dg = true
    · rw [if_pos hok] at hmode
      refine (hmode.seq_norm (hpost _ _ _ _ ?_ ?_ ?_)).cast ?_ ?_
      · simp only [List.length_replicate]; exact hrs
      · exact (fvv_nx_iter_length _ _).trans hy
      · simp only [List.length_drop, hdg]; omega
      · simp [fvv_rk, fvv_nx, hok, dg]
      · simp only [List.length_cons] at hR; omega
    · rw [if_neg hok] at hmode
      exact (ExecLe.seq_halt hmode).cast (by simp [fvv_rk, hok, dg])
        (by simp only [List.length_cons] at hR; omega)
  · -- a vertex of `F`
    have hm := hskip s (by simp at hR; omega) (by simp [fvv_nx]) (by simp [fvv_rk])
    have hmode := ExecLe.pop_cons (cn := fvv_skR) (cf := .seq fvv_rdK fvv_kL) (b := true)
      (s := s) (show fvv_st (true :: s) y Q [] [] y (List.replicate i true) dg
        (List.replicate c true) 0 = true :: s from rfl) (by rw [fvv_u0]; exact hm)
    rcases c with _ | c
    · exact (ExecLe.seq_halt hmode).cast (by simp) (by omega)
    · simp only [Nat.lt_add_one_iff, zero_le, if_true] at hmode
      refine (hmode.seq_norm (hpost _ _ _ _ ?_ ?_ ?_)).cast (by simp) ?_
      · simp only [List.length_replicate]; exact hrk.trans hR
      · omega
      · omega
      · omega

/-! ## The outer loop -/

def fvv_oB : Cmd := .pop 3 (.halt true) (.seq (.push 3 false) fvv_row) (.seq (.push 3 true) fvv_row)

def fvv_oL : Cmd := .loop fvv_oB

/-- Cost of the outer loop. -/
def fvv_To (N : ℕ) : List (List SatSym) → ℕ
  | [] => 2
  | r :: rows => r.length * (5 * N + 16) + 20 * N + 32 + fvv_To N rows

theorem fvv_To_eq (N : ℕ) : ∀ rows : List (List SatSym),
    fvv_To N rows = (rows.map List.length).sum * (5 * N + 16) + rows.length * (20 * N + 32) + 2
  | [] => by simp [fvv_To]
  | r :: rows => by
    simp only [fvv_To, fvv_To_eq N rows, List.map_cons, List.sum_cons, List.length_cons]; ring

theorem fvv_ex_oL (y : Str) (N : ℕ) (hy : y.length ≤ N) : ∀ (rows : List (List SatSym))
    (R : Str) (c i : ℕ), (∀ r ∈ rows, sep ∉ r) → R.length ≤ N → i + rows.length ≤ N →
    ExecLe fvv_oL (fvv_st R y (enc rows) [] [] [] (List.replicate i true) []
      (List.replicate c true)) (.halt (fvv_go y rows R c i)) (fvv_To N rows)
  | [], R, c, i, _, _, _ => (ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt true _))).cast
      (by simp [fvv_go]) (by simp [fvv_To])
  | r :: rows, R, c, i, hrows, hR, hi => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.length_cons] at hi
    rw [enc_cons]
    obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil
      (show r.flatMap ic ++ false :: false :: enc rows ≠ [] by simp)
    have hrow := fvv_ex_row y (enc rows) R r c i N hr hy hR (by omega)
    have hnx := (fvv_nx_length R).trans hR
    have hpk := fun res T (h : ExecLe fvv_row (fvv_st R y (r.flatMap ic ++ false :: false ::
        enc rows) [] [] [] (List.replicate i true) [] (List.replicate c true)) res T) =>
      fvv_peek (cn := .halt true) (b := b) (s := t) (by rw [fvv_st_3, hbt]) h
    by_cases hF : R.head? = some false
    · rw [if_pos hF] at hrow
      by_cases hok : fvv_rowOk (fvv_rk R) r y (List.replicate i true ++ [false]) = true
      · rw [if_pos hok] at hrow
        have ih := fvv_ex_oL y N hy rows (fvv_nx R) c (i + 1) hrs hnx (by omega)
        exact (ExecLe.loop_norm (hpk _ _ hrow) ih).cast (by simp [fvv_go, hF, hok])
          (by simp [fvv_To])
      · rw [if_neg hok] at hrow
        exact (ExecLe.loop_halt (hpk _ _ hrow)).cast (by simp [fvv_go, hF, hok])
          (by simp [fvv_To])
    · rw [if_neg hF] at hrow
      rcases c with _ | c
      · exact (ExecLe.loop_halt (hpk _ _ hrow)).cast (by simp [fvv_go, hF])
          (by simp [fvv_To])
      · simp only [Nat.lt_add_one_iff, zero_le, if_true, Nat.add_sub_cancel] at hrow
        have ih := fvv_ex_oL y N hy rows (fvv_nx R) c (i + 1) hrs hnx (by omega)
        exact (ExecLe.loop_norm (hpk _ _ hrow) ih).cast (by simp [fvv_go, hF])
          (by simp [fvv_To])

/-! ## The budget row -/

theorem fvv_ex_bd (R y Q' : Str) : ∀ (t : List SatSym) (c : ℕ), sep ∉ t →
    ExecLe dsv_bL
      (fvv_st R y (t.flatMap ic ++ false :: false :: Q') [] [] [] [] [] (List.replicate c true))
      (.norm (fvv_st R y Q' [] [] [] [] [] (List.replicate (t.length + c) true)))
      (4 * t.length + 3)
  | [], c, _ => by
    have hb := dsv_pop2 (cE := .halt false) (cX := .halt false) (cZ := .push 6 true)
      (cP := .push 6 true) (cN := .push 6 true) (cS := .brk) (Q := Q') sep
      (σ := fvv_st R y (false :: false :: Q') [] [] [] [] [] (List.replicate c true)) rfl
      (ExecLe.brk _)
    exact (ExecLe.loop_brk hb).cast (by simp) (by simp)
  | s :: t, c, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := fvv_ex_bd R y Q' t (c + 1) (fun e => hr (List.mem_cons_of_mem _ e))
    have hp : ExecLe (hsv_sel s .brk (.push 6 true) (.push 6 true) (.push 6 true))
        (fvv_st R y (t.flatMap ic ++ false :: false :: Q') [] [] [] [] [] (List.replicate c true))
        (.norm (fvv_st R y (t.flatMap ic ++ false :: false :: Q') [] [] [] [] []
          (List.replicate (c + 1) true))) 1 := by
      have := ExecLe.push 6 true
        (fvv_st R y (t.flatMap ic ++ false :: false :: Q') [] [] [] [] [] (List.replicate c true))
      rw [fvv_st_6, fvv_u6, ← List.replicate_succ] at this
      cases s with
      | sep => exact absurd rfl hs
      | _ => exact this
    have hb := dsv_pop2 (cE := .halt false) (cX := .halt false) s
      (Q := t.flatMap ic ++ false :: false :: Q')
      (σ := fvv_st R y ((s :: t).flatMap ic ++ false :: false :: Q') [] [] [] [] []
        (List.replicate c true)) (by simp) (by rw [fvv_u3]; exact hp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp only [List.length_cons]
    congr 3; omega

/-! ## The whole verifier -/

def fvv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq (copyVia 0 1 8) (.seq dsv_bL fvv_oL))))

/-- Time bound of the verifier. -/
def fvv_Tver (n : ℕ) : ℕ := 30 * (n + 2) ^ 2

theorem fvv_exec_ver (z : Str) :
    ExecLe fvv_ver (init [z]).stk (.halt (fvv_vres (dec z).1 (dec z).2)) (fvv_Tver z.length) := by
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
      fvv_st y [] (enc (clauses w)) [] [] [] [] [] [] := by
    funext j
    simp only [σ₂, σ₁, fvv_st, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hC := exec_copyVia (a := 0) (b := 1) (t := 8) (by decide) (by decide) (by decide)
    (fvv_st y [] (enc (clauses w)) [] [] [] [] [] []) rfl
  rw [fvv_st_0, fvv_st_1, List.append_nil, fvv_u1] at hC
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ),
      ExecLe c (fvv_st y y (enc (clauses w)) [] [] [] [] [] []) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq (copyVia 0 1 8) c))))
        (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 +
          (5 * y.length + 4 + T)))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm ((ExecLe.of hC).seq_norm h)))
  have hsep := sep_not_mem_clauses w
  have hz2 : z.length * z.length ≤ (z.length + 2) ^ 2 := by nlinarith
  unfold fvv_vres fvv_ver
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · rw [hcw] at hpre
    refine (hpre _ _ _ (ExecLe.seq_halt (ExecLe.loop_halt
      (ExecLe.pop_nil (σ := fvv_st y y [] [] [] [] [] [] []) rfl (ExecLe.halt false _))))).cast
      rfl ?_
    simp only [htl, fvv_Tver]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    have hB := fvv_ex_bd y y (enc rows) kr 0 (hsep kr (by simp))
    rw [List.replicate_zero, Nat.add_zero] at hB
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hO := fvv_ex_oL y z.length (by omega) rows y kr.length 0
      (fun r hr => hsep r (by simp [hr])) (by omega) (by omega)
    refine (hpre _ _ _ (hB.seq_norm hO)).cast rfl ?_
    rw [fvv_To_eq]
    simp only [htl, fvv_Tver]
    have h1 : (rows.map List.length).sum * (5 * z.length + 16) ≤
        z.length * (5 * z.length + 16) := Nat.mul_le_mul_right _ (by omega)
    have h2 : rows.length * (20 * z.length + 32) ≤ z.length * (20 * z.length + 32) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem fvv_Tver_le (n : ℕ) : fvv_Tver n ≤ tb 7 n := by
  unfold fvv_Tver tb
  have hm : 2 ^ 5 ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have e : (n + 2) ^ 7 = (n + 2) ^ 5 * (n + 2) ^ 2 := by ring
  rw [e]
  have : 30 ≤ (n + 2) ^ 5 := by norm_num at hm; omega
  exact Nat.mul_le_mul_right _ this

end Pnp.Karp.FeedbackVS
