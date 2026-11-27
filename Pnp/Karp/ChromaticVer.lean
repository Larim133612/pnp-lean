import Pnp.Karp.Chromatic
import Pnp.Karp.ColorVer

/-!
# CHROMATIC NUMBER (k-COLORING) ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/Chromatic.lean`, rows `kr :: rows`, `K = |kr|` colors) and a certificate
`y : List Bool`: vertex `i` owns the block of `K` bits `y[iK], …, y[iK + K - 1]` (missing bits
are `false`).  The block must contain a set bit, and the blocks of the two ends of a `pos`
entry must not share a set bit.  Stack layout:

* `0`: the unread certificate bits `R`;  `1`: a full copy of `y`;  `3`: the code of the
  remaining rows `Q`;  `4`: `K` (unary);  `5`: the block `B` of the current row;
* `6`: a work copy of `B` (also the target of the block extraction);  `7`: the column bits `Y`;
* `8`: a temporary;  `9`: a counter;  `10`: one mark per set bit of `B` (unary).

Program (`kcv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3`, `copyVia 0 1 8`: parse the code, copy the certificate;
2. `kcv_frLoop`: read the first row into the unary `K` (halt `false` if there is no row);
3. `kcv_srRow`: start a row: the column bits become `y`; pop `K` bits of `R` into `B`,
   counting the set bits;
4. `kcv_mainLoop`: one symbol per iteration; every symbol pops a block of `K` column bits,
   and at `pos` that block must not share a set bit with `B`; at `sep` the row's block must have
   a set bit (`kcv_endRow`), and the next row is started; at the end of the input, accept.
-/

namespace Pnp.Karp.Chromatic

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics -/

/-- The first `m` bits of `R` (missing bits `false`). -/
def kcv_blk : ℕ → Str → Str
  | 0, _ => []
  | m + 1, R => R.headD false :: kcv_blk m R.tail

/-- The number of set bits among the first `m` bits of `R`. -/
def kcv_cnt : ℕ → Str → ℕ
  | 0, _ => 0
  | m + 1, R => kcv_cnt m R.tail + (if R.headD false then 1 else 0)

/-- Do `B` and `Y` share a set bit (positions `< |B|`)? -/
def kcv_meet : Str → Str → Bool
  | [], _ => false
  | a :: B, Y => (a && Y.headD false) || kcv_meet B Y.tail

/-- Check a row with block `B` against the column bits `Y`. -/
def kcv_rowOk (B : Str) : List SatSym → Str → Bool
  | [], _ => true
  | s :: r, Y => !(isPos s && kcv_meet B Y) && kcv_rowOk B r (Y.drop B.length)

/-- What the main loop computes (`R`: the unread certificate bits at the start of a row). -/
def kcv_go (K : ℕ) (y : Str) : List (List SatSym) → Str → Bool
  | [], _ => true
  | r :: rows, R => kcv_rowOk (kcv_blk K R) r y && decide (0 < kcv_cnt K R) &&
      kcv_go K y rows (R.drop K)

/-- The answer of the verifier on `(w, y)`. -/
def kcv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | kr :: rows => kcv_go kr.length y rows y

theorem kcv_blk_length : ∀ (m : ℕ) (R : Str), (kcv_blk m R).length = m
  | 0, _ => rfl
  | m + 1, R => by simp [kcv_blk, kcv_blk_length m R.tail]

theorem kcv_cnt_le : ∀ (m : ℕ) (R : Str), kcv_cnt m R ≤ m
  | 0, _ => le_rfl
  | m + 1, R => by
    have := kcv_cnt_le m R.tail
    simp only [kcv_cnt]; split <;> omega

/-! ## Stack layout -/

/-- The stacks of the main phase. -/
def kcv_st (R y Q B W Y X F : Str) (K : ℕ) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 1 then y else if j = 3 then Q else
  if j = 4 then List.replicate K true else if j = 5 then B else if j = 6 then W else
  if j = 7 then Y else if j = 9 then X else if j = 10 then F else []

/-- Equality of stack assignments. -/
local macro "kcv_stx" : tactic =>
  `(tactic| (funext j; simp only [kcv_st, update_apply]; split_ifs <;> simp_all))

section St
variable {R y Q B W Y X F : Str} {K : ℕ}
@[simp] theorem kcv_st_0 : kcv_st R y Q B W Y X F K 0 = R := rfl
@[simp] theorem kcv_st_1 : kcv_st R y Q B W Y X F K 1 = y := rfl
@[simp] theorem kcv_st_3 : kcv_st R y Q B W Y X F K 3 = Q := rfl
@[simp] theorem kcv_st_4 : kcv_st R y Q B W Y X F K 4 = List.replicate K true := rfl
@[simp] theorem kcv_st_5 : kcv_st R y Q B W Y X F K 5 = B := rfl
@[simp] theorem kcv_st_6 : kcv_st R y Q B W Y X F K 6 = W := rfl
@[simp] theorem kcv_st_7 : kcv_st R y Q B W Y X F K 7 = Y := rfl
@[simp] theorem kcv_st_8 : kcv_st R y Q B W Y X F K 8 = [] := rfl
@[simp] theorem kcv_st_9 : kcv_st R y Q B W Y X F K 9 = X := rfl
@[simp] theorem kcv_st_10 : kcv_st R y Q B W Y X F K 10 = F := rfl
theorem kcv_u0 (R' : Str) : update (kcv_st R y Q B W Y X F K) 0 R' = kcv_st R' y Q B W Y X F K := by
  kcv_stx
theorem kcv_u1 (y' : Str) : update (kcv_st R y Q B W Y X F K) 1 y' = kcv_st R y' Q B W Y X F K := by
  kcv_stx
theorem kcv_u3 (Q' : Str) : update (kcv_st R y Q B W Y X F K) 3 Q' = kcv_st R y Q' B W Y X F K := by
  kcv_stx
theorem kcv_u4 (K' : ℕ) : update (kcv_st R y Q B W Y X F K) 4 (List.replicate K' true) =
    kcv_st R y Q B W Y X F K' := by kcv_stx
theorem kcv_u5 (B' : Str) : update (kcv_st R y Q B W Y X F K) 5 B' = kcv_st R y Q B' W Y X F K := by
  kcv_stx
theorem kcv_u6 (W' : Str) : update (kcv_st R y Q B W Y X F K) 6 W' = kcv_st R y Q B W' Y X F K := by
  kcv_stx
theorem kcv_u7 (Y' : Str) : update (kcv_st R y Q B W Y X F K) 7 Y' = kcv_st R y Q B W Y' X F K := by
  kcv_stx
theorem kcv_u9 (X' : Str) : update (kcv_st R y Q B W Y X F K) 9 X' = kcv_st R y Q B W Y X' F K := by
  kcv_stx
theorem kcv_u10 (F' : Str) : update (kcv_st R y Q B W Y X F K) 10 F' =
    kcv_st R y Q B W Y X F' K := by kcv_stx
end St

/-! ## Block extraction -/

/-- Pop a bit of `R` (missing: `false`) onto `W`, marking a set bit. -/
def kcv_exBody : Cmd :=
  .pop 0 (.push 6 false) (.push 6 false) (.seq (.push 6 true) (.push 10 true))

def kcv_exB : Cmd := .pop 9 .brk kcv_exBody kcv_exBody

def kcv_exLoop : Cmd := .loop kcv_exB

section Ex
variable {y Q B Y : Str} {K : ℕ}

theorem kcv_ex_exBody (R W X F : Str) :
    ExecLe kcv_exBody (kcv_st R y Q B W Y X F K)
      (.norm (kcv_st R.tail y Q B (R.headD false :: W) Y X
        (if R.headD false then true :: F else F) K)) 3 := by
  rcases R with _ | ⟨_ | _, R'⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.push 6 false _)).cast (by simp [kcv_u6]) (by omega)
  · exact (ExecLe.pop_cons (b := false) rfl (by rw [kcv_u0]; exact ExecLe.push 6 false _)).cast
      (by simp [kcv_u6]) (by omega)
  · exact (ExecLe.pop_cons (b := true) rfl (by
      rw [kcv_u0]; exact (ExecLe.push 6 true _).seq_norm (ExecLe.push 10 true _))).cast
      (by simp [kcv_u6, kcv_u10]) (by omega)

theorem kcv_drop_succ (R : Str) (m : ℕ) : R.drop (m + 1) = R.tail.drop m := by
  cases R <;> simp

theorem kcv_rep_if (a : ℕ) (b : Bool) (F : Str) :
    List.replicate a true ++ (if b then true :: F else F) =
      List.replicate (a + if b then 1 else 0) true ++ F := by
  cases b <;> simp [List.replicate_succ']

theorem kcv_ex_exLoop : ∀ (m : ℕ) (R W F : Str),
    ExecLe kcv_exLoop (kcv_st R y Q B W Y (List.replicate m true) F K)
      (.norm (kcv_st (R.drop m) y Q B ((kcv_blk m R).reverse ++ W) Y []
        (List.replicate (kcv_cnt m R) true ++ F) K)) (4 * m + 2)
  | 0, R, W, F => (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [kcv_blk, kcv_cnt]) (by omega)
  | m + 1, R, W, F => by
    have hb : ExecLe kcv_exB (kcv_st R y Q B W Y (List.replicate (m + 1) true) F K)
        (.norm (kcv_st R.tail y Q B (R.headD false :: W) Y (List.replicate m true)
          (if R.headD false then true :: F else F) K)) 4 :=
      ExecLe.pop_cons (b := true) (s := List.replicate m true) rfl
        (by rw [kcv_u9]; exact kcv_ex_exBody R W _ F)
    have ih := kcv_ex_exLoop m R.tail (R.headD false :: W)
      (if R.headD false then true :: F else F)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    rw [kcv_drop_succ, kcv_rep_if]
    simp [kcv_blk, kcv_cnt]

end Ex

/-! ## Rows -/

/-- Start a row: column bits `y`, the block of the row from `R`. -/
def kcv_srRow : Cmd :=
  .seq (copyVia 1 7 8) (.seq (copyVia 4 9 8) (.seq kcv_exLoop (move 6 5)))

section Row
variable {y : Str} {K : ℕ}

theorem kcv_ex_srRow (R Q : Str) :
    ExecLe kcv_srRow (kcv_st R y Q [] [] [] [] [] K)
      (.norm (kcv_st (R.drop K) y Q (kcv_blk K R) [] y [] (List.replicate (kcv_cnt K R) true) K))
      (5 * y.length + 11 * K + 12) := by
  have h1 := exec_copyVia (a := 1) (b := 7) (t := 8) (by decide) (by decide) (by decide)
    (kcv_st R y Q [] [] [] [] [] K) rfl
  rw [kcv_st_1, kcv_st_7, List.append_nil, kcv_u7] at h1
  have h2 := exec_copyVia (a := 4) (b := 9) (t := 8) (by decide) (by decide) (by decide)
    (kcv_st R y Q [] [] y [] [] K) rfl
  rw [kcv_st_4, kcv_st_9, List.append_nil, kcv_u9] at h2
  have h3 := kcv_ex_exLoop (y := y) (Q := Q) (B := []) (Y := y) (K := K) K R [] []
  rw [List.append_nil, List.append_nil] at h3
  have h4 := exec_move (a := 6) (b := 5) (by decide) _
    (kcv_st (R.drop K) y Q [] (kcv_blk K R).reverse y [] (List.replicate (kcv_cnt K R) true) K) rfl
  rw [kcv_st_5, kcv_st_6, List.append_nil, List.reverse_reverse, kcv_u6, kcv_u5] at h4
  refine ((ExecLe.of h1).seq_norm ((ExecLe.of h2).seq_norm (h3.seq_norm (ExecLe.of h4)))).cast
    rfl ?_
  simp [kcv_blk_length]; omega

/-- Compare the work copy of the block with the column bits (`ok`: the symbol is `pos`). -/
def kcv_cmpB (ok : Bool) : Cmd :=
  .pop 6 .brk (.pop 7 .skip .skip .skip) (.pop 7 .skip .skip (if ok then .halt false else .skip))

def kcv_cmpLoop (ok : Bool) : Cmd := .loop (kcv_cmpB ok)

theorem kcv_ex_cmpB (ok : Bool) (R Q B F : Str) (a : Bool) (W Y : Str) :
    ExecLe (kcv_cmpB ok) (kcv_st R y Q B (a :: W) Y [] F K)
      (if ok && a && Y.headD false then .halt false else .norm (kcv_st R y Q B W Y.tail [] F K))
      3 := by
  cases a
  · rcases Y with _ | ⟨_ | _, Y'⟩
    · exact (ExecLe.pop_cons (b := false) rfl (by
        rw [kcv_u6]; exact ExecLe.pop_nil rfl (ExecLe.skip _))).cast (by simp) (by omega)
    · exact (ExecLe.pop_cons (b := false) rfl (by
        rw [kcv_u6]; exact ExecLe.pop_cons (b := false) rfl (by rw [kcv_u7]; exact ExecLe.skip _))).cast
        (by simp) (by omega)
    · exact (ExecLe.pop_cons (b := false) rfl (by
        rw [kcv_u6]; exact ExecLe.pop_cons (b := true) rfl (by rw [kcv_u7]; exact ExecLe.skip _))).cast
        (by simp) (by omega)
  · rcases Y with _ | ⟨_ | _, Y'⟩
    · exact (ExecLe.pop_cons (b := true) rfl (by
        rw [kcv_u6]; exact ExecLe.pop_nil rfl (ExecLe.skip _))).cast (by simp) (by omega)
    · exact (ExecLe.pop_cons (b := true) rfl (by
        rw [kcv_u6]; exact ExecLe.pop_cons (b := false) rfl (by rw [kcv_u7]; exact ExecLe.skip _))).cast
        (by simp) (by omega)
    · cases ok
      · exact (ExecLe.pop_cons (b := true) rfl (by
          rw [kcv_u6]; exact ExecLe.pop_cons (b := true) rfl (by
            rw [kcv_u7]; exact ExecLe.skip _))).cast (by simp) (by omega)
      · exact (ExecLe.pop_cons (b := true) rfl (by
          rw [kcv_u6]; exact ExecLe.pop_cons (b := true) rfl (ExecLe.halt false _))).cast
          (by simp) (by omega)

theorem kcv_ex_cmp (ok : Bool) (R Q B F : Str) : ∀ (W Y : Str),
    ExecLe (kcv_cmpLoop ok) (kcv_st R y Q B W Y [] F K)
      (if ok && kcv_meet W Y then .halt false
        else .norm (kcv_st R y Q B [] (Y.drop W.length) [] F K)) (3 * W.length + 2)
  | [], Y => (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [kcv_meet]) (by simp)
  | a :: W, Y => by
    have hb := kcv_ex_cmpB (y := y) (K := K) ok R Q B F a W Y
    cases hc : (ok && a && Y.headD false)
    · rw [hc] at hb; simp only [Bool.false_eq_true, if_false] at hb
      have ih := kcv_ex_cmp ok R Q B F W Y.tail
      refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
      have e : (ok && kcv_meet (a :: W) Y) = (ok && kcv_meet W Y.tail) := by
        simp only [kcv_meet]
        cases ok <;> simp_all
      rw [e]
      cases Y <;> simp
    · rw [hc] at hb; simp only [if_true] at hb
      refine (ExecLe.loop_halt hb).cast ?_ (by simp; omega)
      have e : (ok && kcv_meet (a :: W) Y) = true := by
        simp only [kcv_meet]
        cases ok <;> cases a <;> simp_all
      rw [e]; rfl

/-- One column of a row (`ok`: the symbol is `pos`). -/
def kcv_colStep (ok : Bool) : Cmd := .seq (copyVia 5 6 8) (kcv_cmpLoop ok)

theorem kcv_ex_colStep (ok : Bool) (R Q B Y F : Str) :
    ExecLe (kcv_colStep ok) (kcv_st R y Q B [] Y [] F K)
      (if ok && kcv_meet B Y then .halt false
        else .norm (kcv_st R y Q B [] (Y.drop B.length) [] F K)) (8 * B.length + 6) := by
  have h1 := exec_copyVia (a := 5) (b := 6) (t := 8) (by decide) (by decide) (by decide)
    (kcv_st R y Q B [] Y [] F K) rfl
  rw [kcv_st_5, kcv_st_6, List.append_nil, kcv_u6] at h1
  exact ((ExecLe.of h1).seq_norm (kcv_ex_cmp ok R Q B F B Y)).cast rfl (by omega)

/-- End of a row: the block must have a set bit; clear the marks, the block and the column
bits. -/
def kcv_endRow : Cmd :=
  .seq (.pop 10 (.halt false) .skip .skip) (.seq (drain 10) (.seq (drain 5) (drain 7)))

theorem kcv_ex_endRow (R Q B Y : Str) (c : ℕ) :
    ExecLe kcv_endRow (kcv_st R y Q B [] Y [] (List.replicate c true) K)
      (if 0 < c then .norm (kcv_st R y Q [] [] [] [] [] K) else .halt false)
      (2 * c + 2 * B.length + 2 * Y.length + 8) := by
  rcases c with _ | c
  · exact (ExecLe.seq_halt (ExecLe.pop_nil rfl (ExecLe.halt false _))).cast (by simp) (by omega)
  · have h1 : ExecLe (.pop 10 (.halt false) .skip .skip)
        (kcv_st R y Q B [] Y [] (List.replicate (c + 1) true) K)
        (.norm (kcv_st R y Q B [] Y [] (List.replicate c true) K)) 2 :=
      (ExecLe.pop_cons (b := true) (s := List.replicate c true) rfl (ExecLe.skip _)).cast
        (by rw [kcv_u10]) le_rfl
    have h2 := exec_drain 10 _ (kcv_st R y Q B [] Y [] (List.replicate c true) K) rfl
    rw [kcv_u10] at h2
    have h3 := exec_drain 5 _ (kcv_st R y Q B [] Y [] [] K) rfl
    rw [kcv_u5] at h3
    have h4 := exec_drain 7 _ (kcv_st R y Q [] [] Y [] [] K) rfl
    rw [kcv_u7] at h4
    refine (h1.seq_norm ((ExecLe.of h2).seq_norm ((ExecLe.of h3).seq_norm (ExecLe.of h4)))).cast
      (by simp) ?_
    simp; omega

/-- Loop body of the main phase. -/
def kcv_mainB : Cmd :=
  .pop 3 (.halt true) (.pop 3 (.halt false) (.seq kcv_endRow kcv_srRow) (kcv_colStep false))
    (.pop 3 (.halt false) (kcv_colStep true) (kcv_colStep false))

def kcv_mainLoop : Cmd := .loop kcv_mainB

variable {R Q B W Y X F : Str}

theorem kcv_mainB_sym {s : SatSym} (hs : s ≠ sep) {r : Res} {T : ℕ}
    (h : ExecLe (kcv_colStep (isPos s)) (kcv_st R y Q B W Y X F K) r T) :
    ExecLe kcv_mainB (kcv_st R y (ic s ++ Q) B W Y X F K) r (T + 2) := by
  cases s with
  | sep => exact absurd rfl hs
  | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [kcv_u3, isPos] using h))
  | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [kcv_u3, isPos] using h))
  | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [kcv_u3, isPos] using h))

theorem kcv_mainB_sep {r : Res} {T : ℕ}
    (h : ExecLe (.seq kcv_endRow kcv_srRow) (kcv_st R y Q B W Y X F K) r T) :
    ExecLe kcv_mainB (kcv_st R y (false :: false :: Q) B W Y X F K) r (T + 2) :=
  ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [kcv_u3] using h))

/-- One row (`R`: the unread certificate bits, i.e. those of the next row). -/
theorem kcv_ex_row (N : ℕ) (hy : y.length ≤ N) (hK : K ≤ N) (R Q' B : Str) (c : ℕ)
    (hB : B.length ≤ N) (hc : c ≤ N) : ∀ (r : List SatSym) (Y : Str),
    sep ∉ r → Y.length ≤ N → ∀ (res : Res) (T' : ℕ),
    ExecLe kcv_mainLoop (kcv_st (R.drop K) y Q' (kcv_blk K R) [] y []
      (List.replicate (kcv_cnt K R) true) K) res T' →
    ExecLe kcv_mainLoop (kcv_st R y (r.flatMap ic ++ false :: false :: Q') B [] Y []
        (List.replicate c true) K)
      (if kcv_rowOk B r Y then (if 0 < c then res else .halt false) else .halt false)
      (T' + (r.length * (8 * N + 8) + 24 * N + 22))
  | [], Y, _, hY, res, T', h => by
    have he := kcv_ex_endRow (y := y) (K := K) R Q' B Y c
    by_cases hc0 : 0 < c
    · rw [if_pos hc0] at he
      have hb := kcv_mainB_sep (he.seq_norm (kcv_ex_srRow R Q'))
      exact (ExecLe.loop_norm hb h).cast (by simp [kcv_rowOk, hc0]) (by simp; omega)
    · rw [if_neg hc0] at he
      exact (ExecLe.loop_halt (kcv_mainB_sep (ExecLe.seq_halt he))).cast
        (by simp [kcv_rowOk, hc0]) (by omega)
  | s :: r, Y, hr, hY, res, T', h => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have hcs := kcv_ex_colStep (y := y) (K := K) (isPos s) R
      (r.flatMap ic ++ false :: false :: Q') B Y (List.replicate c true)
    have hb := kcv_mainB_sym (Q := r.flatMap ic ++ false :: false :: Q') hs hcs
    simp only [List.flatMap_cons, List.append_assoc]
    cases hm : (isPos s && kcv_meet B Y)
    · rw [hm] at hb; simp only [Bool.false_eq_true, if_false] at hb
      have ih := kcv_ex_row N hy hK R Q' B c hB hc r (Y.drop B.length) hr'
        (by simp; omega) res T' h
      refine (ExecLe.loop_norm hb ih).cast (by simp [kcv_rowOk, hm]) ?_
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      have : B.length * 8 ≤ N * 8 := Nat.mul_le_mul_right _ hB
      omega
    · rw [hm] at hb; simp only [if_true] at hb
      refine (ExecLe.loop_halt hb).cast (by simp [kcv_rowOk, hm]) ?_
      have : B.length * 8 ≤ N * 8 := Nat.mul_le_mul_right _ hB
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Cost of the main phase. -/
def kcv_Trows (N : ℕ) : List (List SatSym) → ℕ
  | [] => 2
  | r :: rows => r.length * (8 * N + 8) + 24 * N + 22 + kcv_Trows N rows

theorem kcv_ex_rows (N : ℕ) (hy : y.length ≤ N) (hK : K ≤ N) :
    ∀ (rows : List (List SatSym)) (R : Str), (∀ r ∈ rows, sep ∉ r) →
    ExecLe kcv_mainLoop (kcv_st (R.drop K) y (enc rows) (kcv_blk K R) [] y []
      (List.replicate (kcv_cnt K R) true) K) (.halt (kcv_go K y rows R)) (kcv_Trows N rows)
  | [], R, _ => (ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt true _))).cast
      (by simp [kcv_go]) (by simp [kcv_Trows])
  | r :: rows, R, hrows => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    have ih := kcv_ex_rows N hy hK rows (R.drop K) hrs
    rw [enc_cons]
    have := kcv_ex_row N hy hK (R.drop K) (enc rows) (kcv_blk K R) (kcv_cnt K R)
      (by rw [kcv_blk_length]; exact hK) ((kcv_cnt_le K R).trans hK) r y hr hy _ _ ih
    refine this.cast ?_ (by simp [kcv_Trows]; omega)
    simp only [kcv_go]
    cases kcv_rowOk (kcv_blk K R) r y <;> by_cases h0 : 0 < kcv_cnt K R <;> simp [h0]

end Row

/-! ## The first row -/

def kcv_frB : Cmd :=
  .pop 3 (.halt false) (.pop 3 (.halt false) .brk (.push 4 true))
    (.pop 3 (.halt false) (.push 4 true) (.push 4 true))

def kcv_frLoop : Cmd := .loop kcv_frB

theorem kcv_ex_frLoop (R y B W Y X F Q' : Str) : ∀ (kr : List SatSym) (K : ℕ),
    sep ∉ kr → ExecLe kcv_frLoop (kcv_st R y (kr.flatMap ic ++ false :: false :: Q') B W Y X F K)
      (.norm (kcv_st R y Q' B W Y X F (K + kr.length))) (3 * kr.length + 3)
  | [], K, _ => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) rfl
      (ExecLe.pop_cons (b := false) (s := Q') (by simp) (ExecLe.brk _)))).cast
      (by simp [kcv_u3]) (by simp)
  | s :: kr, K, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := kcv_ex_frLoop R y B W Y X F Q' kr (K + 1) (fun e => hr (List.mem_cons_of_mem _ e))
    set Q := kr.flatMap ic ++ false :: false :: Q'
    have hb : ExecLe kcv_frB (kcv_st R y (ic s ++ Q) B W Y X F K)
        (.norm (kcv_st R y Q B W Y X F (K + 1))) 3 := by
      have hp : ExecLe (.push 4 true) (kcv_st R y Q B W Y X F K)
          (.norm (kcv_st R y Q B W Y X F (K + 1))) 1 :=
        (ExecLe.push 4 true _).cast (by rw [kcv_st_4, ← List.replicate_succ, kcv_u4]) le_rfl
      cases s with
      | sep => exact absurd rfl hs
      | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
          (by simp) (by simpa [kcv_u3] using hp))
      | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
          (by simp) (by simpa [kcv_u3] using hp))
      | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
          (by simp) (by simpa [kcv_u3] using hp))
    refine (ExecLe.loop_norm (by simpa [Q] using hb) ih).cast (by simp; ring_nf) (by simp; omega)

/-! ## The whole verifier -/

def kcv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq (copyVia 0 1 8)
    (.seq kcv_frLoop (.seq kcv_srRow kcv_mainLoop)))))

/-- Time bound of the verifier. -/
def kcv_Tver (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (5 * n + 4) + (3 * n + 3) +
  (16 * n + 12) + (n * (8 * n + 8) + n * (24 * n + 22) + 2)

theorem kcv_Trows_eq (N : ℕ) : ∀ rows : List (List SatSym),
    kcv_Trows N rows = (rows.map List.length).sum * (8 * N + 8) + rows.length * (24 * N + 22) + 2
  | [] => by simp [kcv_Trows]
  | r :: rows => by
    simp only [kcv_Trows, kcv_Trows_eq N rows, List.map_cons, List.sum_cons, List.length_cons]
    ring

theorem kcv_exec_ver (z : Str) :
    ExecLe kcv_ver (init [z]).stk (.halt (kcv_vres (dec z).1 (dec z).2)) (kcv_Tver z.length) := by
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
      kcv_st y [] (enc (clauses w)) [] [] [] [] [] 0 := by
    funext j
    simp only [σ₂, σ₁, kcv_st, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hC := exec_copyVia (a := 0) (b := 1) (t := 8) (by decide) (by decide) (by decide)
    (kcv_st y [] (enc (clauses w)) [] [] [] [] [] 0) rfl
  rw [kcv_st_0, kcv_st_1, List.append_nil, kcv_u1] at hC
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ),
      ExecLe c (kcv_st y y (enc (clauses w)) [] [] [] [] [] 0) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq (copyVia 0 1 8) c))))
        (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 +
          (5 * y.length + 4 + T)))) := by
    intro c r T h
    refine hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm ((ExecLe.of hC).seq_norm h))) |>.cast
      rfl ?_
    simp
  unfold kcv_vres kcv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq kcv_frLoop (.seq kcv_srRow kcv_mainLoop))
        (kcv_st y y (enc []) [] [] [] [] [] 0) (.halt false) 2 :=
      ExecLe.seq_halt (ExecLe.loop_halt ((ExecLe.pop_nil rfl (ExecLe.halt false _)).cast rfl le_rfl))
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, kcv_Tver]; nlinarith
  · rw [hcw] at hsum hcl hsep hpre
    rw [enc_cons] at hpre
    have hF := kcv_ex_frLoop y y [] [] [] [] [] (enc rows) kr 0 (hsep kr (by simp))
    have hS := kcv_ex_srRow (y := y) (K := 0 + kr.length) y (enc rows)
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum hcl
    have hR := kcv_ex_rows (y := y) (K := 0 + kr.length) z.length (by omega) (by omega) rows y
      (fun r hr => hsep r (by simp [hr]))
    refine (hpre _ _ _ (hF.seq_norm (hS.seq_norm hR))).cast (by simp) ?_
    rw [kcv_Trows_eq]
    simp only [htl, kcv_Tver]
    have h1 : (rows.map List.length).sum * (8 * z.length + 8) ≤ z.length * (8 * z.length + 8) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : rows.length * (24 * z.length + 22) ≤ z.length * (24 * z.length + 22) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem kcv_Tver_le (n : ℕ) : kcv_Tver n ≤ tb 7 n := by
  unfold kcv_Tver tb
  have hm : 2 ^ 5 ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  norm_num at hm
  have e : (n + 2) ^ 7 = (n + 2) ^ 5 * (n + 2) ^ 2 := by ring
  have : 32 * (n + 2) ^ 2 ≤ (n + 2) ^ 5 * (n + 2) ^ 2 := Nat.mul_le_mul_right _ hm
  nlinarith

end Pnp.Karp.Chromatic
