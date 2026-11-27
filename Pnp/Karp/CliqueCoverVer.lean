import Pnp.Karp.CliqueCover
import Pnp.Karp.CliqueVer

/-!
# CLIQUE COVER ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/CliqueCover.lean`, rows `kr :: rows`, `k = |kr|`) and a certificate `y : List Bool`:
vertex `v` belongs to class `t < k` iff bit `v * k + t` of `y` is set (missing bits are
`false`).  Stack layout:

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the bound `k` (unary);  `6`: the certificate blocks read so far `Dn` (reversed);
* `7`: the column bits `Y` of the current row (the certificate with the block of the row
  cleared);  `8`: a temporary;  `9`: the flag "the row has a class" (nonempty);
* `10`: the block `A` of the current row;  `11`: a copy of `A`;  `12`: a counter;
  `13`: the block being read (reversed).

Program (`ccv_ver`):
1. `phaseA`; `trimC 2`; `move 2 3`; `ccv_frLoop`: read the first row into the unary `k`;
2. `ccv_srRow` ("start row"): pop the next `k` bits of `R` (the block `A`), set the flag if one
   of them is set, build the column bits `Dn.reverse ++ false^k ++ R`;
3. `ccv_mainL`: one symbol per iteration; every symbol pops a block of `k` column bits, and if
   the symbol is not `pos`, that block must not share a set bit with `A`; at `sep` the flag must
   be set, the remaining column blocks must not share a set bit with `A` (`ccv_restL`), and the
   next row is started; at the end of the input, accept.
-/

namespace Pnp.Karp.CliqueCover

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics -/

/-- `A` and the first `|A|` bits of `Y` share a set bit. -/
def ccv_hits : Str → Str → Bool
  | [], _ => false
  | a :: A, Y => (a && Y.headD false) || ccv_hits A Y.tail

/-- No block of `Y` (blocks of length `|A|`) shares a set bit with `A`. -/
def ccv_rest (A Y : Str) : Bool :=
  if _h : A = [] ∨ Y = [] then true else !ccv_hits A Y && ccv_rest A (Y.drop A.length)
termination_by Y.length
decreasing_by
  simp only [not_or] at _h
  have h1 : 0 < A.length := List.length_pos_of_ne_nil _h.1
  have h2 : 0 < Y.length := List.length_pos_of_ne_nil _h.2
  simp only [List.length_drop]; omega

/-- The first `m` bits (missing bits `false`). -/
def ccv_blk : ℕ → Str → Str
  | 0, _ => []
  | m + 1, R => R.headD false :: ccv_blk m R.tail

/-- Push a mark onto `F` for each set bit of the list. -/
def ccv_fp : Str → Str → Str
  | [], F => F
  | b :: B, F => ccv_fp B (if b then true :: F else F)

/-- Check a row (block `A`, flag `F`) against the column bits `Y`. -/
def ccv_rowOk (A F : Str) : List SatSym → Str → Bool
  | [], Y => !F.isEmpty && ccv_rest A Y
  | s :: r, Y => (isPos s || !ccv_hits A Y) && ccv_rowOk A F r (Y.drop A.length)

/-- The column bits of a row. -/
def ccv_Y (K : ℕ) (R Dn : Str) : Str := Dn.reverse ++ List.replicate K false ++ R.drop K

/-- What the main loop computes. -/
def ccv_go (K : ℕ) : List (List SatSym) → Str → Str → Bool
  | [], _, _ => true
  | r :: rows, R, Dn => ccv_rowOk (ccv_blk K R) (ccv_fp (ccv_blk K R) []) r (ccv_Y K R Dn) &&
      ccv_go K rows (R.drop K) ((ccv_blk K R).reverse ++ Dn)

/-- The answer of the verifier on `(w, y)`. -/
def ccv_res (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | kr :: rows => ccv_go kr.length rows y []

@[simp] theorem ccv_length_blk : ∀ (m : ℕ) (R : Str), (ccv_blk m R).length = m
  | 0, _ => rfl
  | m + 1, R => by simp [ccv_blk, ccv_length_blk m]

theorem ccv_length_fp : ∀ (B F : Str), (ccv_fp B F).length ≤ B.length + F.length
  | [], F => by simp [ccv_fp]
  | b :: B, F => by
    have := ccv_length_fp B (if b then true :: F else F)
    have h2 : (if b then true :: F else F).length ≤ F.length + 1 := by split <;> simp
    simp only [ccv_fp, List.length_cons]; omega

theorem ccv_fp_nil_ne : ∀ (B : Str), ccv_fp B [] ≠ [] → B ≠ []
  | [], h => absurd rfl h
  | _ :: _, _ => List.cons_ne_nil _ _

/-! ## Stack layout -/

/-- The stacks of the main phase. -/
def ccv_st (K : ℕ) (R Q Dn Y A F : Str) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 4 then List.replicate K true else
  if j = 6 then Dn else if j = 7 then Y else if j = 9 then F else if j = 10 then A else []

/-- Equality of stack assignments. -/
local macro "ccx" : tactic =>
  `(tactic| (funext j; rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|_|j <;>
    simp [ccv_st, update_apply]))

section St
variable {K : ℕ} {R Q Dn Y A F : Str}
@[simp] theorem ccv_st_0 : ccv_st K R Q Dn Y A F 0 = R := rfl
@[simp] theorem ccv_st_3 : ccv_st K R Q Dn Y A F 3 = Q := rfl
@[simp] theorem ccv_st_4 : ccv_st K R Q Dn Y A F 4 = List.replicate K true := rfl
@[simp] theorem ccv_st_6 : ccv_st K R Q Dn Y A F 6 = Dn := rfl
@[simp] theorem ccv_st_7 : ccv_st K R Q Dn Y A F 7 = Y := rfl
@[simp] theorem ccv_st_8 : ccv_st K R Q Dn Y A F 8 = [] := rfl
@[simp] theorem ccv_st_9 : ccv_st K R Q Dn Y A F 9 = F := rfl
@[simp] theorem ccv_st_10 : ccv_st K R Q Dn Y A F 10 = A := rfl
@[simp] theorem ccv_st_11 : ccv_st K R Q Dn Y A F 11 = [] := rfl
@[simp] theorem ccv_st_12 : ccv_st K R Q Dn Y A F 12 = [] := rfl
@[simp] theorem ccv_st_13 : ccv_st K R Q Dn Y A F 13 = [] := rfl
theorem ccv_u0 (R' : Str) : update (ccv_st K R Q Dn Y A F) 0 R' = ccv_st K R' Q Dn Y A F := by ccx
theorem ccv_u3 (Q' : Str) : update (ccv_st K R Q Dn Y A F) 3 Q' = ccv_st K R Q' Dn Y A F := by ccx
theorem ccv_u4 (K' : ℕ) : update (ccv_st K R Q Dn Y A F) 4 (List.replicate K' true) =
    ccv_st K' R Q Dn Y A F := by ccx
theorem ccv_u7 (Y' : Str) : update (ccv_st K R Q Dn Y A F) 7 Y' = ccv_st K R Q Dn Y' A F := by ccx
theorem ccv_u9 (F' : Str) : update (ccv_st K R Q Dn Y A F) 9 F' = ccv_st K R Q Dn Y A F' := by ccx
theorem ccv_u10 (A' : Str) : update (ccv_st K R Q Dn Y A F) 10 A' = ccv_st K R Q Dn Y A' F := by
  ccx
end St

/-! ## One column -/

/-- Halt `false` (when `ok` is not set). -/
def ccv_bad (ok : Bool) : Cmd := if ok then .skip else .halt false

/-- Loop body: pop a bit of the copy of `A` and a column bit. -/
def ccv_blkB (ok : Bool) : Cmd :=
  .pop 11 .brk (.pop 7 .skip .skip .skip) (.pop 7 .skip .skip (ccv_bad ok))

def ccv_blkL (ok : Bool) : Cmd := .loop (ccv_blkB ok)

section Col
variable (ok : Bool) (K : ℕ) (R Q Dn A F : Str)

theorem ccv_step (a b : Bool) (T Y : Str) :
    ExecLe (ccv_blkB ok) (update (ccv_st K R Q Dn (b :: Y) A F) 11 (a :: T))
      (if a && b && !ok then .halt false else .norm (update (ccv_st K R Q Dn Y A F) 11 T)) 3 := by
  refine ExecLe.pop_cons (b := a) (s := T) (by simp) ?_
  have e : update (update (update (ccv_st K R Q Dn (b :: Y) A F) 11 (a :: T)) 11 T) 7 Y =
      update (ccv_st K R Q Dn Y A F) 11 T := by ccx
  cases a
  · refine ExecLe.pop_cons (b := b) (s := Y) (by simp) ?_
    rw [e]
    cases b <;> exact (ExecLe.skip _).cast (by simp) le_rfl
  · refine ExecLe.pop_cons (b := b) (s := Y) (by simp) ?_
    rw [e]
    cases b
    · exact (ExecLe.skip _).cast (by simp) le_rfl
    · cases ok
      · exact (ExecLe.halt false _).cast (by simp) le_rfl
      · exact (ExecLe.skip _).cast (by simp) le_rfl

theorem ccv_ex_blkL : ∀ (T Y : Str),
    ExecLe (ccv_blkL ok) (update (ccv_st K R Q Dn Y A F) 11 T)
      (if !ok && ccv_hits T Y then .halt false else .norm (ccv_st K R Q Dn (Y.drop T.length) A F))
      (3 * T.length + 2)
  | [], Y => (ExecLe.loop_brk (ExecLe.pop_nil (by simp) (ExecLe.brk _))).cast
      (by simp only [ccv_hits, Bool.and_false]; simp only [Bool.false_eq_true, if_false,
        List.length_nil, List.drop_zero]; congr 1; ccx) (by simp)
  | a :: T, [] => by
    have hb : ExecLe (ccv_blkB ok) (update (ccv_st K R Q Dn [] A F) 11 (a :: T))
        (.norm (update (ccv_st K R Q Dn [] A F) 11 T)) 3 := by
      refine ExecLe.pop_cons (b := a) (s := T) (by simp) ?_
      rw [update_idem]
      cases a <;> exact ExecLe.pop_nil (by simp) (ExecLe.skip _)
    have ih := ccv_ex_blkL T []
    exact (ExecLe.loop_norm hb ih).cast (by simp [ccv_hits]) (by simp; omega)
  | a :: T, b :: Y => by
    have hs := ccv_step ok K R Q Dn A F a b T Y
    have ih := ccv_ex_blkL T Y
    by_cases h : (a && b && !ok) = true
    · rw [if_pos h] at hs
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact (ExecLe.loop_halt hs).cast (by simp [ccv_hits]) (by simp; omega)
    · rw [if_neg h] at hs
      refine (ExecLe.loop_norm hs ih).cast ?_ (by simp; omega)
      cases a <;> cases b <;> cases ok <;> simp_all [ccv_hits]

/-- One column of a row (`ok`: the symbol is `pos`). -/
def ccv_col (ok : Bool) : Cmd := .seq (copyVia 10 11 8) (ccv_blkL ok)

theorem ccv_ex_col (Y : Str) :
    ExecLe (ccv_col ok) (ccv_st K R Q Dn Y A F)
      (if !ok && ccv_hits A Y then .halt false else .norm (ccv_st K R Q Dn (Y.drop A.length) A F))
      (8 * A.length + 6) := by
  have h1 := exec_copyVia (a := 10) (b := 11) (t := 8) (by decide) (by decide) (by decide)
    (ccv_st K R Q Dn Y A F) rfl
  rw [ccv_st_10, ccv_st_11, List.append_nil] at h1
  exact ((ExecLe.of h1).seq_norm (ccv_ex_blkL ok K R Q Dn A F A Y)).cast rfl (by omega)

end Col

/-! ## The remaining columns of a row -/

def ccv_restB : Cmd :=
  .pop 7 .brk (.seq (.push 7 false) (ccv_col false)) (.seq (.push 7 true) (ccv_col false))

def ccv_restL : Cmd := .loop ccv_restB

theorem ccv_rest_cons (A : Str) (hA : A ≠ []) (b : Bool) (Y : Str) :
    ccv_rest A (b :: Y) = (!ccv_hits A (b :: Y) && ccv_rest A ((b :: Y).drop A.length)) := by
  rw [ccv_rest]; simp [hA]

theorem ccv_rest_nil (A : Str) : ccv_rest A [] = true := by
  rw [ccv_rest]; simp

theorem ccv_ex_restL (K : ℕ) (R Q Dn A : Str) (hA : A ≠ []) : ∀ (n : ℕ) (Y : Str), Y.length ≤ n →
    ExecLe ccv_restL (ccv_st K R Q Dn Y A [])
      (if ccv_rest A Y then .norm (ccv_st K R Q Dn [] A []) else .halt false)
      (n * (8 * A.length + 8) + 2)
  | n, [], _ => (ExecLe.loop_brk (ExecLe.pop_nil (by simp) (ExecLe.brk _))).cast
      (by simp [ccv_rest_nil]) (by omega)
  | 0, b :: Y, h => by simp at h
  | n + 1, b :: Y, hY => by
    have hcol := ccv_ex_col false K R Q Dn A [] (b :: Y)
    have hb : ExecLe ccv_restB (ccv_st K R Q Dn (b :: Y) A [])
        (if !false && ccv_hits A (b :: Y) then .halt false
          else .norm (ccv_st K R Q Dn ((b :: Y).drop A.length) A [])) (8 * A.length + 8) := by
      refine ExecLe.pop_cons (b := b) (s := Y) (by simp) ?_
      have e : update (update (ccv_st K R Q Dn (b :: Y) A []) 7 Y) 7
          (b :: update (ccv_st K R Q Dn (b :: Y) A []) 7 Y 7) = ccv_st K R Q Dn (b :: Y) A [] := by
        ccx
      cases b
      · exact (((ExecLe.push 7 false _).cast (by rw [e]) le_rfl).seq_norm hcol).cast rfl
          (by omega)
      · exact (((ExecLe.push 7 true _).cast (by rw [e]) le_rfl).seq_norm hcol).cast rfl
          (by omega)
    have hl : 0 < A.length := List.length_pos_of_ne_nil hA
    rw [ccv_rest_cons A hA]
    cases hh : ccv_hits A (b :: Y)
    · simp only [hh, Bool.not_false, Bool.and_false, Bool.false_eq_true, if_false] at hb
      have ih := ccv_ex_restL K R Q Dn A hA n ((b :: Y).drop A.length)
        (by simp only [List.length_drop, List.length_cons] at hY ⊢; omega)
      exact (ExecLe.loop_norm hb ih).cast (by simp) (by nlinarith)
    · simp only [hh, Bool.not_false, Bool.and_true, if_true] at hb
      exact (ExecLe.loop_halt hb).cast (by simp) (by nlinarith)

/-- End of a row: check the flag and the remaining columns, clear `A`. -/
def ccv_endRow : Cmd := .seq (.pop 9 (.halt false) (drain 9) (drain 9)) (.seq ccv_restL (drain 10))

theorem ccv_ex_endRow (K n : ℕ) (R Q Dn Y A F : Str) (hFA : F ≠ [] → A ≠ []) (hY : Y.length ≤ n) :
    ExecLe ccv_endRow (ccv_st K R Q Dn Y A F)
      (if !F.isEmpty && ccv_rest A Y then .norm (ccv_st K R Q Dn [] [] []) else .halt false)
      (2 * F.length + n * (8 * A.length + 8) + 2 * A.length + 7) := by
  rcases F with _ | ⟨f, F⟩
  · exact (ExecLe.seq_halt (ExecLe.pop_nil (by simp) (ExecLe.halt false _))).cast (by simp)
      (by omega)
  · have hA := hFA (List.cons_ne_nil _ _)
    have hd := exec_drain 9 F (update (ccv_st K R Q Dn Y A (f :: F)) 9 F) (by simp)
    simp only [ccv_u9] at hd
    have h1 : ExecLe (.pop 9 (.halt false) (drain 9) (drain 9)) (ccv_st K R Q Dn Y A (f :: F))
        (.norm (ccv_st K R Q Dn Y A [])) (2 * F.length + 3) :=
      ExecLe.pop_same (b := f) (s := F) (by simp) (by rw [ccv_u9]; exact ExecLe.of hd)
    have h2 := ccv_ex_restL K R Q Dn A hA n Y hY
    cases hr : ccv_rest A Y
    · rw [hr] at h2; simp only [Bool.false_eq_true, if_false] at h2
      exact (h1.seq_norm (ExecLe.seq_halt h2)).cast (by simp) (by simp; omega)
    · rw [hr] at h2; simp only [if_true] at h2
      have h3 := exec_drain 10 A (ccv_st K R Q Dn [] A []) rfl
      rw [ccv_u10] at h3
      exact (h1.seq_norm (h2.seq_norm (ExecLe.of h3))).cast (by simp) (by simp; omega)

/-! ## Starting a row -/

def ccv_popBit : Cmd := .pop 0 (.push 13 false) (.push 13 false) (.seq (.push 13 true) (.push 9 true))
def ccv_popL : Cmd := .loop (.pop 12 .brk ccv_popBit ccv_popBit)
def ccv_fillL : Cmd := .loop (.pop 12 .brk (.push 7 false) (.push 7 false))

theorem ccv_ex_popL (K : ℕ) (Q Dn : Str) : ∀ (m : ℕ) (R P F : Str),
    ExecLe ccv_popL (update (update (ccv_st K R Q Dn [] [] F) 12 (List.replicate m true)) 13 P)
      (.norm (update (ccv_st K (R.drop m) Q Dn [] [] (ccv_fp (ccv_blk m R) F)) 13
        ((ccv_blk m R).reverse ++ P))) (4 * m + 2)
  | 0, R, P, F => (ExecLe.loop_brk (ExecLe.pop_nil (by simp) (ExecLe.brk _))).cast
      (by congr 1; simp only [List.drop_zero, ccv_blk, ccv_fp, List.reverse_nil, List.nil_append]
          ccx) (by omega)
  | m + 1, R, P, F => by
    have hs : ExecLe (.pop 12 .brk ccv_popBit ccv_popBit)
        (update (update (ccv_st K R Q Dn [] [] F) 12 (List.replicate (m + 1) true)) 13 P)
        (.norm (update (update (ccv_st K R.tail Q Dn [] []
          (if R.headD false then true :: F else F)) 12 (List.replicate m true)) 13
          (R.headD false :: P))) 4 := by
      refine ExecLe.pop_same (b := true) (s := List.replicate m true) (by simp [List.replicate_succ]) ?_
      rcases R with _ | ⟨_ | _, R'⟩
      · exact (ExecLe.pop_nil (by simp) ((ExecLe.push 13 false _).cast (by congr 1; ccx) le_rfl)).cast
          rfl (by omega)
      · exact (ExecLe.pop_cons (b := false) (s := R') (by simp)
          ((ExecLe.push 13 false _).cast (by congr 1; ccx) le_rfl)).cast rfl (by omega)
      · exact (ExecLe.pop_cons (b := true) (s := R') (by simp)
          (((ExecLe.push 13 true _).seq_norm (ExecLe.push 9 true _)).cast (by congr 1; ccx)
            le_rfl)).cast rfl (by omega)
    have ih := ccv_ex_popL K Q Dn m R.tail (R.headD false :: P)
      (if R.headD false then true :: F else F)
    refine (ExecLe.loop_norm hs ih).cast ?_ (by omega)
    have e : R.tail.drop m = R.drop (m + 1) := by rcases R with _ | ⟨_, _⟩ <;> simp
    simp only [ccv_blk, ccv_fp, List.reverse_cons, List.append_assoc, List.singleton_append, e]

theorem ccv_ex_fillL : ∀ (m : ℕ) (σ : ℕ → Str), σ 12 = List.replicate m true →
    ExecLe ccv_fillL σ (.norm (update (update σ 12 []) 7 (List.replicate m false ++ σ 7)))
      (2 * m + 2)
  | 0, σ, h => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk _))).cast
      (by
        congr 1; funext j
        by_cases h7 : j = 7
        · subst h7; simp
        · by_cases h12 : j = 12
          · subst h12; simp [h]
          · simp [h7, h12]) (by omega)
  | m + 1, σ, h => by
    have hs : ExecLe (.pop 12 .brk (.push 7 false) (.push 7 false)) σ
        (.norm (update (update σ 12 (List.replicate m true)) 7 (false :: σ 7))) 2 :=
      ExecLe.pop_same (b := true) (s := List.replicate m true) (by simp [h, List.replicate_succ])
        ((ExecLe.push 7 false _).cast (by simp) le_rfl)
    have ih := ccv_ex_fillL m _ (by simp : (update (update σ 12 (List.replicate m true)) 7
      (false :: σ 7)) 12 = List.replicate m true)
    refine (ExecLe.loop_norm hs ih).cast ?_ (by omega)
    congr 1; funext j
    by_cases h7 : j = 7
    · subst h7; simp [List.replicate_succ']
    · by_cases h12 : j = 12
      · subst h12; simp
      · simp [h7, h12]

def ccv_srRow : Cmd :=
  .seq (copyVia 4 12 8) (.seq ccv_popL (.seq (copyVia 0 7 8) (.seq (copyVia 4 12 8)
    (.seq ccv_fillL (.seq (moveTwo 6 7 8) (.seq (move 8 6) (.seq (copyVia 13 6 8)
      (move 13 10))))))))

/-- The state after `ccv_srRow`. -/
def ccv_post (K : ℕ) (R Dn Q : Str) : ℕ → Str :=
  ccv_st K (R.drop K) Q ((ccv_blk K R).reverse ++ Dn) (ccv_Y K R Dn) (ccv_blk K R)
    (ccv_fp (ccv_blk K R) [])

theorem ccv_ex_srRow (K : ℕ) (R Q Dn : Str) :
    ExecLe ccv_srRow (ccv_st K R Q Dn [] [] []) (.norm (ccv_post K R Dn Q))
      (23 * K + 5 * R.length + 5 * Dn.length + 26) := by
  set B := ccv_blk K R
  set R' := R.drop K
  set F := ccv_fp B []
  have h1 := exec_copyVia (a := 4) (b := 12) (t := 8) (by decide) (by decide) (by decide)
    (ccv_st K R Q Dn [] [] []) rfl
  have e1 : update (ccv_st K R Q Dn [] [] []) 12 (ccv_st K R Q Dn [] [] [] 4 ++
      ccv_st K R Q Dn [] [] [] 12) =
      update (update (ccv_st K R Q Dn [] [] []) 12 (List.replicate K true)) 13 [] := by ccx
  rw [e1] at h1
  have h2 := ccv_ex_popL K Q Dn K R [] []
  rw [List.append_nil] at h2
  set σ2 := update (ccv_st K R' Q Dn [] [] F) 13 B.reverse
  have h3 := exec_copyVia (a := 0) (b := 7) (t := 8) (by decide) (by decide) (by decide) σ2
    (by simp [σ2])
  set σ3 := update (ccv_st K R' Q Dn R' [] F) 13 B.reverse
  have e3 : update σ2 7 (σ2 0 ++ σ2 7) = σ3 := by simp only [σ2, σ3]; ccx
  rw [e3] at h3
  have h4 := exec_copyVia (a := 4) (b := 12) (t := 8) (by decide) (by decide) (by decide) σ3
    (by simp [σ3])
  have h5 := ccv_ex_fillL K (update σ3 12 (σ3 4 ++ σ3 12)) (by simp [σ3])
  set σ5 := update (ccv_st K R' Q Dn (List.replicate K false ++ R') [] F) 13 B.reverse
  have e5 : update (update (update σ3 12 (σ3 4 ++ σ3 12)) 12 []) 7
      (List.replicate K false ++ update σ3 12 (σ3 4 ++ σ3 12) 7) = σ5 := by
    simp only [σ3, σ5]; ccx
  rw [e5] at h5
  have h6 := exec_moveTwo (s := 6) (a := 7) (b := 8) (by decide) (by decide) (by decide) Dn σ5
    (by simp [σ5])
  set σ6 := update (update (ccv_st K R' Q [] (ccv_Y K R Dn) [] F) 13 B.reverse) 8 Dn.reverse
  have e6 : update (update (update σ5 6 []) 7 (Dn.reverse ++ σ5 7)) 8 (Dn.reverse ++ σ5 8) = σ6 := by
    simp only [σ5, σ6, ccv_Y, R']; ccx
  rw [e6] at h6
  have h7 := exec_move (a := 8) (b := 6) (by decide) Dn.reverse σ6 (by simp [σ6])
  set σ7 := update (ccv_st K R' Q Dn (ccv_Y K R Dn) [] F) 13 B.reverse
  have e7 : update (update σ6 8 []) 6 (Dn.reverse.reverse ++ σ6 6) = σ7 := by
    simp only [σ6, σ7]; ccx
  rw [e7] at h7
  have h8 := exec_copyVia (a := 13) (b := 6) (t := 8) (by decide) (by decide) (by decide) σ7
    (by simp [σ7])
  set σ8 := update (ccv_st K R' Q (B.reverse ++ Dn) (ccv_Y K R Dn) [] F) 13 B.reverse
  have e8 : update σ7 6 (σ7 13 ++ σ7 6) = σ8 := by simp only [σ7, σ8]; ccx
  rw [e8] at h8
  have h9 := exec_move (a := 13) (b := 10) (by decide) B.reverse σ8 (by simp [σ8])
  have e9 : update (update σ8 13 []) 10 (B.reverse.reverse ++ σ8 10) = ccv_post K R Dn Q := by
    simp only [σ8, ccv_post, R', B, F]; ccx
  rw [e9] at h9
  refine ((ExecLe.of h1).seq_norm (h2.seq_norm ((ExecLe.of h3).seq_norm ((ExecLe.of h4).seq_norm
    (h5.seq_norm ((ExecLe.of h6).seq_norm ((ExecLe.of h7).seq_norm ((ExecLe.of h8).seq_norm
    (ExecLe.of h9))))))))).cast rfl ?_
  simp [σ2, σ3, σ7, B, R']
  omega

/-! ## The main loop -/

def ccv_mainB : Cmd :=
  .pop 3 (.halt true) (.pop 3 (.halt false) (.seq ccv_endRow ccv_srRow) (ccv_col false))
    (.pop 3 (.halt false) (ccv_col true) (ccv_col false))

def ccv_mainL : Cmd := .loop ccv_mainB

section Main

variable {K : ℕ} {R Q Dn Y A F : Str}

theorem ccv_mainB_sym {s : SatSym} (hs : s ≠ sep) {r : Res} {T : ℕ}
    (h : ExecLe (ccv_col (isPos s)) (ccv_st K R Q Dn Y A F) r T) :
    ExecLe ccv_mainB (ccv_st K R (ic s ++ Q) Dn Y A F) r (T + 2) := by
  cases s with
  | sep => exact absurd rfl hs
  | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [ccv_u3, isPos] using h))
  | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [ccv_u3, isPos] using h))
  | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [ccv_u3, isPos] using h))

theorem ccv_mainB_sep {r : Res} {T : ℕ}
    (h : ExecLe (.seq ccv_endRow ccv_srRow) (ccv_st K R Q Dn Y A F) r T) :
    ExecLe ccv_mainB (ccv_st K R (false :: false :: Q) Dn Y A F) r (T + 2) :=
  ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [ccv_u3] using h))

end Main

/-- Cost of the end of a row. -/
def ccv_Tend (K N : ℕ) : ℕ := 2 * N * (8 * K + 8) + 27 * K + 10 * N + 35

/-- One row. -/
theorem ccv_ex_row (K N : ℕ) (R Dn Q' A F : Str) (hA : A.length = K) (hFA : F ≠ [] → A ≠ [])
    (hF : F.length ≤ K) (hR : R.length ≤ N) (hD : Dn.length ≤ N) (res : Res) (T' : ℕ)
    (h : ExecLe ccv_mainL (ccv_post K R Dn Q') res T') : ∀ (r : List SatSym) (Y : Str),
    sep ∉ r → Y.length ≤ 2 * N →
    ExecLe ccv_mainL (ccv_st K R (r.flatMap ic ++ false :: false :: Q') Dn Y A F)
      (if ccv_rowOk A F r Y then res else .halt false)
      (T' + (r.length * (8 * K + 8) + ccv_Tend K N))
  | [], Y, _, hY => by
    have he := ccv_ex_endRow K (2 * N) R Q' Dn Y A F hFA hY
    rw [hA] at he
    have hT : 2 * F.length + 2 * N * (8 * K + 8) + 2 * K + 7 + 2 ≤ ccv_Tend K N := by
      unfold ccv_Tend; omega
    cases hc : (!F.isEmpty && ccv_rest A Y)
    · rw [hc] at he; simp only [Bool.false_eq_true, if_false] at he
      exact (ExecLe.loop_halt (ccv_mainB_sep (ExecLe.seq_halt he))).cast
        (by simp [ccv_rowOk, hc]) (by simp; omega)
    · rw [hc] at he; simp only [if_true] at he
      have hb := ccv_mainB_sep (he.seq_norm (ccv_ex_srRow K R Q' Dn))
      refine (ExecLe.loop_norm hb h).cast (by simp [ccv_rowOk, hc]) ?_
      simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
      unfold ccv_Tend at hT ⊢; omega
  | s :: r, Y, hr, hY => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have hcs := ccv_ex_col (isPos s) K R (r.flatMap ic ++ false :: false :: Q') Dn A F Y
    have hb := ccv_mainB_sym (Q := r.flatMap ic ++ false :: false :: Q') hs hcs
    simp only [List.flatMap_cons, List.append_assoc]
    cases hc : (!isPos s && ccv_hits A Y)
    · rw [hc] at hb; simp only [Bool.false_eq_true, if_false] at hb
      have ih := ccv_ex_row K N R Dn Q' A F hA hFA hF hR hD res T' h r (Y.drop A.length) hr'
        (by simp only [List.length_drop]; omega)
      have hok : (isPos s || !ccv_hits A Y) = true := by
        revert hc; cases isPos s <;> cases ccv_hits A Y <;> simp
      refine (ExecLe.loop_norm hb ih).cast (by simp [ccv_rowOk, hok]) ?_
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · rw [hc] at hb; simp only [if_true] at hb
      have hok : (isPos s || !ccv_hits A Y) = false := by
        revert hc; cases isPos s <;> cases ccv_hits A Y <;> simp
      exact (ExecLe.loop_halt hb).cast (by simp [ccv_rowOk, hok])
        (by simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)

/-- Cost of the main phase. -/
def ccv_Trows (K N : ℕ) : List (List SatSym) → ℕ
  | [] => 2
  | r :: rows => r.length * (8 * K + 8) + ccv_Tend K N + ccv_Trows K N rows

theorem ccv_ex_rows (K N : ℕ) : ∀ (rows : List (List SatSym)) (R Dn : Str),
    (∀ r ∈ rows, sep ∉ r) → R.length ≤ N → Dn.length + K * (rows.length + 1) ≤ N →
    ExecLe ccv_mainL (ccv_post K R Dn (enc rows)) (.halt (ccv_go K rows R Dn))
      (ccv_Trows K N rows)
  | [], R, Dn, _, _, _ => (ExecLe.loop_halt (ExecLe.pop_nil (by simp [ccv_post, enc])
      (ExecLe.halt true _))).cast (by simp [ccv_go]) (by simp [ccv_Trows])
  | r :: rows, R, Dn, hrows, hR, hD => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.length_cons] at hD
    have hK : K * (rows.length + 1 + 1) = K * (rows.length + 1) + K := by ring
    have hK1 : K ≤ K * (rows.length + 1) := Nat.le_mul_of_pos_right K (by omega)
    have ih := ccv_ex_rows K N rows (R.drop K) ((ccv_blk K R).reverse ++ Dn) hrs
      (by simp; omega) (by simp; omega)
    rw [enc_cons]
    have hfp := ccv_length_fp (ccv_blk K R) []
    simp only [ccv_length_blk, List.length_nil, Nat.add_zero] at hfp
    have := ccv_ex_row K N (R.drop K) ((ccv_blk K R).reverse ++ Dn) (enc rows) (ccv_blk K R)
      (ccv_fp (ccv_blk K R) []) (by simp) (ccv_fp_nil_ne _) hfp (by simp; omega)
      (by simp; omega) _ _ ih r (ccv_Y K R Dn) hr (by simp [ccv_Y]; omega)
    refine this.cast ?_ (by simp [ccv_Trows]; omega)
    simp only [ccv_go]
    cases ccv_rowOk (ccv_blk K R) (ccv_fp (ccv_blk K R) []) r (ccv_Y K R Dn) <;> rfl

/-! ## The first row -/

theorem ccv_ex_frLoop (R Dn Y A F Q' : Str) : ∀ (kr : List SatSym) (K : ℕ),
    sep ∉ kr → ExecLe frLoop (ccv_st K R (kr.flatMap ic ++ false :: false :: Q') Dn Y A F)
      (.norm (ccv_st (K + kr.length) R Q' Dn Y A F)) (3 * kr.length + 3)
  | [], K, _ => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) rfl
      (ExecLe.pop_cons (b := false) (s := Q') (by simp) (ExecLe.brk _)))).cast
      (by simp [ccv_u3]) (by simp)
  | s :: kr, K, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := ccv_ex_frLoop R Dn Y A F Q' kr (K + 1) (fun e => hr (List.mem_cons_of_mem _ e))
    set Q := kr.flatMap ic ++ false :: false :: Q'
    have hb : ExecLe frB (ccv_st K R (ic s ++ Q) Dn Y A F)
        (.norm (ccv_st (K + 1) R Q Dn Y A F)) 3 := by
      have hp : ExecLe (.push 4 true) (ccv_st K R Q Dn Y A F)
          (.norm (ccv_st (K + 1) R Q Dn Y A F)) 1 :=
        (ExecLe.push 4 true _).cast (by rw [ccv_st_4, ← List.replicate_succ, ccv_u4]) le_rfl
      cases s with
      | sep => exact absurd rfl hs
      | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
          (by simp) (by simpa [ccv_u3] using hp))
      | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
          (by simp) (by simpa [ccv_u3] using hp))
      | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
          (by simp) (by simpa [ccv_u3] using hp))
    refine (ExecLe.loop_norm (by simpa [Q] using hb) ih).cast (by simp; ring_nf) (by simp; omega)

/-! ## The whole verifier -/

def ccv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq frLoop (.seq ccv_srRow ccv_mainL))))

/-- Time bound of the verifier. -/
def ccv_Tver (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (3 * n + 3) +
  (28 * n + 26) + (n * (8 * n + 8) + n * ccv_Tend n (n * n + n) + 2)

theorem ccv_Trows_eq (K N : ℕ) : ∀ rows : List (List SatSym),
    ccv_Trows K N rows = (rows.map List.length).sum * (8 * K + 8) + rows.length * ccv_Tend K N + 2
  | [] => by simp [ccv_Trows]
  | r :: rows => by simp only [ccv_Trows, ccv_Trows_eq K N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem ccv_exec_ver (z : Str) :
    ExecLe ccv_ver (init [z]).stk (.halt (ccv_res (dec z).1 (dec z).2)) (ccv_Tver z.length) := by
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
      ccv_st 0 y (enc (clauses w)) [] [] [] [] := by
    funext j
    rcases j with _|_|_|_|j <;> simp [σ₂, σ₁, ccv_st, enc, trunc, he]
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ),
      ExecLe c (ccv_st 0 y (enc (clauses w)) [] [] [] []) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold ccv_res ccv_ver
  have hsep := sep_not_mem_clauses w
  have hTe : ∀ K, K ≤ z.length → ccv_Tend K (z.length * z.length + z.length) ≤
      ccv_Tend z.length (z.length * z.length + z.length) := by
    intro K hK; unfold ccv_Tend; nlinarith
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq frLoop (.seq ccv_srRow ccv_mainL)) (ccv_st 0 y (enc []) [] [] [] [])
        (.halt false) 2 :=
      ExecLe.seq_halt (ExecLe.loop_halt ((ExecLe.pop_nil rfl (ExecLe.halt false _)).cast rfl
        le_rfl))
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, ccv_Tver]; nlinarith
  · rw [hcw] at hsum hcl hsep hpre
    rw [enc_cons] at hpre
    have hF := ccv_ex_frLoop y [] [] [] [] (enc rows) kr 0 (hsep kr (by simp))
    rw [Nat.zero_add] at hF
    have hS := ccv_ex_srRow kr.length y (enc rows) []
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum hcl
    have hKn : kr.length * (rows.length + 1) ≤ z.length * z.length :=
      Nat.mul_le_mul (by omega) (by omega)
    have hR := ccv_ex_rows kr.length (z.length * z.length + z.length) rows y []
      (fun r hr => hsep r (by simp [hr])) (by nlinarith) (by simp; omega)
    refine (hpre _ _ _ (hF.seq_norm (hS.seq_norm hR))).cast (by simp) ?_
    rw [ccv_Trows_eq]
    simp only [htl, ccv_Tver, List.length_nil]
    have h1 : rows.length * ccv_Tend kr.length (z.length * z.length + z.length) ≤
        z.length * ccv_Tend z.length (z.length * z.length + z.length) :=
      Nat.mul_le_mul (by omega) (hTe _ (by omega))
    have h2 : (rows.map List.length).sum * (8 * kr.length + 8) ≤ z.length * (8 * z.length + 8) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

theorem ccv_Tver_le (n : ℕ) : ccv_Tver n ≤ tb 6 n := by
  unfold ccv_Tver ccv_Tend tb
  ring_nf
  nlinarith [Nat.zero_le (n ^ 5), Nat.zero_le (n ^ 6), Nat.zero_le (n ^ 4), Nat.zero_le (n ^ 3),
    Nat.zero_le (n ^ 2)]

end Pnp.Karp.CliqueCover
