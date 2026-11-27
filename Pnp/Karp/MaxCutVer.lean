import Pnp.Karp.MaxCut
import Pnp.Karp.CliqueVer

/-!
# MAX CUT ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/MaxCut.lean`) and a certificate `y : List Bool` (bit `i` is the side of vertex `i`,
missing bits are `false`).  Stack layout (the CLIQUE layout `st1`, `Pnp/Karp/CliqueVer.lean`):

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the bound `K` (unary);  `5`: the number of cut edges found so far (unary);
* `6`: the certificate bits read so far `Dn` (reversed);  `7`: the column bits `Y` of the
  current row (the sides of the vertices `j < i`);  `8`: a temporary;
* `9`: the side of the current row.

Program (`mcv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3`, `frLoop` (from the CLIQUE verifier): parse the code, read the
   first row into the unary `K`;
2. `mcv_srM` ("start row"): the column bits become `Dn.reverse` (exactly the columns `j < i`),
   then the next certificate bit is popped onto `Dn` and becomes the side of the row;
3. `mcv_mainLoop`: one symbol per iteration; every symbol pops a column bit (none left: column
   `≥ i`, ignored), and at `pos` a column bit different from the row side increments the
   counter; at `sep` the row is ended and the next row is started; at the end, `K ≤ count`.

`mcv_exec_ver`: the program halts with `mcv_vres (dec z).1 (dec z).2` on every input `z`, within
`mcv_Tver |z|` steps.
-/

namespace Pnp.Karp.MaxCut

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics -/

/-- The increment of one column. -/
def mcv_inc (ok b : Bool) : Str → ℕ
  | [] => 0
  | x :: _ => if ok && (x != b) then 1 else 0

/-- The cut edges of a row of side `b` against the column bits `Y`. -/
def mcv_rowCnt (b : Bool) : List SatSym → Str → ℕ
  | [], _ => 0
  | s :: r, Y => mcv_inc (isPos s) b Y + mcv_rowCnt b r Y.tail

/-- What the main loop computes. -/
def mcv_go (K : ℕ) : List (List SatSym) → Str → Str → ℕ → Bool
  | [], _, _, c => decide (K ≤ c)
  | r :: rows, R, Dn, c =>
      mcv_go K rows R.tail (R.headD false :: Dn) (c + mcv_rowCnt (R.headD false) r Dn.reverse)

/-- The answer of the verifier on `(w, y)`. -/
def mcv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | kr :: rows => mcv_go kr.length rows y [] 0

theorem mcv_inc_le (ok b : Bool) (Y : Str) : mcv_inc ok b Y ≤ 1 := by
  unfold mcv_inc; split
  · omega
  · split <;> omega

theorem mcv_rowCnt_le (b : Bool) : ∀ (r : List SatSym) (Y : Str), mcv_rowCnt b r Y ≤ r.length
  | [], _ => by simp [mcv_rowCnt]
  | s :: r, Y => by
    have := mcv_inc_le (isPos s) b Y
    have := mcv_rowCnt_le b r Y.tail
    simp only [mcv_rowCnt, List.length_cons]; omega

/-! ## Commands -/

/-- Pop the side bit of the row. -/
def mcv_bit : Cmd := .pop 0 (.push 6 false) (.push 6 false) (.seq (.push 6 true) (.push 9 true))

/-- Start a row. -/
def mcv_srM : Cmd := .seq (moveTwo 6 7 8) (.seq (move 8 6) mcv_bit)

/-- The state after `mcv_srM`. -/
def mcv_post (R Dn Q : Str) (K c : ℕ) : ℕ → Str :=
  st1 R.tail Q (R.headD false :: Dn) Dn.reverse K c (R.headD false)

theorem mcv_ex_srM (R Dn Q : Str) (K c : ℕ) :
    ExecLe mcv_srM (st1 R Q Dn [] K c false) (.norm (mcv_post R Dn Q K c))
      (5 * Dn.length + 8) := by
  have h3 := exec_moveTwo (s := 6) (a := 7) (b := 8) (by decide) (by decide) (by decide) Dn
    (st1 R Q Dn [] K c false) rfl
  have e3 : update (update (update (st1 R Q Dn [] K c false) 6 []) 7
      (Dn.reverse ++ (st1 R Q Dn [] K c false) 7)) 8
      (Dn.reverse ++ (st1 R Q Dn [] K c false) 8) =
      update (st1 R Q [] Dn.reverse K c false) 8 Dn.reverse := by
    rw [st1_7, st1_8, List.append_nil, u6, u7]
  rw [e3] at h3
  have h4 := exec_move (a := 8) (b := 6) (by decide) Dn.reverse
    (update (st1 R Q [] Dn.reverse K c false) 8 Dn.reverse) (by simp)
  rw [e_move86 R Q Dn _ K c] at h4
  have h5 : ExecLe mcv_bit (st1 R Q Dn Dn.reverse K c false) (.norm (mcv_post R Dn Q K c)) 3 := by
    rcases R with _ | ⟨_ | _, R'⟩
    · exact (ExecLe.pop_nil rfl (ExecLe.push 6 false _)).cast
        (by rw [st1_6, u6]; rfl) (by omega)
    · exact (ExecLe.pop_cons (b := false) (s := R') rfl
        (by rw [u0]; exact ExecLe.push 6 false _)).cast (by rw [st1_6, u6]; rfl) (by omega)
    · exact (ExecLe.pop_cons (b := true) (s := R') rfl (by
        rw [u0]; exact (ExecLe.push 6 true _).seq_norm (ExecLe.push 9 true _))).cast
        (by rw [st1_6, u6, st1_9]; congr 1; exact u9 true) (by omega)
  exact ((ExecLe.of h3).seq_norm ((ExecLe.of h4).seq_norm h5)).cast rfl
    (by simp only [List.length_reverse]; omega)

/-- One column of a row (`ok`: the symbol is `pos`). -/
def mcv_colStep (ok : Bool) : Cmd :=
  .pop 7 .skip
    (if ok then .pop 9 .skip .skip (.seq (.push 9 true) (.push 5 true)) else .skip)
    (if ok then .pop 9 (.push 5 true) (.push 5 true) (.push 9 true) else .skip)

theorem mcv_ex_push5 (R Q Dn Y : Str) (K c : ℕ) (b : Bool) :
    ExecLe (.push 5 true) (st1 R Q Dn Y K c b) (.norm (st1 R Q Dn Y K (c + 1) b)) 1 :=
  (ExecLe.push 5 true _).cast (by rw [st1_5, ← List.replicate_succ, u5]) le_rfl

theorem mcv_ex_colStep (ok b : Bool) (R Q Dn Y : Str) (K c : ℕ) :
    ExecLe (mcv_colStep ok) (st1 R Q Dn Y K c b)
      (.norm (st1 R Q Dn Y.tail K (c + mcv_inc ok b Y) b)) 4 := by
  rcases Y with _ | ⟨x, Y'⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [mcv_inc]) (by omega)
  have e9f : st1 R Q Dn Y' K c false 9 = [] := rfl
  have e9t : st1 R Q Dn Y' K c true 9 = true :: [] := rfl
  have et : update (st1 R Q Dn Y' K c true) 9 [] = st1 R Q Dn Y' K c false := u9 false
  have et' : update (st1 R Q Dn Y' K c false) 9 (true :: st1 R Q Dn Y' K c false 9) =
      st1 R Q Dn Y' K c true := u9 true
  refine ExecLe.pop_cons (T := 3) (b := x) (s := Y') rfl ?_
  rw [u7]
  cases ok
  · cases x
    · exact (ExecLe.skip _).cast (by simp [mcv_inc]) (by omega)
    · exact (ExecLe.skip _).cast (by simp [mcv_inc]) (by omega)
  cases x <;> cases b
  · exact (ExecLe.pop_nil e9f (ExecLe.skip _)).cast (by simp [mcv_inc]) (by omega)
  · refine (ExecLe.pop_cons e9t (by
      rw [et]; exact (ExecLe.push 9 true _).seq_norm (by rw [et']; exact mcv_ex_push5 ..))).cast
      (by simp [mcv_inc]) (by omega)
  · exact (ExecLe.pop_nil e9f (mcv_ex_push5 ..)).cast (by simp [mcv_inc]) (by omega)
  · exact (ExecLe.pop_cons e9t (by
      rw [et]; exact (ExecLe.push 9 true _).cast (by rw [et']) le_rfl)).cast
      (by simp [mcv_inc]) (by omega)

/-- End of a row: clear the column bits and the side flag. -/
def mcv_endRow : Cmd := .seq (drain 7) (.pop 9 .skip .skip .skip)

theorem mcv_ex_endRow (b : Bool) (R Q Dn Y : Str) (K c : ℕ) :
    ExecLe mcv_endRow (st1 R Q Dn Y K c b) (.norm (st1 R Q Dn [] K c false))
      (2 * Y.length + 4) := by
  have h1 := exec_drain 7 Y (st1 R Q Dn Y K c b) rfl
  rw [u7] at h1
  have h2 : ExecLe (.pop 9 .skip .skip .skip) (st1 R Q Dn [] K c b)
      (.norm (st1 R Q Dn [] K c false)) 2 := by
    cases b
    · exact ExecLe.pop_nil rfl (ExecLe.skip _)
    · exact ExecLe.pop_cons (b := true) (s := []) rfl
        (by rw [if_pos rfl]; exact (ExecLe.skip _).cast (by rw [← u9 (sel := true) false]; rfl) le_rfl)
  exact ((ExecLe.of h1).seq_norm h2).cast rfl (by omega)

/-- Final check: `K ≤ c`, i.e. `K < c + 1`. -/
def mcv_final : Cmd := .seq (.push 5 true) (.seq (gtCmd 5 4) (.halt false))

theorem mcv_ex_final (R Q Dn Y : Str) (K c : ℕ) (b : Bool) :
    ExecLe mcv_final (st1 R Q Dn Y K c b) (.halt (decide (K ≤ c))) (5 * K + 2 * c + 11) := by
  have hg := ex_gtHalt (st1 R Q Dn Y K (c + 1) b)
  simp only [st1_4, st1_5, List.length_replicate] at hg
  refine ((mcv_ex_push5 R Q Dn Y K c b).seq_norm hg).cast ?_ (by omega)
  congr 1; simp only [decide_eq_decide]; omega

/-! ## The main loop -/

/-- Loop body of the main phase. -/
def mcv_mainB : Cmd :=
  .pop 3 mcv_final (.pop 3 (.halt false) (.seq mcv_endRow mcv_srM) (mcv_colStep false))
    (.pop 3 (.halt false) (mcv_colStep true) (mcv_colStep false))

def mcv_mainLoop : Cmd := .loop mcv_mainB

section Main

variable {R Dn Y Q : Str} {K c : ℕ} {b : Bool}

theorem mcv_mainB_sym {s : SatSym} (hs : s ≠ sep) {r : Res} {T : ℕ}
    (h : ExecLe (mcv_colStep (isPos s)) (st1 R Q Dn Y K c b) r T) :
    ExecLe mcv_mainB (st1 R (ic s ++ Q) Dn Y K c b) r (T + 2) := by
  cases s with
  | sep => exact absurd rfl hs
  | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [u3, isPos] using h))
  | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [u3, isPos] using h))
  | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [u3, isPos] using h))

theorem mcv_mainB_sep {r : Res} {T : ℕ}
    (h : ExecLe (.seq mcv_endRow mcv_srM) (st1 R Q Dn Y K c b) r T) :
    ExecLe mcv_mainB (st1 R (false :: false :: Q) Dn Y K c b) r (T + 2) :=
  ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [u3] using h))

/-- One row. -/
theorem mcv_ex_row (N : ℕ) (hN : Dn.length ≤ N) (Q' : Str) : ∀ (r : List SatSym) (Y : Str) (c : ℕ),
    sep ∉ r → Y.length ≤ N → ∀ (res : Res) (T' : ℕ),
    ExecLe mcv_mainLoop (mcv_post R Dn Q' K (c + mcv_rowCnt b r Y)) res T' →
    ExecLe mcv_mainLoop (st1 R (r.flatMap ic ++ false :: false :: Q') Dn Y K c b) res
      (T' + (6 * r.length + 7 * N + 14))
  | [], Y, c, _, hY, res, T', h => by
    have hb := mcv_mainB_sep ((mcv_ex_endRow b R Q' Dn Y K c).seq_norm (mcv_ex_srM R Dn Q' K c))
    simp only [mcv_rowCnt, Nat.add_zero] at h
    exact (ExecLe.loop_norm hb h).cast rfl (by simp; omega)
  | s :: r, Y, c, hr, hY, res, T', h => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have hcs := mcv_ex_colStep (isPos s) b R (r.flatMap ic ++ false :: false :: Q') Dn Y K c
    have hb := mcv_mainB_sym (Q := r.flatMap ic ++ false :: false :: Q') hs hcs
    have ih := mcv_ex_row N hN Q' r Y.tail (c + mcv_inc (isPos s) b Y) hr'
      (by simp only [List.length_tail]; omega) res T'
      (by simpa only [mcv_rowCnt, Nat.add_assoc] using h)
    simp only [List.flatMap_cons, List.append_assoc]
    exact (ExecLe.loop_norm hb ih).cast rfl (by simp; omega)

/-- Cost of the main phase. -/
def mcv_Trows (N : ℕ) : List (List SatSym) → ℕ
  | [] => 7 * N + 12
  | r :: rows => 6 * r.length + 7 * N + 14 + mcv_Trows N rows

theorem mcv_ex_rows (N : ℕ) (hK : K ≤ N) : ∀ (rows : List (List SatSym)) (R Dn : Str) (c : ℕ),
    (∀ r ∈ rows, sep ∉ r) → Dn.length + rows.length ≤ N → c + (rows.map List.length).sum ≤ N →
    ExecLe mcv_mainLoop (mcv_post R Dn (enc rows) K c) (.halt (mcv_go K rows R Dn c))
      (mcv_Trows N rows)
  | [], R, Dn, c, _, hN, hc => by
    have hf := mcv_ex_final R.tail [] (R.headD false :: Dn) Dn.reverse K c (R.headD false)
    have hb : ExecLe mcv_mainB (mcv_post R Dn [] K c) (.halt (mcv_go K [] R Dn c))
        (5 * K + 2 * c + 11 + 1) :=
      ExecLe.pop_nil rfl (hf.cast (by simp [mcv_go]) le_rfl)
    exact (ExecLe.loop_halt hb).cast rfl (by simp [mcv_Trows] at hc ⊢; omega)
  | r :: rows, R, Dn, c, hrows, hN, hc => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.length_cons, List.map_cons, List.sum_cons] at hN hc
    have hle := mcv_rowCnt_le (R.headD false) r Dn.reverse
    have ih := mcv_ex_rows N hK rows R.tail (R.headD false :: Dn)
      (c + mcv_rowCnt (R.headD false) r Dn.reverse) hrs (by simp; omega) (by omega)
    rw [enc_cons]
    have := mcv_ex_row (R := R.tail) (Dn := R.headD false :: Dn) (K := K) (b := R.headD false)
      N (by simp; omega) (enc rows) r Dn.reverse c hr (by simp; omega) _ _ ih
    exact this.cast (by simp [mcv_go]) (by simp [mcv_Trows]; omega)

end Main

/-! ## The whole verifier -/

def mcv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq frLoop (.seq mcv_srM mcv_mainLoop))))

/-- Time bound of the verifier. -/
def mcv_Tver (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (3 * n + 3) + 8 +
  (6 * n + n * (7 * n + 14) + 7 * n + 12)

theorem mcv_Trows_eq (N : ℕ) : ∀ rows : List (List SatSym),
    mcv_Trows N rows = 6 * (rows.map List.length).sum + rows.length * (7 * N + 14) + 7 * N + 12
  | [] => by simp [mcv_Trows]
  | r :: rows => by simp only [mcv_Trows, mcv_Trows_eq N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem mcv_exec_ver (z : Str) :
    ExecLe mcv_ver (init [z]).stk (.halt (mcv_vres (dec z).1 (dec z).2)) (mcv_Tver z.length) := by
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
      st1 y (enc (clauses w)) [] [] 0 0 false := by
    funext j
    simp only [σ₂, σ₁, st1, update_apply, enc, trunc, CookLevin.fl]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ),
      ExecLe c (st1 y (enc (clauses w)) [] [] 0 0 false) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold mcv_vres mcv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq frLoop (.seq mcv_srM mcv_mainLoop)) (st1 y (enc []) [] [] 0 0 false)
        (.halt false) 2 :=
      ExecLe.seq_halt (ExecLe.loop_halt ((ExecLe.pop_nil rfl (ExecLe.halt false _)).cast rfl
        le_rfl))
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, mcv_Tver]; nlinarith
  · rw [hcw] at hsum hcl hsep hpre
    rw [enc_cons] at hpre
    have hF := ex_frLoop y [] [] (enc rows) 0 false kr 0 (hsep kr (by simp))
    have hS := mcv_ex_srM y [] (enc rows) (0 + kr.length) 0
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum hcl
    have hR := mcv_ex_rows (K := 0 + kr.length) z.length (by omega) rows y [] 0
      (fun r hr => hsep r (by simp [hr])) (by simp; omega) (by omega)
    refine (hpre _ _ _ (hF.seq_norm (hS.seq_norm hR))).cast (by simp) ?_
    rw [mcv_Trows_eq]
    simp only [htl, mcv_Tver, List.length_nil]
    have h1 : rows.length * (7 * z.length + 14) ≤ z.length * (7 * z.length + 14) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem mcv_Tver_le (n : ℕ) : mcv_Tver n ≤ tb 6 n := by
  unfold mcv_Tver tb
  have hm : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  norm_num at hm
  have e : (n + 2) ^ 6 = (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by ring
  have : 16 * (n + 2) ^ 2 ≤ (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by nlinarith
  nlinarith

end Pnp.Karp.MaxCut
