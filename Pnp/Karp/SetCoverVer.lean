import Pnp.Karp.SetCover
import Pnp.Karp.X3CVer

/-!
# SET COVER ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/SetCover.lean`) and a certificate `y : List Bool` (bit `i` says whether row `i` of
the sets is selected; missing bits are `false`).  It reuses the stack layout `xv_st` of the
X3C verifier (`Pnp/Karp/X3CVer.lean`):

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the covered vector `V` (bit `p`: position `p` is covered by a selected row so far);
* `5`: the new covered vector of the current row (reversed);  `6`: the unary budget `K`.

Program (`scv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3`: parse the code of `w`, drop the unfinished tail;
2. `xv_hL`: read the header row, pushing one `false` per symbol onto `V`; `scv_bL`: read the
   budget row, pushing one `true` per symbol onto `K` (halt `false` if a row is missing);
3. `scv_mL`: per row, pop a certificate bit `sel` and scan the row together with `V`
   (`scv_rL sel`): every symbol pops a bit `v` of `V` (if any; positions `≥ |V|` are ignored)
   and pushes `v || (sel && s = pos)`; at the `sep` a selected row pops one budget bit (halt
   `false` if the budget is exhausted); then the rest of `V` is appended (`move 4 5`,
   `move 5 4`).  At the end of the input accept iff every bit of `V` is set (`xv_fin`).

`scv_exec_ver`: the program halts with `scv_vres (dec z).1 (dec z).2` on every input `z`,
within `scv_Tver |z|` steps.
-/

namespace Pnp.Karp.SetCover

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM

/-! ## Semantics -/

/-- The scanned prefix of the covered vector `V` after the row `r` (selected iff `sel`). -/
def scv_pre (sel : Bool) : List SatSym → Str → Str
  | [], _ => []
  | _ :: _, [] => []
  | s :: r, v :: V => (v || (sel && decide (s = pos))) :: scv_pre sel r V

/-- The covered vector after the row `r` (selected iff `sel`). -/
def scv_or (sel : Bool) (r : List SatSym) (V : Str) : Str := scv_pre sel r V ++ V.drop r.length

/-- What the main loop computes (`V`: covered vector, `K`: budget, `y`: unread bits). -/
def scv_go : Str → Str → List (List SatSym) → Str → Bool
  | V, _, [], _ => V.all id
  | V, K, r :: rows, y =>
    if y.headD false && K.isEmpty then false
    else scv_go (scv_or (y.headD false) r V) (if y.headD false then K.tail else K) rows y.tail

/-- The answer of the verifier on `(w, y)`. -/
def scv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | u :: kr :: rows => scv_go (List.replicate u.length false) (List.replicate kr.length true) rows y
  | _ => false

theorem scv_pre_nil (sel : Bool) : ∀ r : List SatSym, scv_pre sel r [] = []
  | [] => rfl
  | _ :: _ => rfl

theorem scv_pre_cons (sel : Bool) (s : SatSym) (r : List SatSym) (V : Str) :
    scv_pre sel (s :: r) V = scv_pre sel [s] V ++ scv_pre sel r V.tail := by
  rcases V with _ | ⟨v, V⟩ <;> simp [scv_pre, scv_pre_nil]

theorem scv_pre_single_rev (sel : Bool) (s : SatSym) (V : Str) :
    (scv_pre sel [s] V).reverse = scv_pre sel [s] V := by
  rcases V with _ | ⟨v, V⟩ <;> simp [scv_pre]

theorem scv_pre_length (sel : Bool) : ∀ (r : List SatSym) (V : Str),
    (scv_pre sel r V).length + (V.drop r.length).length = V.length
  | [], V => by simp [scv_pre]
  | _ :: _, [] => by simp [scv_pre]
  | s :: r, v :: V => by
    have := scv_pre_length sel r V
    simp only [scv_pre, List.length_cons, List.drop_succ_cons]; omega

theorem scv_or_length (sel : Bool) (r : List SatSym) (V : Str) :
    (scv_or sel r V).length = V.length := by
  rw [scv_or, List.length_append, scv_pre_length]

/-! ## Scanning a row -/

def scv_cZ : Cmd := .pop 4 .skip (.push 5 false) (.push 5 true)

def scv_cP (sel : Bool) : Cmd := .pop 4 .skip (.push 5 sel) (.push 5 true)

def scv_cS : Bool → Cmd
  | true => .pop 6 (.halt false) .brk .brk
  | false => .brk

def scv_rB (sel : Bool) : Cmd :=
  .pop 3 xv_fin (.pop 3 (.halt false) (scv_cS sel) scv_cZ)
    (.pop 3 (.halt false) (scv_cP sel) scv_cZ)

def scv_rL (sel : Bool) : Cmd := .loop (scv_rB sel)

theorem scv_pop2r (sel : Bool) {R Q V W K : Str} (s : SatSym) {r : Res} {T' : ℕ}
    (h : ExecLe (xv_sel s (scv_cS sel) scv_cZ (scv_cP sel) scv_cZ) (xv_st R Q V W K) r T') :
    ExecLe (scv_rB sel) (xv_st R (ic s ++ Q) V W K) r (T' + 2) := xv_pop2 s h

theorem scv_ex_sym (sel : Bool) (R Q W K : Str) (s : SatSym) (hs : s ≠ sep) (V : Str) :
    ExecLe (scv_rB sel) (xv_st R (ic s ++ Q) V W K)
      (.norm (xv_st R Q V.tail (scv_pre sel [s] V ++ W) K)) 4 := by
  refine scv_pop2r sel s ?_
  rcases V with _ | ⟨v, V⟩ <;> cases s <;> (try exact absurd rfl hs) <;>
    simp only [xv_sel, scv_cZ, scv_cP]
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [scv_pre]) le_rfl
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [scv_pre]) le_rfl
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [scv_pre]) le_rfl
  all_goals
    refine ExecLe.pop_cons (b := v) (s := V) rfl ?_
    cases v <;> cases sel <;> simp only [if_true, if_false, Bool.false_eq_true] <;>
      exact (ExecLe.push 5 _ _).cast (by simp [scv_pre]) le_rfl

theorem scv_ex_row (sel : Bool) (R Q' : Str) : ∀ (r : List SatSym) (V W K : Str), sep ∉ r →
    ExecLe (scv_rL sel) (xv_st R (r.flatMap ic ++ false :: false :: Q') V W K)
      (if sel && K.isEmpty then .halt false else
        .norm (xv_st R Q' (V.drop r.length) ((scv_pre sel r V).reverse ++ W)
          (if sel then K.tail else K)))
      (4 * r.length + 4)
  | [], V, W, K, _ => by
    cases sel
    · have hb := scv_pop2r false (R := R) (Q := Q') (V := V) (W := W) (K := K) sep
        (r := .brk (xv_st R Q' V W K)) (T' := 1) (ExecLe.brk _)
      exact (ExecLe.loop_brk hb).cast (by simp [scv_pre]) (by simp)
    · rcases K with _ | ⟨b, K⟩
      · have hb := scv_pop2r true (R := R) (Q := Q') (V := V) (W := W) (K := []) sep
          (r := .halt false) (T' := 2) (ExecLe.pop_nil rfl (ExecLe.halt false _))
        exact (ExecLe.loop_halt hb).cast (by simp) (by simp)
      · have hb := scv_pop2r true (R := R) (Q := Q') (V := V) (W := W) (K := b :: K) sep
          (r := .brk (xv_st R Q' V W K)) (T' := 2)
          (ExecLe.pop_same (b := b) (s := K) rfl (by rw [xv_u6]; exact ExecLe.brk _))
        exact (ExecLe.loop_brk hb).cast (by simp [scv_pre]) (by simp)
  | s :: r, V, W, K, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have hb := scv_ex_sym sel R (r.flatMap ic ++ false :: false :: Q') W K s hs V
    have ih := scv_ex_row sel R Q' r V.tail (scv_pre sel [s] V ++ W) K hr'
    simp only [List.flatMap_cons, List.append_assoc]
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    rw [scv_pre_cons sel s r V, List.drop_tail, List.reverse_append, List.append_assoc,
      List.length_cons, scv_pre_single_rev]

theorem scv_ex_rowEnd (sel : Bool) (R V W K : Str) :
    ExecLe (scv_rL sel) (xv_st R [] V W K) (.halt (V.all id)) (2 * V.length + 3) :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (xv_ex_fin R [] W K V))

/-! ## One row, the main loop -/

def scv_rC (sel : Bool) : Cmd := .seq (scv_rL sel) (.seq (move 4 5) (move 5 4))

theorem scv_ex_rC (sel : Bool) (R Q' : Str) (r : List SatSym) (V K : Str) (hr : sep ∉ r) :
    ExecLe (scv_rC sel) (xv_st R (r.flatMap ic ++ false :: false :: Q') V [] K)
      (if sel && K.isEmpty then .halt false else
        .norm (xv_st R Q' (scv_or sel r V) [] (if sel then K.tail else K)))
      (4 * r.length + 4 * V.length + 8) := by
  have h1 := scv_ex_row sel R Q' r V [] K hr
  by_cases hc : (sel && K.isEmpty) = true
  · rw [if_pos hc] at h1 ⊢
    exact (ExecLe.seq_halt h1).cast rfl (by omega)
  · rw [if_neg hc] at h1 ⊢
    set K' := if sel then K.tail else K
    set D := V.drop r.length
    set P := scv_pre sel r V
    have hl : P.length + D.length = V.length := scv_pre_length sel r V
    have hM1 := exec_move (a := 4) (b := 5) (by decide) D (xv_st R Q' D (P.reverse ++ []) K') rfl
    have e1 : update (update (xv_st R Q' D (P.reverse ++ []) K') 4 []) 5
        (D.reverse ++ xv_st R Q' D (P.reverse ++ []) K' 5) =
        xv_st R Q' [] (D.reverse ++ P.reverse) K' := by simp
    rw [e1] at hM1
    have hM2 := exec_move (a := 5) (b := 4) (by decide) (D.reverse ++ P.reverse)
      (xv_st R Q' [] (D.reverse ++ P.reverse) K') rfl
    have e2 : update (update (xv_st R Q' [] (D.reverse ++ P.reverse) K') 5 []) 4
        ((D.reverse ++ P.reverse).reverse ++ xv_st R Q' [] (D.reverse ++ P.reverse) K' 4) =
        xv_st R Q' (scv_or sel r V) [] K' := by simp [scv_or, P, D]
    rw [e2] at hM2
    have hD : D.length ≤ V.length := by omega
    exact (h1.seq_norm ((ExecLe.of hM1).seq_norm (ExecLe.of hM2))).cast rfl
      (by simp; omega)

def scv_mB : Cmd := .pop 0 (scv_rC false) (scv_rC false) (scv_rC true)

def scv_mL : Cmd := .loop scv_mB

theorem scv_ex_mB {R Q V W K : Str} {r : Res} {T : ℕ}
    (h : ExecLe (scv_rC (R.headD false)) (xv_st R.tail Q V W K) r T) :
    ExecLe scv_mB (xv_st R Q V W K) r (T + 1) := by
  rcases R with _ | ⟨_ | _, R'⟩
  · exact ExecLe.pop_nil rfl h
  · exact ExecLe.pop_cons (b := false) (s := R') rfl (by rw [xv_u0]; exact h)
  · exact ExecLe.pop_cons (b := true) (s := R') rfl (by rw [xv_u0]; exact h)

/-- Cost of the main loop. -/
def scv_Tm (N : ℕ) : List (List SatSym) → ℕ
  | [] => 2 * N + 4
  | r :: rows => 4 * r.length + 4 * N + 9 + scv_Tm N rows

theorem scv_Tm_eq (N : ℕ) : ∀ rows : List (List SatSym),
    scv_Tm N rows = 4 * (rows.map List.length).sum + rows.length * (4 * N + 9) + 2 * N + 4
  | [] => by simp [scv_Tm]
  | r :: rows => by simp only [scv_Tm, scv_Tm_eq N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem scv_ex_main (N : ℕ) : ∀ (rows : List (List SatSym)) (R V K : Str),
    (∀ r ∈ rows, sep ∉ r) → V.length ≤ N →
    ExecLe scv_mL (xv_st R (enc rows) V [] K) (.halt (scv_go V K rows R)) (scv_Tm N rows)
  | [], R, V, K, _, hN => by
    have h : ExecLe scv_mB (xv_st R [] V [] K) (.halt (V.all id)) (2 * V.length + 4) :=
      scv_ex_mB (ExecLe.seq_halt (scv_ex_rowEnd (R.headD false) R.tail V [] K))
    exact (ExecLe.loop_halt h).cast (by simp [scv_go]) (by simp [scv_Tm]; omega)
  | r :: rows, R, V, K, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    rw [enc_cons]
    have hb := scv_ex_mB (scv_ex_rC (R.headD false) R.tail (enc rows) r V K hr)
    by_cases hc : (R.headD false && K.isEmpty) = true
    · rw [if_pos hc] at hb
      exact (ExecLe.loop_halt hb).cast (by rw [scv_go, if_pos hc]) (by simp [scv_Tm]; omega)
    · rw [if_neg hc] at hb
      have hl := scv_or_length (R.headD false) r V
      have ih := scv_ex_main N rows R.tail (scv_or (R.headD false) r V)
        (if R.headD false then K.tail else K) hrs (by omega)
      exact (ExecLe.loop_norm hb ih).cast (by rw [scv_go, if_neg hc]) (by simp [scv_Tm]; omega)

/-! ## The budget row -/

def scv_bB : Cmd :=
  .pop 3 (.halt false) (.pop 3 (.halt false) .brk (.push 6 true))
    (.pop 3 (.halt false) (.push 6 true) (.push 6 true))

def scv_bL : Cmd := .loop scv_bB

theorem scv_ex_bd (R Q' V : Str) : ∀ (t : List SatSym) (K : Str), sep ∉ t →
    ExecLe scv_bL (xv_st R (t.flatMap ic ++ false :: false :: Q') V [] K)
      (.norm (xv_st R Q' V [] (List.replicate t.length true ++ K))) (3 * t.length + 3)
  | [], K, _ => by
    have hb := xv_pop2 (cE := .halt false) (cX := .halt false) (cZ := .push 6 true)
      (cP := .push 6 true) (cN := .push 6 true) (R := R) (Q := Q') (V := V) (W := [])
      (K := K) sep (r := .brk (xv_st R Q' V [] K)) (T' := 1) (ExecLe.brk _)
    exact (ExecLe.loop_brk hb).cast (by simp) (by simp)
  | s :: t, K, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := scv_ex_bd R Q' V t (true :: K) (fun e => hr (List.mem_cons_of_mem _ e))
    have hp : ExecLe (xv_sel s .brk (.push 6 true) (.push 6 true) (.push 6 true))
        (xv_st R (t.flatMap ic ++ false :: false :: Q') V [] K)
        (.norm (xv_st R (t.flatMap ic ++ false :: false :: Q') V [] (true :: K))) 1 := by
      cases s with
      | sep => exact absurd rfl hs
      | _ => exact (ExecLe.push 6 true _).cast (by simp) le_rfl
    have hb := xv_pop2 (cE := .halt false) (cX := .halt false) s hp
    simp only [List.flatMap_cons, List.append_assoc]
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp [List.replicate_succ']

theorem scv_ex_bdEnd (R V : Str) : ExecLe scv_bL (xv_st R [] V [] []) (.halt false) 2 :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt false _))

/-! ## The whole verifier -/

/-- The SET COVER verifier program. -/
def scv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq xv_hL (.seq scv_bL scv_mL))))

/-- Time bound of the verifier. -/
def scv_Tver (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (3 * n + 3) + (3 * n + 3) +
  (4 * n + n * (4 * n + 9) + 2 * n + 4)

theorem scv_exec_ver (z : Str) :
    ExecLe scv_ver (init [z]).stk (.halt (scv_vres (dec z).1 (dec z).2)) (scv_Tver z.length) := by
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
      xv_st y (enc (clauses w)) [] [] [] := by
    funext j
    simp only [σ₂, σ₁, xv_st, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ), ExecLe c (xv_st y (enc (clauses w)) [] [] []) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold scv_vres scv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨t, _ | ⟨kr, rows⟩⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq xv_hL (.seq scv_bL scv_mL)) (xv_st y (enc []) [] [] []) (.halt false)
        2 := ExecLe.seq_halt (xv_ex_hdEnd y)
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, scv_Tver]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    have hH := xv_ex_hd y (enc []) t [] (hsep t (by simp))
    rw [List.append_nil] at hH
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.map_nil, List.sum_nil,
      List.length_nil] at hsum
    have hf := hH.seq_norm (ExecLe.seq_halt (d := scv_mL) (scv_ex_bdEnd y _))
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, scv_Tver]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons, enc_cons] at hpre
    have hH := xv_ex_hd y (enc (kr :: rows)) t [] (hsep t (by simp))
    rw [List.append_nil, enc_cons] at hH
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hB := scv_ex_bd y (enc rows) (List.replicate t.length false) kr [] (hsep kr (by simp))
    rw [List.append_nil] at hB
    have hR := scv_ex_main z.length rows y (List.replicate t.length false)
      (List.replicate kr.length true) (fun r hr => hsep r (by simp [hr])) (by simp; omega)
    refine (hpre _ _ _ (hH.seq_norm (hB.seq_norm hR))).cast rfl ?_
    rw [scv_Tm_eq]
    simp only [htl, scv_Tver]
    have h1 : rows.length * (4 * z.length + 9) ≤ z.length * (4 * z.length + 9) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem scv_Tver_le (n : ℕ) : scv_Tver n ≤ tb 5 n := by
  unfold scv_Tver tb
  have hm : 2 ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  norm_num at hm
  have e : (n + 2) ^ 5 = (n + 2) ^ 3 * (n + 2) ^ 2 := by ring
  have : 8 * (n + 2) ^ 2 ≤ (n + 2) ^ 3 * (n + 2) ^ 2 := Nat.mul_le_mul_right _ hm
  nlinarith

end Pnp.Karp.SetCover
