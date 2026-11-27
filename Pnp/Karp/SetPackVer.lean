import Pnp.Karp.SetPacking
import Pnp.Karp.SetCoverVer

/-!
# SET PACKING ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/SetPacking.lean`) and a certificate `y : List Bool` (bit `i` says whether row `i`
of the sets is selected; missing bits are `false`).  It reuses the stack layout `xv_st` of the
X3C verifier and most of the SET COVER verifier (`Pnp/Karp/SetCoverVer.lean`):

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the covered vector `V` (bit `p`: position `p` lies in a selected row so far);
* `5`: the new covered vector of the current row (reversed);  `6`: the unary target `K`.

Program (`spkv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3`: parse the code of `w`, drop the unfinished tail;
2. `xv_hL`: read the header row, pushing one `false` per symbol onto `V`; `scv_bL`: read the
   target row, pushing one `true` per symbol onto `K` (halt `false` if a row is missing);
3. `spkv_mL`: per row, pop a certificate bit `sel` and scan the row together with `V`
   (`spkv_rL sel`): every symbol pops a bit `v` of `V` (if any; positions `≥ |V|` are ignored)
   and pushes `v || (sel && s = pos)`, halting `false` if `sel`, `v` and `s = pos` (a point
   hit twice); at the `sep` a selected row pops one target bit (if any); then the rest of `V`
   is appended.  At the end of the input accept iff `K` is empty.

`spkv_exec_ver`: the program halts with `spkv_vres (dec z).1 (dec z).2` on every input `z`,
within `spkv_Tver |z|` steps.
-/

namespace Pnp.Karp.SetPacking

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM Pnp.Karp.SetCover

/-! ## Semantics -/

/-- Whether the row `r` (selected iff `sel`) hits a point already set in `V`. -/
def spkv_clash (sel : Bool) : List SatSym → Str → Bool
  | s :: r, v :: V => (sel && v && decide (s = pos)) || spkv_clash sel r V
  | _, _ => false

/-- What the main loop computes (`V`: covered vector, `K`: target, `y`: unread bits). -/
def spkv_go : Str → Str → List (List SatSym) → Str → Bool
  | _, K, [], _ => K.isEmpty
  | V, K, r :: rows, y =>
    if spkv_clash (y.headD false) r V then false
    else spkv_go (scv_or (y.headD false) r V) (if y.headD false then K.tail else K) rows y.tail

/-- The answer of the verifier on `(w, y)`. -/
def spkv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | u :: kr :: rows =>
    spkv_go (List.replicate u.length false) (List.replicate kr.length true) rows y
  | _ => false

theorem spkv_clash_cons (sel : Bool) (s : SatSym) (r : List SatSym) (V : Str) :
    spkv_clash sel (s :: r) V =
      ((sel && V.headD false && decide (s = pos)) || spkv_clash sel r V.tail) := by
  rcases V with _ | ⟨v, V⟩
  · cases r <;> simp [spkv_clash]
  · simp [spkv_clash]

/-! ## Scanning a row -/

def spkv_cP (sel : Bool) : Cmd :=
  .pop 4 .skip (.push 5 sel) (if sel then .halt false else .push 5 true)

def spkv_cS : Bool → Cmd
  | true => .pop 6 .brk .brk .brk
  | false => .brk

def spkv_fin : Cmd := .pop 6 (.halt true) (.halt false) (.halt false)

def spkv_rB (sel : Bool) : Cmd :=
  .pop 3 spkv_fin (.pop 3 (.halt false) (spkv_cS sel) scv_cZ)
    (.pop 3 (.halt false) (spkv_cP sel) scv_cZ)

def spkv_rL (sel : Bool) : Cmd := .loop (spkv_rB sel)

theorem spkv_ex_fin (R Q V W K : Str) :
    ExecLe spkv_fin (xv_st R Q V W K) (.halt K.isEmpty) 2 := by
  rcases K with _ | ⟨b, K⟩
  · exact ExecLe.pop_nil rfl (ExecLe.halt true _)
  · exact ExecLe.pop_same (b := b) (s := K) rfl (ExecLe.halt false _)

theorem spkv_pop2r (sel : Bool) {R Q V W K : Str} (s : SatSym) {r : Res} {T' : ℕ}
    (h : ExecLe (xv_sel s (spkv_cS sel) scv_cZ (spkv_cP sel) scv_cZ) (xv_st R Q V W K) r T') :
    ExecLe (spkv_rB sel) (xv_st R (ic s ++ Q) V W K) r (T' + 2) := xv_pop2 s h

theorem spkv_ex_sym (sel : Bool) (R Q W K : Str) (s : SatSym) (hs : s ≠ sep) (V : Str) :
    ExecLe (spkv_rB sel) (xv_st R (ic s ++ Q) V W K)
      (if (sel && V.headD false && decide (s = pos)) = true then .halt false
        else .norm (xv_st R Q V.tail (scv_pre sel [s] V ++ W) K)) 4 := by
  refine spkv_pop2r sel s ?_
  rcases V with _ | ⟨v, V⟩ <;> cases s <;> (try exact absurd rfl hs) <;>
    simp only [xv_sel, scv_cZ, spkv_cP]
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [scv_pre]) le_rfl
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [scv_pre]) le_rfl
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [scv_pre]) le_rfl
  all_goals
    refine ExecLe.pop_cons (b := v) (s := V) rfl ?_
    cases v <;> cases sel <;> simp only [if_true, if_false, Bool.false_eq_true]
  all_goals first
    | exact (ExecLe.push 5 _ _).cast (by simp [scv_pre]) le_rfl
    | exact (ExecLe.halt false _).cast (by simp) (by omega)

theorem spkv_ex_row (sel : Bool) (R Q' : Str) : ∀ (r : List SatSym) (V W K : Str), sep ∉ r →
    ExecLe (spkv_rL sel) (xv_st R (r.flatMap ic ++ false :: false :: Q') V W K)
      (if spkv_clash sel r V = true then .halt false else
        .norm (xv_st R Q' (V.drop r.length) ((scv_pre sel r V).reverse ++ W)
          (if sel then K.tail else K)))
      (4 * r.length + 4)
  | [], V, W, K, _ => by
    cases sel
    · have hb := spkv_pop2r false (R := R) (Q := Q') (V := V) (W := W) (K := K) sep
        (r := .brk (xv_st R Q' V W K)) (T' := 1) (ExecLe.brk _)
      exact (ExecLe.loop_brk hb).cast (by simp [scv_pre, spkv_clash]) (by simp)
    · rcases K with _ | ⟨b, K⟩
      · have hb := spkv_pop2r true (R := R) (Q := Q') (V := V) (W := W) (K := []) sep
          (r := .brk (xv_st R Q' V W [])) (T' := 2) (ExecLe.pop_nil rfl (ExecLe.brk _))
        exact (ExecLe.loop_brk hb).cast (by simp [scv_pre, spkv_clash]) (by simp)
      · have hb := spkv_pop2r true (R := R) (Q := Q') (V := V) (W := W) (K := b :: K) sep
          (r := .brk (xv_st R Q' V W K)) (T' := 2)
          (ExecLe.pop_same (b := b) (s := K) rfl (by rw [xv_u6]; exact ExecLe.brk _))
        exact (ExecLe.loop_brk hb).cast (by simp [scv_pre, spkv_clash]) (by simp)
  | s :: r, V, W, K, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have hb := spkv_ex_sym sel R (r.flatMap ic ++ false :: false :: Q') W K s hs V
    simp only [List.flatMap_cons, List.append_assoc]
    rw [spkv_clash_cons]
    by_cases hc : (sel && V.headD false && decide (s = pos)) = true
    · rw [if_pos hc] at hb
      rw [hc, Bool.true_or, if_pos rfl]
      exact (ExecLe.loop_halt hb).cast rfl (by omega)
    · rw [if_neg hc] at hb
      rw [Bool.eq_false_iff.2 hc, Bool.false_or]
      have ih := spkv_ex_row sel R Q' r V.tail (scv_pre sel [s] V ++ W) K hr'
      refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
      rw [scv_pre_cons sel s r V, List.drop_tail, List.reverse_append, List.append_assoc,
        List.length_cons, scv_pre_single_rev]

theorem spkv_ex_rowEnd (sel : Bool) (R V W K : Str) :
    ExecLe (spkv_rL sel) (xv_st R [] V W K) (.halt K.isEmpty) 3 :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (spkv_ex_fin R [] V W K))

/-! ## One row, the main loop -/

def spkv_rC (sel : Bool) : Cmd := .seq (spkv_rL sel) (.seq (move 4 5) (move 5 4))

theorem spkv_ex_rC (sel : Bool) (R Q' : Str) (r : List SatSym) (V K : Str) (hr : sep ∉ r) :
    ExecLe (spkv_rC sel) (xv_st R (r.flatMap ic ++ false :: false :: Q') V [] K)
      (if spkv_clash sel r V = true then .halt false else
        .norm (xv_st R Q' (scv_or sel r V) [] (if sel then K.tail else K)))
      (4 * r.length + 4 * V.length + 8) := by
  have h1 := spkv_ex_row sel R Q' r V [] K hr
  by_cases hc : spkv_clash sel r V = true
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

def spkv_mB : Cmd := .pop 0 (spkv_rC false) (spkv_rC false) (spkv_rC true)

def spkv_mL : Cmd := .loop spkv_mB

theorem spkv_ex_mB {R Q V W K : Str} {r : Res} {T : ℕ}
    (h : ExecLe (spkv_rC (R.headD false)) (xv_st R.tail Q V W K) r T) :
    ExecLe spkv_mB (xv_st R Q V W K) r (T + 1) := by
  rcases R with _ | ⟨_ | _, R'⟩
  · exact ExecLe.pop_nil rfl h
  · exact ExecLe.pop_cons (b := false) (s := R') rfl (by rw [xv_u0]; exact h)
  · exact ExecLe.pop_cons (b := true) (s := R') rfl (by rw [xv_u0]; exact h)

/-- Cost of the main loop. -/
def spkv_Tm (N : ℕ) : List (List SatSym) → ℕ
  | [] => 5
  | r :: rows => 4 * r.length + 4 * N + 9 + spkv_Tm N rows

theorem spkv_Tm_eq (N : ℕ) : ∀ rows : List (List SatSym),
    spkv_Tm N rows = 4 * (rows.map List.length).sum + rows.length * (4 * N + 9) + 5
  | [] => by simp [spkv_Tm]
  | r :: rows => by simp only [spkv_Tm, spkv_Tm_eq N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem spkv_ex_main (N : ℕ) : ∀ (rows : List (List SatSym)) (R V K : Str),
    (∀ r ∈ rows, sep ∉ r) → V.length ≤ N →
    ExecLe spkv_mL (xv_st R (enc rows) V [] K) (.halt (spkv_go V K rows R)) (spkv_Tm N rows)
  | [], R, V, K, _, _ => by
    have h : ExecLe spkv_mB (xv_st R [] V [] K) (.halt K.isEmpty) 4 :=
      spkv_ex_mB (ExecLe.seq_halt (spkv_ex_rowEnd (R.headD false) R.tail V [] K))
    exact (ExecLe.loop_halt h).cast (by simp [spkv_go]) (by simp [spkv_Tm])
  | r :: rows, R, V, K, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    rw [enc_cons]
    have hb := spkv_ex_mB (spkv_ex_rC (R.headD false) R.tail (enc rows) r V K hr)
    by_cases hc : spkv_clash (R.headD false) r V = true
    · rw [if_pos hc] at hb
      exact (ExecLe.loop_halt hb).cast (by rw [spkv_go, if_pos hc]) (by simp [spkv_Tm]; omega)
    · rw [if_neg hc] at hb
      have hl := scv_or_length (R.headD false) r V
      have ih := spkv_ex_main N rows R.tail (scv_or (R.headD false) r V)
        (if R.headD false then K.tail else K) hrs (by omega)
      exact (ExecLe.loop_norm hb ih).cast (by rw [spkv_go, if_neg hc])
        (by simp [spkv_Tm]; omega)

/-! ## The whole verifier -/

/-- The SET PACKING verifier program. -/
def spkv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq xv_hL (.seq scv_bL spkv_mL))))

/-- Time bound of the verifier. -/
def spkv_Tver (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (3 * n + 3) +
  (3 * n + 3) + (4 * n + n * (4 * n + 9) + 5)

theorem spkv_exec_ver (z : Str) :
    ExecLe spkv_ver (init [z]).stk (.halt (spkv_vres (dec z).1 (dec z).2))
      (spkv_Tver z.length) := by
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
  unfold spkv_vres spkv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨t, _ | ⟨kr, rows⟩⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq xv_hL (.seq scv_bL spkv_mL)) (xv_st y (enc []) [] [] []) (.halt false)
        2 := ExecLe.seq_halt (xv_ex_hdEnd y)
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, spkv_Tver]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    have hH := xv_ex_hd y (enc []) t [] (hsep t (by simp))
    rw [List.append_nil] at hH
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.map_nil, List.sum_nil,
      List.length_nil] at hsum
    have hf := hH.seq_norm (ExecLe.seq_halt (d := spkv_mL) (scv_ex_bdEnd y _))
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, spkv_Tver]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons, enc_cons] at hpre
    have hH := xv_ex_hd y (enc (kr :: rows)) t [] (hsep t (by simp))
    rw [List.append_nil, enc_cons] at hH
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hB := scv_ex_bd y (enc rows) (List.replicate t.length false) kr [] (hsep kr (by simp))
    rw [List.append_nil] at hB
    have hR := spkv_ex_main z.length rows y (List.replicate t.length false)
      (List.replicate kr.length true) (fun r hr => hsep r (by simp [hr])) (by simp; omega)
    refine (hpre _ _ _ (hH.seq_norm (hB.seq_norm hR))).cast rfl ?_
    rw [spkv_Tm_eq]
    simp only [htl, spkv_Tver]
    have h1 : rows.length * (4 * z.length + 9) ≤ z.length * (4 * z.length + 9) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem spkv_Tver_le (n : ℕ) : spkv_Tver n ≤ tb 5 n := by
  unfold spkv_Tver tb
  have hm : 2 ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  norm_num at hm
  have e : (n + 2) ^ 5 = (n + 2) ^ 3 * (n + 2) ^ 2 := by ring
  have : 8 * (n + 2) ^ 2 ≤ (n + 2) ^ 3 * (n + 2) ^ 2 := Nat.mul_le_mul_right _ hm
  nlinarith

end Pnp.Karp.SetPacking
