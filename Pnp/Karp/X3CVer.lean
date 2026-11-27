import Pnp.Karp.ThreeDM
import Pnp.Karp.CliqueVer

/-!
# EXACT COVER BY 3-SETS ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/ThreeDM.lean`) and a certificate `y : List Bool` (bit `i` says whether row `i` of
the sets is selected; missing bits are `false`).  Stack layout:

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the covered vector `V` (bit `p`: position `p` is covered by a selected row so far);
* `5`: the new covered vector of the current row (reversed);  `6`: the unary counter `K` of
  the `pos` entries still allowed in the current row (`3` at the start of a row).

Program (`xv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3`: parse the code of `w`, drop the unfinished tail;
2. `xv_hL`: read the header row, pushing one `false` per symbol onto `V` (halt `false` if
   there is no row); `xv_k3`: `K := 3`;
3. `xv_mL`: per row, pop a certificate bit `sel` and scan the row together with `V`
   (`xv_rL sel`): every symbol pops a bit `v` of `V` and pushes the new bit (`v`, or
   `v || sel` for `pos`, which also pops `K`; halt `false` if `sel`, `v` and `pos`); at the
   `sep` both `V` and `K` must be empty (so the row has length `|V|` and exactly three `pos`);
   then `V` := the new vector, `K := 3`.  At the end of the input accept iff every bit of `V`
   is set (`xv_fin`).

`xv_exec_ver`: the program halts with `xv_vres (dec z).1 (dec z).2` on every input `z`,
within `xv_Tver |z|` steps.
-/

namespace Pnp.Karp.ThreeDM

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

/-! ## Semantics -/

/-- The scan of a row `r` selected iff `sel` against the covered vector `V`, with `k` more
`pos` entries required: the new covered vector, or `none` (rejection). -/
def xv_rs (sel : Bool) : List SatSym → Str → ℕ → Option Str
  | [], [], k => if k = 0 then some [] else none
  | [], _ :: _, _ => none
  | _ :: _, [], _ => none
  | s :: r, v :: V, k =>
    if s = pos then
      (if k = 0 then none else if sel && v then none else
        (xv_rs sel r V (k - 1)).map ((v || sel) :: ·))
    else (xv_rs sel r V k).map (v :: ·)

/-- What the main loop computes (`V`: covered vector, `y`: unread certificate bits). -/
def xv_go : Str → List (List SatSym) → Str → Bool
  | V, [], _ => V.all id
  | V, r :: rows, y => (xv_rs (y.headD false) r V 3).elim false (fun V' => xv_go V' rows y.tail)

/-- The answer of the verifier on `(w, y)`. -/
def xv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | u :: rows => xv_go (List.replicate u.length false) rows y

theorem xv_rs_length (sel : Bool) : ∀ (r : List SatSym) (V : Str) (k : ℕ) (V' : Str),
    xv_rs sel r V k = some V' → V'.length = V.length
  | [], [], k, V', h => by
    simp only [xv_rs] at h; split_ifs at h; cases h; rfl
  | [], _ :: _, _, _, h => by simp [xv_rs] at h
  | _ :: _, [], _, _, h => by simp [xv_rs] at h
  | s :: r, v :: V, k, V', h => by
    simp only [xv_rs] at h
    split_ifs at h
    · obtain ⟨V'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      simp [xv_rs_length sel r V _ V'' h1]
    · obtain ⟨V'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      simp [xv_rs_length sel r V _ V'' h1]

/-! ## Stack layout -/

/-- The stacks of the verifier. -/
def xv_st (R Q V W K : Str) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 4 then V else if j = 5 then W else
  if j = 6 then K else []

local macro "xv_stx" : tactic =>
  `(tactic| (funext j; simp only [xv_st, update_apply]; split_ifs <;> simp_all))

section St
variable {R Q V W K : Str}
@[simp] theorem xv_st_0 : xv_st R Q V W K 0 = R := rfl
@[simp] theorem xv_st_3 : xv_st R Q V W K 3 = Q := rfl
@[simp] theorem xv_st_4 : xv_st R Q V W K 4 = V := rfl
@[simp] theorem xv_st_5 : xv_st R Q V W K 5 = W := rfl
@[simp] theorem xv_st_6 : xv_st R Q V W K 6 = K := rfl
@[simp] theorem xv_u0 (R' : Str) : update (xv_st R Q V W K) 0 R' = xv_st R' Q V W K := by xv_stx
@[simp] theorem xv_u3 (Q' : Str) : update (xv_st R Q V W K) 3 Q' = xv_st R Q' V W K := by xv_stx
@[simp] theorem xv_u4 (V' : Str) : update (xv_st R Q V W K) 4 V' = xv_st R Q V' W K := by xv_stx
@[simp] theorem xv_u5 (W' : Str) : update (xv_st R Q V W K) 5 W' = xv_st R Q V W' K := by xv_stx
@[simp] theorem xv_u6 (K' : Str) : update (xv_st R Q V W K) 6 K' = xv_st R Q V W K' := by xv_stx
end St

/-- Select a branch by a symbol. -/
def xv_sel (s : SatSym) (cS cZ cP cN : Cmd) : Cmd :=
  match s with
  | sep => cS
  | zero => cZ
  | pos => cP
  | neg => cN

theorem xv_pop2 {R Q V W K : Str} {cE cX cS cZ cP cN : Cmd} (s : SatSym) {r : Res}
    {T' : ℕ} (h : ExecLe (xv_sel s cS cZ cP cN) (xv_st R Q V W K) r T') :
    ExecLe (.pop 3 cE (.pop 3 cX cS cZ) (.pop 3 cX cP cN)) (xv_st R (ic s ++ Q) V W K) r
      (T' + 2) := by
  cases s with
  | sep => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [xv_sel] using h))
  | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [xv_sel] using h))
  | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [xv_sel] using h))
  | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [xv_sel] using h))

/-! ## The final check -/

def xv_finB : Cmd := .pop 4 (.halt true) (.halt false) .skip

def xv_fin : Cmd := .loop xv_finB

theorem xv_ex_fin (R Q W K : Str) : ∀ V : Str,
    ExecLe xv_fin (xv_st R Q V W K) (.halt (V.all id)) (2 * V.length + 2)
  | [] => (ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt true _))).cast (by simp) (by simp)
  | false :: V => (ExecLe.loop_halt (ExecLe.pop_cons (b := false) (s := V) rfl
      (ExecLe.halt false _))).cast (by simp) (by simp)
  | true :: V => by
    have ih := xv_ex_fin R Q W K V
    have hb : ExecLe xv_finB (xv_st R Q (true :: V) W K) (.norm (xv_st R Q V W K)) 2 :=
      ExecLe.pop_cons (b := true) (s := V) rfl (by rw [xv_u4]; exact ExecLe.skip _)
    exact (ExecLe.loop_norm hb ih).cast (by simp) (by simp; omega)

/-! ## Scanning a row -/

def xv_cZ : Cmd := .pop 4 (.halt false) (.push 5 false) (.push 5 true)

def xv_cP (sel : Bool) : Cmd :=
  .pop 6 (.halt false) (.halt false)
    (.pop 4 (.halt false) (.push 5 sel) (if sel then .halt false else .push 5 true))

def xv_cS : Cmd := .pop 4 (.pop 6 .brk (.halt false) (.halt false)) (.halt false) (.halt false)

def xv_rB (sel : Bool) : Cmd :=
  .pop 3 xv_fin (.pop 3 (.halt false) xv_cS xv_cZ) (.pop 3 (.halt false) (xv_cP sel) xv_cZ)

def xv_rL (sel : Bool) : Cmd := .loop (xv_rB sel)

theorem xv_sel_np (sel : Bool) {s : SatSym} (hp : s ≠ pos) (hs : s ≠ sep) :
    xv_sel s xv_cS xv_cZ (xv_cP sel) xv_cZ = xv_cZ := by
  cases s <;> simp_all [xv_sel]

theorem xv_pop2r (sel : Bool) {R Q V W K : Str} (s : SatSym) {r : Res} {T' : ℕ}
    (h : ExecLe (xv_sel s xv_cS xv_cZ (xv_cP sel) xv_cZ) (xv_st R Q V W K) r T') :
    ExecLe (xv_rB sel) (xv_st R (ic s ++ Q) V W K) r (T' + 2) := xv_pop2 s h

theorem xv_ex_cZ (R Q W K : Str) (v : Bool) (V : Str) :
    ExecLe xv_cZ (xv_st R Q (v :: V) W K) (.norm (xv_st R Q V (v :: W) K)) 2 := by
  refine ExecLe.pop_cons (b := v) (s := V) rfl ?_
  cases v
  · exact (ExecLe.push 5 false _).cast (by simp) le_rfl
  · exact (ExecLe.push 5 true _).cast (by simp) le_rfl

theorem xv_ex_row (sel : Bool) (R Q' : Str) : ∀ (r : List SatSym) (V W : Str) (k : ℕ), sep ∉ r →
    ExecLe (xv_rL sel) (xv_st R (r.flatMap ic ++ false :: false :: Q') V W (List.replicate k true))
      ((xv_rs sel r V k).elim (.halt false) (fun V' => .norm (xv_st R Q' [] (V'.reverse ++ W) [])))
      (6 * r.length + 6)
  | [], [], W, 0, _ => by
    have hb := xv_pop2r sel (R := R) (Q := Q') (V := []) (W := W) (K := []) sep
      (r := .brk (xv_st R Q' [] W [])) (T' := 3)
      (ExecLe.pop_nil rfl (ExecLe.pop_nil rfl (ExecLe.brk _)))
    exact (ExecLe.loop_brk hb).cast (by simp [xv_rs]) (by simp)
  | [], [], W, k + 1, _ => by
    have hb := xv_pop2r sel (R := R) (Q := Q') (V := []) (W := W) (K := List.replicate (k + 1) true) sep
      (r := .halt false) (T' := 3)
      (ExecLe.pop_nil rfl (ExecLe.pop_cons (b := true) (s := List.replicate k true) rfl
        (ExecLe.halt false _)))
    exact (ExecLe.loop_halt hb).cast (by simp [xv_rs]) (by simp)
  | [], v :: V, W, k, _ => by
    have hb := xv_pop2r sel (R := R) (Q := Q') (V := v :: V) (W := W) (K := List.replicate k true) sep
      (r := .halt false) (T' := 2)
      (ExecLe.pop_same (b := v) (s := V) rfl (ExecLe.halt false _))
    exact (ExecLe.loop_halt hb).cast (by simp [xv_rs]) (by simp)
  | s :: r, [], W, k, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have e : xv_rs sel (s :: r) [] k = none := by simp [xv_rs]
    rw [e]
    simp only [List.flatMap_cons, List.append_assoc]
    by_cases hp : s = pos
    · subst hp
      rcases k with _ | k
      · exact (ExecLe.loop_halt (xv_pop2r sel (R := R) (Q := r.flatMap ic ++ false :: false :: Q')
          (V := []) (W := W) (K := []) pos (ExecLe.pop_nil rfl (ExecLe.halt false _)))).cast rfl
          (by simp)
      · exact (ExecLe.loop_halt (xv_pop2r sel (R := R) (Q := r.flatMap ic ++ false :: false :: Q')
          (V := []) (W := W) (K := List.replicate (k + 1) true) pos (ExecLe.pop_cons (b := true)
          (s := List.replicate k true) rfl (ExecLe.pop_nil rfl (ExecLe.halt false _))))).cast rfl
          (by simp)
    · have hb := xv_pop2r sel (R := R) (Q := r.flatMap ic ++ false :: false :: Q')
        (V := []) (W := W) (K := List.replicate k true) s
        (by rw [xv_sel_np sel hp hs]; exact ExecLe.pop_nil rfl (ExecLe.halt false _))
      exact (ExecLe.loop_halt hb).cast rfl (by simp)
  | s :: r, v :: V, W, k, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    simp only [List.flatMap_cons, List.append_assoc]
    by_cases hp : s ≠ pos
    · have ih := xv_ex_row sel R Q' r V (v :: W) k hr'
      have hb := xv_pop2r sel (R := R) (Q := r.flatMap ic ++ false :: false :: Q')
        (V := v :: V) (W := W) (K := List.replicate k true) s
        (by rw [xv_sel_np sel hp hs]; exact xv_ex_cZ _ _ _ _ v V)
      refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
      simp only [xv_rs, if_neg hp]
      rcases xv_rs sel r V k with _ | V' <;> simp
    · simp only [ne_eq, not_not] at hp
      subst hp
      rcases k with _ | k
      · exact (ExecLe.loop_halt (xv_pop2r sel (R := R) (Q := r.flatMap ic ++ false :: false :: Q')
          (V := v :: V) (W := W) (K := []) pos (ExecLe.pop_nil rfl (ExecLe.halt false _)))).cast
          (by simp [xv_rs]) (by simp)
      · have hK : ExecLe (xv_cP sel) (xv_st R (r.flatMap ic ++ false :: false :: Q') (v :: V) W
            (List.replicate (k + 1) true))
            (if sel && v then .halt false else
              .norm (xv_st R (r.flatMap ic ++ false :: false :: Q') V ((v || sel) :: W)
                (List.replicate k true))) 3 := by
          refine ExecLe.pop_cons (b := true) (s := List.replicate k true) rfl ?_
          refine ExecLe.pop_cons (b := v) (s := V) (by simp) ?_
          cases v <;> cases sel
          · exact (ExecLe.push 5 false _).cast (by simp) le_rfl
          · exact (ExecLe.push 5 true _).cast (by simp) le_rfl
          · exact (ExecLe.push 5 true _).cast (by simp) le_rfl
          · exact (ExecLe.halt false _).cast (by simp) (by omega)
        have hb := xv_pop2r sel (R := R) (Q := r.flatMap ic ++ false :: false :: Q')
          (V := v :: V) (W := W) (K := List.replicate (k + 1) true) pos hK
        by_cases hsv : (sel && v) = true
        · rw [if_pos hsv] at hb
          exact (ExecLe.loop_halt hb).cast (by simp [xv_rs, hsv]) (by simp)
        · rw [if_neg hsv] at hb
          have ih := xv_ex_row sel R Q' r V ((v || sel) :: W) k hr'
          refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
          simp only [xv_rs, if_true, hsv, Nat.add_sub_cancel, if_false, Nat.add_one_ne_zero]
          rcases xv_rs sel r V k with _ | V' <;> simp

theorem xv_ex_rowEnd (sel : Bool) (R V W K : Str) :
    ExecLe (xv_rL sel) (xv_st R [] V W K) (.halt (V.all id)) (2 * V.length + 3) :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (xv_ex_fin R [] W K V))

/-! ## One row, the main loop -/

def xv_k3 : Cmd := .seq (.push 6 true) (.seq (.push 6 true) (.push 6 true))

theorem xv_ex_k3 (R Q V W : Str) :
    ExecLe xv_k3 (xv_st R Q V W []) (.norm (xv_st R Q V W (List.replicate 3 true))) 3 :=
  ((ExecLe.push 6 true _).seq_norm ((ExecLe.push 6 true _).seq_norm
    (ExecLe.push 6 true _))).cast (by simp) le_rfl

def xv_rC (sel : Bool) : Cmd := .seq (xv_rL sel) (.seq (move 5 4) xv_k3)

theorem xv_ex_rC (sel : Bool) (R Q' : Str) (r : List SatSym) (V : Str) (hr : sep ∉ r) :
    ExecLe (xv_rC sel) (xv_st R (r.flatMap ic ++ false :: false :: Q') V [] (List.replicate 3 true))
      ((xv_rs sel r V 3).elim (.halt false)
        (fun V' => .norm (xv_st R Q' V' [] (List.replicate 3 true))))
      (6 * r.length + 2 * V.length + 11) := by
  have h1 := xv_ex_row sel R Q' r V [] 3 hr
  rcases h : xv_rs sel r V 3 with _ | V'
  · rw [h] at h1
    exact (ExecLe.seq_halt h1).cast rfl (by omega)
  · rw [h] at h1
    have hl := xv_rs_length sel r V 3 V' h
    have hM := exec_move (a := 5) (b := 4) (by decide) (V'.reverse ++ [])
      (xv_st R Q' [] (V'.reverse ++ []) []) rfl
    have e : update (update (xv_st R Q' [] (V'.reverse ++ []) []) 5 []) 4
        ((V'.reverse ++ []).reverse ++ xv_st R Q' [] (V'.reverse ++ []) [] 4) =
        xv_st R Q' V' [] [] := by simp
    rw [e] at hM
    exact (h1.seq_norm ((ExecLe.of hM).seq_norm (xv_ex_k3 R Q' V' []))).cast rfl
      (by simp; omega)

def xv_mB : Cmd := .pop 0 (xv_rC false) (xv_rC false) (xv_rC true)

def xv_mL : Cmd := .loop xv_mB

theorem xv_ex_mB {R Q V W K : Str} {r : Res} {T : ℕ}
    (h : ExecLe (xv_rC (R.headD false)) (xv_st R.tail Q V W K) r T) :
    ExecLe xv_mB (xv_st R Q V W K) r (T + 1) := by
  rcases R with _ | ⟨_ | _, R'⟩
  · exact ExecLe.pop_nil rfl h
  · exact ExecLe.pop_cons (b := false) (s := R') rfl (by rw [xv_u0]; exact h)
  · exact ExecLe.pop_cons (b := true) (s := R') rfl (by rw [xv_u0]; exact h)

/-- Cost of the main loop. -/
def xv_Tm (N : ℕ) : List (List SatSym) → ℕ
  | [] => 2 * N + 4
  | r :: rows => 6 * r.length + 2 * N + 12 + xv_Tm N rows

theorem xv_Tm_eq (N : ℕ) : ∀ rows : List (List SatSym),
    xv_Tm N rows = 6 * (rows.map List.length).sum + rows.length * (2 * N + 12) + 2 * N + 4
  | [] => by simp [xv_Tm]
  | r :: rows => by simp only [xv_Tm, xv_Tm_eq N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem xv_ex_main (N : ℕ) : ∀ (rows : List (List SatSym)) (R V : Str),
    (∀ r ∈ rows, sep ∉ r) → V.length ≤ N →
    ExecLe xv_mL (xv_st R (enc rows) V [] (List.replicate 3 true)) (.halt (xv_go V rows R))
      (xv_Tm N rows)
  | [], R, V, _, hN => by
    have h : ExecLe xv_mB (xv_st R [] V [] (List.replicate 3 true)) (.halt (V.all id))
        (2 * V.length + 4) :=
      xv_ex_mB (ExecLe.seq_halt (xv_ex_rowEnd (R.headD false) R.tail V [] (List.replicate 3 true)))
    exact (ExecLe.loop_halt h).cast (by simp [xv_go]) (by simp [xv_Tm]; omega)
  | r :: rows, R, V, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    rw [enc_cons]
    have hb := xv_ex_mB (xv_ex_rC (R.headD false) R.tail (enc rows) r V hr)
    rcases h : xv_rs (R.headD false) r V 3 with _ | V'
    · rw [h] at hb
      exact (ExecLe.loop_halt hb).cast (by simp only [xv_go]; rw [h]; rfl) (by simp [xv_Tm]; omega)
    · rw [h] at hb
      have hl := xv_rs_length _ r V 3 V' h
      have ih := xv_ex_main N rows R.tail V' hrs (by omega)
      exact (ExecLe.loop_norm hb ih).cast (by simp only [xv_go]; rw [h]; rfl) (by simp [xv_Tm]; omega)

/-! ## The header row -/

def xv_hB : Cmd :=
  .pop 3 (.halt false) (.pop 3 (.halt false) .brk (.push 4 false))
    (.pop 3 (.halt false) (.push 4 false) (.push 4 false))

def xv_hL : Cmd := .loop xv_hB

theorem xv_ex_hd (R Q' : Str) : ∀ (t : List SatSym) (V : Str), sep ∉ t →
    ExecLe xv_hL (xv_st R (t.flatMap ic ++ false :: false :: Q') V [] [])
      (.norm (xv_st R Q' (List.replicate t.length false ++ V) [] [])) (3 * t.length + 3)
  | [], V, _ => by
    have hb := xv_pop2 (cE := .halt false) (cX := .halt false) (cZ := .push 4 false)
      (cP := .push 4 false) (cN := .push 4 false) (R := R) (Q := Q') (V := V) (W := [])
      (K := []) sep (r := .brk (xv_st R Q' V [] [])) (T' := 1) (ExecLe.brk _)
    exact (ExecLe.loop_brk hb).cast (by simp) (by simp)
  | s :: t, V, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := xv_ex_hd R Q' t (false :: V) (fun e => hr (List.mem_cons_of_mem _ e))
    have hp : ExecLe (xv_sel s .brk (.push 4 false) (.push 4 false) (.push 4 false))
        (xv_st R (t.flatMap ic ++ false :: false :: Q') V [] [])
        (.norm (xv_st R (t.flatMap ic ++ false :: false :: Q') (false :: V) [] [])) 1 := by
      cases s with
      | sep => exact absurd rfl hs
      | _ => exact (ExecLe.push 4 false _).cast (by simp) le_rfl
    have hb := xv_pop2 (cE := .halt false) (cX := .halt false) s hp
    simp only [List.flatMap_cons, List.append_assoc]
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp [List.replicate_succ']

theorem xv_ex_hdEnd (R : Str) : ExecLe xv_hL (xv_st R [] [] [] []) (.halt false) 2 :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt false _))

/-! ## The whole verifier -/

def xv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq xv_hL (.seq xv_k3 xv_mL))))

/-- Time bound of the verifier. -/
def xv_Tver (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (3 * n + 3) + 3 +
  (6 * n + n * (2 * n + 12) + 2 * n + 4)

theorem xv_exec_ver (z : Str) :
    ExecLe xv_ver (init [z]).stk (.halt (xv_vres (dec z).1 (dec z).2)) (xv_Tver z.length) := by
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
  unfold xv_vres xv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨t, rows⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq xv_hL (.seq xv_k3 xv_mL)) (xv_st y (enc []) [] [] []) (.halt false) 2 :=
      ExecLe.seq_halt (xv_ex_hdEnd y)
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, xv_Tver]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    have hH := xv_ex_hd y (enc rows) t [] (hsep t (by simp))
    rw [List.append_nil] at hH
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hK := xv_ex_k3 y (enc rows) (List.replicate t.length false) []
    have hR := xv_ex_main z.length rows y (List.replicate t.length false)
      (fun r hr => hsep r (by simp [hr])) (by simp; omega)
    refine (hpre _ _ _ (hH.seq_norm (hK.seq_norm hR))).cast rfl ?_
    rw [xv_Tm_eq]
    simp only [htl, xv_Tver]
    have h1 : rows.length * (2 * z.length + 12) ≤ z.length * (2 * z.length + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem xv_Tver_le (n : ℕ) : xv_Tver n ≤ tb 5 n := by
  unfold xv_Tver tb
  have hm : 2 ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  norm_num at hm
  have e : (n + 2) ^ 5 = (n + 2) ^ 3 * (n + 2) ^ 2 := by ring
  have : 8 * (n + 2) ^ 2 ≤ (n + 2) ^ 3 * (n + 2) ^ 2 := Nat.mul_le_mul_right _ hm
  nlinarith

end Pnp.Karp.ThreeDM
