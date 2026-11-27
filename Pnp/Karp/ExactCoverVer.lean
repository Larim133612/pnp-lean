import Pnp.Karp.ExactCover
import Pnp.Karp.CliqueVer

/-!
# EXACT COVER ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/ExactCover.lean`) and a certificate `y : List Bool` (bit `i` says whether row `i` of
the sets is selected; missing bits are `false`).  It is the X3C verifier
(`Pnp/Karp/X3CVer.lean`) without the count of the `pos` entries of a row.  Stack layout:

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the covered vector `V` (bit `p`: position `p` is covered by a selected row so far);
* `5`: the new covered vector of the current row (reversed).

Program (`ecv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3`: parse the code of `w`, drop the unfinished tail;
2. `ecv_hL`: read the header row, pushing one `false` per symbol onto `V` (halt `false` if
   there is no row);
3. `ecv_mL`: per row, pop a certificate bit `sel` and scan the row together with `V`
   (`ecv_rL sel`): every symbol pops a bit `v` of `V` and pushes the new bit (`v`, or
   `v || sel` for `pos`; halt `false` if `sel`, `v` and `pos`); at the `sep` `V` must be empty
   (so the row has length `|V|`); then `V` := the new vector.  At the end of the input accept
   iff every bit of `V` is set (`ecv_fin`).

`ecv_exec_ver`: the program halts with `ecv_vres (dec z).1 (dec z).2` on every input `z`,
within `ecv_Tver |z|` steps.
-/

namespace Pnp.Karp.ExactCover

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.ThreeDM

/-! ## Semantics -/

/-- The scan of a row `r` selected iff `sel` against the covered vector `V`: the new covered
vector, or `none` (rejection). -/
def ecv_rs (sel : Bool) : List SatSym → Str → Option Str
  | [], [] => some []
  | [], _ :: _ => none
  | _ :: _, [] => none
  | s :: r, v :: V =>
    if s = pos then
      (if sel && v then none else (ecv_rs sel r V).map ((v || sel) :: ·))
    else (ecv_rs sel r V).map (v :: ·)

/-- What the main loop computes (`V`: covered vector, `y`: unread certificate bits). -/
def ecv_go : Str → List (List SatSym) → Str → Bool
  | V, [], _ => V.all id
  | V, r :: rows, y => (ecv_rs (y.headD false) r V).elim false (fun V' => ecv_go V' rows y.tail)

/-- The answer of the verifier on `(w, y)`. -/
def ecv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | u :: rows => ecv_go (List.replicate u.length false) rows y

theorem ecv_rs_length (sel : Bool) : ∀ (r : List SatSym) (V : Str) (V' : Str),
    ecv_rs sel r V = some V' → V'.length = V.length
  | [], [], V', h => by
    simp only [ecv_rs] at h; cases h; rfl
  | [], _ :: _, _, h => by simp [ecv_rs] at h
  | _ :: _, [], _, h => by simp [ecv_rs] at h
  | s :: r, v :: V, V', h => by
    simp only [ecv_rs] at h
    split_ifs at h
    · obtain ⟨V'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      simp [ecv_rs_length sel r V V'' h1]
    · obtain ⟨V'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      simp [ecv_rs_length sel r V V'' h1]

/-! ## Stack layout -/

/-- The stacks of the verifier. -/
def ecv_st (R Q V W : Str) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 4 then V else if j = 5 then W else []

local macro "ecv_stx" : tactic =>
  `(tactic| (funext j; simp only [ecv_st, update_apply]; split_ifs <;> simp_all))

section St
variable {R Q V W : Str}
@[simp] theorem ecv_st_0 : ecv_st R Q V W 0 = R := rfl
@[simp] theorem ecv_st_3 : ecv_st R Q V W 3 = Q := rfl
@[simp] theorem ecv_st_4 : ecv_st R Q V W 4 = V := rfl
@[simp] theorem ecv_st_5 : ecv_st R Q V W 5 = W := rfl
@[simp] theorem ecv_u0 (R' : Str) : update (ecv_st R Q V W) 0 R' = ecv_st R' Q V W := by ecv_stx
@[simp] theorem ecv_u3 (Q' : Str) : update (ecv_st R Q V W) 3 Q' = ecv_st R Q' V W := by ecv_stx
@[simp] theorem ecv_u4 (V' : Str) : update (ecv_st R Q V W) 4 V' = ecv_st R Q V' W := by ecv_stx
@[simp] theorem ecv_u5 (W' : Str) : update (ecv_st R Q V W) 5 W' = ecv_st R Q V W' := by ecv_stx
end St

/-- Select a branch by a symbol. -/
def ecv_sel (s : SatSym) (cS cZ cP cN : Cmd) : Cmd :=
  match s with
  | sep => cS
  | zero => cZ
  | pos => cP
  | neg => cN

theorem ecv_pop2 {R Q V W : Str} {cE cX cS cZ cP cN : Cmd} (s : SatSym) {r : Res}
    {T' : ℕ} (h : ExecLe (ecv_sel s cS cZ cP cN) (ecv_st R Q V W) r T') :
    ExecLe (.pop 3 cE (.pop 3 cX cS cZ) (.pop 3 cX cP cN)) (ecv_st R (ic s ++ Q) V W) r
      (T' + 2) := by
  cases s with
  | sep => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [ecv_sel] using h))
  | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [ecv_sel] using h))
  | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [ecv_sel] using h))
  | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [ecv_sel] using h))

/-! ## The final check -/

def ecv_finB : Cmd := .pop 4 (.halt true) (.halt false) .skip

def ecv_fin : Cmd := .loop ecv_finB

theorem ecv_ex_fin (R Q W : Str) : ∀ V : Str,
    ExecLe ecv_fin (ecv_st R Q V W) (.halt (V.all id)) (2 * V.length + 2)
  | [] => (ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt true _))).cast (by simp) (by simp)
  | false :: V => (ExecLe.loop_halt (ExecLe.pop_cons (b := false) (s := V) rfl
      (ExecLe.halt false _))).cast (by simp) (by simp)
  | true :: V => by
    have ih := ecv_ex_fin R Q W V
    have hb : ExecLe ecv_finB (ecv_st R Q (true :: V) W) (.norm (ecv_st R Q V W)) 2 :=
      ExecLe.pop_cons (b := true) (s := V) rfl (by rw [ecv_u4]; exact ExecLe.skip _)
    exact (ExecLe.loop_norm hb ih).cast (by simp) (by simp; omega)

/-! ## Scanning a row -/

def ecv_cZ : Cmd := .pop 4 (.halt false) (.push 5 false) (.push 5 true)

def ecv_cP (sel : Bool) : Cmd :=
  .pop 4 (.halt false) (.push 5 sel) (if sel then .halt false else .push 5 true)

def ecv_cS : Cmd := .pop 4 .brk (.halt false) (.halt false)

def ecv_rB (sel : Bool) : Cmd :=
  .pop 3 ecv_fin (.pop 3 (.halt false) ecv_cS ecv_cZ) (.pop 3 (.halt false) (ecv_cP sel) ecv_cZ)

def ecv_rL (sel : Bool) : Cmd := .loop (ecv_rB sel)

theorem ecv_sel_np (sel : Bool) {s : SatSym} (hp : s ≠ pos) (hs : s ≠ sep) :
    ecv_sel s ecv_cS ecv_cZ (ecv_cP sel) ecv_cZ = ecv_cZ := by
  cases s <;> simp_all [ecv_sel]

theorem ecv_pop2r (sel : Bool) {R Q V W : Str} (s : SatSym) {r : Res} {T' : ℕ}
    (h : ExecLe (ecv_sel s ecv_cS ecv_cZ (ecv_cP sel) ecv_cZ) (ecv_st R Q V W) r T') :
    ExecLe (ecv_rB sel) (ecv_st R (ic s ++ Q) V W) r (T' + 2) := ecv_pop2 s h

theorem ecv_ex_cZ (R Q W : Str) (v : Bool) (V : Str) :
    ExecLe ecv_cZ (ecv_st R Q (v :: V) W) (.norm (ecv_st R Q V (v :: W))) 2 := by
  refine ExecLe.pop_cons (b := v) (s := V) rfl ?_
  cases v
  · exact (ExecLe.push 5 false _).cast (by simp) le_rfl
  · exact (ExecLe.push 5 true _).cast (by simp) le_rfl

theorem ecv_ex_row (sel : Bool) (R Q' : Str) : ∀ (r : List SatSym) (V W : Str), sep ∉ r →
    ExecLe (ecv_rL sel) (ecv_st R (r.flatMap ic ++ false :: false :: Q') V W)
      ((ecv_rs sel r V).elim (.halt false) (fun V' => .norm (ecv_st R Q' [] (V'.reverse ++ W))))
      (6 * r.length + 6)
  | [], [], W, _ => by
    have hb := ecv_pop2r sel (R := R) (Q := Q') (V := []) (W := W) sep
      (r := .brk (ecv_st R Q' [] W)) (T' := 2)
      (ExecLe.pop_nil rfl (ExecLe.brk _))
    exact (ExecLe.loop_brk hb).cast (by simp [ecv_rs]) (by simp)
  | [], v :: V, W, _ => by
    have hb := ecv_pop2r sel (R := R) (Q := Q') (V := v :: V) (W := W) sep
      (r := .halt false) (T' := 2)
      (ExecLe.pop_same (b := v) (s := V) rfl (ExecLe.halt false _))
    exact (ExecLe.loop_halt hb).cast (by simp [ecv_rs]) (by simp)
  | s :: r, [], W, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have e : ecv_rs sel (s :: r) [] = none := by simp [ecv_rs]
    rw [e]
    simp only [List.flatMap_cons, List.append_assoc]
    by_cases hp : s = pos
    · subst hp
      exact (ExecLe.loop_halt (ecv_pop2r sel (R := R) (Q := r.flatMap ic ++ false :: false :: Q')
          (V := []) (W := W) pos (ExecLe.pop_nil rfl (ExecLe.halt false _)))).cast rfl
          (by simp)
    · have hb := ecv_pop2r sel (R := R) (Q := r.flatMap ic ++ false :: false :: Q')
        (V := []) (W := W) s
        (by rw [ecv_sel_np sel hp hs]; exact ExecLe.pop_nil rfl (ExecLe.halt false _))
      exact (ExecLe.loop_halt hb).cast rfl (by simp)
  | s :: r, v :: V, W, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    simp only [List.flatMap_cons, List.append_assoc]
    by_cases hp : s ≠ pos
    · have ih := ecv_ex_row sel R Q' r V (v :: W) hr'
      have hb := ecv_pop2r sel (R := R) (Q := r.flatMap ic ++ false :: false :: Q')
        (V := v :: V) (W := W) s
        (by rw [ecv_sel_np sel hp hs]; exact ecv_ex_cZ _ _ _ v V)
      refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
      simp only [ecv_rs, if_neg hp]
      rcases ecv_rs sel r V with _ | V' <;> simp
    · simp only [ne_eq, not_not] at hp
      subst hp
      have hK : ExecLe (ecv_cP sel) (ecv_st R (r.flatMap ic ++ false :: false :: Q') (v :: V) W)
          (if sel && v then .halt false else
            .norm (ecv_st R (r.flatMap ic ++ false :: false :: Q') V ((v || sel) :: W))) 2 := by
        refine ExecLe.pop_cons (b := v) (s := V) (by simp) ?_
        cases v <;> cases sel
        · exact (ExecLe.push 5 false _).cast (by simp) le_rfl
        · exact (ExecLe.push 5 true _).cast (by simp) le_rfl
        · exact (ExecLe.push 5 true _).cast (by simp) le_rfl
        · exact (ExecLe.halt false _).cast (by simp) (by omega)
      have hb := ecv_pop2r sel (R := R) (Q := r.flatMap ic ++ false :: false :: Q')
        (V := v :: V) (W := W) pos hK
      by_cases hsv : (sel && v) = true
      · rw [if_pos hsv] at hb
        exact (ExecLe.loop_halt hb).cast (by simp [ecv_rs, hsv]) (by simp)
      · rw [if_neg hsv] at hb
        have ih := ecv_ex_row sel R Q' r V ((v || sel) :: W) hr'
        refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
        simp only [ecv_rs, if_true, hsv]
        rcases ecv_rs sel r V with _ | V' <;> simp

theorem ecv_ex_rowEnd (sel : Bool) (R V W : Str) :
    ExecLe (ecv_rL sel) (ecv_st R [] V W) (.halt (V.all id)) (2 * V.length + 3) :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (ecv_ex_fin R [] W V))

/-! ## One row, the main loop -/

def ecv_rC (sel : Bool) : Cmd := .seq (ecv_rL sel) (move 5 4)

theorem ecv_ex_rC (sel : Bool) (R Q' : Str) (r : List SatSym) (V : Str) (hr : sep ∉ r) :
    ExecLe (ecv_rC sel) (ecv_st R (r.flatMap ic ++ false :: false :: Q') V [])
      ((ecv_rs sel r V).elim (.halt false) (fun V' => .norm (ecv_st R Q' V' [])))
      (6 * r.length + 2 * V.length + 11) := by
  have h1 := ecv_ex_row sel R Q' r V [] hr
  rcases h : ecv_rs sel r V with _ | V'
  · rw [h] at h1
    exact (ExecLe.seq_halt h1).cast rfl (by omega)
  · rw [h] at h1
    have hl := ecv_rs_length sel r V V' h
    have hM := exec_move (a := 5) (b := 4) (by decide) (V'.reverse ++ [])
      (ecv_st R Q' [] (V'.reverse ++ [])) rfl
    have e : update (update (ecv_st R Q' [] (V'.reverse ++ [])) 5 []) 4
        ((V'.reverse ++ []).reverse ++ ecv_st R Q' [] (V'.reverse ++ []) 4) =
        ecv_st R Q' V' [] := by simp
    rw [e] at hM
    exact (h1.seq_norm (ExecLe.of hM)).cast rfl (by simp; omega)

def ecv_mB : Cmd := .pop 0 (ecv_rC false) (ecv_rC false) (ecv_rC true)

def ecv_mL : Cmd := .loop ecv_mB

theorem ecv_ex_mB {R Q V W : Str} {r : Res} {T : ℕ}
    (h : ExecLe (ecv_rC (R.headD false)) (ecv_st R.tail Q V W) r T) :
    ExecLe ecv_mB (ecv_st R Q V W) r (T + 1) := by
  rcases R with _ | ⟨_ | _, R'⟩
  · exact ExecLe.pop_nil rfl h
  · exact ExecLe.pop_cons (b := false) (s := R') rfl (by rw [ecv_u0]; exact h)
  · exact ExecLe.pop_cons (b := true) (s := R') rfl (by rw [ecv_u0]; exact h)

/-- Cost of the main loop. -/
def ecv_Tm (N : ℕ) : List (List SatSym) → ℕ
  | [] => 2 * N + 4
  | r :: rows => 6 * r.length + 2 * N + 12 + ecv_Tm N rows

theorem ecv_Tm_eq (N : ℕ) : ∀ rows : List (List SatSym),
    ecv_Tm N rows = 6 * (rows.map List.length).sum + rows.length * (2 * N + 12) + 2 * N + 4
  | [] => by simp [ecv_Tm]
  | r :: rows => by simp only [ecv_Tm, ecv_Tm_eq N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem ecv_ex_main (N : ℕ) : ∀ (rows : List (List SatSym)) (R V : Str),
    (∀ r ∈ rows, sep ∉ r) → V.length ≤ N →
    ExecLe ecv_mL (ecv_st R (enc rows) V []) (.halt (ecv_go V rows R)) (ecv_Tm N rows)
  | [], R, V, _, hN => by
    have h : ExecLe ecv_mB (ecv_st R [] V []) (.halt (V.all id)) (2 * V.length + 4) :=
      ecv_ex_mB (ExecLe.seq_halt (ecv_ex_rowEnd (R.headD false) R.tail V []))
    exact (ExecLe.loop_halt h).cast (by simp [ecv_go]) (by simp [ecv_Tm]; omega)
  | r :: rows, R, V, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    rw [enc_cons]
    have hb := ecv_ex_mB (ecv_ex_rC (R.headD false) R.tail (enc rows) r V hr)
    rcases h : ecv_rs (R.headD false) r V with _ | V'
    · rw [h] at hb
      exact (ExecLe.loop_halt hb).cast (by simp only [ecv_go]; rw [h]; rfl)
        (by simp [ecv_Tm]; omega)
    · rw [h] at hb
      have hl := ecv_rs_length _ r V V' h
      have ih := ecv_ex_main N rows R.tail V' hrs (by omega)
      exact (ExecLe.loop_norm hb ih).cast (by simp only [ecv_go]; rw [h]; rfl)
        (by simp [ecv_Tm]; omega)

/-! ## The header row -/

def ecv_hB : Cmd :=
  .pop 3 (.halt false) (.pop 3 (.halt false) .brk (.push 4 false))
    (.pop 3 (.halt false) (.push 4 false) (.push 4 false))

def ecv_hL : Cmd := .loop ecv_hB

theorem ecv_ex_hd (R Q' : Str) : ∀ (t : List SatSym) (V : Str), sep ∉ t →
    ExecLe ecv_hL (ecv_st R (t.flatMap ic ++ false :: false :: Q') V [])
      (.norm (ecv_st R Q' (List.replicate t.length false ++ V) [])) (3 * t.length + 3)
  | [], V, _ => by
    have hb := ecv_pop2 (cE := .halt false) (cX := .halt false) (cZ := .push 4 false)
      (cP := .push 4 false) (cN := .push 4 false) (R := R) (Q := Q') (V := V) (W := [])
      sep (r := .brk (ecv_st R Q' V [])) (T' := 1) (ExecLe.brk _)
    exact (ExecLe.loop_brk hb).cast (by simp) (by simp)
  | s :: t, V, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := ecv_ex_hd R Q' t (false :: V) (fun e => hr (List.mem_cons_of_mem _ e))
    have hp : ExecLe (ecv_sel s .brk (.push 4 false) (.push 4 false) (.push 4 false))
        (ecv_st R (t.flatMap ic ++ false :: false :: Q') V [])
        (.norm (ecv_st R (t.flatMap ic ++ false :: false :: Q') (false :: V) [])) 1 := by
      cases s with
      | sep => exact absurd rfl hs
      | _ => exact (ExecLe.push 4 false _).cast (by simp) le_rfl
    have hb := ecv_pop2 (cE := .halt false) (cX := .halt false) s hp
    simp only [List.flatMap_cons, List.append_assoc]
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp [List.replicate_succ']

theorem ecv_ex_hdEnd (R : Str) : ExecLe ecv_hL (ecv_st R [] [] []) (.halt false) 2 :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt false _))

/-! ## The whole verifier -/

def ecv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq ecv_hL ecv_mL)))

/-- Time bound of the verifier. -/
def ecv_Tver (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (3 * n + 3) +
  (6 * n + n * (2 * n + 12) + 2 * n + 4)

theorem ecv_exec_ver (z : Str) :
    ExecLe ecv_ver (init [z]).stk (.halt (ecv_vres (dec z).1 (dec z).2)) (ecv_Tver z.length) := by
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
      ecv_st y (enc (clauses w)) [] [] := by
    funext j
    simp only [σ₂, σ₁, ecv_st, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ), ExecLe c (ecv_st y (enc (clauses w)) [] []) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold ecv_vres ecv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨t, rows⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq ecv_hL ecv_mL) (ecv_st y (enc []) [] []) (.halt false) 2 :=
      ExecLe.seq_halt (ecv_ex_hdEnd y)
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, ecv_Tver]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    have hH := ecv_ex_hd y (enc rows) t [] (hsep t (by simp))
    rw [List.append_nil] at hH
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hR := ecv_ex_main z.length rows y (List.replicate t.length false)
      (fun r hr => hsep r (by simp [hr])) (by simp; omega)
    refine (hpre _ _ _ (hH.seq_norm hR)).cast rfl ?_
    rw [ecv_Tm_eq]
    simp only [htl, ecv_Tver]
    have h1 : rows.length * (2 * z.length + 12) ≤ z.length * (2 * z.length + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem ecv_Tver_le (n : ℕ) : ecv_Tver n ≤ tb 5 n := by
  unfold ecv_Tver tb
  have hm : 2 ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  norm_num at hm
  have e : (n + 2) ^ 5 = (n + 2) ^ 3 * (n + 2) ^ 2 := by ring
  have : 8 * (n + 2) ^ 2 ≤ (n + 2) ^ 3 * (n + 2) ^ 2 := Nat.mul_le_mul_right _ hm
  nlinarith

end Pnp.Karp.ExactCover
