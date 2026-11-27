import Pnp.Karp.HittingSet
import Pnp.Karp.CliqueVer

/-!
# HITTING SET ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/HittingSet.lean`, rows `u :: kr :: rs`) and a certificate `y : List Bool` (bit `p`
says whether position `p < |u|` is in the hitting set; missing bits are `false`).  Stack layout:

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the indicator vector `V = hsv_pad y |u|` (the first `|u|` certificate bits, padded);
* `5`: the scanned part of `V` (reversed);  `6`: a unary counter / the hit flag.

Program (`hsv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3`: parse the code of `w`, drop the unfinished tail;
2. `hsv_hL`: read the header row `u`, popping one certificate bit per symbol, pushing it onto
   stack `5` and pushing a `true` onto stack `6` for every set bit (halt `false` if there is no
   row); `move 5 4` puts `V` on stack `4`;
3. `hsv_bL`: read the budget row `kr`, popping the counter once per symbol; at its `sep` the
   counter must be empty (halt `false` otherwise or if there is no row);
4. `hsv_mL`: per row `r`, scan `r` in parallel with `V` (`hsv_rL`): every symbol pops a bit `v`
   of `V` (if any), saves it on stack `5` and sets the flag if `v` and the symbol is `pos`; at
   the `sep` the flag must be set (halt `false` otherwise); `move 5 4` restores `V`.  At the end
   of the input accept.

`hsv_exec_ver`: the program halts with `hsv_vres (dec z).1 (dec z).2` on every input `z`,
within `hsv_Tver |z|` steps.
-/

namespace Pnp.Karp.HittingSet

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

/-! ## Semantics -/

/-- The first `n` bits of `R`, padded with `false`. -/
def hsv_pad : Str → ℕ → Str
  | _, 0 => []
  | R, n + 1 => R.headD false :: hsv_pad R.tail n

/-- Does the row `r` contain `pos` at a position whose bit of `V` is set? -/
def hsv_hit : List SatSym → Str → Bool
  | s :: r, v :: V => (v && decide (s = pos)) || hsv_hit r V
  | _, _ => false

/-- The answer of the verifier on `(w, y)`. -/
def hsv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | u :: kr :: rs => decide ((hsv_pad y u.length).count true ≤ kr.length) &&
      rs.all fun r => hsv_hit r (hsv_pad y u.length)
  | _ => false

@[simp] theorem hsv_hit_nil : ∀ r : List SatSym, hsv_hit r [] = false
  | [] => rfl
  | _ :: _ => rfl

theorem hsv_pad_length : ∀ (R : Str) (n : ℕ), (hsv_pad R n).length = n
  | _, 0 => rfl
  | R, n + 1 => by simp [hsv_pad, hsv_pad_length R.tail n]

/-! ## Stack layout -/

/-- The stacks of the verifier. -/
def hsv_st (R Q V W K : Str) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 4 then V else if j = 5 then W else
  if j = 6 then K else []

local macro "hsv_stx" : tactic =>
  `(tactic| (funext j; simp only [hsv_st, update_apply]; split_ifs <;> simp_all))

section St
variable {R Q V W K : Str}
@[simp] theorem hsv_st_0 : hsv_st R Q V W K 0 = R := rfl
@[simp] theorem hsv_st_3 : hsv_st R Q V W K 3 = Q := rfl
@[simp] theorem hsv_st_4 : hsv_st R Q V W K 4 = V := rfl
@[simp] theorem hsv_st_5 : hsv_st R Q V W K 5 = W := rfl
@[simp] theorem hsv_st_6 : hsv_st R Q V W K 6 = K := rfl
@[simp] theorem hsv_u0 (R' : Str) : update (hsv_st R Q V W K) 0 R' = hsv_st R' Q V W K := by
  hsv_stx
@[simp] theorem hsv_u3 (Q' : Str) : update (hsv_st R Q V W K) 3 Q' = hsv_st R Q' V W K := by
  hsv_stx
@[simp] theorem hsv_u4 (V' : Str) : update (hsv_st R Q V W K) 4 V' = hsv_st R Q V' W K := by
  hsv_stx
@[simp] theorem hsv_u5 (W' : Str) : update (hsv_st R Q V W K) 5 W' = hsv_st R Q V W' K := by
  hsv_stx
@[simp] theorem hsv_u6 (K' : Str) : update (hsv_st R Q V W K) 6 K' = hsv_st R Q V W K' := by
  hsv_stx
end St

/-- Select a branch by a symbol. -/
def hsv_sel (s : SatSym) (cS cZ cP cN : Cmd) : Cmd :=
  match s with
  | sep => cS
  | zero => cZ
  | pos => cP
  | neg => cN

theorem hsv_pop2 {R Q V W K : Str} {cE cX cS cZ cP cN : Cmd} (s : SatSym) {r : Res}
    {T' : ℕ} (h : ExecLe (hsv_sel s cS cZ cP cN) (hsv_st R Q V W K) r T') :
    ExecLe (.pop 3 cE (.pop 3 cX cS cZ) (.pop 3 cX cP cN)) (hsv_st R (ic s ++ Q) V W K) r
      (T' + 2) := by
  cases s with
  | sep => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [hsv_sel] using h))
  | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [hsv_sel] using h))
  | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [hsv_sel] using h))
  | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [hsv_sel] using h))

/-- Popping an empty stack `3` in the two-bit dispatch. -/
theorem hsv_pop2_nil {R V W K : Str} {cE cX cS cZ cP cN : Cmd} {r : Res} {T' : ℕ}
    (h : ExecLe cE (hsv_st R [] V W K) r T') :
    ExecLe (.pop 3 cE (.pop 3 cX cS cZ) (.pop 3 cX cP cN)) (hsv_st R [] V W K) r (T' + 1) :=
  ExecLe.pop_nil rfl h

/-! ## The header row -/

def hsv_hZ : Cmd := .pop 0 (.push 5 false) (.push 5 false) (.seq (.push 5 true) (.push 6 true))

def hsv_hB : Cmd :=
  .pop 3 (.halt false) (.pop 3 (.halt false) .brk hsv_hZ) (.pop 3 (.halt false) hsv_hZ hsv_hZ)

def hsv_hL : Cmd := .loop hsv_hB

theorem hsv_ex_hZ (R Q W : Str) (c : ℕ) :
    ExecLe hsv_hZ (hsv_st R Q [] W (List.replicate c true))
      (.norm (hsv_st R.tail Q [] (R.headD false :: W)
        (List.replicate (c + if R.headD false then 1 else 0) true))) 3 := by
  rcases R with _ | ⟨_ | _, R'⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.push 5 false _)).cast (by simp) (by omega)
  · exact (ExecLe.pop_cons (b := false) (s := R') rfl
      (by rw [hsv_u0]; exact ExecLe.push 5 false _)).cast (by simp) (by omega)
  · refine (ExecLe.pop_cons (b := true) (s := R') rfl (by
      rw [hsv_u0]; exact (ExecLe.push 5 true _).seq_norm (ExecLe.push 6 true _))).cast ?_ le_rfl
    simp [List.replicate_succ]

theorem hsv_ex_hd (Q' : Str) : ∀ (t : List SatSym) (R W : Str) (c : ℕ), sep ∉ t →
    ExecLe hsv_hL (hsv_st R (t.flatMap ic ++ false :: false :: Q') [] W (List.replicate c true))
      (.norm (hsv_st (R.drop t.length) Q' [] ((hsv_pad R t.length).reverse ++ W)
        (List.replicate ((hsv_pad R t.length).count true + c) true))) (5 * t.length + 3)
  | [], R, W, c, _ => by
    have hb := hsv_pop2 (cE := .halt false) (cX := .halt false) (cZ := hsv_hZ) (cP := hsv_hZ)
      (cN := hsv_hZ) (R := R) (Q := Q') (V := []) (W := W) (K := List.replicate c true) sep
      (ExecLe.brk _)
    exact (ExecLe.loop_brk hb).cast (by simp [hsv_pad]) (by simp)
  | s :: t, R, W, c, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := hsv_ex_hd Q' t R.tail (R.headD false :: W)
      (c + if R.headD false then 1 else 0) (fun e => hr (List.mem_cons_of_mem _ e))
    have hp : ExecLe (hsv_sel s .brk hsv_hZ hsv_hZ hsv_hZ)
        (hsv_st R (t.flatMap ic ++ false :: false :: Q') [] W (List.replicate c true))
        (.norm (hsv_st R.tail (t.flatMap ic ++ false :: false :: Q') [] (R.headD false :: W)
          (List.replicate (c + if R.headD false then 1 else 0) true))) 3 := by
      cases s with
      | sep => exact absurd rfl hs
      | _ => exact hsv_ex_hZ _ _ _ _
    have hb := hsv_pop2 (cE := .halt false) (cX := .halt false) s hp
    simp only [List.flatMap_cons, List.append_assoc]
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 2
    · simp [List.drop_tail]
    · simp [hsv_pad]
    · simp only [hsv_pad, List.count_cons, List.length_cons]
      congr 1
      cases R.headD false <;> simp; omega

theorem hsv_ex_hdEnd (R W K : Str) : ExecLe hsv_hL (hsv_st R [] [] W K) (.halt false) 2 :=
  ExecLe.loop_halt (hsv_pop2_nil (ExecLe.halt false _))

/-! ## The budget row -/

def hsv_bZ : Cmd := .pop 6 .skip .skip .skip

def hsv_bS : Cmd := .pop 6 .brk (.halt false) (.halt false)

def hsv_bB : Cmd :=
  .pop 3 (.halt false) (.pop 3 (.halt false) hsv_bS hsv_bZ) (.pop 3 (.halt false) hsv_bZ hsv_bZ)

def hsv_bL : Cmd := .loop hsv_bB

theorem hsv_ex_bZ (R Q V W : Str) (c : ℕ) :
    ExecLe hsv_bZ (hsv_st R Q V W (List.replicate c true))
      (.norm (hsv_st R Q V W (List.replicate (c - 1) true))) 2 := by
  rcases c with _ | c
  · exact ExecLe.pop_nil rfl (ExecLe.skip _)
  · exact (ExecLe.pop_cons (b := true) (s := List.replicate c true) rfl
      (by rw [hsv_u6]; exact ExecLe.skip _)).cast (by simp) le_rfl

theorem hsv_ex_bd (R Q' V W : Str) : ∀ (t : List SatSym) (c : ℕ), sep ∉ t →
    ExecLe hsv_bL (hsv_st R (t.flatMap ic ++ false :: false :: Q') V W (List.replicate c true))
      (if c ≤ t.length then .norm (hsv_st R Q' V W []) else .halt false) (4 * t.length + 4)
  | [], 0, _ => by
    have hb := hsv_pop2 (cE := .halt false) (cX := .halt false) (cZ := hsv_bZ) (cP := hsv_bZ)
      (cN := hsv_bZ) (cS := hsv_bS) (R := R) (Q := Q') (V := V) (W := W) (K := []) sep
      (ExecLe.pop_nil rfl (ExecLe.brk _))
    exact (ExecLe.loop_brk hb).cast (by simp) (by simp)
  | [], c + 1, _ => by
    have hb := hsv_pop2 (cE := .halt false) (cX := .halt false) (cZ := hsv_bZ) (cP := hsv_bZ)
      (cN := hsv_bZ) (cS := hsv_bS) (R := R) (Q := Q') (V := V) (W := W)
      (K := List.replicate (c + 1) true) sep
      (ExecLe.pop_cons (b := true) (s := List.replicate c true) rfl (ExecLe.halt false _))
    exact (ExecLe.loop_halt hb).cast (by simp) (by simp)
  | s :: t, c, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := hsv_ex_bd R Q' V W t (c - 1) (fun e => hr (List.mem_cons_of_mem _ e))
    have hp : ExecLe (hsv_sel s hsv_bS hsv_bZ hsv_bZ hsv_bZ)
        (hsv_st R (t.flatMap ic ++ false :: false :: Q') V W (List.replicate c true))
        (.norm (hsv_st R (t.flatMap ic ++ false :: false :: Q') V W
          (List.replicate (c - 1) true))) 2 := by
      cases s with
      | sep => exact absurd rfl hs
      | _ => exact hsv_ex_bZ _ _ _ _ _
    have hb := hsv_pop2 (cE := .halt false) (cX := .halt false) s hp
    simp only [List.flatMap_cons, List.append_assoc]
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp only [List.length_cons]
    congr 1
    exact propext (by omega)

theorem hsv_ex_bdEnd (R V W K : Str) : ExecLe hsv_bL (hsv_st R [] V W K) (.halt false) 2 :=
  ExecLe.loop_halt (hsv_pop2_nil (ExecLe.halt false _))

/-! ## Scanning a row -/

/-- The hit flag. -/
def hsv_F : Bool → Str
  | false => []
  | true => [true]

def hsv_cZ : Cmd := .pop 4 .skip (.push 5 false) (.push 5 true)

def hsv_setF : Cmd := .pop 6 (.push 6 true) (.push 6 true) (.push 6 true)

def hsv_cP : Cmd := .pop 4 .skip (.push 5 false) (.seq (.push 5 true) hsv_setF)

def hsv_cS : Cmd := .pop 6 (.halt false) .brk .brk

def hsv_rB : Cmd :=
  .pop 3 (.halt true) (.pop 3 (.halt false) hsv_cS hsv_cZ) (.pop 3 (.halt false) hsv_cP hsv_cZ)

def hsv_rL : Cmd := .loop hsv_rB

theorem hsv_ex_setF (R Q V W : Str) (f : Bool) :
    ExecLe hsv_setF (hsv_st R Q V W (hsv_F f)) (.norm (hsv_st R Q V W (hsv_F true))) 2 := by
  cases f
  · exact (ExecLe.pop_nil rfl (ExecLe.push 6 true _)).cast (by simp [hsv_F]) le_rfl
  · exact (ExecLe.pop_cons (b := true) (s := []) rfl
      (by rw [hsv_u6]; exact ExecLe.push 6 true _)).cast (by simp [hsv_F]) le_rfl

theorem hsv_ex_sym_nil (R Q W K : Str) {s : SatSym} (hs : s ≠ sep) :
    ExecLe (hsv_sel s hsv_cS hsv_cZ hsv_cP hsv_cZ) (hsv_st R Q [] W K)
      (.norm (hsv_st R Q [] W K)) 2 := by
  cases s with
  | sep => exact absurd rfl hs
  | pos => exact ExecLe.pop_nil rfl (ExecLe.skip _)
  | _ => exact ExecLe.pop_nil rfl (ExecLe.skip _)

theorem hsv_ex_sym (R Q W : Str) (v : Bool) (V : Str) (f : Bool) {s : SatSym} (hs : s ≠ sep) :
    ExecLe (hsv_sel s hsv_cS hsv_cZ hsv_cP hsv_cZ) (hsv_st R Q (v :: V) W (hsv_F f))
      (.norm (hsv_st R Q V (v :: W) (hsv_F (f || (v && decide (s = pos)))))) 4 := by
  have hZ : ExecLe hsv_cZ (hsv_st R Q (v :: V) W (hsv_F f))
      (.norm (hsv_st R Q V (v :: W) (hsv_F f))) 2 := by
    refine ExecLe.pop_cons (b := v) (s := V) rfl ?_
    cases v
    · exact (ExecLe.push 5 false _).cast (by simp) le_rfl
    · exact (ExecLe.push 5 true _).cast (by simp) le_rfl
  cases s with
  | sep => exact absurd rfl hs
  | pos =>
    refine ExecLe.pop_cons (b := v) (s := V) rfl ?_
    cases v
    · exact (ExecLe.push 5 false _).cast (by simp) (show 1 ≤ 3 by omega)
    · refine ((ExecLe.push 5 true _).seq_norm ?_).cast rfl (show 1 + 2 ≤ 3 by omega)
      simp only [hsv_u4, hsv_st_5, hsv_u5]
      exact (hsv_ex_setF _ _ _ _ f).cast (by simp) le_rfl
  | zero => exact (hZ.cast (by simp) (by omega))
  | neg => exact (hZ.cast (by simp) (by omega))

theorem hsv_ex_row (R Q' : Str) : ∀ (r : List SatSym) (V W : Str) (f : Bool), sep ∉ r →
    ExecLe hsv_rL (hsv_st R (r.flatMap ic ++ false :: false :: Q') V W (hsv_F f))
      (if (f || hsv_hit r V) = true then
        .norm (hsv_st R Q' (V.drop r.length) ((V.take r.length).reverse ++ W) [])
      else .halt false)
      (6 * r.length + 4)
  | [], V, W, false, _ => by
    have hb := hsv_pop2 (cE := .halt true) (cX := .halt false) (cZ := hsv_cZ) (cP := hsv_cP)
      (cN := hsv_cZ) (cS := hsv_cS) (R := R) (Q := Q') (V := V) (W := W) (K := []) sep
      (ExecLe.pop_nil rfl (ExecLe.halt false _))
    exact (ExecLe.loop_halt hb).cast (by cases V <;> simp [hsv_hit]) (by simp)
  | [], V, W, true, _ => by
    have hb := hsv_pop2 (cE := .halt true) (cX := .halt false) (cZ := hsv_cZ) (cP := hsv_cP)
      (cN := hsv_cZ) (cS := hsv_cS) (R := R) (Q := Q') (V := V) (W := W) (K := [true]) sep
      (ExecLe.pop_cons (b := true) (s := []) rfl (ExecLe.brk _))
    exact (ExecLe.loop_brk hb).cast (by simp) (by simp)
  | s :: r, [], W, f, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := hsv_ex_row R Q' r [] W f (fun e => hr (List.mem_cons_of_mem _ e))
    have hb := hsv_pop2 (cE := .halt true) (cX := .halt false) s
      (hsv_ex_sym_nil R (r.flatMap ic ++ false :: false :: Q') W (hsv_F f) hs)
    simp only [List.flatMap_cons, List.append_assoc]
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp
  | s :: r, v :: V, W, f, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := hsv_ex_row R Q' r V (v :: W) (f || (v && decide (s = pos)))
      (fun e => hr (List.mem_cons_of_mem _ e))
    have hb := hsv_pop2 (cE := .halt true) (cX := .halt false) s
      (hsv_ex_sym R (r.flatMap ic ++ false :: false :: Q') W v V f hs)
    simp only [List.flatMap_cons, List.append_assoc]
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp only [hsv_hit, Bool.or_assoc, List.length_cons, List.drop_succ_cons,
      List.take_succ_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem hsv_ex_rowEnd (R V W K : Str) : ExecLe hsv_rL (hsv_st R [] V W K) (.halt true) 2 :=
  ExecLe.loop_halt (hsv_pop2_nil (ExecLe.halt true _))

/-! ## The main loop -/

def hsv_mB : Cmd := .seq hsv_rL (move 5 4)

def hsv_mL : Cmd := .loop hsv_mB

/-- Cost of the main loop. -/
def hsv_Tm : List (List SatSym) → ℕ
  | [] => 2
  | r :: rows => 8 * r.length + 6 + hsv_Tm rows

theorem hsv_Tm_eq : ∀ rows : List (List SatSym),
    hsv_Tm rows = 8 * (rows.map List.length).sum + 6 * rows.length + 2
  | [] => by simp [hsv_Tm]
  | r :: rows => by simp only [hsv_Tm, hsv_Tm_eq rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem hsv_ex_main (R V : Str) : ∀ rows : List (List SatSym), (∀ r ∈ rows, sep ∉ r) →
    ExecLe hsv_mL (hsv_st R (enc rows) V [] []) (.halt (rows.all fun r => hsv_hit r V))
      (hsv_Tm rows)
  | [], _ => (ExecLe.loop_halt (ExecLe.seq_halt (hsv_ex_rowEnd R V [] []))).cast (by simp)
      (by simp [hsv_Tm])
  | r :: rows, hrows => by
    have hr : sep ∉ r := hrows r (by simp)
    have ih := hsv_ex_main R V rows fun r' h => hrows r' (by simp [h])
    rw [enc_cons]
    have h1 := hsv_ex_row R (enc rows) r V [] false hr
    simp only [Bool.false_or] at h1
    by_cases hh : hsv_hit r V = true
    · rw [if_pos hh] at h1
      have hM := exec_move (a := 5) (b := 4) (by decide) ((V.take r.length).reverse ++ [])
        (hsv_st R (enc rows) (V.drop r.length) ((V.take r.length).reverse ++ []) []) rfl
      have e : update (update (hsv_st R (enc rows) (V.drop r.length)
          ((V.take r.length).reverse ++ []) []) 5 []) 4
          (((V.take r.length).reverse ++ []).reverse ++ (hsv_st R (enc rows) (V.drop r.length)
            ((V.take r.length).reverse ++ []) []) 4) = hsv_st R (enc rows) V [] [] := by simp
      rw [e] at hM
      have hb := h1.seq_norm (ExecLe.of hM)
      refine (ExecLe.loop_norm hb ih).cast (by simp [hh]) ?_
      have : (V.take r.length).length ≤ r.length := by simp
      simp [hsv_Tm]; omega
    · rw [if_neg hh] at h1
      exact (ExecLe.loop_halt (ExecLe.seq_halt h1)).cast (by simp [hh]) (by simp [hsv_Tm]; omega)

/-! ## The whole verifier -/

def hsv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq hsv_hL (.seq (move 5 4)
    (.seq hsv_bL hsv_mL)))))

/-- Time bound of the verifier. -/
def hsv_Tver (n : ℕ) : ℕ := 20 * n + 30

theorem hsv_exec_ver (z : Str) :
    ExecLe hsv_ver (init [z]).stk (.halt (hsv_vres (dec z).1 (dec z).2))
      (hsv_Tver z.length) := by
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
      hsv_st y (enc (clauses w)) [] [] [] := by
    funext j
    simp only [σ₂, σ₁, hsv_st, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ), ExecLe c (hsv_st y (enc (clauses w)) [] [] []) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold hsv_vres hsv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨u, _ | ⟨kr, rows⟩⟩
  · rw [hcw] at hpre
    refine (hpre _ _ _ (ExecLe.seq_halt (hsv_ex_hdEnd y [] []))).cast rfl ?_
    simp only [htl, hsv_Tver]; omega
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    have hH := hsv_ex_hd [] u y [] 0 (hsep u (by simp))
    simp only [List.append_nil, Nat.add_zero] at hH
    have hMv := exec_move (a := 5) (b := 4) (by decide) (hsv_pad y u.length).reverse
      (hsv_st (y.drop u.length) [] [] (hsv_pad y u.length).reverse
        (List.replicate ((hsv_pad y u.length).count true) true)) rfl
    rw [hsv_u5, hsv_u4] at hMv
    have hB := hsv_ex_bdEnd (y.drop u.length) ((hsv_pad y u.length).reverse.reverse ++ []) []
      (List.replicate ((hsv_pad y u.length).count true) true)
    have := (hH.seq_norm ((ExecLe.of hMv).seq_norm (ExecLe.seq_halt (c := hsv_bL) (d := hsv_mL)
      (by simpa [enc] using hB))))
    refine (hpre _ _ _ this).cast rfl ?_
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.map_nil, List.sum_nil,
      List.length_nil] at hsum
    simp only [htl, hsv_Tver, List.length_reverse, hsv_pad_length]
    omega
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons, enc_cons] at hpre
    have hH := hsv_ex_hd (kr.flatMap ic ++ false :: false :: enc rows) u y [] 0 (hsep u (by simp))
    simp only [List.append_nil, Nat.add_zero] at hH
    have hMv := exec_move (a := 5) (b := 4) (by decide) (hsv_pad y u.length).reverse
      (hsv_st (y.drop u.length) (kr.flatMap ic ++ false :: false :: enc rows) []
        (hsv_pad y u.length).reverse
        (List.replicate ((hsv_pad y u.length).count true) true)) rfl
    rw [hsv_u5, hsv_u4] at hMv
    rw [show ∀ R Q W K : Str, hsv_st R Q [] W K 4 = [] from fun _ _ _ _ => rfl,
      List.reverse_reverse, List.append_nil] at hMv
    have hB := hsv_ex_bd (y.drop u.length) (enc rows) (hsv_pad y u.length) [] kr
      ((hsv_pad y u.length).count true) (hsep kr (by simp))
    have hR := hsv_ex_main (y.drop u.length) (hsv_pad y u.length) rows
      (fun r hr => hsep r (by simp [hr]))
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hTm := hsv_Tm_eq rows
    by_cases hc : (hsv_pad y u.length).count true ≤ kr.length
    · rw [if_pos hc] at hB
      have := hH.seq_norm ((ExecLe.of hMv).seq_norm (hB.seq_norm hR))
      refine (hpre _ _ _ this).cast (by simp [hc]) ?_
      simp only [htl, hsv_Tver, List.length_reverse, hsv_pad_length]
      omega
    · rw [if_neg hc] at hB
      have := hH.seq_norm ((ExecLe.of hMv).seq_norm (ExecLe.seq_halt (d := hsv_mL) hB))
      refine (hpre _ _ _ this).cast (by simp [hc]) ?_
      simp only [htl, hsv_Tver, List.length_reverse, hsv_pad_length]
      omega

theorem hsv_Tver_le (n : ℕ) : hsv_Tver n ≤ tb 5 n := by
  unfold hsv_Tver tb
  have hm : 2 ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  norm_num at hm
  have e : (n + 2) ^ 5 = (n + 2) ^ 3 * (n + 2) ^ 2 := by ring
  have : 8 * (n + 2) ^ 2 ≤ (n + 2) ^ 3 * (n + 2) ^ 2 := Nat.mul_le_mul_right _ hm
  nlinarith

end Pnp.Karp.HittingSet
