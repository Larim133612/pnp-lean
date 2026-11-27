import Pnp.Karp.SubsetSum
import Pnp.Karp.CliqueVer

/-!
# SUBSET SUM ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/SubsetSum.lean`) and a certificate `y : List Bool` (bit `i` says whether item `i`
is selected; missing bits are `false`).  Numbers are bit stacks, least significant bit on top.
Stack layout:

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the target `T`;  `5`: the accumulator `A`;  `6`: the sum bits of the current addition
  (reversed);  `7`: the carry flag;  `8`: a temporary (the target bits, reversed).

Program (`sv_ver`):
1. `phaseA`: parse the code of `w`; `trimC 2`: drop the unfinished tail; `move 2 3`;
2. `sv_frLoop`: read the first row (the target) onto stack `8` (halt `false` if there is no
   row); `move 8 4`;
3. `sv_mainLoop`: per row, pop a certificate bit; if it is set, add the row to the
   accumulator (ripple carry, `sv_addLoop`), otherwise skip the row (`sv_skipLoop`); at the
   end of the input compare the accumulator with the target (`sv_eqLoop`).

`sv_exec_ver`: the program halts with `sv_vres (dec z).1 (dec z).2` on every input `z`,
within `sv_Tver |z|` steps.
-/

namespace Pnp.Karp.SubsetSum

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics -/

/-- The value of a bit string, least significant bit first. -/
def sv_bval : Str → ℕ
  | [] => 0
  | b :: s => (if b then 1 else 0) + 2 * sv_bval s

/-- The bits of a row. -/
def sv_bits (r : List SatSym) : Str := r.map isPos

/-- Majority (the carry of a full adder). -/
def sv_maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- The sum bit of a full adder. -/
def sv_x3 (a b c : Bool) : Bool := xor a (xor b c)

/-- Add the carry `c` to `A`. -/
def sv_propL : Bool → Str → Str
  | c, [] => if c then [true] else []
  | c, a :: A => xor a c :: sv_propL (a && c) A

/-- Add `bs` and the carry `c` to `A` (as the program does it). -/
def sv_addL : Bool → Str → Str → Str
  | c, A, [] => sv_propL c A
  | c, A, b :: bs => sv_x3 (A.headD false) b c :: sv_addL (sv_maj (A.headD false) b c) A.tail bs

/-- Equality of the values (as the program checks it). -/
def sv_eqB : Str → Str → Bool
  | [], [] => true
  | [], b :: T => !b && sv_eqB [] T
  | a :: A, [] => !a && sv_eqB A []
  | a :: A, b :: T => (a == b) && sv_eqB A T

/-- What the main loop computes (`T`: target, `R`: unread certificate bits, `A`: accumulator). -/
def sv_goS (T : Str) : List (List SatSym) → Str → Str → Bool
  | [], _, A => sv_eqB A T
  | r :: rows, R, A =>
    sv_goS T rows R.tail (if R.headD false then sv_addL false A (sv_bits r) else A)

/-- The answer of the verifier on `(w, y)`. -/
def sv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | t :: as => sv_goS (sv_bits t) as y []

theorem sv_propL_length : ∀ (c : Bool) (A : Str), (sv_propL c A).length ≤ A.length + 1
  | c, [] => by cases c <;> simp [sv_propL]
  | c, a :: A => by have := sv_propL_length (a && c) A; simp [sv_propL]; omega

theorem sv_addL_length : ∀ (c : Bool) (A bs : Str),
    (sv_addL c A bs).length ≤ A.length + bs.length + 1
  | c, A, [] => by simpa [sv_addL] using sv_propL_length c A
  | c, A, b :: bs => by
    have := sv_addL_length (sv_maj (A.headD false) b c) A.tail bs
    have : A.tail.length ≤ A.length := by simp
    simp only [sv_addL, List.length_cons] at *; omega

/-! ## Stack layout -/

/-- The stacks of the main phase. -/
def sv_st (R Q T A S : Str) (c : Bool) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 4 then T else if j = 5 then A else
  if j = 6 then S else if j = 7 then CookLevin.fl c else []

/-- Equality of stack assignments. -/
local macro "sv_stx" : tactic =>
  `(tactic| (funext j; simp only [sv_st, update_apply, CookLevin.fl]; split_ifs <;> simp_all))

section St
variable {R Q T A S : Str} {c : Bool}
@[simp] theorem sv_st_0 : sv_st R Q T A S c 0 = R := rfl
@[simp] theorem sv_st_3 : sv_st R Q T A S c 3 = Q := rfl
@[simp] theorem sv_st_4 : sv_st R Q T A S c 4 = T := rfl
@[simp] theorem sv_st_5 : sv_st R Q T A S c 5 = A := rfl
@[simp] theorem sv_st_6 : sv_st R Q T A S c 6 = S := rfl
@[simp] theorem sv_st_7 : sv_st R Q T A S c 7 = CookLevin.fl c := rfl
theorem sv_u0 (R' : Str) : update (sv_st R Q T A S c) 0 R' = sv_st R' Q T A S c := by sv_stx
theorem sv_u3 (Q' : Str) : update (sv_st R Q T A S c) 3 Q' = sv_st R Q' T A S c := by sv_stx
theorem sv_u5 (A' : Str) : update (sv_st R Q T A S c) 5 A' = sv_st R Q T A' S c := by sv_stx
theorem sv_u6 (S' : Str) : update (sv_st R Q T A S c) 6 S' = sv_st R Q T A S' c := by sv_stx
theorem sv_u7n : update (sv_st R Q T A S c) 7 [] = sv_st R Q T A S false := by sv_stx
theorem sv_u7t : update (sv_st R Q T A S c) 7 [true] = sv_st R Q T A S true := by sv_stx
end St

/-! ## Comparison -/

def sv_eqB_cmd : Cmd :=
  .pop 5 (.pop 4 (.halt true) .skip (.halt false)) (.pop 4 .skip .skip (.halt false))
    (.pop 4 (.halt false) (.halt false) .skip)

def sv_eqLoop : Cmd := .loop sv_eqB_cmd

theorem sv_ex_eq : ∀ (A T : Str) (σ : ℕ → Str), σ 5 = A → σ 4 = T →
    ExecLe sv_eqLoop σ (.halt (sv_eqB A T)) (3 * (A.length + T.length) + 3)
  | [], [], σ, h5, h4 => (ExecLe.loop_halt (ExecLe.pop_nil h5 (ExecLe.pop_nil h4
      (ExecLe.halt true _)))).cast (by simp [sv_eqB]) (by simp)
  | [], b :: T, σ, h5, h4 => by
    cases b
    · have ih := sv_ex_eq [] T (update σ 4 T) (by simp [h5]) (by simp)
      exact (ExecLe.loop_norm (ExecLe.pop_nil h5 (ExecLe.pop_cons (b := false) h4
        (ExecLe.skip _))) ih).cast (by simp [sv_eqB]) (by simp ; omega)
    · exact (ExecLe.loop_halt (ExecLe.pop_nil h5 (ExecLe.pop_cons (b := true) h4
        (ExecLe.halt false _)))).cast (by simp [sv_eqB]) (by simp)
  | a :: A, [], σ, h5, h4 => by
    cases a
    · have ih := sv_ex_eq A [] (update σ 5 A) (by simp) (by simp [h4])
      exact (ExecLe.loop_norm (ExecLe.pop_cons (b := false) h5 (ExecLe.pop_nil
        (by simp [h4]) (ExecLe.skip _))) ih).cast (by simp [sv_eqB]) (by simp ; omega)
    · exact (ExecLe.loop_halt (ExecLe.pop_cons (b := true) h5 (ExecLe.pop_nil
        (by simp [h4]) (ExecLe.halt false _)))).cast (by simp [sv_eqB]) (by simp)
  | a :: A, b :: T, σ, h5, h4 => by
    have h4' : update σ 5 A 4 = b :: T := by simp [h4]
    cases a <;> cases b
    · have ih := sv_ex_eq A T (update (update σ 5 A) 4 T) (by simp) (by simp)
      exact (ExecLe.loop_norm (ExecLe.pop_cons (b := false) h5 (ExecLe.pop_cons (b := false) h4'
        (ExecLe.skip _))) ih).cast (by simp [sv_eqB]) (by simp ; omega)
    · exact (ExecLe.loop_halt (ExecLe.pop_cons (b := false) h5 (ExecLe.pop_cons (b := true) h4'
        (ExecLe.halt false _)))).cast (by simp [sv_eqB]) (by simp)
    · exact (ExecLe.loop_halt (ExecLe.pop_cons (b := true) h5 (ExecLe.pop_cons (b := false) h4'
        (ExecLe.halt false _)))).cast (by simp [sv_eqB]) (by simp)
    · have ih := sv_ex_eq A T (update (update σ 5 A) 4 T) (by simp) (by simp)
      exact (ExecLe.loop_norm (ExecLe.pop_cons (b := true) h5 (ExecLe.pop_cons (b := true) h4'
        (ExecLe.skip _))) ih).cast (by simp [sv_eqB]) (by simp ; omega)

/-! ## Addition -/

/-- Push the sum bit and set the carry. -/
def sv_out (a b c : Bool) : Cmd :=
  .seq (.push 6 (sv_x3 a b c)) (if sv_maj a b c then .push 7 true else .skip)

section Add
variable {R Q T A S : Str}

theorem sv_ex_out (a b c : Bool) :
    ExecLe (sv_out a b c) (sv_st R Q T A S false)
      (.norm (sv_st R Q T A (sv_x3 a b c :: S) (sv_maj a b c))) 2 := by
  unfold sv_out
  cases h : sv_maj a b c
  · exact ((ExecLe.push 6 _ _).seq_norm (ExecLe.skip _)).cast (by rw [sv_st_6, sv_u6]) le_rfl
  · refine ((ExecLe.push 6 _ _).seq_norm (ExecLe.push 7 true _)).cast ?_ le_rfl
    rw [sv_st_6, sv_u6]; congr 1; sv_stx

/-- A full adder step: pop the carry. -/
def sv_fa (b a : Bool) : Cmd := .pop 7 (sv_out a b false) (sv_out a b false) (sv_out a b true)

theorem sv_ex_fa (b a c : Bool) :
    ExecLe (sv_fa b a) (sv_st R Q T A S c)
      (.norm (sv_st R Q T A (sv_x3 a b c :: S) (sv_maj a b c))) 3 := by
  cases c
  · exact ExecLe.pop_nil rfl (sv_ex_out a b false)
  · exact ExecLe.pop_cons (b := true) (s := []) rfl (by rw [sv_u7n]; exact sv_ex_out a b true)

/-- A full adder step: pop the accumulator bit (missing = `0`). -/
def sv_addStep (b : Bool) : Cmd := .pop 5 (sv_fa b false) (sv_fa b false) (sv_fa b true)

theorem sv_ex_addStep (b c : Bool) :
    ExecLe (sv_addStep b) (sv_st R Q T A S c)
      (.norm (sv_st R Q T A.tail (sv_x3 (A.headD false) b c :: S) (sv_maj (A.headD false) b c)))
      4 := by
  rcases A with _ | ⟨a, A'⟩
  · exact ExecLe.pop_nil rfl (sv_ex_fa b false c)
  · refine ExecLe.pop_cons (b := a) (s := A') rfl ?_
    rw [sv_u5]
    cases a
    · exact sv_ex_fa b false c
    · exact sv_ex_fa b true c

/-- Propagate the carry through the rest of the accumulator. -/
def sv_propB : Cmd :=
  .pop 5 (.pop 7 .brk .brk (.seq (.push 6 true) .brk)) (sv_fa false false) (sv_fa false true)

def sv_prop : Cmd := .loop sv_propB

theorem sv_ex_prop : ∀ (A S : Str) (c : Bool),
    ExecLe sv_prop (sv_st R Q T A S c)
      (.norm (sv_st R Q T [] ((sv_propL c A).reverse ++ S) false)) (4 * A.length + 4)
  | [], S, false => (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.pop_nil rfl
      (ExecLe.brk _)))).cast (by simp [sv_propL]) (by simp)
  | [], S, true => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.pop_cons (b := true) (s := []) rfl
      ((ExecLe.push 6 true _).seq_norm (ExecLe.brk _))))).cast ?_ (by simp)
    rw [sv_u7n, sv_st_6, sv_u6]; simp [sv_propL]
  | a :: A, S, c => by
    have ih := sv_ex_prop A (sv_x3 a false c :: S) (sv_maj a false c)
    have hb : ExecLe sv_propB (sv_st R Q T (a :: A) S c)
        (.norm (sv_st R Q T A (sv_x3 a false c :: S) (sv_maj a false c))) 4 := by
      refine ExecLe.pop_cons (b := a) (s := A) rfl ?_
      rw [sv_u5]
      cases a
      · exact sv_ex_fa false false c
      · exact sv_ex_fa false true c
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp ; omega)
    have e1 : sv_maj a false c = (a && c) := by cases a <;> cases c <;> rfl
    have e2 : sv_x3 a false c = xor a c := by cases a <;> cases c <;> rfl
    rw [e1, e2]; simp [sv_propL]

theorem sv_ex_move65 (S : Str) :
    ExecLe (move 6 5) (sv_st R Q T [] S false) (.norm (sv_st R Q T S.reverse [] false))
      (2 * S.length + 2) := by
  have h := exec_move (a := 6) (b := 5) (by decide) S (sv_st R Q T [] S false) rfl
  refine (ExecLe.of h).cast ?_ le_rfl
  congr 1; sv_stx

end Add

/-! ## Rows -/

/-- Select a branch by a symbol. -/
def sv_sel (s : SatSym) (cS cZ cP cN : Cmd) : Cmd :=
  match s with
  | sep => cS
  | zero => cZ
  | pos => cP
  | neg => cN

theorem sv_pop2 {R Q T A S : Str} {c : Bool} {cE cX cS cZ cP cN : Cmd} (s : SatSym) {r : Res}
    {T' : ℕ} (h : ExecLe (sv_sel s cS cZ cP cN) (sv_st R Q T A S c) r T') :
    ExecLe (.pop 3 cE (.pop 3 cX cS cZ) (.pop 3 cX cP cN)) (sv_st R (ic s ++ Q) T A S c) r
      (T' + 2) := by
  cases s with
  | sep => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [sv_u3, sv_sel] using h))
  | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [sv_u3, sv_sel] using h))
  | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [sv_u3, sv_sel] using h))
  | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [sv_u3, sv_sel] using h))

def sv_endAdd : Cmd := .seq sv_prop (.seq (move 6 5) .brk)

def sv_addB : Cmd :=
  .pop 3 sv_eqLoop (.pop 3 (.halt false) sv_endAdd (sv_addStep false))
    (.pop 3 (.halt false) (sv_addStep true) (sv_addStep false))

def sv_addLoop : Cmd := .loop sv_addB

def sv_skipB : Cmd :=
  .pop 3 sv_eqLoop (.pop 3 (.halt false) .brk .skip) (.pop 3 (.halt false) .skip .skip)

def sv_skipLoop : Cmd := .loop sv_skipB

section Rows
variable {R T : Str}

theorem sv_ex_addRow (N : ℕ) (Q' : Str) : ∀ (r : List SatSym) (A S : Str) (c : Bool),
    sep ∉ r → A.length + S.length + r.length ≤ N →
    ExecLe sv_addLoop (sv_st R (r.flatMap ic ++ false :: false :: Q') T A S c)
      (.norm (sv_st R Q' T (S.reverse ++ sv_addL c A (sv_bits r)) [] false))
      (7 * r.length + 8 * N + 20)
  | [], A, S, c, _, hN => by
    have h1 := sv_ex_prop (R := R) (Q := Q') (T := T) A S c
    have h2 := sv_ex_move65 (R := R) (Q := Q') (T := T) ((sv_propL c A).reverse ++ S)
    have hb := sv_pop2 (cE := sv_eqLoop) (cX := .halt false) (cZ := sv_addStep false)
      (cP := sv_addStep true) (cN := sv_addStep false) (Q := Q') (R := R) (T := T) (A := A)
      (S := S) (c := c) sep (h1.seq_norm (h2.seq_norm (ExecLe.brk _)))
    have hl := sv_propL_length c A
    refine (ExecLe.loop_brk (c := sv_addB)
      (σ := sv_st R (([] : List SatSym).flatMap ic ++ false :: false :: Q') T A S c) hb).cast ?_ ?_
    · simp [sv_addL, sv_bits]
    · simp at hN ⊢; omega
  | s :: r, A, S, c, hr, hN => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have hA : A.tail.length ≤ A.length := by simp
    simp only [List.length_cons] at hN
    have ih := sv_ex_addRow N Q' r A.tail (sv_x3 (A.headD false) (isPos s) c :: S)
      (sv_maj (A.headD false) (isPos s) c) hr' (by simp ; omega)
    have hst := sv_ex_addStep (R := R) (Q := r.flatMap ic ++ false :: false :: Q') (T := T)
      (A := A) (S := S) (isPos s) c
    have e : sv_sel s sv_endAdd (sv_addStep false) (sv_addStep true) (sv_addStep false) =
        sv_addStep (isPos s) := by cases s <;> simp_all [sv_sel, isPos]
    have hb := sv_pop2 (cE := sv_eqLoop) (cX := .halt false) (cS := sv_endAdd)
      (cZ := sv_addStep false) (cP := sv_addStep true) (cN := sv_addStep false) s
      (r := .norm _) (T' := 4) (by rw [e]; exact hst)
    simp only [List.flatMap_cons, List.append_assoc]
    refine (ExecLe.loop_norm (c := sv_addB) hb ih).cast ?_ (by simp ; omega)
    simp [sv_addL, sv_bits]

theorem sv_ex_skipRow (A : Str) (Q' : Str) : ∀ (r : List SatSym), sep ∉ r →
    ExecLe sv_skipLoop (sv_st R (r.flatMap ic ++ false :: false :: Q') T A [] false)
      (.norm (sv_st R Q' T A [] false)) (3 * r.length + 3)
  | [], _ => by
    have hb := sv_pop2 (cE := sv_eqLoop) (cX := .halt false) (cZ := .skip) (cP := .skip)
      (cN := .skip) (Q := Q') (R := R) (T := T) (A := A) (S := []) (c := false) sep
      (ExecLe.brk _)
    exact (ExecLe.loop_brk (c := sv_skipB)
      (σ := sv_st R (([] : List SatSym).flatMap ic ++ false :: false :: Q') T A [] false) hb).cast
      rfl (by simp)
  | s :: r, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := sv_ex_skipRow A Q' r (fun e => hr (List.mem_cons_of_mem _ e))
    have hb := sv_pop2 (cE := sv_eqLoop) (cX := .halt false) (cS := .brk) (cZ := .skip)
      (cP := .skip) (cN := .skip) (Q := r.flatMap ic ++ false :: false :: Q') (R := R) (T := T)
      (A := A) (S := []) (c := false) s (r := .norm _) (T' := 1)
      (by cases s <;> first | exact absurd rfl hs | exact ExecLe.skip _)
    simp only [List.flatMap_cons, List.append_assoc]
    exact (ExecLe.loop_norm (c := sv_skipB) hb ih).cast rfl (by simp ; omega)

theorem sv_ex_addEnd (A S : Str) (c : Bool) :
    ExecLe sv_addLoop (sv_st R [] T A S c) (.halt (sv_eqB A T))
      (3 * (A.length + T.length) + 4) :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (sv_ex_eq A T _ rfl rfl))

theorem sv_ex_skipEnd (A S : Str) (c : Bool) :
    ExecLe sv_skipLoop (sv_st R [] T A S c) (.halt (sv_eqB A T))
      (3 * (A.length + T.length) + 4) :=
  ExecLe.loop_halt (ExecLe.pop_nil rfl (sv_ex_eq A T _ rfl rfl))

end Rows

/-! ## The main loop -/

def sv_mainB : Cmd := .pop 0 sv_skipLoop sv_skipLoop sv_addLoop

def sv_mainLoop : Cmd := .loop sv_mainB

/-- Cost of the main phase. -/
def sv_Trows (N : ℕ) : List (List SatSym) → ℕ
  | [] => 6 * N + 10
  | r :: rows => 7 * r.length + 8 * N + 25 + sv_Trows N rows

theorem sv_ex_rows {T : Str} (N : ℕ) (hT : T.length ≤ N) : ∀ (rows : List (List SatSym))
    (R A : Str), (∀ r ∈ rows, sep ∉ r) → A.length + (rows.map List.length).sum + rows.length ≤ N →
    ExecLe sv_mainLoop (sv_st R (enc rows) T A [] false) (.halt (sv_goS T rows R A))
      (sv_Trows N rows)
  | [], R, A, _, hN => by
    simp only [List.map_nil, List.sum_nil, List.length_nil] at hN
    have hc : ExecLe sv_mainB (sv_st R (enc []) T A [] false) (.halt (sv_eqB A T))
        (3 * (A.length + T.length) + 5) := by
      rcases R with _ | ⟨_ | _, R'⟩
      · exact ExecLe.pop_nil rfl (sv_ex_skipEnd A [] false)
      · exact ExecLe.pop_cons (b := false) (s := R') rfl
          (by rw [sv_u0]; exact sv_ex_skipEnd A [] false)
      · exact ExecLe.pop_cons (b := true) (s := R') rfl
          (by rw [sv_u0]; exact sv_ex_addEnd A [] false)
    exact (ExecLe.loop_halt hc).cast (by simp [sv_goS]) (by simp [sv_Trows] ; omega)
  | r :: rows, R, A, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hN
    rw [enc_cons]
    rcases R with _ | ⟨_ | _, R'⟩
    · have ih := sv_ex_rows N hT rows [] A hrs (by omega)
      have hb : ExecLe sv_mainB (sv_st [] (r.flatMap ic ++ false :: false :: enc rows) T A [] false)
          (.norm (sv_st [] (enc rows) T A [] false)) (3 * r.length + 4) :=
        ExecLe.pop_nil rfl (sv_ex_skipRow A _ r hr)
      exact (ExecLe.loop_norm hb ih).cast (by simp [sv_goS]) (by simp [sv_Trows] ; omega)
    · have ih := sv_ex_rows N hT rows R' A hrs (by omega)
      have hb : ExecLe sv_mainB
          (sv_st (false :: R') (r.flatMap ic ++ false :: false :: enc rows) T A [] false)
          (.norm (sv_st R' (enc rows) T A [] false)) (3 * r.length + 4) :=
        ExecLe.pop_cons (b := false) (s := R') rfl (by rw [sv_u0]; exact sv_ex_skipRow A _ r hr)
      exact (ExecLe.loop_norm hb ih).cast (by simp [sv_goS]) (by simp [sv_Trows] ; omega)
    · have hl := sv_addL_length false A (sv_bits r)
      simp only [sv_bits, List.length_map] at hl
      have ih := sv_ex_rows N hT rows R' (sv_addL false A (sv_bits r)) hrs
        (by simp only [sv_bits] at *; omega)
      have hb : ExecLe sv_mainB
          (sv_st (true :: R') (r.flatMap ic ++ false :: false :: enc rows) T A [] false)
          (.norm (sv_st R' (enc rows) T (sv_addL false A (sv_bits r)) [] false))
          (7 * r.length + 8 * N + 21) :=
        ExecLe.pop_cons (b := true) (s := R') rfl (by
          rw [sv_u0]
          exact (sv_ex_addRow N (enc rows) r A [] false hr (by simp ; omega)).cast
            (by simp) le_rfl)
      exact (ExecLe.loop_norm hb ih).cast (by simp [sv_goS]) (by simp [sv_Trows])

theorem sv_Trows_eq (N : ℕ) : ∀ rows : List (List SatSym),
    sv_Trows N rows = 7 * (rows.map List.length).sum + rows.length * (8 * N + 25) + 6 * N + 10
  | [] => by simp [sv_Trows]
  | r :: rows => by simp only [sv_Trows, sv_Trows_eq N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

/-! ## The first row -/

/-- The stacks of the first phase. -/
def sv_st0 (R Q U : Str) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 8 then U else []

def sv_frB : Cmd :=
  .pop 3 (.halt false) (.pop 3 (.halt false) .brk (.push 8 false))
    (.pop 3 (.halt false) (.push 8 true) (.push 8 false))

def sv_frLoop : Cmd := .loop sv_frB

theorem sv_u03 {R Q U : Str} (Q' : Str) : update (sv_st0 R Q U) 3 Q' = sv_st0 R Q' U := by
  funext j; simp only [sv_st0, update_apply]; split_ifs <;> simp_all

theorem sv_ex_fr (R Q' : Str) : ∀ (t : List SatSym) (U : Str), sep ∉ t →
    ExecLe sv_frLoop (sv_st0 R (t.flatMap ic ++ false :: false :: Q') U)
      (.norm (sv_st0 R Q' ((sv_bits t).reverse ++ U))) (3 * t.length + 3)
  | [], U, _ => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) rfl
      (ExecLe.pop_cons (b := false) (s := Q') (by simp) (ExecLe.brk _)))).cast
      (by simp [sv_u03, sv_bits]) (by simp)
  | s :: t, U, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := sv_ex_fr R Q' t (isPos s :: U) (fun e => hr (List.mem_cons_of_mem _ e))
    set Q := t.flatMap ic ++ false :: false :: Q'
    have hp : ExecLe (.push 8 (isPos s)) (sv_st0 R Q U) (.norm (sv_st0 R Q (isPos s :: U))) 1 :=
      (ExecLe.push 8 _ _).cast (by
        congr 1; funext j; simp only [sv_st0, update_apply]; split_ifs <;> simp_all) le_rfl
    have hb : ExecLe sv_frB (sv_st0 R (ic s ++ Q) U) (.norm (sv_st0 R Q (isPos s :: U))) 3 := by
      cases s with
      | sep => exact absurd rfl hs
      | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
          (by simp) (by simpa [sv_u03, isPos] using hp))
      | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
          (by simp) (by simpa [sv_u03, isPos] using hp))
      | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
          (by simp) (by simpa [sv_u03, isPos] using hp))
    refine (ExecLe.loop_norm (by simpa [Q] using hb) ih).cast (by simp [sv_bits]) (by simp ; omega)

theorem sv_ex_move84 (R Q : Str) (L : Str) :
    ExecLe (move 8 4) (sv_st0 R Q L.reverse) (.norm (sv_st R Q L [] [] false))
      (2 * L.length + 2) := by
  have h := exec_move (a := 8) (b := 4) (by decide) L.reverse (sv_st0 R Q L.reverse) rfl
  refine (ExecLe.of h).cast ?_ (by simp)
  congr 1; funext j; simp only [sv_st0, sv_st, update_apply, CookLevin.fl]
  split_ifs <;> simp_all

/-! ## The whole verifier -/

def sv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq sv_frLoop (.seq (move 8 4) sv_mainLoop))))

/-- Time bound of the verifier. -/
def sv_Tver (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (3 * n + 3) + (2 * n + 2) +
  (7 * n + n * (8 * n + 25) + 6 * n + 10)

theorem sv_exec_ver (z : Str) :
    ExecLe sv_ver (init [z]).stk (.halt (sv_vres (dec z).1 (dec z).2)) (sv_Tver z.length) := by
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
  have hσ : update (update σ₂ 2 []) 3 ((σ₂ 2).reverse ++ σ₂ 3) = sv_st0 y (enc (clauses w)) [] := by
    funext j
    simp only [σ₂, σ₁, sv_st0, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ), ExecLe c (sv_st0 y (enc (clauses w)) []) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold sv_vres sv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨t, rows⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq sv_frLoop (.seq (move 8 4) sv_mainLoop)) (sv_st0 y (enc []) [])
        (.halt false) 2 :=
      ExecLe.seq_halt (ExecLe.loop_halt ((ExecLe.pop_nil rfl (ExecLe.halt false _)).cast rfl
        le_rfl))
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, sv_Tver]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    have hF := sv_ex_fr y (enc rows) t [] (hsep t (by simp))
    rw [List.append_nil] at hF
    have hM2 := sv_ex_move84 y (enc rows) (sv_bits t)
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hR := sv_ex_rows (T := sv_bits t) z.length (by simp [sv_bits]; omega) rows y []
      (fun r hr => hsep r (by simp [hr])) (by simp ; omega)
    refine (hpre _ _ _ (hF.seq_norm (hM2.seq_norm hR))).cast rfl ?_
    rw [sv_Trows_eq]
    simp only [htl, sv_Tver, sv_bits, List.length_map]
    have h1 : rows.length * (8 * z.length + 25) ≤ z.length * (8 * z.length + 25) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem sv_Tver_le (n : ℕ) : sv_Tver n ≤ tb 6 n := by
  unfold sv_Tver tb
  have hm : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  norm_num at hm
  have e : (n + 2) ^ 6 = (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by ring
  have : 16 * (n + 2) ^ 2 ≤ (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by nlinarith
  nlinarith

end Pnp.Karp.SubsetSum
