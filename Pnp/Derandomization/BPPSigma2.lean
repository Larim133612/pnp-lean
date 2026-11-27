import Pnp.Oracle.StructLib
import Pnp.Oracle.CheckProg
import Pnp.Derandomization.LautemannList
import Pnp.Derandomization.BPP
import Pnp.TM2.Homomorphism

/-!
# `BPP ⊆ Σ₂ᴾ` (Sipser–Gács–Lautemann), official version

We put every language of the official-style class `Pnp.Derand.InBPP` into the official second
level `Millennium.polynomial_hierarchy_sigma_level 2` of the polynomial hierarchy.

The mathematical part is `Pnp.Derand.lautemann_list`; the inner predicate
`lautSpec (R w) (|w|^k) u y` has to be shown polynomial-time in the official sense.  We write
an explicit program of our own stack-machine model (`Pnp/Oracle/Struct.lean`) that

1. parses the bit-pair code of `((w, u), y)` into three stacks,
2. computes `ℓ = |w|^k`, `a = sglReps ℓ`, `L = a ℓ` and `L²` in unary,
3. treats `ℓ = 0` separately (one call of the verifier on the empty certificate),
4. checks `|u| = L²` and `|y| = L`,
5. for every `i < L` counts the accepting blocks `j < a` of `tᵢ ⊕ y` by calling the
   verifier program of `Pnp.Relativize.NPEquiv.checkProg` (on the certificate built from the
   block) and halts `true` at the first majority,

proves it correct and polynomial-time on *all* inputs, and transfers it to the official class
`P` with `Pnp.TM2Hom.inPolynomialTime_of_code`; `Pnp.Derand.sigma2_intro` concludes.

The machine memory is a record `Mem` of 26 stacks (stacks `24, 25` are the input stacks of the
called verifier).
-/

namespace Pnp.Derand.BPPS2

open Function Pnp.Relativize Pnp.Relativize.Struct
open scoped Classical

noncomputable section

/-- The 26 stacks of the program. -/
structure Mem where
  (z w1 u1 y1 w u y nn p c ta tm k24 aa lm qq e1 e2 ci yc cj cb yes no x0 x1 : Str)

/-- The stacks as a list. -/
def Mem.l (m : Mem) : List Str :=
  [m.z, m.w1, m.u1, m.y1, m.w, m.u, m.y, m.nn, m.p, m.c, m.ta, m.tm, m.k24, m.aa, m.lm, m.qq, m.e1, m.e2, m.ci, m.yc, m.cj, m.cb, m.yes, m.no, m.x0, m.x1]

/-- The stack contents seen by the machine. -/
def Mem.f (m : Mem) : ℕ → Str := fun j => m.l.getD j []

theorem update_getD (l : List Str) (k : ℕ) (hk : k < l.length) (s : Str) :
    update (fun j => l.getD j []) k s = fun j => (l.set k s).getD j [] := by
  funext j
  by_cases h : j = k
  · subst h; simp [List.getD_eq_getElem?_getD, hk]
  · rw [update_of_ne h]; simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h]

@[simp] theorem Mem.f_0 (m : Mem) : m.f 0 = m.z := rfl
@[simp] theorem Mem.f_1 (m : Mem) : m.f 1 = m.w1 := rfl
@[simp] theorem Mem.f_2 (m : Mem) : m.f 2 = m.u1 := rfl
@[simp] theorem Mem.f_3 (m : Mem) : m.f 3 = m.y1 := rfl
@[simp] theorem Mem.f_4 (m : Mem) : m.f 4 = m.w := rfl
@[simp] theorem Mem.f_5 (m : Mem) : m.f 5 = m.u := rfl
@[simp] theorem Mem.f_6 (m : Mem) : m.f 6 = m.y := rfl
@[simp] theorem Mem.f_7 (m : Mem) : m.f 7 = m.nn := rfl
@[simp] theorem Mem.f_8 (m : Mem) : m.f 8 = m.p := rfl
@[simp] theorem Mem.f_9 (m : Mem) : m.f 9 = m.c := rfl
@[simp] theorem Mem.f_10 (m : Mem) : m.f 10 = m.ta := rfl
@[simp] theorem Mem.f_11 (m : Mem) : m.f 11 = m.tm := rfl
@[simp] theorem Mem.f_12 (m : Mem) : m.f 12 = m.k24 := rfl
@[simp] theorem Mem.f_13 (m : Mem) : m.f 13 = m.aa := rfl
@[simp] theorem Mem.f_14 (m : Mem) : m.f 14 = m.lm := rfl
@[simp] theorem Mem.f_15 (m : Mem) : m.f 15 = m.qq := rfl
@[simp] theorem Mem.f_16 (m : Mem) : m.f 16 = m.e1 := rfl
@[simp] theorem Mem.f_17 (m : Mem) : m.f 17 = m.e2 := rfl
@[simp] theorem Mem.f_18 (m : Mem) : m.f 18 = m.ci := rfl
@[simp] theorem Mem.f_19 (m : Mem) : m.f 19 = m.yc := rfl
@[simp] theorem Mem.f_20 (m : Mem) : m.f 20 = m.cj := rfl
@[simp] theorem Mem.f_21 (m : Mem) : m.f 21 = m.cb := rfl
@[simp] theorem Mem.f_22 (m : Mem) : m.f 22 = m.yes := rfl
@[simp] theorem Mem.f_23 (m : Mem) : m.f 23 = m.no := rfl
@[simp] theorem Mem.f_24 (m : Mem) : m.f 24 = m.x0 := rfl
@[simp] theorem Mem.f_25 (m : Mem) : m.f 25 = m.x1 := rfl
@[simp] theorem Mem.upd_0 (m : Mem) (s : Str) : update m.f 0 s = {m with z := s}.f :=
  update_getD m.l 0 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_1 (m : Mem) (s : Str) : update m.f 1 s = {m with w1 := s}.f :=
  update_getD m.l 1 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_2 (m : Mem) (s : Str) : update m.f 2 s = {m with u1 := s}.f :=
  update_getD m.l 2 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_3 (m : Mem) (s : Str) : update m.f 3 s = {m with y1 := s}.f :=
  update_getD m.l 3 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_4 (m : Mem) (s : Str) : update m.f 4 s = {m with w := s}.f :=
  update_getD m.l 4 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_5 (m : Mem) (s : Str) : update m.f 5 s = {m with u := s}.f :=
  update_getD m.l 5 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_6 (m : Mem) (s : Str) : update m.f 6 s = {m with y := s}.f :=
  update_getD m.l 6 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_7 (m : Mem) (s : Str) : update m.f 7 s = {m with nn := s}.f :=
  update_getD m.l 7 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_8 (m : Mem) (s : Str) : update m.f 8 s = {m with p := s}.f :=
  update_getD m.l 8 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_9 (m : Mem) (s : Str) : update m.f 9 s = {m with c := s}.f :=
  update_getD m.l 9 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_10 (m : Mem) (s : Str) : update m.f 10 s = {m with ta := s}.f :=
  update_getD m.l 10 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_11 (m : Mem) (s : Str) : update m.f 11 s = {m with tm := s}.f :=
  update_getD m.l 11 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_12 (m : Mem) (s : Str) : update m.f 12 s = {m with k24 := s}.f :=
  update_getD m.l 12 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_13 (m : Mem) (s : Str) : update m.f 13 s = {m with aa := s}.f :=
  update_getD m.l 13 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_14 (m : Mem) (s : Str) : update m.f 14 s = {m with lm := s}.f :=
  update_getD m.l 14 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_15 (m : Mem) (s : Str) : update m.f 15 s = {m with qq := s}.f :=
  update_getD m.l 15 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_16 (m : Mem) (s : Str) : update m.f 16 s = {m with e1 := s}.f :=
  update_getD m.l 16 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_17 (m : Mem) (s : Str) : update m.f 17 s = {m with e2 := s}.f :=
  update_getD m.l 17 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_18 (m : Mem) (s : Str) : update m.f 18 s = {m with ci := s}.f :=
  update_getD m.l 18 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_19 (m : Mem) (s : Str) : update m.f 19 s = {m with yc := s}.f :=
  update_getD m.l 19 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_20 (m : Mem) (s : Str) : update m.f 20 s = {m with cj := s}.f :=
  update_getD m.l 20 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_21 (m : Mem) (s : Str) : update m.f 21 s = {m with cb := s}.f :=
  update_getD m.l 21 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_22 (m : Mem) (s : Str) : update m.f 22 s = {m with yes := s}.f :=
  update_getD m.l 22 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_23 (m : Mem) (s : Str) : update m.f 23 s = {m with no := s}.f :=
  update_getD m.l 23 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_24 (m : Mem) (s : Str) : update m.f 24 s = {m with x0 := s}.f :=
  update_getD m.l 24 (by simp [Mem.l]) s
@[simp] theorem Mem.upd_25 (m : Mem) (s : Str) : update m.f 25 s = {m with x1 := s}.f :=
  update_getD m.l 25 (by simp [Mem.l]) s

theorem Mem.f_ge (m : Mem) {j : ℕ} (hj : 26 ≤ j) : m.f j = [] := by
  unfold Mem.f; rw [List.getD_eq_default _ _ (by simp [Mem.l]; omega)]

theorem Mem.view (m : Mem) : view m.f 24 = (init [m.x0, m.x1]).stk := by
  funext j
  rcases j with _ | _ | j
  · rfl
  · rfl
  · simp only [view_apply, init]
    rw [Mem.f_ge m (by omega)]; simp

theorem Mem.cut (m : Mem) :
    (fun j => if j < 24 then m.f j else []) = {m with x0 := [], x1 := []}.f := by
  funext j
  by_cases hj : j < 24
  · rw [if_pos hj]; interval_cases j <;> rfl
  · rw [if_neg hj]
    obtain ⟨d, rfl⟩ : ∃ d, j = 24 + d := ⟨j - 24, by omega⟩
    rcases d with _ | _ | d
    · rfl
    · rfl
    · rw [Mem.f_ge _ (by omega)]

theorem Mem.f_ge24 (m : Mem) (h0 : m.x0 = []) (h1 : m.x1 = []) {j : ℕ} (hj : 24 ≤ j) :
    m.f j = [] := by
  obtain ⟨d, rfl⟩ : ∃ d, j = 24 + d := ⟨j - 24, by omega⟩
  rcases d with _ | _ | d
  · exact h0
  · exact h1
  · exact Mem.f_ge _ (by omega)

/-- All stacks empty. -/
def Mem.e : Mem := ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩

/-! ## The program -/

section Prog

variable (q : Prog) (cc : Bool → Str)

/-- Parse `dbl w ++ [t,t] ++ dbl u ++ [t,t] ++ dbl y` from stack `0` into stacks `4, 5, 6`. -/
def parseCmd : Cmd :=
  .seq (segCmd 0 1) (.seq (segCmd 0 2) (.seq (segCmd 0 3) (.seq (drain 0)
    (.seq (move 1 4) (.seq (move 2 5) (move 3 6))))))

/-- `|w|^j` marks on stack `8` (from `|w|` marks on stack `7`). -/
def powCmd : ℕ → Cmd
  | 0 => .push 8 true
  | j + 1 => .seq (powCmd j) (.seq (mul 8 7 9 10 11) (.seq (drain 8) (move 9 8)))

/-- Unary arithmetic: `ℓ` (stack 8), `24` (12), `a = sglReps ℓ` (13), `L` (14), `L²` (15). -/
def arithCmd (k : ℕ) : Cmd :=
  .seq (marks 4 7 9) (.seq (powCmd k) (.seq (pushList 12 (List.replicate 24 true))
    (.seq (mul 8 12 9 10 11) (.seq (.push 9 true) (.seq (mul 9 12 13 10 11) (.seq (drain 9)
      (.seq (mul 13 8 14 10 11) (.seq (copyVia 14 9 11) (.seq (mul 9 14 15 10 11)
        (drain 9))))))))))

/-- The case `ℓ = 0`: one call on the empty certificate. -/
def zeroCmd : Cmd :=
  .pop 8 (.seq (copyVia 4 24 11) (.call q 24 (.halt false) (.halt true))) (.push 8 false)
    (.push 8 true)

/-- Check `|u| = L²` (else reject) and `|y| = L` (else accept). -/
def checkCmd : Cmd :=
  .seq (copyVia 5 16 11) (.seq (eqLen 16 15 false) (.seq (copyVia 6 16 11)
    (.seq (copyVia 14 17 11) (eqLen 16 17 true))))

/-- Second half of a certificate step. -/
def popY (x : Bool) : Cmd :=
  .pop 19 .skip (pushList 25 (cc (xor x false)).reverse) (pushList 25 (cc (xor x true)).reverse)

/-- One certificate step: pop a bit of `u` and of `y`, push the code of their xor. -/
def bodyB : Cmd := .pop 5 .skip (popY cc false) (popY cc true)

/-- Build the certificate of one block. -/
def bLoop : Cmd := .loop (.pop 21 .brk (bodyB cc) (bodyB cc))

/-- One block: build the certificate, call the verifier, record the vote. -/
def bodyJ : Cmd :=
  .seq (copyVia 8 21 11) (.seq (bLoop cc) (.seq (copyVia 4 24 11) (callDrain q 24 22 23)))

/-- All blocks of one shift. -/
def jLoop : Cmd := .loop (.pop 20 .brk (bodyJ q cc) (bodyJ q cc))

/-- One shift: count the votes, accept on a majority. -/
def bodyI : Cmd :=
  .seq (copyVia 6 19 11) (.seq (copyVia 13 20 11) (.seq (jLoop q cc) (gtCmd 22 23)))

/-- All shifts. -/
def iLoop : Cmd := .loop (.pop 18 .brk (bodyI q cc) (bodyI q cc))

/-- Main loop, rejecting if no shift has a majority. -/
def mainCmd : Cmd := .seq (copyVia 14 18 11) (.seq (iLoop q cc) (.halt false))

/-- The whole program. -/
def prog (k : ℕ) : Cmd :=
  .seq parseCmd (.seq (arithCmd k) (.seq (zeroCmd q) (.seq checkCmd (mainCmd q cc))))

end Prog

/-- Maximal code length (crude). -/
def Bc (cc : Bool → Str) : ℕ := (cc false).length + (cc true).length

theorem cc_len_le (cc : Bool → Str) (x : Bool) : (cc x).length ≤ Bc cc := by
  cases x <;> simp [Bc]

/-! ## The certificate loop -/

section Cert

variable (cc : Bool → Str)

theorem exec_bodyB (m : Mem) (bu bv : Bool) (us vs : Str) (hu : m.u = bu :: us)
    (hv : m.yc = bv :: vs) :
    ExecLe (bodyB cc) m.f
      (.norm {m with u := us, yc := vs, x1 := (cc (xor bu bv)).reverse ++ m.x1}.f) (Bc cc + 3) := by
  refine ExecLe.pop_cons (k := 5) (by simpa using hu) ?_
  have e1 : (if bu then popY cc true else popY cc false) = popY cc bu := by cases bu <;> rfl
  rw [e1, Mem.upd_5]
  refine ExecLe.pop_cons (k := 19) (by simpa using hv) ?_
  have e2 : (if bv then pushList 25 (cc (xor bu true)).reverse
      else pushList 25 (cc (xor bu false)).reverse) = pushList 25 (cc (xor bu bv)).reverse := by
    cases bv <;> rfl
  rw [e2, Mem.upd_19]
  refine (ExecLe.of (exec_pushList 25 _ _)).cast (by simp) ?_
  have := cc_len_le cc (xor bu bv)
  simp; omega

/-- The certificate bits. -/
def bitF (u y : Str) (pu py b : ℕ) : Bool := xor (u.getD (pu + b) false) (y.getD (py + b) false)

theorem bitF_succ (u y : Str) (pu py b : ℕ) :
    bitF u y pu py (b + 1) = bitF u y (pu + 1) (py + 1) b := by
  simp only [bitF, show pu + (b + 1) = pu + 1 + b by omega, show py + (b + 1) = py + 1 + b by omega]

theorem drop_cons_getD (u : Str) {p : ℕ} (hp : p < u.length) :
    u.drop p = u.getD p false :: u.drop (p + 1) := by
  rw [List.drop_eq_getElem_cons hp, List.getD_eq_getElem _ _ hp]

theorem exec_bLoop (u y : Str) : ∀ (r pu py : ℕ) (m : Mem), m.cb = List.replicate r true →
    m.u = u.drop pu → m.yc = y.drop py → pu + r ≤ u.length → py + r ≤ y.length →
    ExecLe (bLoop cc) m.f (.norm {m with
        cb := [], u := u.drop (pu + r), yc := y.drop (py + r),
        x1 := (((List.range r).map (bitF u y pu py)).flatMap cc).reverse ++ m.x1}.f)
      (r * (Bc cc + 4) + 2)
  | 0, pu, py, m, hcb, hu, hv, _, _ => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil (k := 21) (by simpa using hcb)
      (ExecLe.brk _))).cast ?_ (by simp)
    congr 1; cases m; simp_all
  | r + 1, pu, py, m, hcb, hu, hv, h1, h2 => by
    have hu' : m.u = u.getD pu false :: u.drop (pu + 1) := by rw [hu, drop_cons_getD u (by omega)]
    have hv' : m.yc = y.getD py false :: y.drop (py + 1) := by
      rw [hv, drop_cons_getD y (by omega)]
    have hb := exec_bodyB cc {m with cb := List.replicate r true} _ _ _ _ hu' hv'
    have ih := exec_bLoop u y r (pu + 1) (py + 1)
      {m with
        cb := List.replicate r true, u := u.drop (pu + 1), yc := y.drop (py + 1),
        x1 := (cc (xor (u.getD pu false) (y.getD py false))).reverse ++ m.x1}
      rfl rfl rfl (by omega) (by omega)
    have hpop : ExecLe (.pop 21 .brk (bodyB cc) (bodyB cc)) m.f
        (.norm {m with
          cb := List.replicate r true, u := u.drop (pu + 1), yc := y.drop (py + 1),
          x1 := (cc (xor (u.getD pu false) (y.getD py false))).reverse ++ m.x1}.f)
        (Bc cc + 3 + 1) :=
      ExecLe.pop_same (k := 21) (b := true) (s := List.replicate r true)
        (by simp [hcb, List.replicate_succ]) (by rw [Mem.upd_21]; exact hb)
    refine (ExecLe.loop_norm hpop ih).cast ?_ (by rw [Nat.succ_mul]; omega)
    congr 1
    have e1 : pu + 1 + r = pu + (r + 1) := by omega
    have e2 : py + 1 + r = py + (r + 1) := by omega
    have e3 : (List.range (r + 1)).map (bitF u y pu py) =
        bitF u y pu py 0 :: (List.range r).map (bitF u y (pu + 1) (py + 1)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1; exact List.map_congr_left (fun b _ => bitF_succ u y pu py b)
    simp only [e1, e2, e3, List.flatMap_cons, List.reverse_append, List.append_assoc]
    simp [bitF]

theorem flatMap_len_le (ys : Str) : (ys.flatMap cc).length ≤ ys.length * Bc cc := by
  induction ys with
  | nil => simp
  | cons x ys ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]
                    have := cc_len_le cc x; rw [Nat.succ_mul]; omega

/-- Record a vote. -/
def Mem.vote (m : Mem) (b : Bool) : Mem :=
  if b then {m with yes := true :: m.yes} else {m with no := true :: m.no}

/-- Cost bound of one block. -/
def Tj (q : Prog) (Tq n ℓ : ℕ) : ℕ := 3 * Tq + 7 * n + ℓ * (3 * Bc cc + 9) +
  2 * (Official.nW q + 2) + 13

theorem exec_bodyJ (q : Prog) (Tq : ℕ) (Rw : Str → Prop) (w u y : Str) (ℓ : ℕ)
    (hq : ∀ ys : Str, ys.length = ℓ →
      runFor ∅ q Tq (.run (init [w, (ys.flatMap cc).reverse])) = .done (decide (Rw ys)))
    (pu py : ℕ) (m : Mem) (hp : m.p = List.replicate ℓ true) (hcb : m.cb = [])
    (htm : m.tm = []) (hx0 : m.x0 = []) (hx1 : m.x1 = []) (hw : m.w = w)
    (hu : m.u = u.drop pu) (hv : m.yc = y.drop py) (h1 : pu + ℓ ≤ u.length)
    (h2 : py + ℓ ≤ y.length) :
    ExecLe (bodyJ q cc) m.f
      (.norm ({m with u := u.drop (pu + ℓ), yc := y.drop (py + ℓ)}.vote
        (decide (Rw ((List.range ℓ).map (bitF u y pu py))))).f) (Tj cc q Tq w.length ℓ) := by
  set ys := (List.range ℓ).map (bitF u y pu py) with hys
  have c1 : ExecLe (copyVia 8 21 11) m.f (.norm {m with cb := List.replicate ℓ true}.f)
      (5 * ℓ + 4) :=
    ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
      (by simp [hp, hcb]) (by simp [hp])
  have c2 := exec_bLoop cc u y ℓ pu py {m with cb := List.replicate ℓ true} rfl hu hv h1 h2
  set m2 : Mem := {m with
    cb := [], u := u.drop (pu + ℓ), yc := y.drop (py + ℓ),
    x1 := (ys.flatMap cc).reverse} with hm2
  have c2' : ExecLe (bLoop cc) {m with cb := List.replicate ℓ true}.f (.norm m2.f)
      (ℓ * (Bc cc + 4) + 2) := c2.cast (by simp [hm2, hx1, hys]) le_rfl
  have c3 : ExecLe (copyVia 4 24 11) m2.f (.norm {m2 with x0 := w}.f) (5 * w.length + 4) :=
    ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa [hm2] using htm))
      (by simp [hm2, hw, hx0]) (by simp [hm2, hw])
  set m3 : Mem := {m2 with x0 := w} with hm3
  have hrun : runFor ∅ q Tq (.run ⟨0, view m3.f 24⟩) = .done (decide (Rw ys)) := by
    rw [Mem.view]; exact hq ys (by simp [hys])
  have c4 := exec_callDrain (yes := 22) (no := 23) (by decide) (by decide)
    (fun j hj => Mem.f_ge m3 (by omega)) hrun
  have hlen : (ys.flatMap cc).reverse.length ≤ ℓ * Bc cc := by
    rw [List.length_reverse]
    exact (flatMap_len_le cc ys).trans (by simp [hys])
  refine (ExecLe.seq_norm c1 (ExecLe.seq_norm c2' (ExecLe.seq_norm c3 c4))).cast ?_ ?_
  · congr 1
    have e : (fun j => if j < 24 then update m3.f (if decide (Rw ys) then 22 else 23)
        (true :: m3.f (if decide (Rw ys) then 22 else 23)) j else []) =
        (fun j => if j < 24 then (m3.vote (decide (Rw ys))).f j else []) := by
      by_cases hR : Rw ys <;> simp [hR, Mem.vote]
    rw [e, Mem.cut]
    by_cases hR : Rw ys <;> (cases m; simp_all [Mem.vote])
  · simp only [Tj, hm3, hm2, show (24 : ℕ) + 1 = 25 from rfl, Mem.f_24, Mem.f_25]
    nlinarith [hlen]

/-- Number of `j' < j` with `P j'`. -/
def cnt (P : ℕ → Prop) (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, if P i then 1 else 0

theorem cnt_succ (P : ℕ → Prop) (j : ℕ) : cnt P (j + 1) = cnt P j + if P j then 1 else 0 := by
  simp only [cnt, Finset.sum_range_succ]

theorem cnt_le (P : ℕ → Prop) : ∀ j, cnt P j ≤ j
  | 0 => by simp [cnt]
  | j + 1 => by have := cnt_le P j; rw [cnt_succ]; split <;> omega

theorem card_filter_fin (P : ℕ → Prop) (a : ℕ) :
    (Finset.univ.filter fun j : Fin a => P j).card = cnt P a := by
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i => if P i then 1 else 0) a

/-- The certificate of block `j` of shift `i` (the first `pu0` bits of `u` are used up). -/
def blk (u y : Str) (ℓ pu0 j : ℕ) : Str := (List.range ℓ).map (bitF u y (pu0 + j * ℓ) (j * ℓ))

/-- State of the block loop after `j` blocks. -/
def jSt (Rw : Str → Prop) (u y : Str) (ℓ a pu0 : ℕ) (m : Mem) (j : ℕ) : Mem :=
  {m with
    cj := List.replicate (a - j) true, u := u.drop (pu0 + j * ℓ), yc := y.drop (j * ℓ),
    yes := List.replicate (cnt (fun j' => Rw (blk u y ℓ pu0 j')) j) true,
    no := List.replicate (j - cnt (fun j' => Rw (blk u y ℓ pu0 j')) j) true}

theorem exec_jLoop (q : Prog) (Tq : ℕ) (Rw : Str → Prop) (w u y : Str) (ℓ : ℕ)
    (hq : ∀ ys : Str, ys.length = ℓ →
      runFor ∅ q Tq (.run (init [w, (ys.flatMap cc).reverse])) = .done (decide (Rw ys)))
    (a pu0 : ℕ) (m : Mem) (hp : m.p = List.replicate ℓ true) (hcb : m.cb = [])
    (htm : m.tm = []) (hx0 : m.x0 = []) (hx1 : m.x1 = []) (hw : m.w = w)
    (h1 : pu0 + a * ℓ ≤ u.length) (h2 : a * ℓ ≤ y.length) :
    ExecLe (jLoop q cc) (jSt Rw u y ℓ a pu0 m 0).f (.norm (jSt Rw u y ℓ a pu0 m a).f)
      (a * (Tj cc q Tq w.length ℓ + 1) + 2) := by
  refine ExecLe.loop_iter a (fun j => (jSt Rw u y ℓ a pu0 m j).f) (fun i hi => ?_) ?_
  · have hle : (i + 1) * ℓ ≤ a * ℓ := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at hle
    have hb := exec_bodyJ cc q Tq Rw w u y ℓ hq (pu0 + i * ℓ) (i * ℓ)
      {jSt Rw u y ℓ a pu0 m i with cj := List.replicate (a - (i + 1)) true}
      hp hcb htm hx0 hx1 hw rfl rfl (by omega) (by omega)
    refine ExecLe.pop_same (k := 20) (b := true) (s := List.replicate (a - (i + 1)) true)
      (by simp [jSt, ← List.replicate_succ]; congr 1; omega) ?_
    rw [Mem.upd_20]
    refine hb.cast ?_ le_rfl
    congr 1
    have e1 : pu0 + i * ℓ + ℓ = pu0 + (i + 1) * ℓ := by ring
    have e2 : i * ℓ + ℓ = (i + 1) * ℓ := by ring
    have hc := cnt_le (fun j' => Rw (blk u y ℓ pu0 j')) i
    by_cases hR : Rw (blk u y ℓ pu0 i)
    · have hR' : Rw ((List.range ℓ).map (bitF u y (pu0 + i * ℓ) (i * ℓ))) := hR
      simp only [Mem.vote, hR', decide_true, if_true, jSt, e1, e2, cnt_succ, hR, if_true]
      congr 2 <;> first | (rw [List.replicate_succ]; done) | (congr 1; omega)
    · have hR' : ¬ Rw ((List.range ℓ).map (bitF u y (pu0 + i * ℓ) (i * ℓ))) := hR
      simp only [Mem.vote, hR', decide_false, Bool.false_eq_true, if_false, jSt, e1, e2, cnt_succ,
        hR]
      congr 2
      rw [show i + 1 - (cnt (fun j' => Rw (blk u y ℓ pu0 j')) i + 0) =
        (i - cnt (fun j' => Rw (blk u y ℓ pu0 j')) i) + 1 by omega, List.replicate_succ]
  · refine (ExecLe.loop_brk (ExecLe.pop_nil (k := 20) (by simp [jSt]) (ExecLe.brk _))).cast
      rfl (by omega)

/-- Majority of accepting blocks for shift `i` (in counting form). -/
def majI (Rw : Str → Prop) (u y : Str) (ℓ a i : ℕ) : Prop :=
  a < 2 * cnt (fun j => Rw (blk u y ℓ (i * (a * ℓ)) j)) a

/-- Cost bound of one shift. -/
def Ti (q : Prog) (Tq n ℓ a : ℕ) : ℕ := 5 * (a * ℓ) + 12 * a + a * (Tj cc q Tq n ℓ + 1) + 17

theorem exec_bodyI (q : Prog) (Tq : ℕ) (Rw : Str → Prop) (w u y : Str) (ℓ a : ℕ)
    (hq : ∀ ys : Str, ys.length = ℓ →
      runFor ∅ q Tq (.run (init [w, (ys.flatMap cc).reverse])) = .done (decide (Rw ys)))
    (hul : u.length = (a * ℓ) * (a * ℓ)) (hyl : y.length = a * ℓ) (i : ℕ) (hi : i < a * ℓ)
    (m : Mem) (hp : m.p = List.replicate ℓ true) (hcb : m.cb = [])
    (htm : m.tm = []) (hx0 : m.x0 = []) (hx1 : m.x1 = []) (hw : m.w = w) (hy : m.y = y)
    (haa : m.aa = List.replicate a true) (hyc : m.yc = []) (hcj : m.cj = []) (hyes : m.yes = [])
    (hno : m.no = []) (hu : m.u = u.drop (i * (a * ℓ))) :
    (majI Rw u y ℓ a i → ExecLe (bodyI q cc) m.f (.halt true) (Ti cc q Tq w.length ℓ a)) ∧
    (¬ majI Rw u y ℓ a i → ExecLe (bodyI q cc) m.f
      (.norm {m with u := u.drop ((i + 1) * (a * ℓ))}.f) (Ti cc q Tq w.length ℓ a)) := by
  have c1 : ExecLe (copyVia 6 19 11) m.f (.norm {m with yc := y}.f) (5 * (a * ℓ) + 4) :=
    ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
      (by simp [hy, hyc]) (by simp [hy, hyl])
  have c2 : ExecLe (copyVia 13 20 11) {m with yc := y}.f
      (.norm (jSt Rw u y ℓ a (i * (a * ℓ)) m 0).f) (5 * a + 4) :=
    ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
      (by congr 1; cases m; simp_all [jSt, cnt]) (by simp [haa])
  have hle : i * (a * ℓ) + (a * ℓ) ≤ (a * ℓ) * (a * ℓ) := by
    have := Nat.mul_le_mul_right (a * ℓ) (show i + 1 ≤ (a * ℓ) by omega); rw [Nat.succ_mul] at this; omega
  have c3 := exec_jLoop cc q Tq Rw w u y ℓ hq a (i * (a * ℓ)) m hp hcb htm hx0 hx1 hw
    (by rw [hul]; omega) (by rw [hyl])
  set ms := jSt Rw u y ℓ a (i * (a * ℓ)) m a with hms
  have hc := cnt_le (fun j' => Rw (blk u y ℓ (i * (a * ℓ)) j')) a
  have g := exec_gtCmd (yes := 22) (no := 23) (by decide) ms.f
  have hlno : (ms.f 23).length = a - cnt (fun j' => Rw (blk u y ℓ (i * (a * ℓ)) j')) a := by
    simp [hms, jSt]
  have hlyes : (ms.f 22).length = cnt (fun j' => Rw (blk u y ℓ (i * (a * ℓ)) j')) a := by
    simp [hms, jSt]
  rw [hlno, hlyes] at g
  refine ⟨fun hmaj => ?_, fun hmaj => ?_⟩
  · have g1 := g.1 (by unfold majI at hmaj; omega)
    refine (ExecLe.seq_norm c1 (ExecLe.seq_norm c2 (ExecLe.seq_norm c3 g1))).cast rfl ?_
    simp only [Ti]; omega
  · have g2 := g.2 (by unfold majI at hmaj; omega)
    refine (ExecLe.seq_norm c1 (ExecLe.seq_norm c2 (ExecLe.seq_norm c3 g2))).cast ?_ ?_
    · congr 1
      have e : y.drop (a * ℓ) = [] := List.drop_eq_nil_of_le (by omega)
      have e2 : i * (a * ℓ) + a * ℓ = (i + 1) * (a * ℓ) := by rw [Nat.succ_mul]
      rw [hms]; simp only [jSt, e, e2]
      cases m; simp_all
    · simp only [Ti]; omega

/-- State of the shift loop before shift `i`. -/
def iSt (u : Str) (L : ℕ) (m : Mem) (i : ℕ) : Mem :=
  {m with ci := List.replicate (L - i) true, u := u.drop (i * L)}

theorem exec_iLoop (q : Prog) (Tq : ℕ) (Rw : Str → Prop) (w u y : Str) (ℓ a : ℕ)
    (hq : ∀ ys : Str, ys.length = ℓ →
      runFor ∅ q Tq (.run (init [w, (ys.flatMap cc).reverse])) = .done (decide (Rw ys)))
    (hul : u.length = (a * ℓ) * (a * ℓ)) (hyl : y.length = a * ℓ)
    (m : Mem) (hp : m.p = List.replicate ℓ true) (hcb : m.cb = [])
    (htm : m.tm = []) (hx0 : m.x0 = []) (hx1 : m.x1 = []) (hw : m.w = w) (hy : m.y = y)
    (haa : m.aa = List.replicate a true) (hyc : m.yc = []) (hcj : m.cj = []) (hyes : m.yes = [])
    (hno : m.no = []) : ∀ (d i : ℕ), a * ℓ - i = d → i ≤ a * ℓ →
    ExecLe (iLoop q cc) (iSt u (a * ℓ) m i).f
      (if ∃ i', i ≤ i' ∧ i' < a * ℓ ∧ majI Rw u y ℓ a i' then .halt true
        else .norm (iSt u (a * ℓ) m (a * ℓ)).f) (d * (Ti cc q Tq w.length ℓ a + 1) + 2)
  | 0, i, hd, hi => by
    have hiL : i = a * ℓ := by omega
    subst hiL
    rw [if_neg (by rintro ⟨i', h1, h2, -⟩; omega)]
    exact (ExecLe.loop_brk (ExecLe.pop_nil (k := 18) (by simp [iSt]) (ExecLe.brk _))).cast
      rfl (by omega)
  | d + 1, i, hd, hi => by
    have hiL : i < a * ℓ := by omega
    have hb := exec_bodyI cc q Tq Rw w u y ℓ a hq hul hyl i hiL
      {iSt u (a * ℓ) m i with ci := List.replicate (a * ℓ - (i + 1)) true}
      hp hcb htm hx0 hx1 hw hy haa hyc hcj hyes hno rfl
    have hpop : (iSt u (a * ℓ) m i).f 18 = true :: List.replicate (a * ℓ - (i + 1)) true := by
      simp [iSt, ← List.replicate_succ]; congr 1; omega
    by_cases hmaj : majI Rw u y ℓ a i
    · rw [if_pos ⟨i, le_rfl, hiL, hmaj⟩]
      refine (ExecLe.loop_halt (ExecLe.pop_same (k := 18) (T := Ti cc q Tq w.length ℓ a) hpop
        ?_)).cast rfl ?_
      · rw [Mem.upd_18]; exact hb.1 hmaj
      · rw [Nat.succ_mul]; omega
    · have ih := exec_iLoop q Tq Rw w u y ℓ a hq hul hyl m hp hcb htm hx0 hx1 hw hy haa hyc hcj
        hyes hno d (i + 1) (by omega) (by omega)
      have hex : (∃ i', i ≤ i' ∧ i' < a * ℓ ∧ majI Rw u y ℓ a i') ↔
          (∃ i', i + 1 ≤ i' ∧ i' < a * ℓ ∧ majI Rw u y ℓ a i') := by
        constructor
        · rintro ⟨i', h1, h2, h3⟩
          rcases Nat.eq_or_lt_of_le h1 with h | h
          · subst h; exact absurd h3 hmaj
          · exact ⟨i', h, h2, h3⟩
        · rintro ⟨i', h1, h2, h3⟩; exact ⟨i', by omega, h2, h3⟩
      have hbody : ExecLe (.pop 18 .brk (bodyI q cc) (bodyI q cc)) (iSt u (a * ℓ) m i).f
          (.norm (iSt u (a * ℓ) m (i + 1)).f) (Ti cc q Tq w.length ℓ a + 1) := by
        refine ExecLe.pop_same (k := 18) hpop ?_
        rw [Mem.upd_18]
        exact (hb.2 hmaj).cast (by simp [iSt]) le_rfl
      rw [show (if ∃ i', i ≤ i' ∧ i' < a * ℓ ∧ majI Rw u y ℓ a i' then Res.halt true
          else .norm (iSt u (a * ℓ) m (a * ℓ)).f) =
          (if ∃ i', i + 1 ≤ i' ∧ i' < a * ℓ ∧ majI Rw u y ℓ a i' then Res.halt true
          else .norm (iSt u (a * ℓ) m (a * ℓ)).f) by rw [if_congr hex rfl rfl]]
      exact (ExecLe.loop_norm hbody ih).cast rfl (by rw [Nat.succ_mul]; omega)

/-- Cost bound of the main loop. -/
def Tmain (q : Prog) (Tq n ℓ a : ℕ) : ℕ := 5 * (a * ℓ) + (a * ℓ) * (Ti cc q Tq n ℓ a + 1) + 7

theorem exec_mainCmd (q : Prog) (Tq : ℕ) (Rw : Str → Prop) (w u y : Str) (ℓ a : ℕ)
    (hq : ∀ ys : Str, ys.length = ℓ →
      runFor ∅ q Tq (.run (init [w, (ys.flatMap cc).reverse])) = .done (decide (Rw ys)))
    (hul : u.length = (a * ℓ) * (a * ℓ)) (hyl : y.length = a * ℓ)
    (m : Mem) (hp : m.p = List.replicate ℓ true) (hcb : m.cb = [])
    (htm : m.tm = []) (hx0 : m.x0 = []) (hx1 : m.x1 = []) (hw : m.w = w) (hy : m.y = y)
    (haa : m.aa = List.replicate a true) (hyc : m.yc = []) (hcj : m.cj = []) (hyes : m.yes = [])
    (hno : m.no = []) (hu : m.u = u) (hci : m.ci = []) (hlm : m.lm = List.replicate (a * ℓ) true) :
    ExecLe (mainCmd q cc) m.f
      (.halt (decide (∃ i, i < a * ℓ ∧ majI Rw u y ℓ a i))) (Tmain cc q Tq w.length ℓ a) := by
  have c1 : ExecLe (copyVia 14 18 11) m.f (.norm (iSt u (a * ℓ) m 0).f) (5 * (a * ℓ) + 4) :=
    ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
      (by congr 1; cases m; simp_all [iSt]) (by simp [hlm])
  have c2 := exec_iLoop cc q Tq Rw w u y ℓ a hq hul hyl m hp hcb htm hx0 hx1 hw hy haa hyc hcj
    hyes hno (a * ℓ) 0 (by omega) (by omega)
  by_cases hex : ∃ i, i < a * ℓ ∧ majI Rw u y ℓ a i
  · rw [if_pos (by obtain ⟨i, h1, h2⟩ := hex; exact ⟨i, by omega, h1, h2⟩)] at c2
    rw [decide_eq_true hex]
    exact (ExecLe.seq_norm c1 (ExecLe.seq_halt c2)).cast rfl (by unfold Tmain; omega)
  · rw [if_neg (by rintro ⟨i, -, h1, h2⟩; exact hex ⟨i, h1, h2⟩)] at c2
    rw [decide_eq_false hex]
    exact (ExecLe.seq_norm c1 (ExecLe.seq_norm c2 (ExecLe.halt false _))).cast rfl
      (by unfold Tmain; omega)

/-- The specification computed after the arithmetic phase. -/
def tailSpec (Rw : Str → Prop) (u y : Str) (ℓ a : ℕ) : Prop :=
  if ℓ = 0 then Rw [] else
    u.length = (a * ℓ) * (a * ℓ) ∧ (y.length = a * ℓ → ∃ i, i < a * ℓ ∧ majI Rw u y ℓ a i)

/-- Cost bound after the arithmetic phase. -/
def Ttail (q : Prog) (Tq n su sy ℓ a : ℕ) : ℕ :=
  Tq + 5 * n + 8 * su + 8 * sy + 10 * (a * ℓ) + Tmain cc q Tq n ℓ a + 40

theorem exec_tail (q : Prog) (Tq : ℕ) (Rw : Str → Prop) (w u y : Str) (ℓ a : ℕ)
    (hq : ∀ ys : Str, ys.length = ℓ →
      runFor ∅ q Tq (.run (init [w, (ys.flatMap cc).reverse])) = .done (decide (Rw ys)))
    (m : Mem) (hp : m.p = List.replicate ℓ true) (hcb : m.cb = [])
    (htm : m.tm = []) (hx0 : m.x0 = []) (hx1 : m.x1 = []) (hw : m.w = w) (hy : m.y = y)
    (haa : m.aa = List.replicate a true) (hyc : m.yc = []) (hcj : m.cj = []) (hyes : m.yes = [])
    (hno : m.no = []) (hu : m.u = u) (hci : m.ci = []) (hlm : m.lm = List.replicate (a * ℓ) true)
    (hqq : m.qq = List.replicate ((a * ℓ) * (a * ℓ)) true) (he1 : m.e1 = []) (he2 : m.e2 = []) :
    ExecLe (.seq (zeroCmd q) (.seq checkCmd (mainCmd q cc))) m.f
      (.halt (decide (tailSpec Rw u y ℓ a)))
      (Ttail cc q Tq w.length u.length y.length ℓ a) := by
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · -- the case `ℓ = 0`
    subst h0
    have c1 : ExecLe (copyVia 4 24 11) m.f (.norm {m with x0 := w}.f) (5 * w.length + 4) :=
      ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
        (by simp [hw, hx0]) (by simp [hw])
    have hrun : runFor ∅ q Tq (.run ⟨0, view {m with x0 := w}.f 24⟩) =
        .done (decide (Rw [])) := by
      rw [Mem.view]
      show runFor ∅ q Tq (.run (init [w, m.x1])) = _
      rw [hx1]; simpa using hq [] rfl
    obtain ⟨t, τ, ht, -, -, hc⟩ := Exec.call_of_runFor (cf := .halt false) (ct := .halt true) hrun
    have c2 : ExecLe (.call q 24 (.halt false) (.halt true)) {m with x0 := w}.f
        (.halt (decide (Rw []))) (Tq + 1) := by
      refine ⟨t + 1 + 1, by omega, hc ?_⟩
      by_cases hR : Rw [] <;> simp [hR] <;> exact Exec.halt _ _
    have c3 := ExecLe.pop_nil (k := 8) (cf := .push 8 false) (ct := .push 8 true)
      (by simpa using hp) (ExecLe.seq_norm c1 c2)
    rw [show tailSpec Rw u y 0 a = Rw [] by simp [tailSpec]]
    exact (ExecLe.seq_halt c3).cast rfl (by unfold Ttail; omega)
  · have hne : ℓ ≠ 0 := by omega
    have c0 : ExecLe (zeroCmd q) m.f (.norm m.f) 2 := by
      refine ExecLe.pop_cons (k := 8) (b := true) (s := List.replicate (ℓ - 1) true)
        (by simp [hp, ← List.replicate_succ]; congr 1; omega) ?_
      simp only [if_true, Mem.upd_8]
      refine (ExecLe.push 8 true _).cast ?_ le_rfl
      congr 1; simp only [Mem.upd_8, Mem.f_8]
      rw [← List.replicate_succ, show ℓ - 1 + 1 = ℓ by omega, ← hp]
    have k1 : ExecLe (copyVia 5 16 11) m.f (.norm {m with e1 := u}.f) (5 * u.length + 4) :=
      ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
        (by simp [hu, he1]) (by simp [hu])
    have k2 := exec_eqLen (a := 16) (b := 15) (by decide) false u
      (List.replicate ((a * ℓ) * (a * ℓ)) true) {m with e1 := u}.f (by simp) (by simpa using hqq)
    simp only [List.length_replicate] at k2
    rw [show tailSpec Rw u y ℓ a = (u.length = (a * ℓ) * (a * ℓ) ∧
      (y.length = a * ℓ → ∃ i, i < a * ℓ ∧ majI Rw u y ℓ a i)) by simp [tailSpec, hne]]
    by_cases hU : u.length = (a * ℓ) * (a * ℓ)
    · have k2' : ExecLe (eqLen 16 15 false) {m with e1 := u}.f (.norm {m with qq := []}.f)
          (3 * u.length + 3) := ExecLe.of_eq (k2.1 hU) (by simp [he1]) le_rfl
      have k3 : ExecLe (copyVia 6 16 11) {m with qq := []}.f (.norm {m with qq := [], e1 := y}.f)
          (5 * y.length + 4) :=
        ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
          (by simp [hy, he1]) (by simp [hy])
      have k4 : ExecLe (copyVia 14 17 11) {m with qq := [], e1 := y}.f
          (.norm {m with qq := [], e1 := y, e2 := List.replicate (a * ℓ) true}.f)
          (5 * (a * ℓ) + 4) :=
        ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
          (by simp [hlm, he2]) (by simp [hlm])
      have k5 := exec_eqLen (a := 16) (b := 17) (by decide) true y
        (List.replicate (a * ℓ) true) {m with qq := [], e1 := y, e2 := List.replicate (a * ℓ) true}.f
        (by simp) (by simp)
      simp only [List.length_replicate] at k5
      by_cases hY : y.length = a * ℓ
      · have k5' : ExecLe (eqLen 16 17 true)
            {m with qq := [], e1 := y, e2 := List.replicate (a * ℓ) true}.f
            (.norm {m with qq := []}.f) (3 * y.length + 3) :=
          ExecLe.of_eq (k5.1 hY) (by simp [he1, he2]) le_rfl
        have k6 := exec_mainCmd cc q Tq Rw w u y ℓ a hq hU hY {m with qq := []} hp hcb htm hx0
          hx1 hw hy haa hyc hcj hyes hno hu hci hlm
        have e : (u.length = (a * ℓ) * (a * ℓ) ∧
            (y.length = a * ℓ → ∃ i, i < a * ℓ ∧ majI Rw u y ℓ a i)) ↔
            ∃ i, i < a * ℓ ∧ majI Rw u y ℓ a i := ⟨fun h => h.2 hY, fun h => ⟨hU, fun _ => h⟩⟩
        rw [decide_eq_decide.2 e]
        refine (ExecLe.seq_norm c0 (ExecLe.seq_norm (ExecLe.seq_norm k1 (ExecLe.seq_norm k2'
          (ExecLe.seq_norm k3 (ExecLe.seq_norm k4 k5')))) k6)).cast rfl ?_
        unfold Ttail; omega
      · have e : (u.length = (a * ℓ) * (a * ℓ) ∧
            (y.length = a * ℓ → ∃ i, i < a * ℓ ∧ majI Rw u y ℓ a i)) :=
          ⟨hU, fun h => absurd h hY⟩
        refine (ExecLe.seq_norm c0 (ExecLe.seq_halt (ExecLe.seq_norm k1 (ExecLe.seq_norm k2'
          (ExecLe.seq_norm k3 (ExecLe.seq_norm k4 (k5.2 hY))))))).cast (by simp [hU, hY]) ?_
        unfold Ttail; omega
    · have e : ¬ (u.length = (a * ℓ) * (a * ℓ) ∧
          (y.length = a * ℓ → ∃ i, i < a * ℓ ∧ majI Rw u y ℓ a i)) := fun h => hU h.1
      refine (ExecLe.seq_norm c0 (ExecLe.seq_halt (ExecLe.seq_norm k1
        (ExecLe.seq_halt (k2.2 hU))))).cast (by simp [hU]) ?_
      unfold Ttail; omega

end Cert

/-! ## The arithmetic phase -/

/-- Exact cost of `powCmd`. -/
def Tpow (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => Tpow n j + (n ^ j * (5 * n + 8) + 4) + (2 * n ^ j + 2) + (2 * (n ^ j * n) + 2)

theorem exec_powCmd (n : ℕ) : ∀ (j : ℕ) (m : Mem), m.p = [] → m.nn = List.replicate n true →
    m.c = [] → m.ta = [] → m.tm = [] →
    Exec (powCmd j) m.f (.norm {m with p := List.replicate (n ^ j) true}.f) (Tpow n j)
  | 0, m, hp, _, _, _, _ => (Exec.push 8 true _).cast (by simp [hp]) rfl
  | j + 1, m, hp, hn, hc, hta, htm => by
    have h1 := exec_powCmd n j m hp hn hc hta htm
    have h2 := exec_mul (a := 8) (b := 7) (c := 9) (ta := 10) (tm := 11) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (n ^ j) n {m with p := List.replicate (n ^ j) true}.f (by simp) (by simpa using hn)
      (by simpa using hta) (by simpa using htm)
    have h3 := exec_drain 8 _
      {m with p := List.replicate (n ^ j) true, c := List.replicate (n ^ j * n) true}.f rfl
    have h4 := exec_move (a := 9) (b := 8) (by decide) _
      {m with p := [], c := List.replicate (n ^ j * n) true}.f rfl
    refine (Exec.seq_norm h1 (Exec.seq_norm (h2.cast (by simp [hc]) rfl)
      (Exec.seq_norm (h3.cast (by simp) rfl) h4))).cast ?_ ?_
    · simp [hc, pow_succ]
    · simp [Tpow]; ring

/-- Cost of the arithmetic phase after the power. -/
def Far (ℓ : ℕ) : ℕ :=
  25 + (ℓ * (5 * 24 + 8) + 4) + 1 + ((ℓ * 24 + 1) * (5 * 24 + 8) + 4) +
    (2 * (ℓ * 24 + 1) + 2) + ((ℓ * 24 + 1) * 24 * (5 * ℓ + 8) + 4) +
    (5 * ((ℓ * 24 + 1) * 24 * ℓ) + 4) +
    (((ℓ * 24 + 1) * 24 * ℓ) * (5 * ((ℓ * 24 + 1) * 24 * ℓ) + 8) + 4) +
    (2 * ((ℓ * 24 + 1) * 24 * ℓ) + 2)

/-- Exact cost of the arithmetic phase. -/
def Tarith (n k : ℕ) : ℕ := 5 * n + 4 + Tpow n k + Far (n ^ k)

theorem exec_arith (k : ℕ) (m : Mem) (hnn : m.nn = []) (hp : m.p = []) (hc : m.c = [])
    (hta : m.ta = []) (htm : m.tm = []) (hk : m.k24 = []) (haa : m.aa = []) (hlm : m.lm = [])
    (hqq : m.qq = []) :
    Exec (arithCmd k) m.f (.norm {m with
        nn := List.replicate m.w.length true, p := List.replicate (m.w.length ^ k) true,
        k24 := List.replicate 24 true,
        aa := List.replicate ((m.w.length ^ k * 24 + 1) * 24) true,
        lm := List.replicate ((m.w.length ^ k * 24 + 1) * 24 * m.w.length ^ k) true,
        qq := List.replicate ((m.w.length ^ k * 24 + 1) * 24 * m.w.length ^ k *
          ((m.w.length ^ k * 24 + 1) * 24 * m.w.length ^ k)) true}.f)
      (Tarith m.w.length k) := by
  set n := m.w.length with hn
  set ℓ := n ^ k with hℓ
  set a := (ℓ * 24 + 1) * 24 with ha
  have s1 := exec_marks (a := 4) (d := 7) (t := 9) (by decide) (by decide) (by decide) m.f
    (by simpa using hc)
  set m1 := {m with nn := List.replicate n true} with hm1
  have s1' : Exec (marks 4 7 9) m.f (.norm m1.f) (5 * n + 4) := s1.cast (by simp [hm1, hnn, ← hn]) (by simp [← hn])
  have s2 := exec_powCmd n k m1 hp (by simp [hm1]) hc hta htm
  set m2 := {m1 with p := List.replicate ℓ true} with hm2
  have s3 := exec_pushList 12 (List.replicate 24 true) m2.f
  set m3 := {m2 with k24 := List.replicate 24 true} with hm3
  have s3' : Exec (pushList 12 (List.replicate 24 true)) m2.f (.norm m3.f) 25 :=
    s3.cast (by simp [hm3, hm2, hm1, hk]) (by simp)
  have s4 := exec_mul (a := 8) (b := 12) (c := 9) (ta := 10) (tm := 11) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ℓ 24 m3.f (by simp [hm3, hm2]) (by simp [hm3]) (by simpa using hta)
    (by simpa using htm)
  set m4 := {m3 with c := List.replicate (ℓ * 24) true} with hm4
  have s4' : Exec (mul 8 12 9 10 11) m3.f (.norm m4.f) (ℓ * (5 * 24 + 8) + 4) :=
    s4.cast (by simp [hm4, hm3, hm2, hm1, hc]) rfl
  have s5 := Exec.push 9 true m4.f
  set m5 := {m3 with c := List.replicate (ℓ * 24 + 1) true} with hm5
  have s5' : Exec (.push 9 true) m4.f (.norm m5.f) 1 :=
    s5.cast (by simp [hm5, hm4, List.replicate_succ]) rfl
  have s6 := exec_mul (a := 9) (b := 12) (c := 13) (ta := 10) (tm := 11) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (ℓ * 24 + 1) 24 m5.f (by simp [hm5]) (by simp [hm5, hm3]) (by simpa using hta)
    (by simpa using htm)
  set m6 := {m5 with aa := List.replicate a true} with hm6
  have s6' : Exec (mul 9 12 13 10 11) m5.f (.norm m6.f) ((ℓ * 24 + 1) * (5 * 24 + 8) + 4) :=
    s6.cast (by simp [hm6, hm5, hm3, hm2, hm1, haa, ha]) rfl
  have s7 := exec_drain 9 _ m6.f rfl
  set m7 := {m3 with aa := List.replicate a true} with hm7
  have s7' : Exec (drain 9) m6.f (.norm m7.f) (2 * (ℓ * 24 + 1) + 2) :=
    s7.cast (by simp [hm7, hm6, hm5, hm3, hm2, hm1, hc]) (by simp [hm6, hm5])
  have s8 := exec_mul (a := 13) (b := 8) (c := 14) (ta := 10) (tm := 11) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) a ℓ m7.f (by simp [hm7]) (by simp [hm7, hm3, hm2]) (by simpa using hta)
    (by simpa using htm)
  set m8 := {m7 with lm := List.replicate (a * ℓ) true} with hm8
  have s8' : Exec (mul 13 8 14 10 11) m7.f (.norm m8.f) (a * (5 * ℓ + 8) + 4) :=
    s8.cast (by simp [hm8, hm7, hm3, hm2, hm1, hlm]) rfl
  have s9 := exec_copyVia (a := 14) (b := 9) (t := 11) (by decide) (by decide) (by decide) m8.f
    (by simpa using htm)
  set m9 := {m8 with c := List.replicate (a * ℓ) true} with hm9
  have s9' : Exec (copyVia 14 9 11) m8.f (.norm m9.f) (5 * (a * ℓ) + 4) :=
    s9.cast (by simp [hm9, hm8, hm7, hm3, hm2, hm1, hc]) (by simp [hm8])
  have s10 := exec_mul (a := 9) (b := 14) (c := 15) (ta := 10) (tm := 11) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (a * ℓ) (a * ℓ) m9.f (by simp [hm9]) (by simp [hm9, hm8]) (by simpa using hta)
    (by simpa using htm)
  set m10 := {m9 with qq := List.replicate ((a * ℓ) * (a * ℓ)) true} with hm10
  have s10' : Exec (mul 9 14 15 10 11) m9.f (.norm m10.f) ((a * ℓ) * (5 * (a * ℓ) + 8) + 4) :=
    s10.cast (by simp [hm10, hm9, hm8, hm7, hm3, hm2, hm1, hqq]) rfl
  have s11 := exec_drain 9 _ m10.f rfl
  refine (Exec.seq_norm s1' (Exec.seq_norm s2 (Exec.seq_norm s3' (Exec.seq_norm s4'
    (Exec.seq_norm s5' (Exec.seq_norm s6' (Exec.seq_norm s7' (Exec.seq_norm s8'
    (Exec.seq_norm s9' (Exec.seq_norm s10' s11)))))))))).cast ?_ ?_
  · simp [hm10, hm9, hm8, hm7, hm3, hm2, hm1, hc]
  · simp only [Tarith, Far, hm10, hm9, Mem.f_9, List.length_replicate]; ring

/-! ## Parsing -/

theorem init_eq (z : Str) : (init [z]).stk = {Mem.e with z := z}.f := by
  funext j
  rcases j with _ | j
  · rfl
  · by_cases hj : j + 1 < 26
    · have : j < 25 := by omega
      interval_cases j <;> rfl
    · rw [Mem.f_ge _ (by omega)]; simp [init]

theorem exec_parse (z : Str) :
    ExecLe parseCmd {Mem.e with z := z}.f (.norm {Mem.e with
        w := (seg z).1, u := (seg (seg z).2).1, y := (seg (seg (seg z).2).2).1}.f)
      (14 * z.length + 17) := by
  have l1 := seg_length z
  have l2 := seg_length (seg z).2
  have l3 := seg_length (seg (seg z).2).2
  have p1 := exec_seg (src := 0) (dst := 1) (by decide) z {Mem.e with z := z}.f rfl
  have p2 := exec_seg (src := 0) (dst := 2) (by decide) (seg z).2
    {Mem.e with z := (seg z).2, w1 := (seg z).1.reverse}.f rfl
  have p3 := exec_seg (src := 0) (dst := 3) (by decide) (seg (seg z).2).2
    {Mem.e with z := (seg (seg z).2).2, w1 := (seg z).1.reverse, u1 := (seg (seg z).2).1.reverse}.f rfl
  have p4 := exec_drain 0 (seg (seg (seg z).2).2).2 {Mem.e with
    z := (seg (seg (seg z).2).2).2, w1 := (seg z).1.reverse, u1 := (seg (seg z).2).1.reverse, y1 := (seg (seg (seg z).2).2).1.reverse}.f rfl
  have p5 := exec_move (a := 1) (b := 4) (by decide) _ {Mem.e with
    w1 := (seg z).1.reverse, u1 := (seg (seg z).2).1.reverse, y1 := (seg (seg (seg z).2).2).1.reverse}.f rfl
  have p6 := exec_move (a := 2) (b := 5) (by decide) _ {Mem.e with
    w := (seg z).1, u1 := (seg (seg z).2).1.reverse, y1 := (seg (seg (seg z).2).2).1.reverse}.f rfl
  have p7 := exec_move (a := 3) (b := 6) (by decide) _ {Mem.e with
    w := (seg z).1, u := (seg (seg z).2).1, y1 := (seg (seg (seg z).2).2).1.reverse}.f rfl
  refine (ExecLe.seq_norm (p1.cast (by simp [Mem.e]) le_rfl) (ExecLe.seq_norm
    (p2.cast (by simp [Mem.e]) le_rfl) (ExecLe.seq_norm (p3.cast (by simp [Mem.e]) le_rfl)
    (ExecLe.seq_norm (ExecLe.of_eq p4 (by simp [Mem.e]) le_rfl)
    (ExecLe.seq_norm (ExecLe.of_eq p5 (by simp [Mem.e]) le_rfl)
    (ExecLe.seq_norm (ExecLe.of_eq p6 (by simp [Mem.e]) le_rfl)
    (ExecLe.of_eq p7 (by simp [Mem.e]) le_rfl))))))).cast rfl ?_
  simp only [Mem.f_1, Mem.f_2, Mem.f_3, List.length_reverse]
  omega

/-! ## The whole program -/

theorem exec_prog (q : Prog) (cc : Bool → Str) (k K : ℕ) (R : Str → Str → Prop)
    (hq : ∀ x ys : Str, ys.length ≤ x.length ^ k →
      runFor ∅ q (tb K x.length) (.run (init [x, (ys.flatMap cc).reverse])) =
        .done (decide (R x ys))) (z : Str) :
    ExecLe (prog q cc k) (init [z]).stk
      (.halt (decide (tailSpec (R (seg z).1) (seg (seg z).2).1 (seg (seg (seg z).2).2).1
        ((seg z).1.length ^ k) (((seg z).1.length ^ k * 24 + 1) * 24))))
      (14 * z.length + 17 + Tarith (seg z).1.length k +
        Ttail cc q (tb K (seg z).1.length) (seg z).1.length (seg (seg z).2).1.length
          (seg (seg (seg z).2).2).1.length ((seg z).1.length ^ k)
          (((seg z).1.length ^ k * 24 + 1) * 24)) := by
  set w := (seg z).1
  set u := (seg (seg z).2).1
  set y := (seg (seg (seg z).2).2).1
  set ℓ := w.length ^ k
  have hp := exec_parse z
  set mP : Mem := {Mem.e with w := w, u := u, y := y} with hmP
  have ha := exec_arith k mP rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hq' : ∀ ys : Str, ys.length = ℓ →
      runFor ∅ q (tb K w.length) (.run (init [w, (ys.flatMap cc).reverse])) =
        .done (decide (R w ys)) := fun ys h => hq w ys h.le
  have ht := exec_tail cc q (tb K w.length) (R w) w u y ℓ ((ℓ * 24 + 1) * 24) hq'
    {mP with
      nn := List.replicate mP.w.length true, p := List.replicate (mP.w.length ^ k) true,
      k24 := List.replicate 24 true,
      aa := List.replicate ((mP.w.length ^ k * 24 + 1) * 24) true,
      lm := List.replicate ((mP.w.length ^ k * 24 + 1) * 24 * mP.w.length ^ k) true,
      qq := List.replicate ((mP.w.length ^ k * 24 + 1) * 24 * mP.w.length ^ k *
        ((mP.w.length ^ k * 24 + 1) * 24 * mP.w.length ^ k)) true}
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [init_eq]
  exact (ExecLe.seq_norm hp (ExecLe.seq_norm (ExecLe.of ha) ht)).cast rfl (le_of_eq (by ring))

/-! ## Correctness: the computed predicate is `lautSpec` -/

theorem blk_eq (u y : Str) (ℓ i j : ℕ) : blk u y ℓ (i * sgL ℓ) j = lblock ℓ u y i j := by
  unfold blk lblock
  apply List.ext_getElem
  · simp
  · intro b h1 h2
    simp [bitF, lbit, add_assoc]

theorem tailSpec_iff (Rw : Str → Prop) (u y : Str) (ℓ : ℕ) :
    tailSpec Rw u y ℓ ((ℓ * 24 + 1) * 24) ↔ lautSpec Rw ℓ u y := by
  have ha : (ℓ * 24 + 1) * 24 = sglReps ℓ := by unfold sglReps; ring
  rw [ha]
  unfold tailSpec lautSpec
  split_ifs with h
  · exact Iff.rfl
  · have hL : sglReps ℓ * ℓ = sgL ℓ := rfl
    rw [hL]
    refine and_congr Iff.rfl (imp_congr Iff.rfl (exists_congr fun i => and_congr Iff.rfl ?_))
    unfold majI lmaj
    rw [card_filter_fin (fun j => Rw (lblock ℓ u y i j)), hL]
    simp only [blk_eq]

/-! ## Time bound -/

theorem Tpow_le (n : ℕ) : ∀ j, Tpow n j ≤ (j + 1) * 30 * (n + 1) ^ (j + 1)
  | 0 => by simp [Tpow]; omega
  | j + 1 => by
    have ih := Tpow_le n j
    have hA1 : 1 ≤ (n + 1) ^ (j + 1) := Nat.one_le_pow _ _ (by omega)
    have hAB : (n + 1) ^ (j + 1) ≤ (n + 1) ^ (j + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : n ^ j ≤ (n + 1) ^ (j + 1) :=
      (Nat.pow_le_pow_left (by omega) j).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : n ^ j * n ≤ (n + 1) ^ (j + 1) := by
      rw [← pow_succ]; exact Nat.pow_le_pow_left (by omega) _
    have h3 := Nat.mul_le_mul_left ((j + 1) * 30) hAB
    simp only [Tpow]
    nlinarith

/-- Generic cost bounds with all parameters replaced by one bound `V`. -/
def TjV (V : ℕ) : ℕ := 3 * V + 7 * V + V * (3 * V + 9) + 2 * (V + 2) + 13
def TiV (V : ℕ) : ℕ := 5 * (V * V) + 12 * V + V * (TjV V + 1) + 17
def TmainV (V : ℕ) : ℕ := 5 * (V * V) + (V * V) * (TiV V + 1) + 7
def TtailV (V : ℕ) : ℕ := V + 5 * V + 8 * V + 8 * V + 10 * (V * V) + TmainV V + 40

theorem Ttail_le (cc : Bool → Str) (q : Prog) {Tq n su sy ℓ a V : ℕ} (hB : Bc cc ≤ V)
    (hN : Official.nW q ≤ V) (hTq : Tq ≤ V) (hn : n ≤ V) (hsu : su ≤ V) (hsy : sy ≤ V)
    (hℓ : ℓ ≤ V) (ha : a ≤ V) : Ttail cc q Tq n su sy ℓ a ≤ TtailV V := by
  have hj : Tj cc q Tq n ℓ ≤ TjV V := by unfold Tj TjV; gcongr
  have hi : Ti cc q Tq n ℓ a ≤ TiV V := by unfold Ti TiV; gcongr
  have hm : Tmain cc q Tq n ℓ a ≤ TmainV V := by unfold Tmain TmainV; gcongr
  unfold Ttail TtailV; gcongr

theorem Far_mono {ℓ V : ℕ} (h : ℓ ≤ V) : Far ℓ ≤ Far V := by unfold Far; gcongr

theorem poly_le (V : ℕ) (hV : 1 ≤ V) : 5 * V + 30 * (V * V) + Far V + TtailV V ≤
    10 ^ 8 * V ^ 5 := by
  have h1 : 1 ≤ V ^ 5 := Nat.one_le_pow _ _ (by omega)
  have h2 : V ≤ V ^ 5 := by
    calc V = V ^ 1 := (pow_one V).symm
      _ ≤ V ^ 5 := Nat.pow_le_pow_right hV (by omega)
  have h3 : V ^ 2 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by omega)
  have h4 : V ^ 3 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by omega)
  have h5 : V ^ 4 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by omega)
  unfold Far TtailV TmainV TiV TjV
  ring_nf
  nlinarith

/-- The exponent of the final time bound. -/
def Kfin (cc : Bool → Str) (q : Prog) (k K : ℕ) : ℕ :=
  10 ^ 8 * (1000 * (Bc cc + Official.nW q + k + 1)) ^ 5 + 14 + 21 + 5 * (k + K + 1)

theorem total_le (cc : Bool → Str) (q : Prog) (k K : ℕ) (z : Str) :
    14 * z.length + 17 + Tarith (seg z).1.length k +
        Ttail cc q (tb K (seg z).1.length) (seg z).1.length (seg (seg z).2).1.length
          (seg (seg (seg z).2).2).1.length ((seg z).1.length ^ k)
          (((seg z).1.length ^ k * 24 + 1) * 24) ≤ tb (Kfin cc q k K) z.length := by
  set n := (seg z).1.length with hn
  have l1 := seg_length z
  have l2 := seg_length (seg z).2
  have l3 := seg_length (seg (seg z).2).2
  have hnz : n ≤ z.length := by omega
  have hsu : (seg (seg z).2).1.length ≤ z.length := by omega
  have hsy : (seg (seg (seg z).2).2).1.length ≤ z.length := by omega
  set X := z.length + 2 with hX
  set E := k + K + 1 with hE
  set P := X ^ E with hP
  set c0 := Bc cc + Official.nW q + k + 1 with hc0
  set V := 1000 * c0 * P with hV
  have hX1 : 1 ≤ X := by omega
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hXP : X ≤ P := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ P := Nat.pow_le_pow_right hX1 (by omega)
  have hPV : P ≤ V := by
    have : 1 ≤ 1000 * c0 := by omega
    calc P = 1 * P := (one_mul P).symm
      _ ≤ 1000 * c0 * P := Nat.mul_le_mul_right _ this
  have hcV : c0 ≤ V := by
    calc c0 = c0 * 1 := (mul_one c0).symm
      _ ≤ c0 * (1000 * P) := Nat.mul_le_mul_left _ (by omega)
      _ = V := by rw [hV]; ring
  have hV1 : 1 ≤ V := hP1.trans hPV
  have hnV : n ≤ V := by omega
  have hℓP : n ^ k ≤ P := (Nat.pow_le_pow_left (by omega) k).trans
    (Nat.pow_le_pow_right hX1 (by omega))
  have hℓV : n ^ k ≤ V := hℓP.trans hPV
  have haV : (n ^ k * 24 + 1) * 24 ≤ V := by
    have : (n ^ k * 24 + 1) * 24 ≤ 1000 * P := by nlinarith
    calc (n ^ k * 24 + 1) * 24 ≤ 1000 * P := this
      _ ≤ 1000 * c0 * P := Nat.mul_le_mul_right _ (by nlinarith)
  have hTqV : tb K n ≤ V := by
    unfold tb
    exact ((Nat.pow_le_pow_left (by omega) K).trans (Nat.pow_le_pow_right hX1 (by omega))).trans
      hPV
  have hpow : Tpow n k ≤ 30 * (V * V) := by
    have h1 := Tpow_le n k
    have h2 : (n + 1) ^ (k + 1) ≤ V :=
      ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hX1 (by omega))).trans hPV
    have h3 : k + 1 ≤ V := by omega
    calc Tpow n k ≤ (k + 1) * 30 * (n + 1) ^ (k + 1) := h1
      _ ≤ V * 30 * V := by gcongr
      _ = 30 * (V * V) := by ring
  have ht := Ttail_le cc q (by omega) (by omega) hTqV hnV (hsu.trans (by omega))
    (hsy.trans (by omega)) hℓV haV
  have hfar := Far_mono hℓV
  have hpoly := poly_le V hV1
  have hV5 : V ^ 5 = (1000 * c0) ^ 5 * X ^ (5 * E) := by rw [hV, hP, mul_pow, ← pow_mul]; ring_nf
  have hXE : X ≤ X ^ (5 * E) := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ (5 * E) := Nat.pow_le_pow_right hX1 (by omega)
  have hfin := Pnp.Relativize.OfficialP.absorb (10 ^ 8 * (1000 * c0) ^ 5 + 14) 21 (5 * E)
    z.length
  rw [← hX] at hfin
  have hkf : Kfin cc q k K = 10 ^ 8 * (1000 * c0) ^ 5 + 14 + 21 + 5 * E := by
    simp only [Kfin, hc0, hE]
  rw [show tb (Kfin cc q k K) z.length = X ^ Kfin cc q k K from rfl, hkf]
  refine le_trans ?_ hfin
  have hT : Tarith n k ≤ 5 * V + 4 + 30 * (V * V) + Far V := by
    unfold Tarith; omega
  rw [hV5] at hpoly
  have hz : z.length ≤ X ^ (5 * E) := by omega
  generalize Far V = F at *
  generalize TtailV V = G at *
  generalize Tarith n k = T1 at *
  generalize X ^ (5 * E) = A at *
  generalize (1000 * c0) ^ 5 = B at *
  have e : (10 ^ 8 * B + 14) * A = 10 ^ 8 * (B * A) + 14 * A := by ring
  rw [e]
  have e2 : 10 ^ 8 * (B * A) = 10 ^ 8 * B * A := by ring
  omega

/-! ## Codes of triples -/

open Millennium in
/-- The nested Cook pair encoding of `((w, u), y)`. -/
abbrev enc3 : Computability.FinEncoding ((List Bool × List Bool) × List Bool) :=
  pair_encoding (pair_encoding (fin_encoding_string Bool) (fin_encoding_string Bool))
    (fin_encoding_string Bool)

/-- Symbol code: data bits `b ↦ [false, b]`, separators `↦ [true, true]`. -/
def symc : (Bool ⊕ Option Bool) ⊕ Option Bool → Str
  | .inl (.inl b) => [false, b]
  | .inl (.inr none) => [true, true]
  | .inl (.inr (some b)) => [false, b]
  | .inr none => [true, true]
  | .inr (some b) => [false, b]

theorem flatMap_enc3 (w u y : Str) :
    (enc3.encode ((w, u), y)).flatMap symc =
      dbl w ++ true :: true :: (dbl u ++ true :: true :: dbl y) := by
  have h1 : ∀ s : Str, (s.map (fun b => (Sum.inl (Sum.inl b) : (Bool ⊕ Option Bool) ⊕ Option Bool))).flatMap symc = dbl s := by
    intro s; induction s with
    | nil => rfl
    | cons b s ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl
  have h2 : ∀ s : Str, (s.map (fun b => (Sum.inl (Sum.inr (some b)) : (Bool ⊕ Option Bool) ⊕ Option Bool))).flatMap symc = dbl s := by
    intro s; induction s with
    | nil => rfl
    | cons b s ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl
  have h3 : ∀ s : Str, (s.map (fun b => (Sum.inr (some b) : (Bool ⊕ Option Bool) ⊕ Option Bool))).flatMap symc = dbl s := by
    intro s; induction s with
    | nil => rfl
    | cons b s ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl
  show (((w.map Sum.inl ++ Sum.inr none :: u.map (fun b => Sum.inr (some b))).map Sum.inl ++
      Sum.inr none :: y.map (fun b => Sum.inr (some b))) :
      List ((Bool ⊕ Option Bool) ⊕ Option Bool)).flatMap symc = _
  rw [List.map_append, List.map_cons, List.map_map, List.map_map]
  rw [List.flatMap_append, List.flatMap_cons, List.flatMap_append, List.flatMap_cons]
  rw [show (Sum.inl ∘ Sum.inl : Bool → (Bool ⊕ Option Bool) ⊕ Option Bool) =
    fun b => Sum.inl (Sum.inl b) from rfl, h1]
  rw [show (Sum.inl ∘ fun b => Sum.inr (some b) : Bool → (Bool ⊕ Option Bool) ⊕ Option Bool) =
    fun b => Sum.inl (Sum.inr (some b)) from rfl, h2, h3]
  simp [symc]

theorem seg_code (w u y : Str) :
    let z := dbl w ++ true :: true :: (dbl u ++ true :: true :: dbl y)
    (seg z).1 = w ∧ (seg (seg z).2).1 = u ∧ (seg (seg (seg z).2).2).1 = y := by
  simp [seg_dbl_sep, seg_dbl]

end

end Pnp.Derand.BPPS2

namespace Pnp.Derand

open Pnp.Relativize Pnp.Relativize.Struct Pnp.Derand.BPPS2

theorem lautSpec_Q (R : List Bool → Prop) (ℓ : ℕ) (u : List Bool) {Q : ℕ} (hQ : sgL ℓ ≤ Q) :
    (∀ y : List Bool, y.length ≤ Q → lautSpec R ℓ u y) ↔
      (∀ y : List Bool, y.length ≤ sgL ℓ → lautSpec R ℓ u y) := by
  refine ⟨fun h y hy => h y (hy.trans hQ), fun h y hy => ?_⟩
  unfold lautSpec
  split_ifs with h0
  · have := h [] (by simp); rwa [lautSpec, if_pos h0] at this
  · have h1 := h (List.replicate (sgL ℓ) false) (by simp)
    rw [lautSpec, if_neg h0] at h1
    refine ⟨h1.1, fun hy' => ?_⟩
    have h2 := h y (by omega)
    rw [lautSpec, if_neg h0] at h2
    exact h2.2 hy'

theorem sgL_pow_mono (k : ℕ) {m m' : ℕ} (h : m ≤ m') : sgL (m ^ k) ≤ sgL (m' ^ k) := by
  unfold sgL sglReps; gcongr

/-- **`BPP ⊆ Σ₂ᴾ`** (Sipser–Gács–Lautemann), for the official classes: every language in
`BPP` (official-style, `Pnp.Derand.InBPP`) is in the official second level of the polynomial
hierarchy. -/
theorem bpp_subset_sigma2 {L : Millennium.Language (List Bool)} (h : InBPP L) :
    Millennium.polynomial_hierarchy_sigma_level 2 (Millennium.fin_encoding_string Bool) L := by
  classical
  obtain ⟨R, k, hR, herr⟩ := h
  obtain ⟨q, cc, K, hq⟩ := Pnp.Relativize.NPEquiv.checkProg hR k
  have hrun := fun z => ((exec_prog q cc k K R hq z).mono (total_le cc q k K z)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg (prog q cc k)) (tb (Kfin cc q k K) z.length)
    (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg (prog q cc k), Kfin cc q k K, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  let D : Millennium.Language ((List Bool × List Bool) × List Bool) :=
    fun t => lautSpec (R t.1.1) (t.1.1.length ^ k) t.1.2 t.2
  have hD : Millennium.InPolynomialTime enc3 D := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code enc3 symc S hS D (fun t => ?_)
    obtain ⟨⟨w, u⟩, y⟩ := t
    erw [flatMap_enc3]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun]
    obtain ⟨e1, e2, e3⟩ := seg_code w u y
    rw [e1, e2, e3]
    simp only [State.done.injEq, decide_eq_true_iff, tailSpec_iff]
    exact Iff.rfl
  let pL : Polynomial ℕ := 2 * (12 * (24 * Polynomial.X ^ k + 1)) * Polynomial.X ^ k
  have hpL : ∀ m, pL.eval m = sgL (m ^ k) := by
    intro m; simp [pL, sgL, sglReps]
  refine sigma2_intro (Millennium.fin_encoding_string Bool) L Bool Bool D hD (pL * pL) pL
    (fun a => ?_)
  rw [lautemann_list (R a) (L a) (a.length ^ k) (sgL (a.length ^ k)) le_rfl (herr a)]
  simp only [Millennium.fin_encoding_string_encode, Polynomial.eval_mul, hpL,
    Millennium.pair_encoding.length_eq]
  refine exists_congr fun u => and_congr Iff.rfl ?_
  show _ ↔ ∀ c : List Bool, c.length ≤ sgL ((a.length + 1 + u.length) ^ k) →
    lautSpec (R a) (a.length ^ k) u c
  rw [lautSpec_Q (R a) _ u (sgL_pow_mono k (show a.length ≤ a.length + 1 + u.length by omega))]

end Pnp.Derand
