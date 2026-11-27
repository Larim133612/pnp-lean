import Pnp.KarpLipton.DTab
import Pnp.Oracle.Horner

/-!
# The program for the inner predicate of the Karp–Lipton `Σ₂` form (M32e, part 2)

A program of our structured stack language (`Pnp/Oracle/Struct.lean`), described by the raw data
`Par` (table widths and codes, fixed separator codes, two polynomials and the called decider `q`):

1. **parse** the input bit string `z` into the table indices `iw` (first region), the bit string
   `W` (second region, a bit-pair code) and the table indices `ib` (third region), with
   `n = |iw|`, `m = |ib|` marks;
2. **arith**: if `m > p(n)` accept; else `N = Q(n + 1 + m)` marks;
3. **build** the fixed prefix code `pp` (codes of `iw`, separator, codes of `ib`, separator) and the
   wire values `V` (blocks of `iw`, separator block, blocks of `ib`);
4. **select** the `m`-th segment `G` of `W`;
5. **evaluate** `R = evalD G V [] false false` (`evalCmd`) and reverse it;
6. **main loop** for `t = 0, …, N`: call `q` on `pp ++` codes of the first `t` decoded blocks;
   accept on answer `false`; decode the next block of `kC` bits by a table look-up.

`exec_prog`: on **every** input the program halts with the answer `Dsem z`, within an explicit
cost.  The called program is only assumed to halt on the inputs it can actually receive, which
are built from fixed codes only.
-/

namespace Pnp.KarpLipton.DP

open Function Pnp.Relativize Pnp.Relativize.Struct

noncomputable section

/-- The raw data of the program. -/
structure Par where
  (kA kB kC dA dB dC BA BB BC : ℕ)
  (SA TA SB TB SC : ℕ → Str)
  (sWB sC bS : Str)
  (p Q : Polynomial ℕ)
  (q : Prog)

/-- The assumptions on the data: bounds on the table codes. -/
structure Par.Ok (π : Par) : Prop where
  hA : ∀ j, (π.SA j).length + (π.TA j).length ≤ π.BA
  hB : ∀ j, (π.SB j).length + (π.TB j).length ≤ π.BB
  hC : ∀ j, (π.SC j).length + ([] : Str).length ≤ π.BC

/-- The 31 stacks of the program. -/
structure Mem where
  (z pw vw nn wr pb vb mm ws jk gr g v s fu fw pp xs ac nx ta tm c1 xx cnt ra t1 yes no x0 x1 : Str)

/-- The stacks as a list. -/
def Mem.l (m : Mem) : List Str :=
  [m.z, m.pw, m.vw, m.nn, m.wr, m.pb, m.vb, m.mm, m.ws, m.jk, m.gr, m.g, m.v, m.s, m.fu, m.fw, m.pp, m.xs, m.ac, m.nx, m.ta, m.tm, m.c1, m.xx, m.cnt, m.ra, m.t1, m.yes, m.no, m.x0, m.x1]

/-- The stack contents seen by the machine. -/
def Mem.f (m : Mem) : ℕ → Str := fun j => m.l.getD j []

theorem update_getD (l : List Str) (k : ℕ) (hk : k < l.length) (s : Str) :
    update (fun j => l.getD j []) k s = fun j => (l.set k s).getD j [] := by
  funext j
  by_cases h : j = k
  · subst h; simp [List.getD_eq_getElem?_getD, hk]
  · rw [update_of_ne h]; simp [List.getD_eq_getElem?_getD, Ne.symm h]

@[simp] theorem Mem.f_0 (m : Mem) : m.f 0 = m.z := rfl
@[simp] theorem Mem.f_1 (m : Mem) : m.f 1 = m.pw := rfl
@[simp] theorem Mem.f_2 (m : Mem) : m.f 2 = m.vw := rfl
@[simp] theorem Mem.f_3 (m : Mem) : m.f 3 = m.nn := rfl
@[simp] theorem Mem.f_4 (m : Mem) : m.f 4 = m.wr := rfl
@[simp] theorem Mem.f_5 (m : Mem) : m.f 5 = m.pb := rfl
@[simp] theorem Mem.f_6 (m : Mem) : m.f 6 = m.vb := rfl
@[simp] theorem Mem.f_7 (m : Mem) : m.f 7 = m.mm := rfl
@[simp] theorem Mem.f_8 (m : Mem) : m.f 8 = m.ws := rfl
@[simp] theorem Mem.f_9 (m : Mem) : m.f 9 = m.jk := rfl
@[simp] theorem Mem.f_10 (m : Mem) : m.f 10 = m.gr := rfl
@[simp] theorem Mem.f_11 (m : Mem) : m.f 11 = m.g := rfl
@[simp] theorem Mem.f_12 (m : Mem) : m.f 12 = m.v := rfl
@[simp] theorem Mem.f_13 (m : Mem) : m.f 13 = m.s := rfl
@[simp] theorem Mem.f_14 (m : Mem) : m.f 14 = m.fu := rfl
@[simp] theorem Mem.f_15 (m : Mem) : m.f 15 = m.fw := rfl
@[simp] theorem Mem.f_16 (m : Mem) : m.f 16 = m.pp := rfl
@[simp] theorem Mem.f_17 (m : Mem) : m.f 17 = m.xs := rfl
@[simp] theorem Mem.f_18 (m : Mem) : m.f 18 = m.ac := rfl
@[simp] theorem Mem.f_19 (m : Mem) : m.f 19 = m.nx := rfl
@[simp] theorem Mem.f_20 (m : Mem) : m.f 20 = m.ta := rfl
@[simp] theorem Mem.f_21 (m : Mem) : m.f 21 = m.tm := rfl
@[simp] theorem Mem.f_22 (m : Mem) : m.f 22 = m.c1 := rfl
@[simp] theorem Mem.f_23 (m : Mem) : m.f 23 = m.xx := rfl
@[simp] theorem Mem.f_24 (m : Mem) : m.f 24 = m.cnt := rfl
@[simp] theorem Mem.f_25 (m : Mem) : m.f 25 = m.ra := rfl
@[simp] theorem Mem.f_26 (m : Mem) : m.f 26 = m.t1 := rfl
@[simp] theorem Mem.f_27 (m : Mem) : m.f 27 = m.yes := rfl
@[simp] theorem Mem.f_28 (m : Mem) : m.f 28 = m.no := rfl
@[simp] theorem Mem.f_29 (m : Mem) : m.f 29 = m.x0 := rfl
@[simp] theorem Mem.f_30 (m : Mem) : m.f 30 = m.x1 := rfl
@[simp] theorem Mem.upd_0 (m : Mem) (t : Str) : update m.f 0 t = {m with z := t}.f :=
  update_getD m.l 0 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_1 (m : Mem) (t : Str) : update m.f 1 t = {m with pw := t}.f :=
  update_getD m.l 1 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_2 (m : Mem) (t : Str) : update m.f 2 t = {m with vw := t}.f :=
  update_getD m.l 2 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_3 (m : Mem) (t : Str) : update m.f 3 t = {m with nn := t}.f :=
  update_getD m.l 3 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_4 (m : Mem) (t : Str) : update m.f 4 t = {m with wr := t}.f :=
  update_getD m.l 4 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_5 (m : Mem) (t : Str) : update m.f 5 t = {m with pb := t}.f :=
  update_getD m.l 5 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_6 (m : Mem) (t : Str) : update m.f 6 t = {m with vb := t}.f :=
  update_getD m.l 6 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_7 (m : Mem) (t : Str) : update m.f 7 t = {m with mm := t}.f :=
  update_getD m.l 7 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_8 (m : Mem) (t : Str) : update m.f 8 t = {m with ws := t}.f :=
  update_getD m.l 8 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_9 (m : Mem) (t : Str) : update m.f 9 t = {m with jk := t}.f :=
  update_getD m.l 9 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_10 (m : Mem) (t : Str) : update m.f 10 t = {m with gr := t}.f :=
  update_getD m.l 10 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_11 (m : Mem) (t : Str) : update m.f 11 t = {m with g := t}.f :=
  update_getD m.l 11 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_12 (m : Mem) (t : Str) : update m.f 12 t = {m with v := t}.f :=
  update_getD m.l 12 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_13 (m : Mem) (t : Str) : update m.f 13 t = {m with s := t}.f :=
  update_getD m.l 13 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_14 (m : Mem) (t : Str) : update m.f 14 t = {m with fu := t}.f :=
  update_getD m.l 14 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_15 (m : Mem) (t : Str) : update m.f 15 t = {m with fw := t}.f :=
  update_getD m.l 15 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_16 (m : Mem) (t : Str) : update m.f 16 t = {m with pp := t}.f :=
  update_getD m.l 16 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_17 (m : Mem) (t : Str) : update m.f 17 t = {m with xs := t}.f :=
  update_getD m.l 17 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_18 (m : Mem) (t : Str) : update m.f 18 t = {m with ac := t}.f :=
  update_getD m.l 18 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_19 (m : Mem) (t : Str) : update m.f 19 t = {m with nx := t}.f :=
  update_getD m.l 19 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_20 (m : Mem) (t : Str) : update m.f 20 t = {m with ta := t}.f :=
  update_getD m.l 20 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_21 (m : Mem) (t : Str) : update m.f 21 t = {m with tm := t}.f :=
  update_getD m.l 21 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_22 (m : Mem) (t : Str) : update m.f 22 t = {m with c1 := t}.f :=
  update_getD m.l 22 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_23 (m : Mem) (t : Str) : update m.f 23 t = {m with xx := t}.f :=
  update_getD m.l 23 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_24 (m : Mem) (t : Str) : update m.f 24 t = {m with cnt := t}.f :=
  update_getD m.l 24 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_25 (m : Mem) (t : Str) : update m.f 25 t = {m with ra := t}.f :=
  update_getD m.l 25 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_26 (m : Mem) (t : Str) : update m.f 26 t = {m with t1 := t}.f :=
  update_getD m.l 26 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_27 (m : Mem) (t : Str) : update m.f 27 t = {m with yes := t}.f :=
  update_getD m.l 27 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_28 (m : Mem) (t : Str) : update m.f 28 t = {m with no := t}.f :=
  update_getD m.l 28 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_29 (m : Mem) (t : Str) : update m.f 29 t = {m with x0 := t}.f :=
  update_getD m.l 29 (by simp [Mem.l]) t
@[simp] theorem Mem.upd_30 (m : Mem) (t : Str) : update m.f 30 t = {m with x1 := t}.f :=
  update_getD m.l 30 (by simp [Mem.l]) t

theorem Mem.f_ge (m : Mem) {j : ℕ} (hj : 31 ≤ j) : m.f j = [] := by
  unfold Mem.f; rw [List.getD_eq_default _ _ (by simp [Mem.l]; omega)]

theorem Mem.view (m : Mem) : view m.f 29 = (init [m.x0, m.x1]).stk := by
  funext j
  rcases j with _ | _ | j
  · rfl
  · rfl
  · simp only [view_apply, init]
    rw [Mem.f_ge m (by omega)]; simp

theorem Mem.cut (m : Mem) :
    (fun j => if j < 29 then m.f j else []) = {m with x0 := [], x1 := []}.f := by
  funext j
  by_cases hj : j < 29
  · rw [if_pos hj]; interval_cases j <;> rfl
  · rw [if_neg hj]
    obtain ⟨d, rfl⟩ : ∃ d, j = 29 + d := ⟨j - 29, by omega⟩
    rcases d with _ | _ | d
    · rfl
    · rfl
    · rw [Mem.f_ge _ (by omega)]

/-- All stacks empty. -/
def Mem.e : Mem := ⟨[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩

theorem init_eq (z : Str) : (init [z]).stk = {Mem.e with z := z}.f := by
  funext j
  rcases j with _ | j
  · rfl
  · simp only [init]
    by_cases hj : j + 1 < 31
    · have : j < 30 := by omega
      interval_cases j <;> rfl
    · rw [Mem.f_ge _ (by omega)]; simp

/-! ## The program -/

section Prog

variable (π : Par)

/-- Parse the three regions. -/
def parseCmd : Cmd :=
  .seq (slLoop 0 1 2 3 π.SA π.TA π.kA π.dA) (.seq (segCmd 0 4)
    (.seq (slLoop 0 5 6 7 π.SB π.TB π.kB π.dB) (move 4 8)))

/-- Compare: accept if `|mm| > |ac|` (consumes `c1` and part of `ac`). -/
def cmpCmd : Cmd :=
  .seq (copyVia 7 22 21)
    (.loop (.pop 22 .brk (.pop 18 (.halt true) .skip .skip) (.pop 18 (.halt true) .skip .skip)))

/-- Unary arithmetic. -/
def arithCmd : Cmd :=
  .seq (copyVia 3 17 21) (.seq (polyCmd 17 18 19 20 21 π.p) (.seq (cmpCmd) (.seq (drain 18)
    (.seq (.push 17 true) (.seq (copyVia 7 17 21) (.seq (polyCmd 17 18 19 20 21 π.Q)
      (move 18 24)))))))

/-- Build the prefix code and the wire values. -/
def buildCmd : Cmd :=
  .seq (pushList 16 π.sC) (.seq (move 5 16) (.seq (pushList 16 π.sWB) (.seq (move 1 16)
    (.seq (move 6 12) (.seq (pushList 12 π.bS) (move 2 12))))))

/-- Select the `m`-th segment of `W`. -/
def selCmd : Cmd :=
  .seq (copyVia 7 22 21) (.seq (selLoop 22 8 9) (.seq (segCmd 8 10) (move 10 11)))

/-- Evaluate and reverse. -/
def evCmd : Cmd := .seq (evalCmd 11 12 13 14 15) (move 12 23)

/-- One round of the main loop. -/
def mBody : Cmd :=
  .seq (copyVia 25 26 21) (.seq (move 26 29) (.seq (copyVia 16 29 21) (.seq (callDrain π.q 29 27 28)
    (.seq (.pop 28 .skip .skip (.halt true))
      (.pop 24 (.halt false) (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)
        (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC))))))

/-- The main loop. -/
def mLoop : Cmd := .loop (mBody π)

/-- The whole program. -/
def prog : Cmd :=
  .seq (parseCmd π) (.seq (arithCmd π) (.seq (buildCmd π) (.seq (selCmd) (.seq evCmd (mLoop π)))))

end Prog

/-! ## Parsing -/

section Sem

variable (π : Par)

/-- The first region: table indices and rest. -/
def r1 (z : Str) : List ℕ × Str := sl π.kA π.dA z
/-- The second region: the bit string `W` and rest. -/
def r2 (z : Str) : Str × Str := seg (r1 π z).2
/-- The third region: table indices and rest. -/
def r3 (z : Str) : List ℕ × Str := sl π.kB π.dB (r2 π z).2

end Sem

theorem exec_parse (π : Par) (hπ : π.Ok) (z : Str) :
    ExecLe (parseCmd π) {Mem.e with z := z}.f (.norm {Mem.e with
        z := (r3 π z).2,
        pw := (r1 π z).1.reverse.flatMap π.SA, vw := (r1 π z).1.reverse.flatMap π.TA,
        nn := List.replicate (r1 π z).1.length true,
        pb := (r3 π z).1.reverse.flatMap π.SB, vb := (r3 π z).1.reverse.flatMap π.TB,
        mm := List.replicate (r3 π z).1.length true, ws := (r2 π z).1}.f)
      (z.length * (2 * π.kA + π.BA + 2 * π.kB + π.BB + 20) + 20) := by
  have l1 := sl_length π.kA π.dA z
  have l2 := seg_length (r1 π z).2
  have l3 := sl_length π.kB π.dB (r2 π z).2
  have p1 := exec_slLoop (src := 0) (a := 1) (b := 2) (c := 3) π.SA π.TA π.kA π.dA π.BA
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hπ.hA _
    {Mem.e with z := z}.f le_rfl
  have p2 := exec_seg (src := 0) (dst := 4) (by decide) (r1 π z).2
    {Mem.e with
      z := (r1 π z).2,
      pw := (r1 π z).1.reverse.flatMap π.SA, vw := (r1 π z).1.reverse.flatMap π.TA,
      nn := List.replicate (r1 π z).1.length true}.f rfl
  have p3 := exec_slLoop (src := 0) (a := 5) (b := 6) (c := 7) π.SB π.TB π.kB π.dB π.BB
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hπ.hB _
    {Mem.e with
      z := (r2 π z).2,
      pw := (r1 π z).1.reverse.flatMap π.SA, vw := (r1 π z).1.reverse.flatMap π.TA,
      nn := List.replicate (r1 π z).1.length true, wr := (r2 π z).1.reverse}.f le_rfl
  have p4 := exec_move (a := 4) (b := 8) (by decide) _ {Mem.e with
      z := (r3 π z).2,
      pw := (r1 π z).1.reverse.flatMap π.SA, vw := (r1 π z).1.reverse.flatMap π.TA,
      nn := List.replicate (r1 π z).1.length true, wr := (r2 π z).1.reverse,
      pb := (r3 π z).1.reverse.flatMap π.SB, vb := (r3 π z).1.reverse.flatMap π.TB,
      mm := List.replicate (r3 π z).1.length true}.f rfl
  refine (ExecLe.seq_norm (p1.cast (by simp [Mem.e, r1]) le_rfl) (ExecLe.seq_norm
    (p2.cast (by simp [Mem.e, r2]) le_rfl) (ExecLe.seq_norm (p3.cast (by simp [Mem.e, r3]) le_rfl)
    (ExecLe.of_eq p4 (by simp [Mem.e]) le_rfl)))).cast rfl ?_
  simp only [Mem.f_0, Mem.f_4, List.length_reverse, r2, r3, r1] at *
  have hz1 : (sl π.kA π.dA z).2.length ≤ z.length := by omega
  have hz2 : (seg (sl π.kA π.dA z).2).2.length ≤ z.length := by omega
  have hz3 : (seg (sl π.kA π.dA z).2).1.length ≤ z.length := by omega
  have : (seg (sl π.kA π.dA z).2).2.length * (2 * π.kB + π.BB + 6) ≤
      z.length * (2 * π.kB + π.BB + 6) := Nat.mul_le_mul_right _ hz2
  nlinarith

/-! ## Arithmetic -/

/-- The comparison loop. -/
theorem exec_cmpLoop : ∀ (a b : ℕ) (m : Mem), m.c1 = List.replicate a true →
    m.ac = List.replicate b true →
    (a ≤ b → ExecLe (.loop (.pop 22 .brk (.pop 18 (.halt true) .skip .skip)
      (.pop 18 (.halt true) .skip .skip))) m.f
      (.norm {m with c1 := [], ac := List.replicate (b - a) true}.f) (3 * a + 2)) ∧
    (b < a → ExecLe (.loop (.pop 22 .brk (.pop 18 (.halt true) .skip .skip)
      (.pop 18 (.halt true) .skip .skip))) m.f (.halt true) (3 * a + 2))
  | 0, b, m, hc, ha => by
    refine ⟨fun _ => (ExecLe.loop_brk (ExecLe.pop_nil (by simpa using hc) (ExecLe.brk _))).cast ?_
      (by omega), fun h => absurd h (by omega)⟩
    congr 1; cases m; simp_all
  | a + 1, b, m, hc, ha => by
    rw [List.replicate_succ] at hc
    rcases b with _ | b
    · refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      have h0 : ExecLe (.pop 18 (.halt true) .skip .skip)
          {m with c1 := List.replicate a true}.f (.halt true) 2 :=
        ExecLe.pop_nil (σ := {m with c1 := List.replicate a true}.f) (by simpa using ha)
          (ExecLe.halt true _)
      have h1 : ExecLe (.pop 22 .brk (.pop 18 (.halt true) .skip .skip)
          (.pop 18 (.halt true) .skip .skip)) m.f (.halt true) 3 :=
        ExecLe.pop_same (k := 22) (b := true) (s := List.replicate a true)
          (by simpa using hc) (by rw [Mem.upd_22]; exact h0)
      exact (ExecLe.loop_halt h1).cast rfl (by omega)
    · rw [List.replicate_succ] at ha
      have ih := exec_cmpLoop a b {m with c1 := List.replicate a true, ac := List.replicate b true}
        rfl rfl
      have h0 : ExecLe (.pop 18 (.halt true) .skip .skip)
          {m with c1 := List.replicate a true}.f
          (.norm {m with c1 := List.replicate a true, ac := List.replicate b true}.f) 2 := by
        refine ExecLe.pop_same (σ := {m with c1 := List.replicate a true}.f) (k := 18) (b := true)
          (s := List.replicate b true) (by simpa using ha) ?_
        rw [Mem.upd_18]
        exact (ExecLe.skip _).cast rfl (by omega)
      have hbody : ExecLe (.pop 22 .brk (.pop 18 (.halt true) .skip .skip)
          (.pop 18 (.halt true) .skip .skip)) m.f
          (.norm {m with c1 := List.replicate a true, ac := List.replicate b true}.f) 3 :=
        ExecLe.pop_same (k := 22) (b := true) (s := List.replicate a true)
          (by simpa using hc) (by rw [Mem.upd_22]; exact h0)
      refine ⟨fun h => (ExecLe.loop_norm hbody (ih.1 (by omega))).cast ?_ (by omega),
        fun h => (ExecLe.loop_norm hbody (ih.2 (by omega))).cast rfl (by omega)⟩
      rw [show b + 1 - (a + 1) = b - a by omega]

theorem exec_cmp (m : Mem) (a b : ℕ) (hm : m.mm = List.replicate a true)
    (ha : m.ac = List.replicate b true) (hc : m.c1 = []) (htm : m.tm = []) :
    (a ≤ b → ExecLe cmpCmd m.f (.norm {m with ac := List.replicate (b - a) true}.f) (8 * a + 6)) ∧
    (b < a → ExecLe cmpCmd m.f (.halt true) (8 * a + 6)) := by
  have h1 : ExecLe (copyVia 7 22 21) m.f (.norm {m with c1 := List.replicate a true}.f)
      (5 * a + 4) :=
    ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
      (by simp [hm, hc]) (by simp [hm])
  have h2 := exec_cmpLoop a b {m with c1 := List.replicate a true} rfl (by simpa using ha)
  refine ⟨fun h => (h1.seq_norm (h2.1 h)).cast ?_ (by omega),
    fun h => (h1.seq_norm (h2.2 h)).cast rfl (by omega)⟩
  congr 1; cases m; simp_all

/-- Cost of the arithmetic phase. -/
def Tar (π : Par) (n m : ℕ) : ℕ :=
  5 * n + 4 + polyT π.p n + (8 * m + 6) + (2 * (π.p.eval n - m) + 2) + 1 + (5 * m + 4) +
    polyT π.Q (m + 1 + n) + (2 * π.Q.eval (m + 1 + n) + 2)

theorem exec_arith (π : Par) (m0 : Mem) (n m : ℕ) (hn : m0.nn = List.replicate n true)
    (hm : m0.mm = List.replicate m true) (hxs : m0.xs = []) (hac : m0.ac = []) (hnx : m0.nx = [])
    (hta : m0.ta = []) (htm : m0.tm = []) (hc1 : m0.c1 = []) (hcnt : m0.cnt = []) :
    (π.p.eval n < m → ExecLe (arithCmd π) m0.f (.halt true) (Tar π n m)) ∧
    (m ≤ π.p.eval n → ExecLe (arithCmd π) m0.f (.norm {m0 with
      xs := List.replicate (m + 1 + n) true,
      cnt := List.replicate (π.Q.eval (m + 1 + n)) true}.f) (Tar π n m)) := by
  have h1 : ExecLe (copyVia 3 17 21) m0.f (.norm {m0 with xs := List.replicate n true}.f)
      (5 * n + 4) :=
    ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
      (by simp [hn, hxs]) (by simp [hn])
  set m1 := {m0 with xs := List.replicate n true}
  have h2 := exec_polyCmd (xs := 17) (acc := 18) (nxt := 19) (ta := 20) (tm := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) π.p n m1.f (by simp [m1]) (by simp [m1, hac])
    (by simp [m1, hnx]) (by simp [m1, hta]) (by simp [m1, htm])
  set m2 := {m1 with ac := List.replicate (π.p.eval n) true}
  have h2' : ExecLe (polyCmd 17 18 19 20 21 π.p) m1.f (.norm m2.f) (polyT π.p n) :=
    ExecLe.of_eq h2 (by simp [m2]) le_rfl
  have h3 := exec_cmp m2 m (π.p.eval n) (by simp [m2, m1, hm]) rfl (by simp [m2, m1, hc1])
    (by simp [m2, m1, htm])
  refine ⟨fun h => (h1.seq_norm (h2'.seq_norm ((h3.2 h).seq_halt))).cast rfl ?_, fun h => ?_⟩
  · unfold Tar; omega
  set m3 := {m2 with ac := List.replicate (π.p.eval n - m) true}
  have h4 := exec_drain 18 _ m3.f rfl
  set m4 := {m3 with ac := []}
  have h4' : ExecLe (drain 18) m3.f (.norm m4.f) (2 * (π.p.eval n - m) + 2) :=
    ExecLe.of_eq h4 (by simp [m4]) (by simp [m3])
  have h5 := ExecLe.push 17 true m4.f
  set m5 := {m4 with xs := true :: List.replicate n true}
  have h5' : ExecLe (.push 17 true) m4.f (.norm m5.f) 1 := h5.cast (by simp [m5, m4, m3, m2, m1]) le_rfl
  have h6 : ExecLe (copyVia 7 17 21) m5.f
      (.norm {m5 with xs := List.replicate (m + 1 + n) true}.f) (5 * m + 4) :=
    ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _
      (by simpa [m5, m4, m3, m2, m1] using htm))
      (by
        congr 1
        simp only [Mem.f_7, Mem.f_17, Mem.upd_17]
        have e : List.replicate m true ++ true :: List.replicate n true =
            List.replicate (m + 1 + n) true := by
          rw [show m + 1 + n = m + (n + 1) by omega, List.replicate_add, List.replicate_succ]
        simp [m5, m4, m3, m2, m1, hm, e]) (by simp [m5, m4, m3, m2, m1, hm])
  set m6 := {m5 with xs := List.replicate (m + 1 + n) true}
  have h7 := exec_polyCmd (xs := 17) (acc := 18) (nxt := 19) (ta := 20) (tm := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) π.Q (m + 1 + n) m6.f (by simp [m6]) (by simp [m6, m5, m4])
    (by simp [m6, m5, m4, m3, m2, m1, hnx]) (by simp [m6, m5, m4, m3, m2, m1, hta])
    (by simp [m6, m5, m4, m3, m2, m1, htm])
  set m7 := {m6 with ac := List.replicate (π.Q.eval (m + 1 + n)) true}
  have h7' : ExecLe (polyCmd 17 18 19 20 21 π.Q) m6.f (.norm m7.f) (polyT π.Q (m + 1 + n)) :=
    ExecLe.of_eq h7 (by simp [m7]) le_rfl
  have h8 := exec_move (a := 18) (b := 24) (by decide) _ m7.f rfl
  have h8' : ExecLe (move 18 24) m7.f (.norm {m0 with
      xs := List.replicate (m + 1 + n) true,
      cnt := List.replicate (π.Q.eval (m + 1 + n)) true}.f) (2 * π.Q.eval (m + 1 + n) + 2) :=
    ExecLe.of_eq h8 (by
      congr 1; simp only [Mem.f_18, Mem.f_24, Mem.upd_18, Mem.upd_24]
      simp [m7, m6, m5, m4, m3, m2, m1, hcnt, hac]) (by simp [m7])
  refine (h1.seq_norm (h2'.seq_norm ((h3.1 h).seq_norm (h4'.seq_norm (h5'.seq_norm
    (h6.seq_norm (h7'.seq_norm h8'))))))).cast rfl ?_
  unfold Tar; omega

/-! ## Building, selecting, evaluating -/

theorem exec_build (π : Par) (m0 : Mem) (hpp : m0.pp = []) (hv : m0.v = []) :
    ExecLe (buildCmd π) m0.f (.norm {m0 with
      pw := [], pb := [], vw := [], vb := [],
      pp := m0.pw.reverse ++ π.sWB ++ m0.pb.reverse ++ π.sC,
      v := m0.vw.reverse ++ π.bS ++ m0.vb.reverse}.f)
      (π.sC.length + π.sWB.length + π.bS.length +
        2 * (m0.pb.length + m0.pw.length + m0.vb.length + m0.vw.length) + 11) := by
  have h1 := exec_pushList 16 π.sC m0.f
  set m1 := {m0 with pp := π.sC}
  have h1' : ExecLe (pushList 16 π.sC) m0.f (.norm m1.f) (π.sC.length + 1) :=
    ExecLe.of_eq h1 (by simp [m1, hpp]) le_rfl
  have h2 := exec_move (a := 5) (b := 16) (by decide) _ m1.f rfl
  set m2 := {m1 with pb := [], pp := m0.pb.reverse ++ π.sC}
  have h2' : ExecLe (move 5 16) m1.f (.norm m2.f) (2 * m0.pb.length + 2) :=
    ExecLe.of_eq h2 (by simp [m2, m1]) (by simp [m1])
  have h3 := exec_pushList 16 π.sWB m2.f
  set m3 := {m2 with pp := π.sWB ++ m0.pb.reverse ++ π.sC}
  have h3' : ExecLe (pushList 16 π.sWB) m2.f (.norm m3.f) (π.sWB.length + 1) :=
    ExecLe.of_eq h3 (by simp [m3, m2]) le_rfl
  have h4 := exec_move (a := 1) (b := 16) (by decide) _ m3.f rfl
  set m4 := {m3 with pw := [], pp := m0.pw.reverse ++ π.sWB ++ m0.pb.reverse ++ π.sC}
  have h4' : ExecLe (move 1 16) m3.f (.norm m4.f) (2 * m0.pw.length + 2) :=
    ExecLe.of_eq h4 (by simp [m4, m3, m2, m1]) (by simp [m3, m2, m1])
  have h5 := exec_move (a := 6) (b := 12) (by decide) _ m4.f rfl
  set m5 := {m4 with vb := [], v := m0.vb.reverse}
  have h5' : ExecLe (move 6 12) m4.f (.norm m5.f) (2 * m0.vb.length + 2) :=
    ExecLe.of_eq h5 (by simp [m5, m4, m3, m2, m1, hv]) (by simp [m4, m3, m2, m1])
  have h6 := exec_pushList 12 π.bS m5.f
  set m6 := {m5 with v := π.bS ++ m0.vb.reverse}
  have h6' : ExecLe (pushList 12 π.bS) m5.f (.norm m6.f) (π.bS.length + 1) :=
    ExecLe.of_eq h6 (by simp [m6, m5]) le_rfl
  have h7 := exec_move (a := 2) (b := 12) (by decide) _ m6.f rfl
  have h7' : ExecLe (move 2 12) m6.f (.norm {m0 with
      pw := [], pb := [], vw := [], vb := [],
      pp := m0.pw.reverse ++ π.sWB ++ m0.pb.reverse ++ π.sC,
      v := m0.vw.reverse ++ π.bS ++ m0.vb.reverse}.f) (2 * m0.vw.length + 2) :=
    ExecLe.of_eq h7 (by simp [m6, m5, m4, m3, m2, m1]) (by simp [m6, m5, m4, m3, m2, m1])
  refine (h1'.seq_norm (h2'.seq_norm (h3'.seq_norm (h4'.seq_norm (h5'.seq_norm
    (h6'.seq_norm h7')))))).cast rfl ?_
  omega

theorem exec_sel (m0 : Mem) (m : ℕ) (W : Str) (hm : m0.mm = List.replicate m true)
    (hws : m0.ws = W) (hc1 : m0.c1 = []) (htm : m0.tm = []) (hjk : m0.jk = []) (hgr : m0.gr = [])
    (hg : m0.g = []) :
    ExecLe selCmd m0.f (.norm {m0 with
      ws := (seg (segIt W m)).2, jk := segJ W m, g := (seg (segIt W m)).1}.f)
      (5 * m + 4 + (m * (2 * W.length + 4) + 2) + (4 * W.length + 5)) := by
  have h1 : ExecLe (copyVia 7 22 21) m0.f (.norm {m0 with c1 := List.replicate m true}.f)
      (5 * m + 4) :=
    ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simpa using htm))
      (by simp [hm, hc1]) (by simp [hm])
  set m1 := {m0 with c1 := List.replicate m true}
  have h2 := exec_selLoop (cnt := 22) (ws := 8) (jk := 9) (by decide) (by decide) (by decide) W m 0
    m1.f (by simp [m1]) (by simp [m1, hws, segIt]) (by simp [m1, hjk, segJ])
  rw [Nat.zero_add] at h2
  set m2 := {m1 with c1 := [], ws := segIt W m, jk := segJ W m}
  have h2' : ExecLe (selLoop 22 8 9) m1.f (.norm m2.f) (m * (2 * W.length + 4) + 2) :=
    h2.cast (by simp [m2]) le_rfl
  have h3 := exec_seg (src := 8) (dst := 10) (by decide) _ m2.f rfl
  set m3 := {m2 with ws := (seg (segIt W m)).2, gr := (seg (segIt W m)).1.reverse}
  have h3' : ExecLe (segCmd 8 10) m2.f (.norm m3.f) (2 * W.length + 3) :=
    h3.cast (by simp [m3, m2, m1, hgr]) (by
      have := segIt_length W m; simp [m2]; omega)
  have h4 := exec_move (a := 10) (b := 11) (by decide) _ m3.f rfl
  have h4' : ExecLe (move 10 11) m3.f (.norm {m0 with
      ws := (seg (segIt W m)).2, jk := segJ W m, g := (seg (segIt W m)).1}.f)
      (2 * W.length + 2) :=
    ExecLe.of_eq h4 (by simp [m3, m2, m1, hg, hgr, hc1]) (by
      have := segIt_length W m; have := seg_length (segIt W m); simp [m3]; omega)
  refine (h1.seq_norm (h2'.seq_norm (h3'.seq_norm h4'))).cast rfl ?_
  omega

theorem mem_upd_ev (m0 : Mem) (R : Str) :
    update (update m0.f 11 []) 12 R = {m0 with g := [], v := R}.f := by simp

theorem exec_ev (m0 : Mem) (G V : Str) (hg : m0.g = G) (hv : m0.v = V) (hs : m0.s = [])
    (hfu : m0.fu = []) (hfw : m0.fw = []) (hxx : m0.xx = []) :
    ExecLe evCmd m0.f (.norm {m0 with
      g := [], v := [], xx := (evalD G V [] false false).reverse}.f)
      ((G.length + 1) * (2 * (V.length + G.length) + 40) + 2 * (V.length + G.length) + 20 +
        (2 * (V.length + G.length) + 2)) := by
  obtain ⟨σ', h1, e1, e2, e3, e4, e5, hF⟩ := exec_evalCmd (g := 11) (v := 12) (s := 13) (u := 14)
    (w := 15) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) m0.f G V (by simpa using hg)
    (by simpa using hv) (by simpa using hs) (by simpa using hfu) (by simpa using hfw)
  set R := evalD G V [] false false
  have hσ : σ' = {m0 with g := [], v := R}.f := by
    rw [← mem_upd_ev]
    funext j
    simp only [update_apply]
    split_ifs with h12 h11
    · subst h12; exact e1
    · subst h11; exact e2
    · by_cases h13 : j = 13
      · subst h13; rw [e3]; simpa using hs.symm
      · by_cases h14 : j = 14
        · subst h14; rw [e4]; simpa using hfu.symm
        · by_cases h15 : j = 15
          · subst h15; rw [e5]; simpa using hfw.symm
          · exact hF j h11 h12 h13 h14 h15
  rw [hσ] at h1
  have h2 := exec_move (a := 12) (b := 23) (by decide) _ {m0 with g := [], v := R}.f rfl
  have hR : R.length ≤ V.length + G.length := by
    have := length_evalD_le G V [] false false; simp at this; omega
  have h2' : ExecLe (move 12 23) {m0 with g := [], v := R}.f (.norm {m0 with
      g := [], v := [], xx := R.reverse}.f) (2 * (V.length + G.length) + 2) :=
    ExecLe.of_eq h2 (by simp [hxx]) (by simp; omega)
  exact (h1.seq_norm h2').cast rfl (by omega)

/-! ## The main loop -/

theorem flatMap_length_le {f : ℕ → Str} {B : ℕ} (hf : ∀ j, (f j).length ≤ B) :
    ∀ l : List ℕ, (l.flatMap f).length ≤ l.length * B
  | [] => by simp
  | j :: l => by
    have := flatMap_length_le hf l; have := hf j
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; rw [Nat.succ_mul]; omega

/-- The decoded table indices of the first `t` blocks. -/
def ic (kC dC : ℕ) (X : Str) (t : ℕ) : List ℕ :=
  (List.range t).map fun s => (fi kC (X.drop (s * kC))).getD dC

theorem ic_succ (kC dC : ℕ) (X : Str) (t : ℕ) :
    ic kC dC X (t + 1) = ic kC dC X t ++ [(fi kC (X.drop (t * kC))).getD dC] := by
  simp [ic, List.range_succ]

theorem length_ic (kC dC : ℕ) (X : Str) (t : ℕ) : (ic kC dC X t).length = t := by simp [ic]

/-- The state of the main loop in round `t`. -/
def mSt (π : Par) (m0 : Mem) (N : ℕ) (X : Str) (t : ℕ) : Mem := {m0 with
  xx := X.drop (t * π.kC), cnt := List.replicate (N - t) true,
  ra := (ic π.kC π.dC X t).reverse.flatMap π.SC, yes := List.replicate t true}

/-- Cost bound of one round. -/
def Cit (π : Par) (N P T : ℕ) : ℕ :=
  7 * (N * π.BC) + 5 * P + 2 * (P + N * π.BC) + 3 * T + 2 * (Official.nW π.q + 2) +
    2 * π.kC + π.BC + 30

theorem elim_zero_add (o : Option ℕ) (d : ℕ) : o.elim d (0 + ·) = o.getD d := by
  cases o <;> simp

open scoped Classical in
theorem exec_mLoop (π : Par) (hπ : π.Ok) (m0 : Mem) (X PP : Str) (N T : ℕ) (A : ℕ → Bool)
    (hpp : m0.pp = PP) (hno : m0.no = []) (ht1 : m0.t1 = []) (htm : m0.tm = [])
    (hx0 : m0.x0 = []) (hx1 : m0.x1 = [])
    (hq : ∀ t ≤ N, runFor ∅ π.q T
      (.run ⟨0, (init [PP ++ ((ic π.kC π.dC X t).reverse.flatMap π.SC).reverse, []]).stk⟩) =
        .done (A t)) :
    ∀ k t, N - t = k → t ≤ N → ExecLe (mLoop π) (mSt π m0 N X t).f
      (.halt (decide (∃ t', t ≤ t' ∧ t' ≤ N ∧ A t' = false))) ((N + 1 - t) * Cit π N PP.length T) := by
  have hra : ∀ t ≤ N, ((ic π.kC π.dC X t).reverse.flatMap π.SC).length ≤ N * π.BC := by
    intro t ht
    have := flatMap_length_le (f := π.SC) (B := π.BC) (fun j => by have := hπ.hC j; simpa using this)
      (ic π.kC π.dC X t).reverse
    rw [List.length_reverse, length_ic] at this
    exact this.trans (Nat.mul_le_mul_right _ ht)
  intro k
  induction k with
  | zero => ?_
  | succ k ih => ?_
  all_goals intro t hk ht
  all_goals
    set ms := mSt π m0 N X t with hms
    set RA := (ic π.kC π.dC X t).reverse.flatMap π.SC with hRA
    have hRAl := hra t ht
    -- build the call input
    have b1 : ExecLe (copyVia 25 26 21) ms.f (.norm {ms with t1 := RA}.f) (5 * RA.length + 4) :=
      ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simp [ms, mSt, htm]))
        (by simp [ms, mSt, ht1, RA]) (by simp [ms, mSt, RA])
    have b2 : ExecLe (move 26 29) {ms with t1 := RA}.f (.norm {ms with x0 := RA.reverse}.f)
        (2 * RA.length + 2) :=
      ExecLe.of_eq (exec_move (by decide) _ _ rfl) (by simp [ms, mSt, hx0, ht1]) (by simp)
    have b3 : ExecLe (copyVia 16 29 21) {ms with x0 := RA.reverse}.f
        (.norm {ms with x0 := PP ++ RA.reverse}.f) (5 * PP.length + 4) :=
      ExecLe.of_eq (exec_copyVia (by decide) (by decide) (by decide) _ (by simp [ms, mSt, htm]))
        (by simp [ms, mSt, hpp]) (by simp [ms, mSt, hpp])
    set mc := {ms with x0 := PP ++ RA.reverse}
    have hrun : runFor ∅ π.q T (.run ⟨0, view mc.f 29⟩) = .done (A t) := by
      rw [Mem.view]; simp only [mc, ms, mSt, hx1]; exact hq t ht
    have b4 := exec_callDrain (yes := 27) (no := 28) (by decide) (by decide)
      (fun j hj => Mem.f_ge mc (by omega)) hrun
    simp only [show (29 : ℕ) + 1 = 30 from rfl, Mem.f_29, Mem.f_30] at b4
    have hx0l : mc.x0.length = PP.length + RA.length := by simp [mc]
    have hx1l : mc.x1 = [] := by simp [mc, ms, mSt, hx1]
    have hRAl' : RA.length ≤ N * π.BC := hRAl
    simp only [hx0l, hx1l, List.length_nil] at b4
  · -- last round
    have htN : t = N := by omega
    cases hA : A t
    · -- accept
      have e : (fun j => if j < 29 then update mc.f (if false = true then 27 else 28)
          (true :: mc.f (if false = true then 27 else 28)) j else []) =
          {mc with no := [true], x0 := [], x1 := []}.f := by
        have h' : update mc.f 28 (true :: mc.f 28) = {mc with no := [true]}.f := by
          simp [mc, ms, mSt, hno]
        simp only [Bool.false_eq_true, if_false]
        rw [h']; exact Mem.cut _
      rw [hA, e] at b4
      have b5 : ExecLe (.seq (.pop 28 .skip .skip (.halt true))
          (.pop 24 (.halt false) (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)
            (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)))
          {mc with no := [true], x0 := [], x1 := []}.f (.halt true) 2 :=
        (ExecLe.pop_cons (b := true) (s := []) (by simp) (ExecLe.halt true _)).seq_halt
      have := b1.seq_norm (b2.seq_norm (b3.seq_norm (b4.seq_norm b5)))
      refine (ExecLe.loop_halt this).cast (by rw [decide_eq_true ⟨t, le_rfl, ht, hA⟩]) ?_
      simp only [Cit, show N + 1 - t = 1 by omega, one_mul]
      omega
    · -- reject
      have e : (fun j => if j < 29 then update mc.f (if true = true then 27 else 28)
          (true :: mc.f (if true = true then 27 else 28)) j else []) =
          {mc with yes := true :: mc.yes, x0 := [], x1 := []}.f := by
        have h' : update mc.f 27 (true :: mc.f 27) = {mc with yes := true :: mc.yes}.f := by
          simp only [Mem.f_27, Mem.upd_27]
        simp only [if_true]
        rw [h']; exact Mem.cut _
      rw [hA, e] at b4
      have b5 : ExecLe (.seq (.pop 28 .skip .skip (.halt true))
          (.pop 24 (.halt false) (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)
            (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)))
          {mc with yes := true :: mc.yes, x0 := [], x1 := []}.f (.halt false) 4 :=
        (ExecLe.pop_nil (by simp [mc, ms, mSt, hno]) (ExecLe.skip _)).seq_norm
          (ExecLe.pop_nil (by simp [mc, ms, mSt, htN]) (ExecLe.halt false _))
      have := b1.seq_norm (b2.seq_norm (b3.seq_norm (b4.seq_norm b5)))
      refine (ExecLe.loop_halt this).cast ?_ ?_
      · congr 1; symm; rw [decide_eq_false_iff_not]
        rintro ⟨t', h1, h2, h3⟩
        rw [show t' = t by omega, hA] at h3; exact absurd h3 (by decide)
      · simp only [Cit, show N + 1 - t = 1 by omega, one_mul]
        omega
  · cases hA : A t
    · -- accept
      have e : (fun j => if j < 29 then update mc.f (if false = true then 27 else 28)
          (true :: mc.f (if false = true then 27 else 28)) j else []) =
          {mc with no := [true], x0 := [], x1 := []}.f := by
        have h' : update mc.f 28 (true :: mc.f 28) = {mc with no := [true]}.f := by
          simp [mc, ms, mSt, hno]
        simp only [Bool.false_eq_true, if_false]
        rw [h']; exact Mem.cut _
      rw [hA, e] at b4
      have b5 : ExecLe (.seq (.pop 28 .skip .skip (.halt true))
          (.pop 24 (.halt false) (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)
            (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)))
          {mc with no := [true], x0 := [], x1 := []}.f (.halt true) 2 :=
        (ExecLe.pop_cons (b := true) (s := []) (by simp) (ExecLe.halt true _)).seq_halt
      have := b1.seq_norm (b2.seq_norm (b3.seq_norm (b4.seq_norm b5)))
      refine (ExecLe.loop_halt this).cast (by rw [decide_eq_true ⟨t, le_rfl, ht, hA⟩]) ?_
      have : 1 ≤ N + 1 - t := by omega
      have hC : 7 * (N * π.BC) + 5 * PP.length + 2 * (PP.length + N * π.BC) + 3 * T + 2 *
          (Official.nW π.q + 2) + 2 * π.kC + π.BC + 30 ≤ (N + 1 - t) * Cit π N PP.length T := by
        unfold Cit; nlinarith
      omega
    · -- continue
      have e : (fun j => if j < 29 then update mc.f (if true = true then 27 else 28)
          (true :: mc.f (if true = true then 27 else 28)) j else []) =
          {mc with yes := true :: mc.yes, x0 := [], x1 := []}.f := by
        have h' : update mc.f 27 (true :: mc.f 27) = {mc with yes := true :: mc.yes}.f := by
          simp only [Mem.f_27, Mem.upd_27]
        simp only [if_true]
        rw [h']; exact Mem.cut _
      rw [hA, e] at b4
      set m5 := {mc with yes := true :: mc.yes, x0 := [], x1 := []}
      have ht5 := exec_tabK (src := 23) (a := 25) (b := 26) π.SC (fun _ => []) π.dC π.BC
        (by decide) (by decide) (by decide) hπ.hC π.kC 0
        {m5 with cnt := List.replicate (N - (t + 1)) true}.f
      have b5 : ExecLe (.seq (.pop 28 .skip .skip (.halt true))
          (.pop 24 (.halt false) (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)
            (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)))
          m5.f (.norm (mSt π m0 N X (t + 1)).f) (2 * π.kC + π.BC + 3 + 3) := by
        have c1 : ExecLe (.pop 28 .skip .skip (.halt true)) m5.f (.norm m5.f) 2 :=
          ExecLe.pop_nil (σ := m5.f) (k := 28) (by simp [m5, mc, ms, mSt, hno]) (ExecLe.skip _)
        have c2 : ExecLe (.pop 24 (.halt false) (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)
            (tabK 23 25 26 π.SC (fun _ => []) π.dC 0 π.kC)) m5.f (.norm (mSt π m0 N X (t + 1)).f)
            (2 * π.kC + π.BC + 3 + 1) := by
          refine ExecLe.pop_same (k := 24) (b := true)
            (s := List.replicate (N - (t + 1)) true) ?_ ?_
          · simp only [m5, mc, ms, mSt, Mem.f_24]
            rw [← List.replicate_succ]; congr 1; omega
          · rw [Mem.upd_24]
            refine ht5.cast ?_ le_rfl
            congr 1
            simp only [st2, Mem.f_23, elim_zero_add]
            simp [m5, mc, ms, mSt, List.drop_drop, ic_succ, Nat.succ_mul, List.replicate_succ,
              Nat.add_comm, hx0, hx1]
        exact (c1.seq_norm c2).cast rfl (by omega)
      have hbody := b1.seq_norm (b2.seq_norm (b3.seq_norm (b4.seq_norm b5)))
      have ih' := ih (t + 1) (by omega) (by omega)
      refine (ExecLe.loop_norm hbody ih').cast ?_ ?_
      · congr 1; congr 1; apply propext
        constructor
        · rintro ⟨t', h1, h2, h3⟩; exact ⟨t', by omega, h2, h3⟩
        · rintro ⟨t', h1, h2, h3⟩
          rcases Nat.eq_or_lt_of_le h1 with h | h
          · subst h; rw [hA] at h3; exact absurd h3 (by decide)
          · exact ⟨t', by omega, h2, h3⟩
      · rw [show N + 1 - t = (N + 1 - (t + 1)) + 1 by omega, Nat.add_mul, one_mul]
        simp only [Cit]
        omega

/-! ## The whole program -/

section Whole

variable (π : Par)

/-- The code of a call input: prefix codes of `iw`, `ib`, the separators and the codes of `ic`. -/
def xc (iw ib ic : List ℕ) : Str :=
  (iw.reverse.flatMap π.SA).reverse ++ π.sWB ++ (ib.reverse.flatMap π.SB).reverse ++ π.sC ++
    (ic.reverse.flatMap π.SC).reverse

/-- The prefix code. -/
def ppS (z : Str) : Str :=
  (((r1 π z).1.reverse.flatMap π.SA).reverse ++ π.sWB ++ ((r3 π z).1.reverse.flatMap π.SB).reverse ++
    π.sC)

/-- The wire values. -/
def vS (z : Str) : Str :=
  ((r1 π z).1.reverse.flatMap π.TA).reverse ++ π.bS ++ ((r3 π z).1.reverse.flatMap π.TB).reverse

/-- The selected circuit code. -/
def gS (z : Str) : Str := (seg (segIt (r2 π z).1 (r3 π z).1.length)).1

/-- The reversed circuit output. -/
def xS (z : Str) : Str := (evalD (gS π z) (vS π z) [] false false).reverse

/-- The loop count. -/
def nS (z : Str) : ℕ := π.Q.eval ((r3 π z).1.length + 1 + (r1 π z).1.length)

/-- **The computed predicate.** -/
def Dsem (ans : List ℕ → List ℕ → List ℕ → Bool) (z : Str) : Prop :=
  π.p.eval (r1 π z).1.length < (r3 π z).1.length ∨
    ∃ t ≤ nS π z, ans (r1 π z).1 (r3 π z).1 (ic π.kC π.dC (xS π z) t) = false

/-- The cost of the whole program. -/
def Tprog (K : ℕ) (z : Str) : ℕ :=
  (z.length * (2 * π.kA + π.BA + 2 * π.kB + π.BB + 20) + 20) +
    Tar π (r1 π z).1.length (r3 π z).1.length +
    (π.sC.length + π.sWB.length + π.bS.length +
      2 * (z.length * π.BB + z.length * π.BA + z.length * π.BB + z.length * π.BA) + 11) +
    (5 * z.length + 4 + (z.length * (2 * z.length + 4) + 2) + (4 * z.length + 5)) +
    ((z.length + 1) * (2 * ((vS π z).length + z.length) + 40) + 2 * ((vS π z).length + z.length) + 20 +
      (2 * ((vS π z).length + z.length) + 2)) +
    (nS π z + 1) * Cit π (nS π z) (ppS π z).length
      (tb K ((ppS π z).length + nS π z * π.BC))

end Whole

theorem init_two (x : Str) : init [x, []] = init [x] := by
  unfold init; congr 1; funext k; rcases k with _ | _ | k <;> rfl

open scoped Classical in
/-- **The whole program**: on every input it halts with the answer `Dsem`. -/
theorem exec_prog (π : Par) (hπ : π.Ok) (K : ℕ) (ans : List ℕ → List ℕ → List ℕ → Bool)
    (hq : ∀ iw ib ic : List ℕ, runFor ∅ π.q (tb K (xc π iw ib ic).length)
      (.run (init [xc π iw ib ic])) = .done (ans iw ib ic)) (z : Str) :
    ExecLe (prog π) (init [z]).stk (.halt (decide (Dsem π ans z))) (Tprog π K z) := by
  set iw := (r1 π z).1
  set W := (r2 π z).1
  set ib := (r3 π z).1
  set n := iw.length
  set m := ib.length
  have l1 := sl_length π.kA π.dA z
  have l2 := seg_length (r1 π z).2
  have l3 := sl_length π.kB π.dB (r2 π z).2
  have hn : n ≤ z.length := by simp only [n, iw, r1] at *; omega
  have hW : W.length ≤ z.length := by simp only [W, r2, r1] at *; omega
  have hm : m ≤ z.length := by simp only [m, ib, r3, r2, r1] at *; omega
  have hp := exec_parse π hπ z
  set mP : Mem := {Mem.e with
    z := (r3 π z).2,
    pw := iw.reverse.flatMap π.SA, vw := iw.reverse.flatMap π.TA,
    nn := List.replicate n true,
    pb := ib.reverse.flatMap π.SB, vb := ib.reverse.flatMap π.TB,
    mm := List.replicate m true, ws := W} with hmP
  have ha := exec_arith π mP n m rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [init_eq]
  by_cases hpm : π.p.eval n < m
  · refine (hp.seq_norm (ha.1 hpm).seq_halt).cast ?_ ?_
    · congr 1; exact (decide_eq_true (show Dsem π ans z from Or.inl hpm)).symm
    · unfold Tprog
      have e1 : (r1 π z).1.length = n := rfl
      have e3 : (r3 π z).1.length = m := rfl
      rw [e1, e3]
      omega
  have ha' := ha.2 (by omega)
  set N := π.Q.eval (m + 1 + n)
  set mA := {mP with xs := List.replicate (m + 1 + n) true, cnt := List.replicate N true}
  have hb := exec_build π mA rfl rfl
  set mB := {mA with
      pw := [], pb := [], vw := [], vb := [],
      pp := mA.pw.reverse ++ π.sWB ++ mA.pb.reverse ++ π.sC,
      v := mA.vw.reverse ++ π.bS ++ mA.vb.reverse}
  have hs := exec_sel mB m W rfl rfl rfl rfl rfl rfl rfl
  set mS := {mB with ws := (seg (segIt W m)).2, jk := segJ W m, g := (seg (segIt W m)).1}
  have he := exec_ev mS (seg (segIt W m)).1 (mA.vw.reverse ++ π.bS ++ mA.vb.reverse) rfl rfl rfl
    rfl rfl rfl
  set mE := {mS with
    g := [], v := [],
    xx := (evalD (seg (segIt W m)).1 (mA.vw.reverse ++ π.bS ++ mA.vb.reverse) [] false false).reverse}
  set PP := mA.pw.reverse ++ π.sWB ++ mA.pb.reverse ++ π.sC
  set X := (evalD (seg (segIt W m)).1 (mA.vw.reverse ++ π.bS ++ mA.vb.reverse) [] false false).reverse
  have hBA : ∀ j, (π.SA j).length ≤ π.BA := fun j => by have := hπ.hA j; omega
  have hBB : ∀ j, (π.SB j).length ≤ π.BB := fun j => by have := hπ.hB j; omega
  have hTA : ∀ j, (π.TA j).length ≤ π.BA := fun j => by have := hπ.hA j; omega
  have hTB : ∀ j, (π.TB j).length ≤ π.BB := fun j => by have := hπ.hB j; omega
  have hBC : ∀ j, (π.SC j).length ≤ π.BC := fun j => by have := hπ.hC j; simpa using this
  have hPP : PP = ppS π z := rfl
  set T := tb K (PP.length + N * π.BC)
  have hq' : ∀ t ≤ N, runFor ∅ π.q T
      (.run ⟨0, (init [PP ++ ((ic π.kC π.dC X t).reverse.flatMap π.SC).reverse, []]).stk⟩) =
        .done (ans iw ib (ic π.kC π.dC X t)) := by
    intro t ht
    have h := hq iw ib (ic π.kC π.dC X t)
    have e : xc π iw ib (ic π.kC π.dC X t) = PP ++ ((ic π.kC π.dC X t).reverse.flatMap π.SC).reverse := by
      simp [xc, PP, mA, mP]
    rw [e] at h
    rw [show (⟨0, (init [PP ++ ((ic π.kC π.dC X t).reverse.flatMap π.SC).reverse, []]).stk⟩ : Cfg) =
      init [PP ++ ((ic π.kC π.dC X t).reverse.flatMap π.SC).reverse] by rw [init_two]; rfl]
    refine runFor_mono h ?_
    unfold T tb
    refine Nat.pow_le_pow_left ?_ _
    have := flatMap_length_le hBC (ic π.kC π.dC X t).reverse
    rw [List.length_reverse, length_ic] at this
    have := Nat.mul_le_mul_right π.BC ht
    simp only [List.length_append, List.length_reverse]
    omega
  have hl := exec_mLoop π hπ mE X PP N T (fun t => ans iw ib (ic π.kC π.dC X t)) rfl rfl rfl rfl rfl
    rfl hq' N 0 (by omega) (by omega)
  have e0 : mSt π mE N X 0 = mE := by simp [mSt, mE, mS, mB, mA, mP, Mem.e, ic, X]
  rw [e0] at hl
  refine (hp.seq_norm (ha'.seq_norm (hb.seq_norm (hs.seq_norm (he.seq_norm hl))))).cast ?_ ?_
  · congr 1
    apply decide_eq_decide.2
    constructor
    · rintro ⟨t', -, h2, h3⟩; exact Or.inr ⟨t', h2, h3⟩
    · rintro (h | ⟨t', h2, h3⟩)
      · exact absurd h hpm
      · exact ⟨t', Nat.zero_le _, h2, h3⟩
  · -- the cost
    have hVl : (mA.vw.reverse ++ π.bS ++ mA.vb.reverse).length = (vS π z).length := rfl
    have hpwl : mA.pw.length ≤ z.length * π.BA := by
      have := flatMap_length_le hBA iw.reverse; simp only [List.length_reverse] at this
      exact this.trans (Nat.mul_le_mul_right _ hn)
    have hpbl : mA.pb.length ≤ z.length * π.BB := by
      have := flatMap_length_le hBB ib.reverse; simp only [List.length_reverse] at this
      exact this.trans (Nat.mul_le_mul_right _ hm)
    have hvwl : mA.vw.length ≤ z.length * π.BA := by
      have := flatMap_length_le hTA iw.reverse; simp only [List.length_reverse] at this
      exact this.trans (Nat.mul_le_mul_right _ hn)
    have hvbl : mA.vb.length ≤ z.length * π.BB := by
      have := flatMap_length_le hTB ib.reverse; simp only [List.length_reverse] at this
      exact this.trans (Nat.mul_le_mul_right _ hm)
    have hGl : (seg (segIt W m)).1.length ≤ z.length := by
      have := seg_length (segIt W m); have := segIt_length W m; omega
    have hm1 : m * (2 * W.length + 4) ≤ z.length * (2 * z.length + 4) :=
      Nat.mul_le_mul hm (by omega)
    have hev : ((seg (segIt W m)).1.length + 1) * (2 * ((vS π z).length +
        (seg (segIt W m)).1.length) + 40) ≤ (z.length + 1) * (2 * ((vS π z).length + z.length) + 40) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [hVl, Nat.sub_zero]
    unfold Tprog
    have e1 : (r1 π z).1.length = n := rfl
    have e3 : (r3 π z).1.length = m := rfl
    rw [e1, e3, show nS π z = N from rfl, ← hPP, show tb K (PP.length + N * π.BC) = T from rfl]
    generalize Cit π N PP.length T = CC
    omega

end

end Pnp.KarpLipton.DP
