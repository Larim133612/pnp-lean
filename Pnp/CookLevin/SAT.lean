import Pnp.Oracle.StructLib
import Pnp.TM2.Homomorphism

/-!
# SAT is in NP (official definition)

We define a concrete version of CNF-satisfiability as a language over a four-letter alphabet
and put it into the official class `NP` (`Millennium.InNondeterministicPolynomialTime`).

## The language

A formula is a word over `SatSym = {pos, neg, zero, sep}` in *dense* form: the word is a sequence
of clauses, each terminated by `sep`; the `j`-th symbol of a clause describes variable `x_j`
(`pos`: the literal `x_j` occurs, `neg`: the literal `¬x_j` occurs, `zero`: `x_j` does not occur).
Symbols after the last `sep` (an unfinished clause) are ignored.  `evalF a w 0 false` evaluates
the formula under the assignment `a : ℕ → Bool`: the flag records whether the current clause is
already satisfied, the index `j` is the current position inside the clause.

`SATLang w` holds iff some assignment satisfies `w`; `clauses_sat_iff` restates this as
“every clause has a true literal”.

## The verifier

The checking relation is `R w y := evalF (fun j => y.getD j false) w 0 false = true` (the
certificate is the list of variable values).  A program of our own stack-machine model
(`Pnp/Oracle/Struct.lean`) decides the bit code of `w # y`:

1. `phaseA`: parse the code of `w` (stack `0`) up to the separator, pushing a 2-bit internal code
   onto stack `2` (reversed); the certificate remains on stack `0`;
2. `move 2 3`: reverse it back onto stack `3`;
3. `phaseC`: scan the formula; the used certificate bits of the current clause go to stack `5`
   and are moved back to stack `0` at each `sep`; stack `4` is the “clause satisfied” flag.

It runs in time `(n+2)^4` on *all* inputs; `Pnp.TM2Hom.inPolynomialTime_of_code` transfers it to
the official class `P`, which gives `sat_in_np`.

This is the first half of the Cook–Levin theorem (SAT is NP-complete); NP-hardness is not proved
here.
-/

namespace Pnp.CookLevin

open Function Pnp.Relativize Pnp.Relativize.Struct

/-! ## The language -/

/-- Symbols of dense CNF formulas. -/
inductive SatSym
  | pos
  | neg
  | zero
  | sep
  deriving DecidableEq, Fintype

open SatSym

/-- Evaluate a dense CNF formula under `a`; `j` is the position inside the current clause and
`F` says whether the current clause is already satisfied. -/
def evalF (a : ℕ → Bool) : List SatSym → ℕ → Bool → Bool
  | [], _, _ => true
  | sep :: w, _, F => F && evalF a w 0 false
  | zero :: w, j, F => evalF a w (j + 1) F
  | pos :: w, j, F => evalF a w (j + 1) (F || a j)
  | neg :: w, j, F => evalF a w (j + 1) (F || !a j)

/-- Satisfiability of dense CNF formulas. -/
def SATLang : Millennium.Language (List SatSym) := fun w => ∃ a : ℕ → Bool, evalF a w 0 false = true

/-- The checking relation: the certificate lists the values of the variables. -/
def SatRel (w : List SatSym) (y : List Bool) : Prop := evalF (fun j => y.getD j false) w 0 false = true

/-- `evalF` only depends on the assignment below `j + |w|`. -/
theorem evalF_congr {a b : ℕ → Bool} : ∀ (w : List SatSym) (j : ℕ) (F : Bool),
    (∀ i, i < j + w.length → a i = b i) → evalF a w j F = evalF b w j F
  | [], _, _, _ => rfl
  | sep :: w, j, F, h => by
    simp only [evalF]
    rw [evalF_congr w 0 false (fun i hi => h i (by simp; omega))]
  | zero :: w, j, F, h => by
    simp only [evalF]
    exact evalF_congr w (j + 1) F (fun i hi => h i (by simp; omega))
  | pos :: w, j, F, h => by
    simp only [evalF]
    rw [h j (by simp), evalF_congr w (j + 1) _ (fun i hi => h i (by simp; omega))]
  | neg :: w, j, F, h => by
    simp only [evalF]
    rw [h j (by simp), evalF_congr w (j + 1) _ (fun i hi => h i (by simp; omega))]

/-- Short certificates suffice. -/
theorem satLang_iff (w : List SatSym) :
    SATLang w ↔ ∃ y : List Bool, y.length ≤ w.length ∧ SatRel w y := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(List.range w.length).map a, by simp, ?_⟩
    unfold SatRel
    rw [← ha]
    refine evalF_congr w 0 false (fun i hi => ?_)
    simp only [zero_add] at hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  · rintro ⟨y, -, hy⟩
    exact ⟨_, hy⟩

/-! ### Clause form -/

/-- The finished clauses of a dense formula (`cur` is the reversed current clause). -/
def clausesAux : List SatSym → List SatSym → List (List SatSym)
  | [], _ => []
  | sep :: w, cur => cur.reverse :: clausesAux w []
  | s :: w, cur => clausesAux w (s :: cur)

/-- The clauses of a dense formula. -/
def clauses (w : List SatSym) : List (List SatSym) := clausesAux w []

/-- A symbol at position `j` of a clause is a true literal under `a`. -/
def litTrue (a : ℕ → Bool) (j : ℕ) : SatSym → Prop
  | pos => a j = true
  | neg => a j = false
  | _ => False

/-- A clause is satisfied if it has a true literal (`zero` is never a true literal). -/
def ClauseSat (a : ℕ → Bool) (c : List SatSym) : Prop :=
  ∃ j < c.length, litTrue a j (c.getD j zero)

theorem clauseSat_append (a : ℕ → Bool) (c : List SatSym) (s : SatSym) :
    ClauseSat a (c ++ [s]) ↔ ClauseSat a c ∨ litTrue a c.length s := by
  constructor
  · rintro ⟨j, hj, h⟩
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact Or.inl ⟨j, hj, by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hj] using h⟩
    · right; simpa [List.getD_eq_getElem?_getD] using h
  · rintro (⟨j, hj, h⟩ | h)
    · exact ⟨j, by simp; omega, by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hj] using h⟩
    · exact ⟨c.length, by simp, by simpa [List.getD_eq_getElem?_getD] using h⟩

theorem evalF_eq_clauses (a : ℕ → Bool) : ∀ (w cur : List SatSym) (F : Bool),
    (F = true ↔ ClauseSat a cur.reverse) →
      (evalF a w cur.length F = true ↔ ∀ c ∈ clausesAux w cur, ClauseSat a c)
  | [], cur, F, _ => by simp [evalF, clausesAux]
  | sep :: w, cur, F, hF => by
    have ih := evalF_eq_clauses a w [] false (by simp [ClauseSat])
    simp only [List.length_nil] at ih
    simp only [evalF, clausesAux, Bool.and_eq_true, ih, List.mem_cons, forall_eq_or_imp, hF]
  | zero :: w, cur, F, hF => by
    have ih := evalF_eq_clauses a w (zero :: cur) F
      (by rw [hF, List.reverse_cons, clauseSat_append]; simp [litTrue])
    simp only [List.length_cons] at ih
    simp only [evalF, clausesAux, ih]
  | pos :: w, cur, F, hF => by
    have ih := evalF_eq_clauses a w (pos :: cur) (F || a cur.length)
      (by rw [Bool.or_eq_true, hF, List.reverse_cons, clauseSat_append, List.length_reverse]; rfl)
    simp only [List.length_cons] at ih
    simp only [evalF, clausesAux, ih]
  | neg :: w, cur, F, hF => by
    have ih := evalF_eq_clauses a w (neg :: cur) (F || !a cur.length)
      (by rw [Bool.or_eq_true, hF, List.reverse_cons, clauseSat_append, List.length_reverse]
          simp [litTrue])
    simp only [List.length_cons] at ih
    simp only [evalF, clausesAux, ih]

/-- `SATLang` in clause form: some assignment makes a literal of every clause true. -/
theorem clauses_sat_iff (w : List SatSym) :
    SATLang w ↔ ∃ a : ℕ → Bool, ∀ c ∈ clauses w, ClauseSat a c := by
  refine exists_congr fun a => ?_
  have := evalF_eq_clauses a w [] false (by simp [ClauseSat])
  simpa [clauses] using this

/-! ## Codes -/

/-- External code of formula symbols (the separator `#` is `[false, false]`). -/
def ec : SatSym → Str
  | sep => [false, true]
  | zero => [true, false]
  | pos => [true, true, false]
  | neg => [true, true, true]

/-- Internal 2-bit code. -/
def ic : SatSym → Str
  | sep => [false, false]
  | zero => [false, true]
  | pos => [true, false]
  | neg => [true, true]

theorem length_flatMap_ic : ∀ w : List SatSym, (w.flatMap ic).length = 2 * w.length
  | [] => rfl
  | s :: w => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_ic w]
    cases s <;> simp [ic] <;> omega

/-- Total decoding of the external code: formula symbols up to `#`, and the rest. -/
def dec : Str → List SatSym × Str
  | false :: false :: r => ([], r)
  | false :: true :: r => (sep :: (dec r).1, (dec r).2)
  | true :: false :: r => (zero :: (dec r).1, (dec r).2)
  | true :: true :: false :: r => (pos :: (dec r).1, (dec r).2)
  | true :: true :: true :: r => (neg :: (dec r).1, (dec r).2)
  | _ => ([], [])

theorem dec_length : ∀ z : Str, 2 * (dec z).1.length + (dec z).2.length ≤ z.length
  | [] => by simp [dec]
  | [b] => by cases b <;> simp [dec]
  | [true, true] => by simp [dec]
  | false :: false :: r => by simp [dec]; omega
  | false :: true :: r => by have := dec_length r; simp [dec]; omega
  | true :: false :: r => by have := dec_length r; simp [dec]; omega
  | true :: true :: false :: r => by have := dec_length r; simp [dec]; omega
  | true :: true :: true :: r => by have := dec_length r; simp [dec]; omega

theorem dec_code (y : Str) : ∀ w : List SatSym, dec (w.flatMap ec ++ false :: false :: y) = (w, y)
  | [] => rfl
  | s :: w => by
    have ih := dec_code y w
    cases s <;> simp [ec, dec, ih]

/-! ## Phase A: parsing -/

/-- Loop body of `phaseA`. -/
def bodyA : Cmd :=
  .pop 0 .brk
    (.pop 0 .brk .brk (.seq (.push 2 false) (.push 2 false)))
    (.pop 0 .brk (.seq (.push 2 false) (.push 2 true))
      (.pop 0 .brk (.seq (.push 2 true) (.push 2 false)) (.seq (.push 2 true) (.push 2 true))))

/-- Parse the formula part. -/
def phaseA : Cmd := .loop bodyA

theorem pushTwo (b₁ b₂ : Bool) (σ : ℕ → Str) :
    ExecLe (.seq (.push 2 b₁) (.push 2 b₂)) σ (.norm (update σ 2 (b₂ :: b₁ :: σ 2))) 2 :=
  (ExecLe.seq_norm (ExecLe.push 2 b₁ σ) (ExecLe.push 2 b₂ _)).cast (by simp) le_rfl

theorem exec_phaseA : ∀ (z : Str) (σ : ℕ → Str), σ 0 = z →
    ExecLe phaseA σ
      (.norm (update (update σ 0 (dec z).2) 2 (((dec z).1.flatMap ic).reverse ++ σ 2)))
      (3 * z.length + 4)
  | [], σ, h => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk σ))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [dec]) (by simp)
  | [false], σ, h => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) h (ExecLe.pop_nil (by simp)
      (ExecLe.brk _)))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [dec]) (by simp)
  | [true], σ, h => (ExecLe.loop_brk (ExecLe.pop_cons (b := true) h (ExecLe.pop_nil (by simp)
      (ExecLe.brk _)))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [dec]) (by simp)
  | [true, true], σ, h => (ExecLe.loop_brk (ExecLe.pop_cons (b := true) h (ExecLe.pop_cons (b := true) (s := [])
      (by simp) (ExecLe.pop_nil (by simp) (ExecLe.brk _))))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [dec]) (by simp)
  | false :: false :: r, σ, h => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) h (ExecLe.pop_cons (b := false) (s := r)
      (by simp) (ExecLe.brk _)))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [dec]) (by simp)
  | false :: true :: r, σ, h => by
    have hb : ExecLe bodyA σ (.norm (update (update σ 0 r) 2 (false :: false :: σ 2))) 4 :=
      ExecLe.pop_cons (b := false) h (ExecLe.pop_cons (b := true) (s := r) (by simp)
        ((pushTwo false false _).cast (by simp) le_rfl))
    have ih := exec_phaseA r _ (by simp : (update (update σ 0 r) 2 (false :: false :: σ 2)) 0 = r)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [dec, ic]
  | true :: false :: r, σ, h => by
    have hb : ExecLe bodyA σ (.norm (update (update σ 0 r) 2 (true :: false :: σ 2))) 4 :=
      ExecLe.pop_cons (b := true) h (ExecLe.pop_cons (b := false) (s := r) (by simp)
        ((pushTwo false true _).cast (by simp) le_rfl))
    have ih := exec_phaseA r _ (by simp : (update (update σ 0 r) 2 (true :: false :: σ 2)) 0 = r)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [dec, ic]
  | true :: true :: false :: r, σ, h => by
    have hb : ExecLe bodyA σ (.norm (update (update σ 0 r) 2 (false :: true :: σ 2))) 5 :=
      ExecLe.pop_cons (b := true) h (ExecLe.pop_cons (b := true) (s := false :: r) (by simp)
        (ExecLe.pop_cons (b := false) (s := r) (by simp) ((pushTwo true false _).cast (by simp) le_rfl)))
    have ih := exec_phaseA r _ (by simp : (update (update σ 0 r) 2 (false :: true :: σ 2)) 0 = r)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [dec, ic]
  | true :: true :: true :: r, σ, h => by
    have hb : ExecLe bodyA σ (.norm (update (update σ 0 r) 2 (true :: true :: σ 2))) 5 :=
      ExecLe.pop_cons (b := true) h (ExecLe.pop_cons (b := true) (s := true :: r) (by simp)
        (ExecLe.pop_cons (b := true) (s := r) (by simp) ((pushTwo true true _).cast (by simp) le_rfl)))
    have ih := exec_phaseA r _ (by simp : (update (update σ 0 r) 2 (true :: true :: σ 2)) 0 = r)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [dec, ic]

/-! ## Phase C: evaluation -/

/-- Set the flag stack `4` to `[true]` (it holds `[]` or `[true]`). -/
def setF : Cmd := .pop 4 (.push 4 true) (.push 4 true) (.push 4 true)

/-- Loop body of `phaseC`. -/
def bodyC : Cmd :=
  .pop 3 (.halt true)
    (.pop 3 (.halt true) (.pop 4 (.halt false) (.halt false) (move 5 0))
      (.pop 0 .skip (.push 5 false) (.push 5 true)))
    (.pop 3 (.halt true) (.pop 0 .skip (.push 5 false) (.seq (.push 5 true) setF))
      (.pop 0 setF (.seq (.push 5 false) setF) (.push 5 true)))

/-- Evaluate the formula on stack `3`. -/
def phaseC : Cmd := .loop bodyC

/-- The flag as a stack. -/
def fl (F : Bool) : Str := if F then [true] else []

/-- What `phaseC` computes (`Y`: unused certificate bits, `U`: used ones, reversed). -/
def run : List SatSym → Str → Str → Bool → Bool
  | [], _, _, _ => true
  | sep :: w, Y, U, F => F && run w (U.reverse ++ Y) [] false
  | zero :: w, [], U, F => run w [] U F
  | zero :: w, b :: Y, U, F => run w Y (b :: U) F
  | pos :: w, [], U, F => run w [] U F
  | pos :: w, b :: Y, U, F => run w Y (b :: U) (F || b)
  | neg :: w, [], U, _ => run w [] U true
  | neg :: w, b :: Y, U, F => run w Y (b :: U) (F || !b)

theorem exec_setF (F : Bool) (σ : ℕ → Str) (h : σ 4 = fl F) :
    ExecLe setF σ (.norm (update σ 4 [true])) 2 := by
  cases F
  · exact (ExecLe.pop_nil h (ExecLe.push 4 true σ)).cast (by simp [h, fl]) le_rfl
  · exact (ExecLe.pop_cons h (ExecLe.push 4 true _)).cast (by simp) le_rfl

/-- Equality of stack assignments built from `update`s. -/
macro "ueq" : tactic =>
  `(tactic| (congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all))

theorem loopC {σ σ' : ℕ → Str} {r : Res} {T₁ T₂ T : ℕ} (hb : ExecLe bodyC σ (.norm σ') T₁)
    (ih : ExecLe phaseC σ' r T₂) (hT : T₁ + T₂ ≤ T) : ExecLe phaseC σ r T :=
  (ExecLe.loop_norm hb ih).cast rfl hT

theorem exec_phaseC (N : ℕ) : ∀ (w : List SatSym) (σ : ℕ → Str) (Y U : Str) (F : Bool),
    σ 3 = w.flatMap ic → σ 0 = Y → σ 5 = U → σ 4 = fl F → U.length + Y.length ≤ N →
    ExecLe phaseC σ (.halt (run w Y U F)) (w.length * (2 * N + 8) + 2)
  | [], σ, Y, U, F, h3, _, _, _, _ =>
    (ExecLe.loop_halt (ExecLe.pop_nil h3 (ExecLe.halt true σ))).cast (by simp [run]) (by simp)
  | sep :: w, σ, Y, U, F, h3, h0, h5, h4, hN => by
    have h3' : σ 3 = false :: false :: w.flatMap ic := by simp [h3, ic]
    cases F
    · have hb : ExecLe bodyC σ (.halt false) (1 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_nil (by simpa [fl] using h4) (ExecLe.halt false _)))
      exact (ExecLe.loop_halt hb).cast (by simp [run]) (by simp; nlinarith)
    · let σ' := update (update (update (update σ 3 (w.flatMap ic)) 4 []) 5 []) 0 (U.reverse ++ Y)
      have hb : ExecLe bodyC σ (.norm σ') (2 * U.length + 2 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_cons (b := true) (s := []) (by simpa [fl] using h4)
            ((ExecLe.of (exec_move (a := 5) (b := 0) (by decide) U _ (by simp [h5]))).cast
              (by simp only [σ']; ueq) le_rfl)))
      have ih := exec_phaseC N w σ' (U.reverse ++ Y) [] false (by simp [σ'])
        (by simp [σ']) (by simp [σ'])
        (by simp [σ', fl]) (by simp; omega)
      exact loopC hb (ih.cast (by simp [run]) le_rfl) (by simp; nlinarith)
  | zero :: w, σ, Y, U, F, h3, h0, h5, h4, hN => by
    have h3' : σ 3 = false :: true :: w.flatMap ic := by simp [h3, ic]
    cases Y with
    | nil =>
      let σ' := update σ 3 (w.flatMap ic)
      have hb : ExecLe bodyC σ (.norm σ') (1 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_nil (by simp [h0]) ((ExecLe.skip _).cast (by simp only [σ']; ueq) le_rfl)))
      have ih := exec_phaseC N w σ' [] U F (by simp [σ']) (by simp [σ', h0])
        (by simp [σ', h5]) (by simp [σ', h4]) (by simpa using hN)
      exact loopC hb (ih.cast (by simp [run]) le_rfl) (by simp; nlinarith)
    | cons b Y =>
      let σ' := update (update (update σ 3 (w.flatMap ic)) 0 Y) 5 (b :: U)
      have hb : ExecLe bodyC σ (.norm σ') (1 + 1 + 1 + 1) := by
        refine ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_cons (b := b) (s := Y) (by simp [h0]) ?_))
        cases b
        · exact (ExecLe.push 5 false _).cast (by simp only [σ']; ueq) le_rfl
        · exact (ExecLe.push 5 true _).cast (by simp only [σ']; ueq) le_rfl
      have ih := exec_phaseC N w σ' Y (b :: U) F (by simp [σ'])
        (by simp [σ']) (by simp [σ'])
        (by simp [σ', h4]) (by simp at hN ⊢; omega)
      exact loopC hb (ih.cast (by simp [run]) le_rfl) (by simp; nlinarith)
  | pos :: w, σ, Y, U, F, h3, h0, h5, h4, hN => by
    have h3' : σ 3 = true :: false :: w.flatMap ic := by simp [h3, ic]
    cases Y with
    | nil =>
      let σ' := update σ 3 (w.flatMap ic)
      have hb : ExecLe bodyC σ (.norm σ') (1 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_nil (by simp [h0]) ((ExecLe.skip _).cast (by simp only [σ']; ueq) le_rfl)))
      have ih := exec_phaseC N w σ' [] U F (by simp [σ']) (by simp [σ', h0])
        (by simp [σ', h5]) (by simp [σ', h4]) (by simpa using hN)
      exact loopC hb (ih.cast (by simp [run]) le_rfl) (by simp; nlinarith)
    | cons b Y =>
      cases b
      · let σ' := update (update (update σ 3 (w.flatMap ic)) 0 Y) 5 (false :: U)
        have hb : ExecLe bodyC σ (.norm σ') (1 + 1 + 1 + 1) :=
          ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
            (by simp) (ExecLe.pop_cons (b := false) (s := Y) (by simp [h0])
              ((ExecLe.push 5 false _).cast (by simp only [σ']; ueq) le_rfl)))
        have ih := exec_phaseC N w σ' Y (false :: U) F (by simp [σ'])
          (by simp [σ']) (by simp [σ'])
          (by simp [σ', h4]) (by simp at hN ⊢; omega)
        exact loopC hb (ih.cast (by simp [run]) le_rfl) (by simp; nlinarith)
      · let σ' := update (update (update (update σ 3 (w.flatMap ic)) 0 Y) 5 (true :: U)) 4 [true]
        have hb : ExecLe bodyC σ (.norm σ') (1 + 2 + 1 + 1 + 1) :=
          ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
            (by simp) (ExecLe.pop_cons (b := true) (s := Y) (by simp [h0])
              ((ExecLe.seq_norm (ExecLe.push 5 true _)
                (exec_setF F _ (by simp [update_apply, h4]))).cast (by simp only [σ']; ueq) le_rfl)))
        have ih := exec_phaseC N w σ' Y (true :: U) true (by simp [σ'])
          (by simp [σ']) (by simp [σ'])
          (by simp [σ', fl]) (by simp at hN ⊢; omega)
        exact loopC hb (ih.cast (by simp [run]) le_rfl) (by simp; nlinarith)
  | neg :: w, σ, Y, U, F, h3, h0, h5, h4, hN => by
    have h3' : σ 3 = true :: true :: w.flatMap ic := by simp [h3, ic]
    cases Y with
    | nil =>
      let σ' := update (update σ 3 (w.flatMap ic)) 4 [true]
      have hb : ExecLe bodyC σ (.norm σ') (2 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_nil (by simp [h0])
            ((exec_setF F _ (by simp [update_apply, h4])).cast (by simp only [σ']; ueq) le_rfl)))
      have ih := exec_phaseC N w σ' [] U true (by simp [σ'])
        (by simp [σ', h0]) (by simp [σ', h5])
        (by simp [σ', fl]) (by simpa using hN)
      exact loopC hb (ih.cast (by simp [run]) le_rfl) (by simp; nlinarith)
    | cons b Y =>
      cases b
      · let σ' := update (update (update (update σ 3 (w.flatMap ic)) 0 Y) 5 (false :: U)) 4 [true]
        have hb : ExecLe bodyC σ (.norm σ') (1 + 2 + 1 + 1 + 1) :=
          ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
            (by simp) (ExecLe.pop_cons (b := false) (s := Y) (by simp [h0])
              ((ExecLe.seq_norm (ExecLe.push 5 false _)
                (exec_setF F _ (by simp [update_apply, h4]))).cast (by simp only [σ']; ueq) le_rfl)))
        have ih := exec_phaseC N w σ' Y (false :: U) true (by simp [σ'])
          (by simp [σ']) (by simp [σ'])
          (by simp [σ', fl]) (by simp at hN ⊢; omega)
        exact loopC hb (ih.cast (by simp [run]) le_rfl) (by simp; nlinarith)
      · let σ' := update (update (update σ 3 (w.flatMap ic)) 0 Y) 5 (true :: U)
        have hb : ExecLe bodyC σ (.norm σ') (1 + 1 + 1 + 1) :=
          ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
            (by simp) (ExecLe.pop_cons (b := true) (s := Y) (by simp [h0])
              ((ExecLe.push 5 true _).cast (by simp only [σ']; ueq) le_rfl)))
        have ih := exec_phaseC N w σ' Y (true :: U) F (by simp [σ'])
          (by simp [σ']) (by simp [σ'])
          (by simp [σ', h4]) (by simp at hN ⊢; omega)
        exact loopC hb (ih.cast (by simp [run]) le_rfl) (by simp; nlinarith)

/-- `run` agrees with `evalF` (with `a j = y_j`, `y = U.reverse ++ Y`). -/
theorem run_eq (y : Str) : ∀ (w : List SatSym) (Y U : Str) (F : Bool) (j : ℕ),
    U.reverse ++ Y = y → U.length ≤ j → (Y ≠ [] → U.length = j) →
    run w Y U F = evalF (fun i => y.getD i false) w j F
  | [], _, _, _, _, _, _, _ => rfl
  | sep :: w, Y, U, F, j, hy, _, _ => by
    simp only [run, evalF]
    rw [run_eq y w _ [] false 0 (by simpa using hy) (by simp) (by simp)]
  | zero :: w, [], U, F, j, hy, hj, _ => by
    simp only [run, evalF]
    exact run_eq y w [] U F (j + 1) hy (by omega) (by simp)
  | zero :: w, b :: Y, U, F, j, hy, _, hj => by
    have hj := hj (by simp)
    simp only [run, evalF]
    exact run_eq y w Y (b :: U) F (j + 1) (by simpa using hy) (by simp; omega) (fun _ => by
      simp; omega)
  | pos :: w, [], U, F, j, hy, hj, _ => by
    have hd : y.getD j false = false := by
      rw [← hy]; simp only [List.append_nil]
      exact List.getD_eq_default _ _ (by simpa using hj)
    simp only [run, evalF, hd, Bool.or_false]
    exact run_eq y w [] U F (j + 1) hy (by omega) (by simp)
  | pos :: w, b :: Y, U, F, j, hy, _, hj => by
    have hj := hj (by simp)
    have hd : y.getD j false = b := by
      rw [← hy, ← hj, ← List.length_reverse]
      simp [List.getD_eq_getElem?_getD]
    simp only [run, evalF, hd]
    exact run_eq y w Y (b :: U) _ (j + 1) (by simpa using hy) (by simp; omega) (fun _ => by
      simp; omega)
  | neg :: w, [], U, F, j, hy, hj, _ => by
    have hd : y.getD j false = false := by
      rw [← hy]; simp only [List.append_nil]
      exact List.getD_eq_default _ _ (by simpa using hj)
    simp only [run, evalF, hd, Bool.not_false, Bool.or_true]
    exact run_eq y w [] U true (j + 1) hy (by omega) (by simp)
  | neg :: w, b :: Y, U, F, j, hy, _, hj => by
    have hj := hj (by simp)
    have hd : y.getD j false = b := by
      rw [← hy, ← hj, ← List.length_reverse]
      simp [List.getD_eq_getElem?_getD]
    simp only [run, evalF, hd]
    exact run_eq y w Y (b :: U) _ (j + 1) (by simpa using hy) (by simp; omega) (fun _ => by
      simp; omega)

/-! ## The whole program -/

/-- The verifier program. -/
def satCmd : Cmd := .seq phaseA (.seq (move 2 3) phaseC)

/-- Time bound of the verifier. -/
def Tsat (n : ℕ) : ℕ := 3 * n + 4 + (2 * n + 2) + (n * (2 * n + 8) + 2)

theorem exec_satCmd (z : Str) :
    ExecLe satCmd (init [z]).stk (.halt (run (dec z).1 (dec z).2 [] false)) (Tsat z.length) := by
  have hl := dec_length z
  set w := (dec z).1
  set Y := (dec z).2
  have h0 : (init [z]).stk 0 = z := rfl
  have he : ∀ j, j ≠ 0 → (init [z]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have hA := exec_phaseA z (init [z]).stk h0
  set σ₁ := update (update (init [z]).stk 0 Y) 2 ((w.flatMap ic).reverse ++ (init [z]).stk 2)
  have hM := exec_move (a := 2) (b := 3) (by decide) _ σ₁ rfl
  have hC := exec_phaseC Y.length w (update (update σ₁ 2 []) 3 ((σ₁ 2).reverse ++ σ₁ 3)) Y [] false
    (by simp [σ₁, update_apply, he 3 (by decide), he 2 (by decide)])
    (by simp [σ₁, update_apply]) (by simp [σ₁, update_apply, he 5 (by decide)])
    (by simp [σ₁, update_apply, he 4 (by decide), fl]) (by simp)
  refine (ExecLe.seq_norm hA (ExecLe.seq_norm (ExecLe.of hM) hC)).cast rfl ?_
  have hw : (w.flatMap ic).length = 2 * w.length := length_flatMap_ic w
  simp only [σ₁, update_self, List.length_append, List.length_reverse, hw, he 2 (by decide),
    List.length_nil, Tsat]
  have : w.length ≤ z.length := by omega
  have : Y.length ≤ z.length := by omega
  nlinarith

theorem Tsat_le (n : ℕ) : Tsat n ≤ tb 4 n := by
  unfold Tsat tb
  have h4 : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have : (n + 2) ^ 4 = (n + 2) ^ 2 * (n + 2) ^ 2 := by ring
  nlinarith

/-! ## Transfer to the official class -/

/-- Code of the symbols of `w # y`. -/
def pc : SatSym ⊕ Option Bool → Str
  | .inl s => ec s
  | .inr none => [false, false]
  | .inr (some b) => [b]

theorem flatMap_pair (w : List SatSym) (y : List Bool) :
    ((Millennium.pair_encoding (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool)).encode (w, y)).flatMap pc =
      w.flatMap ec ++ false :: false :: y := by
  have h1 : ∀ s : List SatSym,
      (s.map (Sum.inl : SatSym → SatSym ⊕ Option Bool)).flatMap pc = s.flatMap ec := by
    intro s; induction s with
    | nil => rfl
    | cons a s ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl
  have h2 : ∀ s : List Bool,
      (s.map (fun b => (Sum.inr (some b) : SatSym ⊕ Option Bool))).flatMap pc = s := by
    intro s; induction s with
    | nil => rfl
    | cons b s ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl
  rw [Millennium.pair_encoding.encode_eq]
  erw [List.flatMap_append, List.flatMap_cons, h1, h2]
  rfl

/-- **SAT ∈ NP** for the official class `NP` (`Millennium.InNondeterministicPolynomialTime`):
the dense-CNF satisfiability language `SATLang` (over the alphabet `SatSym`, identity encoding)
has a polynomial-time checking relation with certificates of length `≤ |w|`. -/
theorem sat_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym) SATLang := by
  classical
  have hrun := fun z => ((exec_satCmd z).mono (Tsat_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg satCmd) (tb 4 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg satCmd, 4, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) SatRel := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
    rw [run_eq y w y [] false 0 (by simp) (by simp) (by simp)]
    rfl
  refine ⟨Bool, inferInstance, SatRel, 1, hR, fun w => ?_⟩
  rw [satLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.CookLevin
