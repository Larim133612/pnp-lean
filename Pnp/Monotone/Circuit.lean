import Mathlib

/-!
# Monotone circuits and the abstract approximation method (M3b, part 1)

A monotone circuit on `n` inputs with `s` gates is a straight-line program in which
gate `i` is an AND or an OR of two earlier wires among the `n + i` available
(same layout as `Pnp.Circuits.Circuit`, with the operation restricted to `∧`/`∨`).

Evaluation is defined once, generically, by `evalWires`: given values for the input
wires in any type `α` and an interpretation `op : Bool → α → α → α` of the two gate
kinds, it propagates values along the circuit. Instantiating `α := Bool` gives the
ordinary evaluation; instantiating `α` with a type of *approximators* gives the
approximator attached to every wire (Razborov / Alon–Boppana).

Main results:
* `MCircuit.eval_monotone`: monotone circuits compute monotone functions.
* `approx_errors_one_sided`, `approximation_method`: if every approximate gate
  step makes at most `d` errors (relative to the exact AND/OR applied to the
  approximators of its inputs) and inputs are approximated exactly, then the final
  approximator errs on at most `s * d` tests.
-/

namespace Pnp.Monotone

open Finset

/-- A monotone gate reading two of the first `m` wires. The `Bool` is the kind:
`true` = AND, `false` = OR. -/
abbrev MGate (m : ℕ) := Bool × Fin m × Fin m

/-- The gate list of a monotone circuit with `n` inputs and `s` gates. -/
abbrev MGates (n s : ℕ) := (i : Fin s) → MGate (n + i.val)

/-- A monotone circuit with `n` inputs and exactly `s` gates, with an output wire. -/
abbrev MCircuit (n s : ℕ) := MGates n s × Fin (n + s)

/-- The Boolean operation of a gate kind: `true ↦ AND`, `false ↦ OR`. -/
def gateOp : Bool → Bool → Bool → Bool
  | true => (· && ·)
  | false => (· || ·)

@[simp] lemma gateOp_true (a b : Bool) : gateOp true a b = (a && b) := rfl
@[simp] lemma gateOp_false (a b : Bool) : gateOp false a b = (a || b) := rfl

lemma gateOp_mono (o : Bool) {a a' b b' : Bool} (ha : a ≤ a') (hb : b ≤ b') :
    gateOp o a b ≤ gateOp o a' b' := by
  revert ha hb; cases o <;> cases a <;> cases a' <;> cases b <;> cases b' <;> decide

/-- Generic propagation of values of type `α` along a monotone circuit. -/
def evalWires {α : Type*} {n : ℕ} (inp : Fin n → α) (op : Bool → α → α → α) :
    (s : ℕ) → MGates n s → Fin (n + s) → α
  | 0, _ => inp
  | s + 1, g =>
    let w := evalWires inp op s (fun i => g i.castSucc)
    let gt := g (Fin.last s)
    Fin.snoc (α := fun _ => α) w (op gt.1 (w gt.2.1) (w gt.2.2))

section evalWires
variable {α : Type*} {n : ℕ} (inp : Fin n → α) (op : Bool → α → α → α)

@[simp] lemma evalWires_zero (g : MGates n 0) : evalWires inp op 0 g = inp := rfl

lemma evalWires_succ_castSucc (s : ℕ) (g : MGates n (s + 1)) (i : Fin (n + s)) :
    evalWires inp op (s + 1) g i.castSucc = evalWires inp op s (fun j => g j.castSucc) i := by
  simp [evalWires]

lemma evalWires_succ_last (s : ℕ) (g : MGates n (s + 1)) :
    evalWires inp op (s + 1) g (Fin.last (n + s)) =
      op (g (Fin.last s)).1 (evalWires inp op s (fun j => g j.castSucc) (g (Fin.last s)).2.1)
        (evalWires inp op s (fun j => g j.castSucc) (g (Fin.last s)).2.2) := by
  simp [evalWires]

/-- Two propagations satisfying a binary relation on inputs, preserved by every gate
operation, satisfy it on every wire. -/
lemma evalWires_rel {β : Type*} (inp' : Fin n → β) (op' : Bool → β → β → β)
    (R : α → β → Prop) (hin : ∀ i, R (inp i) (inp' i))
    (hop : ∀ o a a' b b', R a a' → R b b' → R (op o a b) (op' o a' b')) :
    ∀ (s : ℕ) (g : MGates n s) (w : Fin (n + s)),
      R (evalWires inp op s g w) (evalWires inp' op' s g w) := by
  intro s
  induction s with
  | zero => intro g w; exact hin w
  | succ s ih =>
    intro g w
    refine Fin.lastCases (n := n + s) ?_ (fun i => ?_) w
    · rw [evalWires_succ_last, evalWires_succ_last]
      exact hop _ _ _ _ _ (ih _ _) (ih _ _)
    · rw [evalWires_succ_castSucc, evalWires_succ_castSucc]
      exact ih _ _

/-- A predicate on values preserved by every gate operation holds on every wire. -/
lemma evalWires_pred (P : α → Prop) (hin : ∀ i, P (inp i))
    (hop : ∀ o a b, P a → P b → P (op o a b)) (s : ℕ) (g : MGates n s) (w : Fin (n + s)) :
    P (evalWires inp op s g w) :=
  evalWires_rel inp op inp op (fun a _ => P a) hin (fun o a _ b _ ha hb => hop o a b ha hb) s g w

end evalWires

/-- The Boolean function computed by a monotone circuit. -/
def MCircuit.eval {n s : ℕ} (C : MCircuit n s) (x : Fin n → Bool) : Bool :=
  evalWires x gateOp s C.1 C.2

/-- The approximator attached to the output of `C`, when input wire `i` is approximated
by `ia i` and gate kind `o` is approximated by `aop o`. -/
def MCircuit.approx {A : Type*} {n s : ℕ} (C : MCircuit n s) (ia : Fin n → A)
    (aop : Bool → A → A → A) : A :=
  evalWires ia aop s C.1 C.2

/-- **Monotone circuits compute monotone functions** (pointwise order on `Fin n → Bool`). -/
theorem MCircuit.eval_monotone {n s : ℕ} (C : MCircuit n s) : Monotone C.eval := by
  intro x y hxy
  exact evalWires_rel x gateOp y gateOp (· ≤ ·) hxy
    (fun o _ _ _ _ ha hb => gateOp_mono o ha hb) s C.1 C.2

/-- Sanity check: a one-gate monotone circuit computing `x₀ ∧ x₁`. -/
def mandCircuit : MCircuit 2 1 :=
  (fun _ => (true, ⟨0, by omega⟩, ⟨1, by omega⟩), Fin.last 2)

example : mandCircuit.eval = fun x => x 0 && x 1 := by
  funext x; rfl

/-! ## The abstract approximation method -/

/-- The key Boolean fact behind error propagation: if the exact gate outputs `b` on the
true wire values but `!b` on the approximated values, then some input wire already
carries an error of the same kind. -/
lemma gateOp_err (o b wa wb sa sb : Bool) (hw : gateOp o wa wb = b) (hs : gateOp o sa sb = !b) :
    (wa = b ∧ sa = !b) ∨ (wb = b ∧ sb = !b) := by
  revert hw hs
  cases o <;> cases b <;> cases wa <;> cases wb <;> cases sa <;> cases sb <;> decide

section approx
variable {X A : Type*} [DecidableEq X] {N : ℕ}
  (inp : X → Fin N → Bool) (sem : A → X → Bool) (ia : Fin N → A) (aop : Bool → A → A → A)
  (T : Finset X) (b : Bool)

/-- Error set of one approximate gate step of kind `o` with input approximators `a c`:
the tests where the exact gate applied to the approximators gives `b`, but the
approximate gate gives `!b`. -/
def stepErr (o : Bool) (a c : A) : Finset X :=
  T.filter fun x => gateOp o (sem a x) (sem c x) = b ∧ sem (aop o a c) x = !b

/-- The union of the error sets of all gates of a circuit. -/
def circErr : (s : ℕ) → MGates N s → Finset X
  | 0, _ => ∅
  | s + 1, g =>
    let w := evalWires ia aop s (fun i => g i.castSucc)
    let gt := g (Fin.last s)
    circErr s (fun i => g i.castSucc) ∪ stepErr sem aop T b gt.1 (w gt.2.1) (w gt.2.2)

/-- Every wire-level error (true value `b`, approximator `!b`) on a test lies in the
error set of some gate, provided inputs are approximated without such errors. -/
lemma wireErr_subset_circErr
    (hin : ∀ x ∈ T, ∀ i, ¬ (inp x i = b ∧ sem (ia i) x = !b)) :
    ∀ (s : ℕ) (g : MGates N s) (w : Fin (N + s)),
      (T.filter fun x => evalWires (inp x) gateOp s g w = b ∧ sem (evalWires ia aop s g w) x = !b) ⊆
        circErr sem ia aop T b s g := by
  intro s
  induction s with
  | zero =>
    intro g w x hx
    simp only [mem_filter, evalWires_zero] at hx
    exact absurd hx.2 (hin x hx.1 w)
  | succ s ih =>
    intro g w x hx
    simp only [mem_filter] at hx
    obtain ⟨hxT, hw, hs⟩ := hx
    simp only [circErr, mem_union]
    refine Fin.lastCases (n := N + s) ?_ (fun i => ?_) w hw hs
    · intro hw hs
      rw [evalWires_succ_last] at hw hs
      set g' : MGates N s := fun j => g j.castSucc
      set gt := g (Fin.last s)
      by_cases hstep : gateOp gt.1 (sem (evalWires ia aop s g' gt.2.1) x)
          (sem (evalWires ia aop s g' gt.2.2) x) = b
      · right
        exact mem_filter.2 ⟨hxT, hstep, hs⟩
      · left
        have hs' : gateOp gt.1 (sem (evalWires ia aop s g' gt.2.1) x)
            (sem (evalWires ia aop s g' gt.2.2) x) = !b := by
          cases b <;> simpa using hstep
        rcases gateOp_err _ _ _ _ _ _ hw hs' with h | h
        · exact ih g' gt.2.1 (mem_filter.2 ⟨hxT, h⟩)
        · exact ih g' gt.2.2 (mem_filter.2 ⟨hxT, h⟩)
    · intro hw hs
      rw [evalWires_succ_castSucc] at hw hs
      left
      exact ih _ i (mem_filter.2 ⟨hxT, hw, hs⟩)

/-- If every step error set (on `Good` approximators) has at most `d` elements, the union
over `s` gates has at most `s * d`, and all wire approximators stay `Good`. -/
lemma card_circErr_le (Good : A → Prop) (hGin : ∀ i, Good (ia i))
    (hGop : ∀ o a c, Good a → Good c → Good (aop o a c)) (d : ℕ)
    (hstep : ∀ o a c, Good a → Good c → (stepErr sem aop T b o a c).card ≤ d) :
    ∀ (s : ℕ) (g : MGates N s), (circErr sem ia aop T b s g).card ≤ s * d := by
  intro s
  induction s with
  | zero => intro g; simp [circErr]
  | succ s ih =>
    intro g
    simp only [circErr]
    refine (card_union_le _ _).trans ?_
    rw [Nat.succ_mul]
    have hG : ∀ w, Good (evalWires ia aop s (fun i => g i.castSucc) w) :=
      evalWires_pred ia aop Good hGin hGop s _
    exact Nat.add_le_add (ih _) (hstep _ _ _ (hG _) (hG _))

/-- **Approximation method, one-sided form.** Let `Good` be an invariant of
approximators that holds for the input approximators and is preserved by the
approximate gates. Suppose that on the test set `T`:
* no input wire has an error of kind `b` (true value `b`, approximator value `!b`);
* each approximate gate step on `Good` approximators creates at most `d` errors of
  kind `b` relative to the exact gate applied to the approximators of its inputs.

Then the output approximator is `Good` and has errors of kind `b` (circuit says `b`,
approximator says `!b`) on at most `s * d` tests. -/
theorem approx_errors_one_sided {s : ℕ} (C : MCircuit N s) (Good : A → Prop)
    (hGin : ∀ i, Good (ia i)) (hGop : ∀ o a c, Good a → Good c → Good (aop o a c))
    (d : ℕ) (hin : ∀ x ∈ T, ∀ i, ¬ (inp x i = b ∧ sem (ia i) x = !b))
    (hstep : ∀ o a c, Good a → Good c → (stepErr sem aop T b o a c).card ≤ d) :
    Good (C.approx ia aop) ∧
      (T.filter fun x => C.eval (inp x) = b ∧ sem (C.approx ia aop) x = !b).card ≤ s * d :=
  ⟨evalWires_pred ia aop Good hGin hGop s C.1 C.2,
    (card_le_card (wireErr_subset_circErr inp sem ia aop T b hin s C.1 C.2)).trans
      (card_circErr_le sem ia aop T b Good hGin hGop d hstep s C.1)⟩

end approx

/-- **The approximation method (Razborov; Alon–Boppana), two-sided form.**

Positive tests are elements of `P : Finset XP` (feeding the circuit `inpP x`), negative
tests are elements of `Q : Finset XQ` (feeding `inpQ y`); approximators of type `A`
are interpreted on them by `semP`, `semQ`. Input wire `i` is approximated by `ia i`
exactly on tests, and gate kind `o` (`true` = AND, `false` = OR) by `aop o`, which
preserves an invariant `Good`. If on `Good` approximators each step introduces at most
`dPos` *positive errors* (exact gate on approximators gives `1`, step gives `0`) and
at most `dNeg` *negative errors* (exact gives `0`, step gives `1`), then the final
approximator is `Good`, and if `C` outputs `1` on `P` and `0` on `Q`, the final
approximator is `0` on at most `s * dPos` positive tests and `1` on at most `s * dNeg`
negative tests. -/
theorem approximation_method {XP XQ A : Type*} [DecidableEq XP] [DecidableEq XQ] {N s : ℕ}
    (C : MCircuit N s) (inpP : XP → Fin N → Bool) (inpQ : XQ → Fin N → Bool)
    (semP : A → XP → Bool) (semQ : A → XQ → Bool) (ia : Fin N → A)
    (aop : Bool → A → A → A) (Good : A → Prop)
    (hGin : ∀ i, Good (ia i)) (hGop : ∀ o a c, Good a → Good c → Good (aop o a c))
    (P : Finset XP) (Q : Finset XQ) (dPos dNeg : ℕ)
    (hinP : ∀ x ∈ P, ∀ i, semP (ia i) x = inpP x i)
    (hinQ : ∀ y ∈ Q, ∀ i, semQ (ia i) y = inpQ y i)
    (hstepP : ∀ o a c, Good a → Good c →
      (P.filter fun x => gateOp o (semP a x) (semP c x) = true ∧
        semP (aop o a c) x = false).card ≤ dPos)
    (hstepQ : ∀ o a c, Good a → Good c →
      (Q.filter fun y => gateOp o (semQ a y) (semQ c y) = false ∧
        semQ (aop o a c) y = true).card ≤ dNeg)
    (hP : ∀ x ∈ P, C.eval (inpP x) = true) (hQ : ∀ y ∈ Q, C.eval (inpQ y) = false) :
    Good (C.approx ia aop) ∧
      (P.filter fun x => semP (C.approx ia aop) x = false).card ≤ s * dPos ∧
      (Q.filter fun y => semQ (C.approx ia aop) y = true).card ≤ s * dNeg := by
  have h1 := approx_errors_one_sided inpP semP ia aop P true C Good hGin hGop dPos
    (fun x hx i h => by rw [hinP x hx i] at h; simp at h) hstepP
  have h2 := approx_errors_one_sided inpQ semQ ia aop Q false C Good hGin hGop dNeg
    (fun y hy i h => by rw [hinQ y hy i] at h; simp at h) hstepQ
  refine ⟨h1.1, ?_, ?_⟩
  · refine le_trans (le_of_eq ?_) h1.2
    congr 1
    exact filter_congr fun x hx => by simp [hP x hx]
  · refine le_trans (le_of_eq ?_) h2.2
    congr 1
    exact filter_congr fun y hy => by simp [hQ y hy]

end Pnp.Monotone
