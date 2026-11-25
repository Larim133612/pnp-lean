import Mathlib

/-!
# AC⁰ formulas (M4a)

Unbounded fan-in formulas (trees) on `n` inputs: leaves are literals `xᵢ` / `¬xᵢ`,
internal nodes are `AND` / `OR` gates with any finite number `t` of children, given as
an indexed family `Fin t → Formula n`.

Conventions:
* `size F` is the number of **gates** (internal nodes); leaves count `0`.
* `depth F` is the number of gates on a longest root-to-leaf path; literals have depth `0`.
* An `AND` with no children is the constant `true`, an `OR` with no children is `false`.

Formula (rather than circuit) bounds suffice for AC⁰: a depth-`d` circuit with `s` gates
unfolds to a formula of depth `d` and size `≤ s^d` (not formalized here).
-/

namespace Pnp.AC0

inductive Formula (n : ℕ) where
  /-- `lit i c` is true at `x` iff `x i = c`. -/
  | lit : Fin n → Bool → Formula n
  | and : (t : ℕ) → (Fin t → Formula n) → Formula n
  | or  : (t : ℕ) → (Fin t → Formula n) → Formula n

namespace Formula

variable {n : ℕ}

def eval : Formula n → (Fin n → Bool) → Bool
  | lit i c, x => x i == c
  | and _ f, x => decide (∀ i, (f i).eval x = true)
  | or _ f, x => decide (∃ i, (f i).eval x = true)

/-- Number of gates (internal nodes). -/
def size : Formula n → ℕ
  | lit _ _ => 0
  | and _ f => (∑ i, (f i).size) + 1
  | or _ f => (∑ i, (f i).size) + 1

/-- Depth: number of gates on a longest root-to-leaf path. -/
def depth : Formula n → ℕ
  | lit _ _ => 0
  | and _ f => (Finset.univ.sup fun i => (f i).depth) + 1
  | or _ f => (Finset.univ.sup fun i => (f i).depth) + 1

@[simp] lemma eval_lit (i : Fin n) (c : Bool) (x : Fin n → Bool) :
    (lit i c).eval x = (x i == c) := rfl
@[simp] lemma eval_and (t : ℕ) (f : Fin t → Formula n) (x : Fin n → Bool) :
    (and t f).eval x = decide (∀ i, (f i).eval x = true) := rfl
@[simp] lemma eval_or (t : ℕ) (f : Fin t → Formula n) (x : Fin n → Bool) :
    (or t f).eval x = decide (∃ i, (f i).eval x = true) := rfl

end Formula

end Pnp.AC0
