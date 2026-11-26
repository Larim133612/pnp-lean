import Pnp.AC0.Parity

/-!
# AC⁰ circuits (M6)

Unbounded fan-in circuits (DAGs) on `n` inputs, as straight-line programs:

* a **wire** of a circuit with `k` gates so far is a literal `(i, c)` (true iff `x i = c`) or
  the output of one of the `k` earlier gates (`Wire n k = (Fin n × Bool) ⊕ Fin k`);
* gate number `k` is an `AND` (`isAnd = true`) or `OR` of an arbitrary `Finset` of wires
  among the literals and gates `0, …, k-1` (empty `AND` = `true`, empty `OR` = `false`);
* `Gates n s` is the list of the first `s` gates (built by `snoc`), and a `Circuit n` is
  a list of gates together with an output wire.

Conventions: `size C` is the number of gates (all of them, used or not); the depth of a
literal is `0`, the depth of a gate is `1 +` the maximal depth of its inputs, and
`depth C` is the depth of the output wire (the number of gates on a longest path ending
at the output).

Main results:
* `Circuit.eval_toFormula`, `Circuit.depth_toFormula`, `Circuit.size_toFormula_le`:
  a circuit with `s` gates and depth `d` unfolds to an equivalent `Formula` of depth `d`
  and size `≤ s^d`;
* `parity_ac0_circuit_lower_bound`: a circuit computing PARITY on `n` bits satisfies
  `2^ℓ ≤ 4 · size^depth` whenever `16 · ((2ℓ)^{depth} + 1)² ≤ n + 1`;
* `parity_not_in_AC0_circuits`: for fixed depth `d` and polynomial `c · n^k`, for all large
  `n` every depth-`≤ d` circuit computing PARITY has more than `c · n^k` gates;
* `exists_parity_circuit`: non-vacuity, a depth-`≤ 2` circuit computes PARITY for every `n`.
-/

namespace Pnp.AC0

open Finset

variable {n : ℕ}

/-- A wire available after `k` gates: a literal `(i, c)` or an earlier gate. -/
abbrev Wire (n k : ℕ) := (Fin n × Bool) ⊕ Fin k

/-- A gate whose inputs are wires among the literals and the `k` earlier gates. -/
structure Gate (n k : ℕ) where
  isAnd : Bool
  inputs : Finset (Wire n k)

/-- The first `k` gates of a straight-line program. -/
inductive Gates (n : ℕ) : ℕ → Type
  | nil : Gates n 0
  | snoc {k : ℕ} : Gates n k → Gate n k → Gates n (k + 1)

/-- An unbounded fan-in circuit: `size` gates and an output wire. -/
structure Circuit (n : ℕ) where
  size : ℕ
  gates : Gates n size
  out : Wire n size

/-! ### Semantics, depth, and unfolding of wires and gates -/

namespace Wire

variable {k : ℕ}

/-- Value of a wire, given the values `v` of the earlier gates. -/
def evalWith (v : Fin k → Bool) (x : Fin n → Bool) : Wire n k → Bool
  | .inl (i, c) => x i == c
  | .inr j => v j

/-- Depth of a wire, given the depths `dp` of the earlier gates. -/
def depthWith (dp : Fin k → ℕ) : Wire n k → ℕ
  | .inl _ => 0
  | .inr j => dp j

/-- Formula of a wire, given the formulas `f` of the earlier gates. -/
def toFormulaWith (f : Fin k → Formula n) : Wire n k → Formula n
  | .inl (i, c) => .lit i c
  | .inr j => f j

lemma eval_toFormulaWith (f : Fin k → Formula n) (x : Fin n → Bool) (w : Wire n k) :
    (w.toFormulaWith f).eval x = w.evalWith (fun j => (f j).eval x) x := by
  rcases w with ⟨i, c⟩ | j <;> rfl

lemma depth_toFormulaWith (f : Fin k → Formula n) (w : Wire n k) :
    (w.toFormulaWith f).depth = w.depthWith (fun j => (f j).depth) := by
  rcases w with ⟨i, c⟩ | j <;> rfl

end Wire

namespace Gate

variable {k : ℕ}

/-- Value of a gate, given the values `v` of the earlier gates. -/
def evalWith (g : Gate n k) (v : Fin k → Bool) (x : Fin n → Bool) : Bool :=
  cond g.isAnd (decide (∀ w ∈ g.inputs, w.evalWith v x = true))
    (decide (∃ w ∈ g.inputs, w.evalWith v x = true))

/-- Depth of a gate, given the depths `dp` of the earlier gates. -/
def depthWith (g : Gate n k) (dp : Fin k → ℕ) : ℕ :=
  (g.inputs.sup fun w => w.depthWith dp) + 1

/-- The children of the unfolded gate, enumerated by `Fin |inputs|`. -/
noncomputable def children (g : Gate n k) (f : Fin k → Formula n) :
    Fin g.inputs.card → Formula n :=
  fun j => (g.inputs.equivFin.symm j).1.toFormulaWith f

/-- Formula of a gate, given the formulas `f` of the earlier gates. -/
noncomputable def toFormulaWith (g : Gate n k) (f : Fin k → Formula n) : Formula n :=
  cond g.isAnd (.and _ (g.children f)) (.or _ (g.children f))

lemma forall_children_iff (g : Gate n k) (P : Wire n k → Prop) :
    (∀ j : Fin g.inputs.card, P (g.inputs.equivFin.symm j).1) ↔ ∀ w ∈ g.inputs, P w := by
  constructor
  · intro h w hw
    simpa using h (g.inputs.equivFin ⟨w, hw⟩)
  · intro h j
    exact h _ (g.inputs.equivFin.symm j).2

lemma exists_children_iff (g : Gate n k) (P : Wire n k → Prop) :
    (∃ j : Fin g.inputs.card, P (g.inputs.equivFin.symm j).1) ↔ ∃ w ∈ g.inputs, P w := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨_, (g.inputs.equivFin.symm j).2, hj⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨g.inputs.equivFin ⟨w, hw⟩, by simpa using h⟩

lemma eval_toFormulaWith (g : Gate n k) (f : Fin k → Formula n) (x : Fin n → Bool) :
    (g.toFormulaWith f).eval x = g.evalWith (fun j => (f j).eval x) x := by
  rcases g with ⟨_ | _, s⟩
  · simp only [toFormulaWith, evalWith, cond_false, Formula.eval_or, children,
      Wire.eval_toFormulaWith]
    exact decide_eq_decide.2 (exists_children_iff ⟨false, s⟩ (fun w => w.evalWith (fun j => (f j).eval x) x = true))
  · simp only [toFormulaWith, evalWith, cond_true, Formula.eval_and, children,
      Wire.eval_toFormulaWith]
    exact decide_eq_decide.2 (forall_children_iff ⟨true, s⟩ (fun w => w.evalWith (fun j => (f j).eval x) x = true))

lemma sup_children (g : Gate n k) (φ : Wire n k → ℕ) :
    (univ.sup fun j : Fin g.inputs.card => φ (g.inputs.equivFin.symm j).1) =
      g.inputs.sup φ := by
  refine le_antisymm (Finset.sup_le fun j _ => Finset.le_sup (g.inputs.equivFin.symm j).2)
    (Finset.sup_le fun w hw => ?_)
  have := Finset.le_sup (f := fun j : Fin g.inputs.card => φ (g.inputs.equivFin.symm j).1)
    (mem_univ (g.inputs.equivFin ⟨w, hw⟩))
  simpa using this

lemma sum_children (g : Gate n k) (φ : Wire n k → ℕ) :
    (∑ j : Fin g.inputs.card, φ (g.inputs.equivFin.symm j).1) = ∑ w ∈ g.inputs, φ w := by
  rw [Equiv.sum_comp g.inputs.equivFin.symm (fun w => φ w.1), Finset.sum_coe_sort]

lemma depth_toFormulaWith (g : Gate n k) (f : Fin k → Formula n) :
    (g.toFormulaWith f).depth = g.depthWith (fun j => (f j).depth) := by
  have h := g.sup_children (fun w => (w.toFormulaWith f).depth)
  simp only [Wire.depth_toFormulaWith] at h
  rcases g with ⟨_ | _, s⟩ <;>
  · simp only [toFormulaWith, depthWith, cond_false, cond_true, Formula.depth, children,
      Wire.depth_toFormulaWith]
    rw [h]

lemma size_toFormulaWith (g : Gate n k) (f : Fin k → Formula n) :
    (g.toFormulaWith f).size = (∑ w ∈ g.inputs, (w.toFormulaWith f).size) + 1 := by
  have h := g.sum_children (fun w => (w.toFormulaWith f).size)
  rcases g with ⟨_ | _, s⟩ <;>
  · simp only [toFormulaWith, cond_false, cond_true, Formula.size, children]
    rw [h]

end Gate

/-! ### Gate lists -/

namespace Gates

/-- Values of all gates on input `x`. -/
def vals : {k : ℕ} → Gates n k → (Fin n → Bool) → Fin k → Bool
  | _, nil, _ => Fin.elim0
  | _, snoc G g, x => Fin.snoc (α := fun _ => Bool) (G.vals x) (g.evalWith (G.vals x) x)

/-- Depths of all gates. -/
def depths : {k : ℕ} → Gates n k → Fin k → ℕ
  | _, nil => Fin.elim0
  | _, snoc G g => Fin.snoc (α := fun _ => ℕ) G.depths (g.depthWith G.depths)

/-- Unfolded formulas of all gates. -/
noncomputable def forms : {k : ℕ} → Gates n k → Fin k → Formula n
  | _, nil => Fin.elim0
  | _, snoc G g => Fin.snoc (α := fun _ => Formula n) G.forms (g.toFormulaWith G.forms)

lemma eval_forms {k : ℕ} (G : Gates n k) (x : Fin n → Bool) (j : Fin k) :
    (G.forms j).eval x = G.vals x j := by
  induction G with
  | nil => exact j.elim0
  | snoc G g ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [forms, vals, Fin.snoc_last, Gate.eval_toFormulaWith]
      congr 1
      funext j
      exact ih j
    · simp only [forms, vals, Fin.snoc_castSucc]
      exact ih j

lemma depth_forms {k : ℕ} (G : Gates n k) (j : Fin k) : (G.forms j).depth = G.depths j := by
  induction G with
  | nil => exact j.elim0
  | snoc G g ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [forms, depths, Fin.snoc_last, Gate.depth_toFormulaWith]
      congr 1
      funext j
      exact ih j
    · simp only [forms, depths, Fin.snoc_castSucc]
      exact ih j

/-- `1 + a^D ≤ (a+1)^D` for `D ≥ 1`. -/
lemma one_add_pow_le {a D : ℕ} (hD : 1 ≤ D) : 1 + a ^ D ≤ (a + 1) ^ D := by
  obtain ⟨e, rfl⟩ : ∃ e, D = e + 1 := ⟨D - 1, by omega⟩
  have h1 : a ^ e ≤ (a + 1) ^ e := Nat.pow_le_pow_left (by omega) e
  have h2 : 1 ≤ (a + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ, pow_succ]
  nlinarith

/-- **Size of the unfolding:** in a list of `k` gates, the formula of every gate has size
`≤ k^{depth}`. -/
lemma size_forms_le {k : ℕ} (G : Gates n k) (j : Fin k) : (G.forms j).size ≤ k ^ G.depths j := by
  induction G with
  | nil => exact j.elim0
  | @snoc k G g ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [forms, depths, Fin.snoc_last, Gate.size_toFormulaWith, Gate.depthWith]
      set D := g.inputs.sup fun w => w.depthWith G.depths
      -- bound each child by `0` (literal) or `k^D` (gate)
      let b : Wire n k → ℕ := fun w => Sum.elim (fun _ => 0) (fun _ => k ^ D) w
      have hchild : ∀ w ∈ g.inputs, (w.toFormulaWith G.forms).size ≤ b w := by
        intro w hw
        rcases w with ⟨i, c⟩ | j
        · simp [Wire.toFormulaWith, Formula.size, b]
        · have hd : G.depths j ≤ D :=
            Finset.le_sup (f := fun w => w.depthWith G.depths) hw
          have hk : 1 ≤ k := by have := j.2; omega
          exact (ih j).trans (Nat.pow_le_pow_right hk hd)
      have hsum : (∑ w ∈ g.inputs, (w.toFormulaWith G.forms).size) ≤ k * k ^ D :=
        calc (∑ w ∈ g.inputs, (w.toFormulaWith G.forms).size)
            ≤ ∑ w ∈ g.inputs, b w := Finset.sum_le_sum hchild
          _ ≤ ∑ w, b w := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
          _ = k * k ^ D := by simp [b, Fintype.sum_sum_type]
      have := one_add_pow_le (a := k) (D := D + 1) (by omega)
      rw [pow_succ] at this
      have hc : k * k ^ D = k ^ D * k := Nat.mul_comm _ _
      omega
    · simp only [forms, depths, Fin.snoc_castSucc]
      exact (ih j).trans (Nat.pow_le_pow_left (by omega) _)

end Gates

/-! ### Circuits -/

namespace Circuit

/-- Value of the circuit on input `x`. -/
def eval (C : Circuit n) (x : Fin n → Bool) : Bool := C.out.evalWith (C.gates.vals x) x

/-- Depth of the circuit: depth of the output wire (longest path of gates ending at it). -/
def depth (C : Circuit n) : ℕ := C.out.depthWith C.gates.depths

/-- The circuit unfolded into a formula (tree). -/
noncomputable def toFormula (C : Circuit n) : Formula n := C.out.toFormulaWith C.gates.forms

/-- Unfolding preserves the computed function. -/
theorem eval_toFormula (C : Circuit n) (x : Fin n → Bool) : C.toFormula.eval x = C.eval x := by
  unfold toFormula eval
  rw [Wire.eval_toFormulaWith]
  congr 1
  funext j
  exact C.gates.eval_forms x j

/-- Unfolding preserves depth. -/
theorem depth_toFormula (C : Circuit n) : C.toFormula.depth = C.depth := by
  unfold toFormula depth
  rw [Wire.depth_toFormulaWith]
  congr 1
  funext j
  exact C.gates.depth_forms j

/-- **Unfolding bound:** a circuit with `s` gates and depth `d` unfolds to a formula with
at most `s^d` gates. -/
theorem size_toFormula_le (C : Circuit n) : C.toFormula.size ≤ C.size ^ C.depth := by
  unfold toFormula depth
  rcases C with ⟨s, G, ⟨i, c⟩ | j⟩
  · simp [Wire.toFormulaWith, Formula.size]
  · exact G.size_forms_le j

/-- Every circuit of size `s` and depth `d` is equivalent to a formula of depth `d` and
size `≤ s^d`. -/
theorem exists_formula (C : Circuit n) :
    ∃ F : Formula n, F.depth = C.depth ∧ F.size ≤ C.size ^ C.depth ∧
      ∀ x, F.eval x = C.eval x :=
  ⟨C.toFormula, C.depth_toFormula, C.size_toFormula_le, C.eval_toFormula⟩

end Circuit

/-! ### PARITY ∉ AC⁰ for circuits -/

/-- **PARITY ∉ AC⁰ for circuits, explicit form.** If a circuit `C` computes PARITY on `n`
bits and `16 · ((2ℓ)^{depth C} + 1)² ≤ n + 1`, then `2^ℓ ≤ 4 · (size C)^{depth C}`. -/
theorem parity_ac0_circuit_lower_bound (C : Circuit n) (hC : ∀ x, C.eval x = parityFn x)
    (ℓ : ℕ) (hℓ : 16 * ((2 * ℓ) ^ C.depth + 1) ^ 2 ≤ n + 1) :
    2 ^ ℓ ≤ 4 * C.size ^ C.depth := by
  have h := parity_ac0_lower_bound C.toFormula
    (fun x => (C.eval_toFormula x).trans (hC x)) ℓ (by rwa [C.depth_toFormula])
  exact h.trans (Nat.mul_le_mul_left 4 C.size_toFormula_le)

/-- **PARITY ∉ AC⁰ for circuits, depth-`d` form.** -/
theorem parity_ac0_circuit_lower_bound_of_depth_le {d ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (C : Circuit n)
    (hd : C.depth ≤ d) (hC : ∀ x, C.eval x = parityFn x)
    (hℓ : 16 * ((2 * ℓ) ^ d + 1) ^ 2 ≤ n + 1) : 2 ^ ℓ ≤ 4 * C.size ^ C.depth := by
  have h := parity_ac0_lower_bound_of_depth_le hℓ1 C.toFormula
    (by rw [C.depth_toFormula]; exact hd) (fun x => (C.eval_toFormula x).trans (hC x)) hℓ
  exact h.trans (Nat.mul_le_mul_left 4 C.size_toFormula_le)

/-- **PARITY ∉ AC⁰ (circuits).** For every depth `d` and polynomial `c · n^k`, for all large
`n`, every circuit of depth `≤ d` computing PARITY on `n` bits has more than `c · n^k`
gates. -/
theorem parity_not_in_AC0_circuits (d c k : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ C : Circuit n, C.depth ≤ d → (∀ x, C.eval x = parityFn x) →
      c * n ^ k < C.size := by
  obtain ⟨N, hN⟩ := parity_not_in_AC0 d ((c + 1) ^ d) (k * d)
  refine ⟨max N 1, fun n hn C hd hC => ?_⟩
  by_contra hlt
  push Not at hlt
  have hF := hN n (by omega) C.toFormula (by rw [C.depth_toFormula]; exact hd)
    (fun x => (C.eval_toFormula x).trans (hC x))
  have hn1 : 1 ≤ n ^ k := Nat.one_le_pow _ _ (by omega)
  -- `max s 1 ≤ (c+1) n^k`
  have hm : max C.size 1 ≤ (c + 1) * n ^ k := by
    have : c * n ^ k + n ^ k = (c + 1) * n ^ k := by ring
    omega
  have hsz : C.toFormula.size ≤ (c + 1) ^ d * n ^ (k * d) :=
    calc C.toFormula.size ≤ C.size ^ C.depth := C.size_toFormula_le
      _ ≤ (max C.size 1) ^ C.depth := Nat.pow_le_pow_left (le_max_left _ _) _
      _ ≤ (max C.size 1) ^ d := Nat.pow_le_pow_right (by omega) hd
      _ ≤ ((c + 1) * n ^ k) ^ d := Nat.pow_le_pow_left hm _
      _ = (c + 1) ^ d * n ^ (k * d) := by rw [mul_pow, pow_mul]
  omega

/-! ### Non-vacuity: a depth-2 circuit for PARITY -/

/-- The AND gate of the `n` literals matching the point `y`. -/
def pointGate {k : ℕ} (y : Fin n → Bool) : Gate n k :=
  ⟨true, univ.image fun i => Sum.inl (i, y i)⟩

/-- `m` AND gates, gate `j` testing `x = pts j`. -/
def pointGates (pts : ℕ → Fin n → Bool) : (m : ℕ) → Gates n m
  | 0 => .nil
  | m + 1 => .snoc (pointGates pts m) (pointGate (pts m))

lemma vals_pointGates (pts : ℕ → Fin n → Bool) (x : Fin n → Bool) :
    ∀ (m : ℕ) (j : Fin m), (pointGates pts m).vals x j = decide (x = pts j)
  | 0, j => j.elim0
  | m + 1, j => by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [pointGates, Gates.vals, Fin.snoc_last, pointGate, Gate.evalWith, cond_true]
      simp [Wire.evalWith, funext_iff]
    · simp only [pointGates, Gates.vals, Fin.snoc_castSucc]
      rw [vals_pointGates pts x m j]
      rfl

lemma depths_pointGates (pts : ℕ → Fin n → Bool) :
    ∀ (m : ℕ) (j : Fin m), (pointGates pts m).depths j ≤ 1
  | 0, j => j.elim0
  | m + 1, j => by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [pointGates, Gates.depths, Fin.snoc_last, pointGate, Gate.depthWith]
      refine Nat.succ_le_succ (Finset.sup_le fun w hw => ?_)
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
      exact le_rfl
    · simp only [pointGates, Gates.depths, Fin.snoc_castSucc]
      exact depths_pointGates pts m j

/-- Enumeration of all points of `{0,1}ⁿ` by `ℕ` (junk beyond `2ⁿ`). -/
noncomputable def allPoints (n : ℕ) (j : ℕ) : Fin n → Bool :=
  if h : j < Fintype.card (Fin n → Bool) then (Fintype.equivFin (Fin n → Bool)).symm ⟨j, h⟩
  else fun _ => false

/-- The DNF circuit for PARITY: one AND gate per point, then an OR of the odd points. -/
noncomputable def parityCircuit (n : ℕ) : Circuit n :=
  let N := Fintype.card (Fin n → Bool)
  ⟨N + 1, .snoc (pointGates (allPoints n) N)
      ⟨false, (univ.filter fun j : Fin N => parityFn (allPoints n j) = true).image Sum.inr⟩,
    .inr (Fin.last N)⟩

/-- **Non-vacuity:** for every `n`, some circuit of depth `≤ 2` computes PARITY. -/
theorem exists_parity_circuit (n : ℕ) :
    ∃ C : Circuit n, C.depth ≤ 2 ∧ ∀ x, C.eval x = parityFn x := by
  refine ⟨parityCircuit n, ?_, fun x => ?_⟩
  · have : (((univ.filter fun j : Fin (Fintype.card (Fin n → Bool)) =>
        parityFn (allPoints n j) = true).image Sum.inr).sup
          fun w : Wire n _ => Wire.depthWith (pointGates (allPoints n) _).depths w) ≤ 1 :=
      Finset.sup_le fun w hw => by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hw
        exact depths_pointGates _ _ j
    simp only [parityCircuit, Circuit.depth, Wire.depthWith, Gates.depths, Fin.snoc_last,
      Gate.depthWith] at this ⊢
    omega
  · simp only [parityCircuit, Circuit.eval, Wire.evalWith, Gates.vals, Fin.snoc_last,
      Gate.evalWith, cond_false]
    have hpt : ∀ j : Fin (Fintype.card (Fin n → Bool)),
        allPoints n j = (Fintype.equivFin (Fin n → Bool)).symm j := fun j => by
      rw [allPoints, dif_pos j.2]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hx : parityFn x = true
    · rw [hx, decide_eq_true_iff]
      refine ⟨Sum.inr (Fintype.equivFin _ x), ⟨_, ?_, rfl⟩, ?_⟩
      · rw [hpt, Equiv.symm_apply_apply]; exact hx
      · dsimp only
        rw [vals_pointGates, hpt, Equiv.symm_apply_apply, decide_eq_true_iff]
    · simp only [Bool.not_eq_true] at hx
      rw [hx, decide_eq_false_iff_not]
      rintro ⟨w, ⟨j, hj, rfl⟩, h⟩
      dsimp only at h
      rw [vals_pointGates, decide_eq_true_iff] at h
      rw [← h] at hj
      simp_all

end Pnp.AC0
