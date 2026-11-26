import Pnp.Circuits.Basic

/-!
# Multi-output circuits and circuit constructions

This file builds the pure-circuit infrastructure on top of `Pnp.Circuits.Basic`:

* `MCircuit n m s`: circuits with `n` inputs, `m` outputs and exactly `s` gates, with
  `MCircuit.eval` and `HasMCircuitOfSize F s` (some circuit with at most `s` gates).
* A `ℕ`-indexed view `wv x s g : ℕ → Bool` of the wire values, characterized by
  `wv_input`, `wv_gate` and the uniqueness principle `wv_unique`. All constructions are
  verified through this characterization, which avoids dependent `Fin (n + i)` bookkeeping.
* `seqGates`: sequential composition of gate lists, where the second gate list reads
  arbitrary wires of the first one in place of its inputs (`wv_seqGates_low`,
  `wv_seqGates_high`).
* Closure properties: monotonicity, projections/rewirings (size `0`), composition
  (`HasMCircuitOfSize.comp`), iteration (`HasMCircuitOfSize.iterate`), parallel combination
  (`HasCircuitOfSize.cons`, `hasMCircuitOfSize_of_forall`), and the passage between single-
  and multi-output circuits.
* Juntas: every function depending on `k` of the `n > 0` inputs has a circuit with
  `juntaSize k = 4 * 2 ^ k` gates (`hasCircuitOfSize_junta`), hence every *local* map whose
  `m` outputs each depend on `k` inputs has a circuit with `m * juntaSize k` gates
  (`hasMCircuitOfSize_local`).
-/

namespace Pnp.Circuits

/-! ## Multi-output circuits -/

/-- A circuit with `n` inputs, `m` outputs and exactly `s` gates. -/
abbrev MCircuit (n m s : ℕ) := Gates n s × (Fin m → Fin (n + s))

/-- The function `(Fin n → Bool) → (Fin m → Bool)` computed by a multi-output circuit. -/
def MCircuit.eval {n m s : ℕ} (C : MCircuit n m s) : (Fin n → Bool) → (Fin m → Bool) :=
  fun x j => wires x s C.1 (C.2 j)

/-- `F` has a multi-output circuit with at most `s` gates. -/
def HasMCircuitOfSize {n m : ℕ} (F : (Fin n → Bool) → (Fin m → Bool)) (s : ℕ) : Prop :=
  ∃ t ≤ s, ∃ C : MCircuit n m t, C.eval = F

/-! ## `ℕ`-indexed wire values -/

/-- Wire values indexed by `ℕ` (junk value `false` beyond the last wire). -/
def wv {n : ℕ} (x : Fin n → Bool) (s : ℕ) (g : Gates n s) (j : ℕ) : Bool :=
  if h : j < n + s then wires x s g ⟨j, h⟩ else false

theorem wires_eq_wv {n : ℕ} (x : Fin n → Bool) (s : ℕ) (g : Gates n s) (i : Fin (n + s)) :
    wires x s g i = wv x s g i.val := by
  simp [wv, i.2]

theorem wv_succ {n : ℕ} (x : Fin n → Bool) (s : ℕ) (g : Gates n (s + 1)) {j : ℕ}
    (hj : j < n + s) : wv x (s + 1) g j = wv x s (fun i => g i.castSucc) j := by
  have hj' : j < n + (s + 1) := by omega
  simp only [wv, dif_pos hj, dif_pos hj']
  exact Fin.snoc_castSucc (α := fun _ => Bool) (i := (⟨j, hj⟩ : Fin (n + s))) _ _

theorem wv_input {n : ℕ} (x : Fin n → Bool) :
    ∀ (s : ℕ) (g : Gates n s) {j : ℕ} (hj : j < n), wv x s g j = x ⟨j, hj⟩
  | 0, g, j, hj => by simp [wv, hj, wires]
  | s + 1, g, j, hj => by
    rw [wv_succ x s g (by omega)]
    exact wv_input x s _ hj

theorem wv_gate {n : ℕ} (x : Fin n → Bool) :
    ∀ (s : ℕ) (g : Gates n s) (i : Fin s),
      wv x s g (n + i.val) = (g i).1 (wv x s g (g i).2.1.val) (wv x s g (g i).2.2.val)
  | 0, _, i => i.elim0
  | s + 1, g, i => by
    have h1 : (g i).2.1.val < n + s := by have := (g i).2.1.2; have := i.2; omega
    have h2 : (g i).2.2.val < n + s := by have := (g i).2.2.2; have := i.2; omega
    rw [wv_succ x s g h1, wv_succ x s g h2]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [wv_succ x s g (by have := i'.2; simp)]
      exact wv_gate x s _ i'
    · have hl : n + s < n + (s + 1) := by omega
      simp only [Fin.val_last, wv, dif_pos hl, dif_pos h1, dif_pos h2]
      exact Fin.snoc_last (α := fun _ => Bool) _ _

/-- **Uniqueness principle.** Any `ℕ`-indexed assignment that agrees with the inputs and
satisfies every gate equation agrees with the wire values. -/
theorem wv_unique {n s : ℕ} (x : Fin n → Bool) (g : Gates n s) (w : ℕ → Bool)
    (h0 : ∀ j (hj : j < n), w j = x ⟨j, hj⟩)
    (h1 : ∀ i : Fin s, w (n + i.val) = (g i).1 (w (g i).2.1.val) (w (g i).2.2.val)) :
    ∀ j < n + s, w j = wv x s g j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjn : j < n
    · rw [h0 j hjn, wv_input x s g hjn]
    · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
      have hi : i < s := by omega
      have e1 := (g ⟨i, hi⟩).2.1.2
      have e2 := (g ⟨i, hi⟩).2.2.2
      rw [h1 ⟨i, hi⟩, wv_gate x s g ⟨i, hi⟩, ih _ (by omega) (by omega),
        ih _ (by omega) (by omega)]

/-! ## Gate lists from `ℕ`-indexed data -/

/-- Build a gate list from `ℕ`-indexed operations and input indices. -/
def mkGates (n s : ℕ) (op : ℕ → Bool → Bool → Bool) (a b : ℕ → ℕ)
    (ha : ∀ i < s, a i < n + i) (hb : ∀ i < s, b i < n + i) : Gates n s :=
  fun i => (op i, ⟨a i, ha i i.2⟩, ⟨b i, hb i i.2⟩)

theorem wv_mkGates_unique {n s : ℕ} (x : Fin n → Bool) {op : ℕ → Bool → Bool → Bool}
    {a b : ℕ → ℕ} {ha : ∀ i < s, a i < n + i} {hb : ∀ i < s, b i < n + i} (w : ℕ → Bool)
    (h0 : ∀ j (hj : j < n), w j = x ⟨j, hj⟩)
    (h1 : ∀ i < s, w (n + i) = op i (w (a i)) (w (b i))) :
    ∀ j < n + s, w j = wv x s (mkGates n s op a b ha hb) j :=
  wv_unique x _ w h0 fun i => h1 i i.2

/-- The operation of gate `i` (junk beyond `s`). -/
def opOf {n s : ℕ} (g : Gates n s) (i : ℕ) : Bool → Bool → Bool :=
  if h : i < s then (g ⟨i, h⟩).1 else fun _ _ => false

/-- The first input of gate `i` (junk beyond `s`). -/
def inA {n s : ℕ} (g : Gates n s) (i : ℕ) : ℕ :=
  if h : i < s then (g ⟨i, h⟩).2.1.val else 0

/-- The second input of gate `i` (junk beyond `s`). -/
def inB {n s : ℕ} (g : Gates n s) (i : ℕ) : ℕ :=
  if h : i < s then (g ⟨i, h⟩).2.2.val else 0

theorem inA_lt {n s : ℕ} (g : Gates n s) {i : ℕ} (hi : i < s) : inA g i < n + i := by
  simp only [inA, dif_pos hi]; exact (g ⟨i, hi⟩).2.1.2

theorem inB_lt {n s : ℕ} (g : Gates n s) {i : ℕ} (hi : i < s) : inB g i < n + i := by
  simp only [inB, dif_pos hi]; exact (g ⟨i, hi⟩).2.2.2

theorem wv_gate' {n s : ℕ} (x : Fin n → Bool) (g : Gates n s) {i : ℕ} (hi : i < s) :
    wv x s g (n + i) = opOf g i (wv x s g (inA g i)) (wv x s g (inB g i)) := by
  simp only [opOf, inA, inB, dif_pos hi]
  exact wv_gate x s g ⟨i, hi⟩

/-! ## Sequential composition of gate lists -/

/-- Where wire `k` of the second gate list (with `b` inputs) lands in the combined gate list:
input `k < b` is replaced by wire `σ k` of the first gate list, gate wires are shifted. -/
def seqWire {a s₁ b : ℕ} (σ : Fin b → Fin (a + s₁)) (k : ℕ) : ℕ :=
  if hk : k < b then (σ ⟨k, hk⟩).val else k - b + (a + s₁)

theorem seqWire_lt {a s₁ b : ℕ} (σ : Fin b → Fin (a + s₁)) {k i : ℕ} (hk : k < b + i) :
    seqWire σ k < a + s₁ + i := by
  unfold seqWire
  split_ifs with h
  · have := (σ ⟨k, h⟩).2; omega
  · omega

/-- Sequential composition: the gates of `g`, followed by the gates of `h` whose `b` inputs
are rewired to the wires `σ` of `g`. -/
def seqGates {a s₁ b s₂ : ℕ} (g : Gates a s₁) (σ : Fin b → Fin (a + s₁)) (h : Gates b s₂) :
    Gates a (s₁ + s₂) :=
  mkGates a (s₁ + s₂) (fun i => if i < s₁ then opOf g i else opOf h (i - s₁))
    (fun i => if i < s₁ then inA g i else seqWire σ (inA h (i - s₁)))
    (fun i => if i < s₁ then inB g i else seqWire σ (inB h (i - s₁)))
    (fun i hi => by
      split_ifs with h1
      · exact inA_lt g h1
      · have := seqWire_lt σ (inA_lt h (i := i - s₁) (by omega)); omega)
    (fun i hi => by
      split_ifs with h1
      · exact inB_lt g h1
      · have := seqWire_lt σ (inB_lt h (i := i - s₁) (by omega)); omega)

theorem wv_seqGates {a s₁ b s₂ : ℕ} (x : Fin a → Bool) (g : Gates a s₁)
    (σ : Fin b → Fin (a + s₁)) (h : Gates b s₂) :
    let y : Fin b → Bool := fun k => wv x s₁ g (σ k).val
    ∀ j < a + (s₁ + s₂), (if j < a + s₁ then wv x s₁ g j else wv y s₂ h (j - (a + s₁) + b)) =
      wv x (s₁ + s₂) (seqGates g σ h) j := by
  intro y
  set w : ℕ → Bool := fun j =>
    if j < a + s₁ then wv x s₁ g j else wv y s₂ h (j - (a + s₁) + b) with hw
  have key : ∀ k, w (seqWire σ k) = wv y s₂ h k := by
    intro k
    simp only [hw, seqWire]
    by_cases hk : k < b
    · simp only [dif_pos hk, (σ ⟨k, hk⟩).2, if_true]
      rw [wv_input y s₂ h hk]
    · simp only [dif_neg hk]
      rw [if_neg (by omega)]
      congr 1; omega
  refine wv_mkGates_unique x w (fun j hj => ?_) (fun i hi => ?_)
  · simp only [hw, if_pos (show j < a + s₁ by omega)]
    exact wv_input x s₁ g hj
  · by_cases h1 : i < s₁
    · simp only [if_pos h1]
      have e1 := inA_lt g h1
      have e2 := inB_lt g h1
      simp only [hw, if_pos (show a + i < a + s₁ by omega), if_pos (show inA g i < a + s₁ by omega),
        if_pos (show inB g i < a + s₁ by omega)]
      exact wv_gate' x g h1
    · simp only [if_neg h1, key]
      simp only [hw, if_neg (show ¬ a + i < a + s₁ by omega)]
      rw [show a + i - (a + s₁) + b = b + (i - s₁) by omega]
      exact wv_gate' y h (by omega)

theorem wv_seqGates_low {a s₁ b s₂ : ℕ} (x : Fin a → Bool) (g : Gates a s₁)
    (σ : Fin b → Fin (a + s₁)) (h : Gates b s₂) {j : ℕ} (hj : j < a + s₁) :
    wv x (s₁ + s₂) (seqGates g σ h) j = wv x s₁ g j := by
  rw [← wv_seqGates x g σ h j (by omega), if_pos hj]

theorem wv_seqGates_high {a s₁ b s₂ : ℕ} (x : Fin a → Bool) (g : Gates a s₁)
    (σ : Fin b → Fin (a + s₁)) (h : Gates b s₂) {k : ℕ} (hk : k < b + s₂) :
    wv x (s₁ + s₂) (seqGates g σ h) (seqWire σ k) =
      wv (fun k => wv x s₁ g (σ k).val) s₂ h k := by
  rw [← wv_seqGates x g σ h _ (by have := seqWire_lt σ hk; omega)]
  unfold seqWire
  by_cases hk' : k < b
  · simp only [dif_pos hk', (σ ⟨k, hk'⟩).2, if_true]
    rw [wv_input _ s₂ h hk']
  · simp only [dif_neg hk']
    rw [if_neg (by omega)]
    congr 1; omega

/-! ## Basic closure properties -/

theorem HasMCircuitOfSize.mono {n m : ℕ} {F : (Fin n → Bool) → (Fin m → Bool)} {s s' : ℕ}
    (h : HasMCircuitOfSize F s) (hs : s ≤ s') : HasMCircuitOfSize F s' := by
  obtain ⟨t, ht, C, hC⟩ := h
  exact ⟨t, ht.trans hs, C, hC⟩

theorem HasCircuitOfSize.mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s s' : ℕ}
    (h : HasCircuitOfSize f s) (hs : s ≤ s') : HasCircuitOfSize f s' := by
  obtain ⟨t, ht, C, hC⟩ := h
  exact ⟨t, ht.trans hs, C, hC⟩

/-- Rewirings / projections `x ↦ x ∘ π` need no gates. -/
theorem hasMCircuitOfSize_rewire {n m : ℕ} (π : Fin m → Fin n) :
    HasMCircuitOfSize (fun x : Fin n → Bool => fun j => x (π j)) 0 := by
  refine ⟨0, le_rfl, (fun i => i.elim0, fun j => Fin.castAdd 0 (π j)), ?_⟩
  funext x j
  simp only [MCircuit.eval, wires_eq_wv, Fin.val_castAdd]
  exact wv_input x 0 _ (π j).2

/-- The identity map needs no gates. -/
theorem hasMCircuitOfSize_id (n : ℕ) : HasMCircuitOfSize (fun x : Fin n → Bool => x) 0 :=
  hasMCircuitOfSize_rewire id

/-- An input variable (projection) needs no gates. -/
theorem hasCircuitOfSize_var {n : ℕ} (v : Fin n) :
    HasCircuitOfSize (fun x : Fin n → Bool => x v) 0 := by
  refine ⟨0, le_rfl, (fun i => i.elim0, Fin.castAdd 0 v), ?_⟩
  funext x
  simp only [Circuit.eval, wires_eq_wv, Fin.val_castAdd]
  exact wv_input x 0 _ v.2

/-- A single output of a multi-output circuit. -/
theorem HasMCircuitOfSize.output {n m : ℕ} {F : (Fin n → Bool) → (Fin m → Bool)} {s : ℕ}
    (h : HasMCircuitOfSize F s) (j : Fin m) : HasCircuitOfSize (fun x => F x j) s := by
  obtain ⟨t, ht, C, rfl⟩ := h
  exact ⟨t, ht, (C.1, C.2 j), rfl⟩

/-- A single-output circuit, viewed as a multi-output circuit (all outputs equal). -/
theorem HasCircuitOfSize.toM {n : ℕ} {f : (Fin n → Bool) → Bool} {s : ℕ}
    (h : HasCircuitOfSize f s) (m : ℕ) :
    HasMCircuitOfSize (fun x (_ : Fin m) => f x) s := by
  obtain ⟨t, ht, C, rfl⟩ := h
  exact ⟨t, ht, (C.1, fun _ => C.2), rfl⟩

/-- For one output, single- and multi-output circuit sizes agree. -/
theorem hasMCircuitOfSize_one_iff {n : ℕ} (F : (Fin n → Bool) → (Fin 1 → Bool)) (s : ℕ) :
    HasMCircuitOfSize F s ↔ HasCircuitOfSize (fun x => F x 0) s := by
  refine ⟨fun h => h.output 0, fun h => ?_⟩
  have := h.toM 1
  convert this using 2 with x
  funext j
  rw [Subsingleton.elim j 0]

/-! ## Composition and iteration -/

/-- **Composition.** -/
theorem HasMCircuitOfSize.comp {a b c : ℕ} {F : (Fin a → Bool) → (Fin b → Bool)}
    {G : (Fin b → Bool) → (Fin c → Bool)} {s₁ s₂ : ℕ}
    (hF : HasMCircuitOfSize F s₁) (hG : HasMCircuitOfSize G s₂) :
    HasMCircuitOfSize (G ∘ F) (s₁ + s₂) := by
  obtain ⟨t₁, ht₁, ⟨g, oF⟩, rfl⟩ := hF
  obtain ⟨t₂, ht₂, ⟨h, oG⟩, rfl⟩ := hG
  refine ⟨t₁ + t₂, by omega, (seqGates g oF h, fun j =>
    ⟨seqWire oF (oG j).val, by have := seqWire_lt oF (oG j).2; omega⟩), ?_⟩
  funext x j
  simp only [MCircuit.eval, Function.comp, wires_eq_wv]
  rw [wv_seqGates_high x g oF h (oG j).2]
  congr 1; funext k; simp [MCircuit.eval, wires_eq_wv]

/-- Composition with a single-output circuit. -/
theorem HasMCircuitOfSize.comp_single {a b : ℕ} {F : (Fin a → Bool) → (Fin b → Bool)}
    {g : (Fin b → Bool) → Bool} {s₁ s₂ : ℕ}
    (hF : HasMCircuitOfSize F s₁) (hg : HasCircuitOfSize g s₂) :
    HasCircuitOfSize (g ∘ F) (s₁ + s₂) :=
  (hF.comp (hg.toM 1)).output 0

/-- **Iteration.** -/
theorem HasMCircuitOfSize.iterate {a : ℕ} {F : (Fin a → Bool) → (Fin a → Bool)} {s : ℕ}
    (hF : HasMCircuitOfSize F s) (T : ℕ) : HasMCircuitOfSize (F^[T]) (T * s) := by
  induction T with
  | zero =>
    rw [Function.iterate_zero, Nat.zero_mul]
    exact hasMCircuitOfSize_id a
  | succ T ih =>
    rw [Function.iterate_succ, Nat.succ_mul, Nat.add_comm]
    exact hF.comp ih

/-! ## Parallel combination -/

/-- **Parallel combination** of a single-output circuit and a multi-output circuit on the
same inputs. -/
theorem HasCircuitOfSize.cons {n m : ℕ} {f : (Fin n → Bool) → Bool}
    {F : (Fin n → Bool) → (Fin m → Bool)} {s₁ s₂ : ℕ}
    (hf : HasCircuitOfSize f s₁) (hF : HasMCircuitOfSize F s₂) :
    HasMCircuitOfSize (fun x => (Fin.cons (f x) (F x) : Fin (m + 1) → Bool)) (s₁ + s₂) := by
  obtain ⟨t₁, ht₁, ⟨g, o⟩, rfl⟩ := hf
  obtain ⟨t₂, ht₂, ⟨h, o₂⟩, rfl⟩ := hF
  let σ : Fin n → Fin (n + t₁) := Fin.castAdd t₁
  refine ⟨t₁ + t₂, by omega, (seqGates g σ h, Fin.cons ⟨o.val, by have := o.2; omega⟩
    (fun j => ⟨seqWire σ (o₂ j).val, by have := seqWire_lt σ (o₂ j).2; omega⟩)), ?_⟩
  funext x j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [MCircuit.eval, Circuit.eval, Fin.cons_zero, wires_eq_wv]
    exact wv_seqGates_low x g σ h o.2
  · simp only [MCircuit.eval, Fin.cons_succ, wires_eq_wv]
    rw [wv_seqGates_high x g σ h (o₂ j).2]
    congr 1
    funext k; exact wv_input x t₁ g k.2

/-- The empty map (no outputs) needs no gates. -/
theorem hasMCircuitOfSize_nil {n : ℕ} (F : (Fin n → Bool) → (Fin 0 → Bool)) :
    HasMCircuitOfSize F 0 :=
  ⟨0, le_rfl, (fun i => i.elim0, fun j => j.elim0), funext fun _ => funext fun j => j.elim0⟩

/-- **Parallel combination** of `m` single-output circuits of size `≤ s`. -/
theorem hasMCircuitOfSize_of_forall {n : ℕ} :
    ∀ {m : ℕ} (F : (Fin n → Bool) → (Fin m → Bool)) {s : ℕ},
      (∀ j, HasCircuitOfSize (fun x => F x j) s) → HasMCircuitOfSize F (m * s)
  | 0, F, s, _ => by simpa using hasMCircuitOfSize_nil F
  | m + 1, F, s, h => by
    have ih := hasMCircuitOfSize_of_forall (fun x j => F x j.succ) (fun j => h j.succ)
    have := (h 0).cons ih
    rw [show (m + 1) * s = s + m * s by ring]
    convert this using 2 with x
    exact (Fin.cons_self_tail (F x)).symm

/-! ## Juntas -/

/-- A constant function on `n > 0` inputs needs one gate. -/
theorem hasCircuitOfSize_const {n : ℕ} (hn : 0 < n) (c : Bool) :
    HasCircuitOfSize (fun _ : Fin n → Bool => c) 1 := by
  refine ⟨1, le_rfl, (fun i => (fun _ _ => c, ⟨0, by omega⟩, ⟨0, by omega⟩), Fin.last n), ?_⟩
  funext x
  simp only [Circuit.eval, wires_eq_wv, Fin.val_last]
  exact wv_gate x 1 _ 0

/-- The multiplexer `y ↦ if y 0 then y 1 else y 2`, with three gates. -/
def muxCircuit : Circuit 3 3 :=
  (mkGates 3 3 (fun i => if i = 0 then (· && ·) else if i = 1 then (fun a b => !a && b)
      else (· || ·))
    (fun i => if i = 0 then 0 else if i = 1 then 0 else 3)
    (fun i => if i = 0 then 1 else if i = 1 then 2 else 4)
    (fun i hi => by interval_cases i <;> simp) (fun i hi => by interval_cases i <;> simp),
    Fin.last 5)

theorem muxCircuit_eval : muxCircuit.eval = fun y => if y 0 then y 1 else y 2 := by
  funext y; revert y; decide

theorem hasCircuitOfSize_mux :
    HasCircuitOfSize (fun y : Fin 3 → Bool => if y 0 then y 1 else y 2) 3 :=
  ⟨3, le_rfl, muxCircuit, muxCircuit_eval⟩

/-- Shannon expansion: `g y = if y 0 then g (cons true (tail y)) else g (cons false (tail y))`,
assembled as circuits. Exact size bound `4 * 2 ^ k - 3`. -/
theorem hasCircuitOfSize_junta_aux {n : ℕ} (hn : 0 < n) :
    ∀ (k : ℕ) (g : (Fin k → Bool) → Bool) (ι : Fin k → Fin n),
      HasCircuitOfSize (fun x => g (fun i => x (ι i))) (4 * 2 ^ k - 3)
  | 0, g, ι => by
    have := hasCircuitOfSize_const hn (g (fun i => i.elim0))
    show HasCircuitOfSize _ 1
    convert this using 2 with x
    congr 1; funext i; exact i.elim0
  | k + 1, g, ι => by
    have h1 := hasCircuitOfSize_junta_aux hn k (fun z => g (Fin.cons true z)) (fun i => ι i.succ)
    have h0 := hasCircuitOfSize_junta_aux hn k (fun z => g (Fin.cons false z)) (fun i => ι i.succ)
    have hv := hasCircuitOfSize_var (ι 0)
    have h3 := hv.cons (h1.cons (h0.cons (hasMCircuitOfSize_nil (fun _ => Fin.elim0))))
    have hc := (h3.comp (hasCircuitOfSize_mux.toM 1)).output 0
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hc' := hc.mono (s' := 4 * 2 ^ (k + 1) - 3) (by rw [pow_succ]; omega)
    convert hc' using 2 with x
    simp only [Function.comp, Fin.cons_zero]
    have hx : (fun i => x (ι i)) = Fin.cons (x (ι 0)) (fun i => x (ι i.succ)) := by
      funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
    rw [hx]
    cases x (ι 0)
    · simp; rfl
    · simp

/-- Circuit size sufficient for any function of `k` input variables (independent of `n`). -/
def juntaSize (k : ℕ) : ℕ := 4 * 2 ^ k

/-- **Juntas.** A function of `n > 0` inputs that depends only on the `k` inputs `ι` has a
circuit with `juntaSize k` gates. -/
theorem hasCircuitOfSize_junta {n k : ℕ} (hn : 0 < n) (g : (Fin k → Bool) → Bool)
    (ι : Fin k → Fin n) :
    HasCircuitOfSize (fun x => g (fun i => x (ι i))) (juntaSize k) :=
  (hasCircuitOfSize_junta_aux hn k g ι).mono (by unfold juntaSize; omega)

/-- **Juntas**, stated for an arbitrary `f` with a factorization through `k` inputs. -/
theorem hasCircuitOfSize_of_junta {n k : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool)
    (ι : Fin k → Fin n) (g : (Fin k → Bool) → Bool) (hf : ∀ x, f x = g (fun i => x (ι i))) :
    HasCircuitOfSize f (juntaSize k) := by
  rw [show f = _ from funext hf]
  exact hasCircuitOfSize_junta hn g ι

/-! ## Local maps -/

/-- **Local maps.** If every output of `F` is a function of (at most) `k` inputs, then `F`
has a circuit with `m * juntaSize k` gates. -/
theorem hasMCircuitOfSize_local {n m k : ℕ} (hn : 0 < n) (F : (Fin n → Bool) → (Fin m → Bool))
    (ι : Fin m → Fin k → Fin n) (g : Fin m → (Fin k → Bool) → Bool)
    (hF : ∀ x j, F x j = g j (fun i => x (ι j i))) :
    HasMCircuitOfSize F (m * juntaSize k) :=
  hasMCircuitOfSize_of_forall F fun j =>
    hasCircuitOfSize_of_junta hn _ (ι j) (g j) fun x => hF x j

/-- **Local maps**, with the dependency data given output by output. -/
theorem hasMCircuitOfSize_local' {n m k : ℕ} (hn : 0 < n) (F : (Fin n → Bool) → (Fin m → Bool))
    (hF : ∀ j, ∃ (ι : Fin k → Fin n) (g : (Fin k → Bool) → Bool),
      ∀ x, F x j = g (fun i => x (ι i))) :
    HasMCircuitOfSize F (m * juntaSize k) := by
  choose ι g hg using hF
  exact hasMCircuitOfSize_local hn F ι g fun x j => hg j x

/-- **Local maps on a finite type of input positions.** Inputs are indexed by a `Fintype`
`α` (transported along `Fintype.equivFin α`). -/
theorem hasMCircuitOfSize_local_fintype {α : Type*} [Fintype α] {m k : ℕ}
    (hα : 0 < Fintype.card α) (F : (α → Bool) → (Fin m → Bool))
    (hF : ∀ j, ∃ (ι : Fin k → α) (g : (Fin k → Bool) → Bool),
      ∀ x, F x j = g (fun i => x (ι i))) :
    HasMCircuitOfSize (fun x : Fin (Fintype.card α) → Bool => F (x ∘ Fintype.equivFin α))
      (m * juntaSize k) := by
  refine hasMCircuitOfSize_local' hα _ fun j => ?_
  obtain ⟨ι, g, hg⟩ := hF j
  exact ⟨fun i => Fintype.equivFin α (ι i), g, fun x => hg _⟩

end Pnp.Circuits
