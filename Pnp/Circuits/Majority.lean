import Pnp.Circuits.Multi

/-!
# Circuits for majority and the Goldreich–Levin inverter

* `maj`: strict majority of `m` bits. It has a circuit with `majSize m = O(m²)` gates
  (`hasCircuitOfSize_maj`), built by a threshold dynamic program: after reading `d` inputs the
  state holds the inputs together with the bits `T_k = [k ≤ #{i < d | x_i}]` for `k ≤ m`, and
  one step updates `T_k ← T_k ∨ (x_d ∧ T_{k-1})` (each new bit is a junta on three wires).
* `glInv`: the shape of the Goldreich–Levin inverter, whose output coordinate `i` is the
  majority over `j` of `B(y, c i j) ⊕ d j`. If `B` has a circuit with `sB` gates, then `glInv`
  has a multi-output circuit with `glInvSize n m sB = n (m (sB + 3) + majSize m)` gates
  (`hasMCircuitOfSize_glInv`), and `glInvSize n m sB ≤ 102 n m² (n + sB + 1)` for `m > 0`
  (`glInvSize_le`).
-/

namespace Pnp.Circuits

open Classical

/-- Strict majority of `m` bits. -/
def maj {m : ℕ} (w : Fin m → Bool) : Bool :=
  decide (m < 2 * (Finset.univ.filter (fun j => w j = true)).card)

/-! ## The threshold dynamic program -/

/-- Indicator of input `i` (junk `0` beyond `m`). -/
def bitN {m : ℕ} (x : Fin m → Bool) (i : ℕ) : ℕ :=
  if h : i < m then (if x ⟨i, h⟩ then 1 else 0) else 0

/-- Number of true inputs among the first `d`. -/
def cnt {m : ℕ} (x : Fin m → Bool) (d : ℕ) : ℕ := ∑ i ∈ Finset.range d, bitN x i

theorem cnt_self {m : ℕ} (x : Fin m → Bool) :
    cnt x m = (Finset.univ.filter (fun j => x j = true)).card := by
  rw [Finset.card_filter, cnt, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [bitN, i.2]

/-- The DP state after reading `d` inputs: the inputs and the threshold bits. -/
def thrState {m : ℕ} (x : Fin m → Bool) (d : ℕ) : Fin (m + (m + 1)) → Bool :=
  Fin.append x (fun k : Fin (m + 1) => decide (k.val ≤ cnt x d))

/-- One DP step, reading input `j`. -/
def majStep {m : ℕ} (j : Fin m) (z : Fin (m + (m + 1)) → Bool) : Fin (m + (m + 1)) → Bool :=
  Fin.append (fun i => z (Fin.castAdd (m + 1) i))
    (fun k : Fin (m + 1) => if hk : k.val = 0 then z (Fin.natAdd m k) else
      z (Fin.natAdd m k) || (z (Fin.castAdd (m + 1) j) &&
        z (Fin.natAdd m ⟨k.val - 1, by omega⟩)))

/-- The first `d` DP steps. -/
def majSteps {m : ℕ} : ℕ → (Fin (m + (m + 1)) → Bool) → Fin (m + (m + 1)) → Bool
  | 0 => id
  | d + 1 => fun z => if h : d < m then majStep ⟨d, h⟩ (majSteps d z) else majSteps d z

theorem majSteps_thrState {m : ℕ} (x : Fin m → Bool) :
    ∀ d, d ≤ m → majSteps d (thrState x 0) = thrState x d
  | 0, _ => rfl
  | d + 1, hd => by
    have h : d < m := by omega
    simp only [majSteps, dif_pos h]
    rw [majSteps_thrState x d (by omega)]
    funext p
    refine Fin.addCases (fun i => ?_) (fun k => ?_) p
    · simp [majStep, thrState]
    · have hc : cnt x (d + 1) = cnt x d + (if x ⟨d, h⟩ then 1 else 0) := by
        simp [cnt, Finset.sum_range_succ, bitN, h]
      simp only [majStep, thrState, Fin.append_right, Fin.append_left, hc]
      by_cases hk : k.val = 0
      · simp [hk]
      · rw [dif_neg hk]
        cases x ⟨d, h⟩ <;> simp; omega

theorem hasMCircuitOfSize_majStep {m : ℕ} (j : Fin m) :
    HasMCircuitOfSize (majStep j) ((m + (m + 1)) * juntaSize 3) := by
  refine hasMCircuitOfSize_local' (by omega) _ fun p => ?_
  refine Fin.addCases (fun i => ?_) (fun k => ?_) p
  · exact ⟨fun _ => Fin.castAdd (m + 1) i, fun v => v 0, fun z => by simp [majStep]⟩
  · by_cases hk : k.val = 0
    · exact ⟨fun _ => Fin.natAdd m k, fun v => v 0, fun z => by
        simp only [majStep, Fin.append_right, dif_pos hk]⟩
    · exact ⟨![Fin.natAdd m k, Fin.castAdd (m + 1) j, Fin.natAdd m ⟨k.val - 1, by omega⟩],
        fun v => v 0 || (v 1 && v 2), fun z => by
          simp only [majStep, Fin.append_right, dif_neg hk]; rfl⟩

theorem hasMCircuitOfSize_majSteps {m : ℕ} :
    ∀ d, d ≤ m → HasMCircuitOfSize (majSteps (m := m) d) (d * ((m + (m + 1)) * juntaSize 3))
  | 0, _ => by rw [Nat.zero_mul]; exact hasMCircuitOfSize_id _
  | d + 1, hd => by
    have h : d < m := by omega
    have h1 := hasMCircuitOfSize_majSteps (m := m) d (by omega)
    have h2 := hasMCircuitOfSize_majStep (m := m) ⟨d, h⟩
    have h3 := h1.comp h2
    have e : majSteps (m := m) (d + 1) = majStep ⟨d, h⟩ ∘ majSteps d := by
      funext z; simp only [majSteps, dif_pos h, Function.comp]
    rw [Nat.succ_mul, e]
    exact h3

/-- Circuit size for the majority of `m` bits. -/
def majSize (m : ℕ) : ℕ := (2 * m + 1) + m * ((2 * m + 1) * 32)

/-- **Majority** of `m > 0` bits has a circuit with `majSize m = O(m²)` gates. -/
theorem hasCircuitOfSize_maj {m : ℕ} (hm : 0 < m) :
    HasCircuitOfSize (maj (m := m)) (majSize m) := by
  have hinit : HasMCircuitOfSize (fun x : Fin m → Bool => thrState x 0) ((m + (m + 1)) * 1) := by
    refine hasMCircuitOfSize_of_forall _ fun p => ?_
    refine Fin.addCases (fun i => ?_) (fun k => ?_) p
    · have := hasCircuitOfSize_var i
      convert this.mono (Nat.zero_le 1) using 2 with x
      simp [thrState]
    · have := hasCircuitOfSize_const hm (decide (k.val ≤ 0))
      convert this using 2 with x
      simp [thrState, cnt]
  have h := (hinit.comp (hasMCircuitOfSize_majSteps m le_rfl)).output
    (Fin.natAdd m ⟨m / 2 + 1, by omega⟩)
  have hle : (m + (m + 1)) * 1 + m * ((m + (m + 1)) * juntaSize 3) ≤ majSize m := by
    rw [show m + (m + 1) = 2 * m + 1 by omega, majSize, juntaSize]; norm_num
  convert h.mono hle using 2 with x
  show _ = majSteps m (thrState x 0) _
  rw [majSteps_thrState x m le_rfl, thrState, Fin.append_right, maj, ← cnt_self]
  exact decide_eq_decide.2 (by dsimp only; omega)

/-! ## The Goldreich–Levin inverter -/

/-- XOR with a constant: one gate. -/
theorem hasCircuitOfSize_xor_const (b : Bool) :
    HasCircuitOfSize (fun v : Fin 1 → Bool => xor (v 0) b) 1 := by
  refine ⟨1, le_rfl, (fun _ => (fun a _ => xor a b, ⟨0, by omega⟩, ⟨0, by omega⟩),
    Fin.last 1), ?_⟩
  funext v
  simp only [Circuit.eval, wires_eq_wv, Fin.val_last]
  exact (wv_gate v 1 _ 0).trans
    (congrArg (fun t => xor t b) (wv_input v 1 _ (show 0 < 1 by omega)))

/-- Appending a constant string to the input: two gates (the constants `true`, `false`). -/
theorem hasMCircuitOfSize_append_const {k n : ℕ} (hk : 0 < k) (r : Fin n → Bool) :
    HasMCircuitOfSize (fun y : Fin k → Bool => (Fin.append y r : Fin (k + n) → Bool)) 2 := by
  have h0 := (hasCircuitOfSize_const hk true).cons
    ((hasCircuitOfSize_const hk false).cons (hasMCircuitOfSize_id k))
  let π : Fin (k + n) → Fin (k + 1 + 1) :=
    Fin.append (fun i => i.succ.succ) (fun i => if r i then 0 else 1)
  have h := (h0.comp (hasMCircuitOfSize_rewire π)).mono (s' := 2) (by norm_num)
  convert h using 2 with y
  funext p
  refine Fin.addCases (fun i => ?_) (fun i => ?_) p
  · simp [π]
  · simp only [Function.comp, Fin.append_right, π]
    cases r i <;> simp

/-- Inverter output coordinate `i`: majority over `j` of `B(y, c i j) xor d j`. -/
def glInv {k n m : ℕ} (B : (Fin (k + n) → Bool) → Bool) (c : Fin n → Fin m → (Fin n → Bool))
    (d : Fin m → Bool) (y : Fin k → Bool) : Fin n → Bool :=
  fun i => maj (fun j => xor (B (Fin.append y (c i j))) (d j))

/-- Circuit size for the Goldreich–Levin inverter. -/
def glInvSize (n m sB : ℕ) : ℕ := n * (m * (sB + 3) + majSize m)

/-- **The Goldreich–Levin inverter** has a circuit with `glInvSize n m sB` gates. -/
theorem hasMCircuitOfSize_glInv {k n m sB : ℕ} (hk : 0 < k) (hm : 0 < m)
    {B : (Fin (k + n) → Bool) → Bool} (hB : HasCircuitOfSize B sB)
    (c : Fin n → Fin m → (Fin n → Bool)) (d : Fin m → Bool) :
    HasMCircuitOfSize (glInv B c d) (glInvSize n m sB) := by
  refine hasMCircuitOfSize_of_forall _ fun i => ?_
  have hj : ∀ j, HasCircuitOfSize (fun y : Fin k → Bool => xor (B (Fin.append y (c i j))) (d j))
      (sB + 3) := fun j => by
    have h := ((hasMCircuitOfSize_append_const hk (c i j)).comp (hB.toM 1)).comp_single
      (hasCircuitOfSize_xor_const (d j))
    exact h.mono (by omega)
  have h := (hasMCircuitOfSize_of_forall _ hj).comp_single (hasCircuitOfSize_maj hm)
  exact h

/-- A simple closed-form upper bound on `glInvSize`. -/
theorem glInvSize_le {n m sB : ℕ} (hm : 0 < m) :
    glInvSize n m sB ≤ 102 * n * m ^ 2 * (n + sB + 1) := by
  have h1 : m * (sB + 3) ≤ 3 * (m ^ 2 * (n + sB + 1)) := by
    have : m ≤ m ^ 2 := by nlinarith
    nlinarith
  have h2 : majSize m ≤ 99 * (m ^ 2 * (n + sB + 1)) := by
    have : m ≤ m ^ 2 := by nlinarith
    have : m ^ 2 ≤ m ^ 2 * (n + sB + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold majSize; nlinarith
  unfold glInvSize
  calc n * (m * (sB + 3) + majSize m) ≤ n * (102 * (m ^ 2 * (n + sB + 1))) := by
        gcongr; omega
    _ = 102 * n * m ^ 2 * (n + sB + 1) := by ring

end Pnp.Circuits
