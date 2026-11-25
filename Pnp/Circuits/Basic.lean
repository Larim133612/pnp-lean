import Mathlib

/-!
# Boolean circuits (M1)

A circuit on `n` inputs with `s` gates is a straight-line program: gate `i`
(for `i < s`) applies an arbitrary binary Boolean operation to two earlier
wires among the `n + i` wires available so far (the `n` inputs and the
outputs of gates `0, …, i-1`). One of the `n + s` wires is the output.

This is the standard "fan-in 2, full binary basis B₂" model.
-/

namespace Pnp.Circuits

/-- A gate that may read any of the first `m` wires: an operation and two inputs. -/
abbrev Gate (m : ℕ) := (Bool → Bool → Bool) × Fin m × Fin m

/-- The gate list of a circuit with `n` inputs and `s` gates. -/
abbrev Gates (n s : ℕ) := (i : Fin s) → Gate (n + i.val)

/-- A circuit with `n` inputs and exactly `s` gates, together with an output wire. -/
abbrev Circuit (n s : ℕ) := Gates n s × Fin (n + s)

/-- Values on all `n + s` wires, for input `x`. -/
def wires {n : ℕ} (x : Fin n → Bool) : (s : ℕ) → Gates n s → Fin (n + s) → Bool
  | 0, _ => x
  | s + 1, g =>
    let w := wires x s (fun i => g i.castSucc)
    let gt := g (Fin.last s)
    Fin.snoc (α := fun _ => Bool) w (gt.1 (w gt.2.1) (w gt.2.2))

/-- The Boolean function computed by a circuit. -/
def Circuit.eval {n s : ℕ} (C : Circuit n s) : (Fin n → Bool) → Bool :=
  fun x => wires x s C.1 C.2

/-- `f` has a circuit with at most `s` gates. -/
def HasCircuitOfSize {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ t ≤ s, ∃ C : Circuit n t, C.eval = f

/-- Sanity check: a one-gate circuit computing `x₀ ∧ x₁`. -/
def andCircuit : Circuit 2 1 :=
  (fun _ => ((· && ·), ⟨0, by omega⟩, ⟨1, by omega⟩), Fin.last 2)

example : andCircuit.eval = fun x => x 0 && x 1 := by
  funext x; decide +revert

/-! ## Counting -/

theorem card_gate (m : ℕ) : Fintype.card (Gate m) = 16 * m ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_fun, Fintype.card_bool]
  ring

theorem card_circuit (n t : ℕ) :
    Fintype.card (Circuit n t) = (∏ i : Fin t, 16 * (n + i.val) ^ 2) * (n + t) := by
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [card_gate]

theorem card_circuit_le (n t s : ℕ) (hts : t ≤ s) :
    Fintype.card (Circuit n t) ≤ (n + s) * (16 * (n + s) ^ 2) ^ s := by
  rw [card_circuit, mul_comm]
  have hprod : (∏ i : Fin t, 16 * (n + i.val) ^ 2) ≤ (16 * (n + s) ^ 2) ^ t := by
    have := Finset.prod_le_pow_card (s := (Finset.univ : Finset (Fin t)))
      (f := fun i : Fin t => 16 * (n + i.val) ^ 2) (n := 16 * (n + s) ^ 2)
      (fun i _ => by
        have : i.val ≤ s := by omega
        gcongr)
    simpa using this
  have hpow : (16 * (n + s) ^ 2) ^ t ≤ (16 * (n + s) ^ 2) ^ s := by
    by_cases h0 : n + s = 0
    · have ht0 : t = 0 := by omega
      have hs0 : s = 0 := by omega
      subst ht0 hs0; simp
    · apply Nat.pow_le_pow_right _ hts
      positivity
  calc (n + t) * ∏ i : Fin t, 16 * (n + i.val) ^ 2
      ≤ (n + s) * (16 * (n + s) ^ 2) ^ s := by
        gcongr
        exact hprod.trans hpow

/-- **Counting bound (general form).** If the number of circuits of size `≤ s` is
smaller than the number `2^(2^n)` of Boolean functions on `n` variables, some
function has no circuit of size `≤ s`. -/
theorem exists_hard_function_of_count {n s : ℕ}
    (h : (s + 1) * ((n + s) * (16 * (n + s) ^ 2) ^ s) < 2 ^ 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ¬ HasCircuitOfSize f s := by
  classical
  let S : Finset ((Fin n → Bool) → Bool) :=
    (Finset.range (s + 1)).biUnion fun t => Finset.univ.image (Circuit.eval (n := n) (s := t))
  have hS : S.card < Fintype.card ((Fin n → Bool) → Bool) := by
    calc S.card ≤ ∑ t ∈ Finset.range (s + 1),
          (Finset.univ.image (Circuit.eval (n := n) (s := t))).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ Finset.range (s + 1), (n + s) * (16 * (n + s) ^ 2) ^ s := by
          apply Finset.sum_le_sum
          intro t ht
          exact Finset.card_image_le.trans
            (by rw [Finset.card_univ]; exact card_circuit_le n t s (by simp at ht; omega))
      _ = (s + 1) * ((n + s) * (16 * (n + s) ^ 2) ^ s) := by simp
      _ < 2 ^ 2 ^ n := h
      _ = Fintype.card ((Fin n → Bool) → Bool) := by
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  obtain ⟨f, hf⟩ : ∃ f, f ∉ S := by
    by_contra hc
    push Not at hc
    have : S = Finset.univ := Finset.eq_univ_of_forall hc
    rw [this, Finset.card_univ] at hS
    exact lt_irrefl _ hS
  refine ⟨f, ?_⟩
  rintro ⟨t, ht, C, rfl⟩
  apply hf
  simp only [S, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact ⟨t, by omega, C, rfl⟩

/-! ## Shannon's lower bound -/

lemma six_mul_le_two_pow {n : ℕ} (hn : 5 ≤ n) : 6 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k _ ih => rw [pow_succ]; omega

/-- Arithmetic core: for `n ≥ 5` and `s ≤ 2^n / (10 n)`, circuits of size `≤ s`
are fewer than Boolean functions. -/
theorem count_lt {n s : ℕ} (hn : 5 ≤ n) (hs : s * (10 * n) ≤ 2 ^ n) :
    (s + 1) * ((n + s) * (16 * (n + s) ^ 2) ^ s) < 2 ^ 2 ^ n := by
  have h6 := six_mul_le_two_pow hn
  have hns : n + s ≤ 2 ^ n := by nlinarith
  have hs1 : s + 1 ≤ 2 ^ n := by nlinarith
  have step : (s + 1) * ((n + s) * (16 * (n + s) ^ 2) ^ s) ≤
      2 ^ (n + n + (2 * n + 4) * s) := by
    calc (s + 1) * ((n + s) * (16 * (n + s) ^ 2) ^ s)
        ≤ 2 ^ n * (2 ^ n * (16 * (2 ^ n) ^ 2) ^ s) := by gcongr
      _ = 2 ^ (n + n + (2 * n + 4) * s) := by
        rw [show (16 : ℕ) * (2 ^ n) ^ 2 = 2 ^ (2 * n + 4) by
              rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]; ring_nf,
          ← pow_mul, ← pow_add, ← pow_add]
        congr 1; ring
  have hexp : n + n + (2 * n + 4) * s < 2 ^ n := by nlinarith
  exact step.trans_lt (Nat.pow_lt_pow_right (by norm_num) hexp)

/-- **Shannon (1949).** For every `n ≥ 5` there is a Boolean function on `n`
variables that has no circuit (fan-in 2, full binary basis) with at most
`2^n / (10 n)` gates. -/
theorem shannon_lower_bound {n s : ℕ} (hn : 5 ≤ n) (hs : s * (10 * n) ≤ 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ¬ HasCircuitOfSize f s :=
  exists_hard_function_of_count (count_lt hn hs)

/-- Same statement with an explicit division. -/
theorem shannon_lower_bound' {n : ℕ} (hn : 5 ≤ n) :
    ∃ f : (Fin n → Bool) → Bool, ¬ HasCircuitOfSize f (2 ^ n / (10 * n)) :=
  shannon_lower_bound hn (Nat.div_mul_le_self _ _)

end Pnp.Circuits
