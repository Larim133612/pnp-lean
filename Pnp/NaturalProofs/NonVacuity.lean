import Pnp.NaturalProofs.Barrier
import Pnp.PPoly.NonVacuity

/-!
# Sanity checks for the natural-proofs definitions

The barrier theorem says the three conditions *constructive*, *large* and *useful against
P/poly* cannot hold together if secure pseudorandom functions exist. Here we check that the
conditions are not trivially contradictory in pairs:

* `constructive_univ`, `large_univ`: the property "all functions" is constructive and large.
* `shannon_large`, `shannon_useful`: Shannon's property "has no circuit with `2ⁿ / (10 n)`
  gates" is large (density `≥ 1/2`) and useful against P/poly (`shannon_large_useful`).
  Whether it is also constructive is (a form of) the Minimum Circuit Size Problem; by the
  barrier theorem it is not, if secure pseudorandom functions in P/poly exist.
-/

namespace Pnp.NaturalProofs

open Pnp.Circuits Classical Filter

noncomputable section

/-! ## The trivial property -/

/-- The constant-`true` function on `N ≥ 1` inputs has a one-gate circuit. -/
theorem hasCircuitOfSize_const_true {N : ℕ} (hN : 0 < N) :
    HasCircuitOfSize (fun _ : Fin N → Bool => true) 1 := by
  refine ⟨1, le_rfl, (fun _ => (fun _ _ => true, ⟨0, by omega⟩, ⟨0, by omega⟩), Fin.last N), ?_⟩
  funext x
  simp [Circuit.eval, wires]

theorem constructive_univ : Constructive fun _ => Set.univ :=
  ⟨Polynomial.C 1, fun n => ⟨_, by simpa using hasCircuitOfSize_const_true (by positivity :
    0 < 2 ^ n), fun _ => by simp⟩⟩

theorem large_univ : Large fun _ => Set.univ :=
  ⟨Polynomial.C 1, fun n => by simp⟩

/-! ## Shannon's property -/

/-- Functions with a circuit of size `≤ s` are at most as many as the circuit count bound. -/
theorem card_easy_le (n s : ℕ) :
    (Finset.univ.filter fun f : BoolFun n => HasCircuitOfSize f s).card ≤
      (s + 1) * ((n + s) * (16 * (n + s) ^ 2) ^ s) := by
  let S : Finset (BoolFun n) :=
    (Finset.range (s + 1)).biUnion fun t => Finset.univ.image (Circuit.eval (n := n) (s := t))
  have hsub : (Finset.univ.filter fun f : BoolFun n => HasCircuitOfSize f s) ⊆ S := by
    intro f hf
    obtain ⟨t, ht, C, rfl⟩ := (Finset.mem_filter.1 hf).2
    simp only [S, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨t, by omega, C, rfl⟩
  calc _ ≤ S.card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ Finset.range (s + 1),
          (Finset.univ.image (Circuit.eval (n := n) (s := t))).card := Finset.card_biUnion_le
    _ ≤ ∑ t ∈ Finset.range (s + 1), (n + s) * (16 * (n + s) ^ 2) ^ s := by
        apply Finset.sum_le_sum
        intro t ht
        exact Finset.card_image_le.trans
          (by rw [Finset.card_univ]; exact card_circuit_le n t s (by simp at ht; omega))
    _ = (s + 1) * ((n + s) * (16 * (n + s) ^ 2) ^ s) := by simp

/-- At most half of all functions have small circuits (Shannon range). -/
theorem two_mul_count_le {n s : ℕ} (hn : 5 ≤ n) (hs : s * (10 * n) ≤ 2 ^ n) :
    2 * ((s + 1) * ((n + s) * (16 * (n + s) ^ 2) ^ s)) ≤ 2 ^ 2 ^ n := by
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
  have hexp : n + n + (2 * n + 4) * s + 1 ≤ 2 ^ n := by nlinarith
  calc 2 * ((s + 1) * ((n + s) * (16 * (n + s) ^ 2) ^ s))
      ≤ 2 * 2 ^ (n + n + (2 * n + 4) * s) := by gcongr
    _ = 2 ^ (n + n + (2 * n + 4) * s + 1) := by ring
    _ ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hexp

/-- Shannon's property: for `n ≥ 5`, no circuit with `2ⁿ / (10 n)` gates (all functions for
`n < 5`). -/
def shannonProp (n : ℕ) : Set (BoolFun n) :=
  {f | 5 ≤ n → ¬ HasCircuitOfSize f (2 ^ n / (10 * n))}

theorem shannon_large : Large shannonProp := by
  refine ⟨Polynomial.C 2, fun n => ?_⟩
  rw [Polynomial.eval_C]
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BoolFun n))) (· ∈ shannonProp n)
  rw [Finset.card_univ, card_boolFun] at htot
  by_cases hn : 5 ≤ n
  · have heq : (Finset.univ.filter fun f : BoolFun n => ¬ f ∈ shannonProp n) =
        Finset.univ.filter fun f => HasCircuitOfSize f (2 ^ n / (10 * n)) := by
      ext f; simp [shannonProp, hn]
    have h1 : (Finset.univ.filter fun f : BoolFun n => ¬ f ∈ shannonProp n).card ≤
        (2 ^ n / (10 * n) + 1) * ((n + 2 ^ n / (10 * n)) *
          (16 * (n + 2 ^ n / (10 * n)) ^ 2) ^ (2 ^ n / (10 * n))) := by
      rw [heq]; convert card_easy_le n (2 ^ n / (10 * n))
    have h2 := two_mul_count_le hn (Nat.div_mul_le_self (2 ^ n) (10 * n))
    omega
  · have heq : (Finset.univ.filter fun f : BoolFun n => ¬ f ∈ shannonProp n) = ∅ := by
      ext f; simp [shannonProp, hn]
    rw [heq, Finset.card_empty] at htot
    omega

theorem shannon_useful : UsefulAgainstPPoly shannonProp := by
  intro p N
  obtain ⟨c, d, hcd⟩ := Pnp.PPoly.eval_le_mul_pow p
  obtain ⟨n, hn⟩ := ((Pnp.PPoly.eventually_mul_pow_le_two_pow (10 * c) (d + 1)).and
    (eventually_ge_atTop (max N 5))).exists
  have hn5 : 5 ≤ n := le_of_max_le_right hn.2
  refine ⟨n, le_of_max_le_left hn.2, fun f hf hsmall => hf hn5 (hsmall.mono ?_)⟩
  rw [Nat.le_div_iff_mul_le (by omega)]
  calc p.eval n * (10 * n) ≤ c * n ^ d * (10 * n) := by gcongr; exact hcd n (by omega)
    _ = 10 * c * n ^ (d + 1) := by ring
    _ ≤ 2 ^ n := hn.1

/-- Largeness and usefulness are compatible; the barrier concerns constructivity. -/
theorem shannon_large_useful : Large shannonProp ∧ UsefulAgainstPPoly shannonProp :=
  ⟨shannon_large, shannon_useful⟩

end

end Pnp.NaturalProofs
