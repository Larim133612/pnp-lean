import Pnp.Monotone.Razborov
import Pnp.Monotone.Construct

/-!
# An explicit superpolynomial monotone lower bound for CLIQUE (M3e)

We instantiate `razborov_alon_boppana_gen` with explicit parameters. For `ℓ ≥ 2` take
* plucking parameter `p = ℓ + 1` (so `L = ℓ! · ℓ^ℓ ≤ ℓ^ℓ · ℓ^ℓ`),
* clique size `K ℓ = 2 ℓ⁶ + 1` (so negative tests use `k - 1 = 2ℓ⁶` colours),
* number of vertices `M ℓ = 2 ℓ⁴ · K ℓ + ℓ = 4ℓ¹⁰ + 2ℓ⁴ + ℓ`.

Then every monotone circuit computing `CLIQUE(M ℓ, K ℓ)` has at least `2^ℓ` gates
(`monotone_clique_lower_bound`). Since `M ℓ ≤ 7 ℓ¹⁰`, i.e. `ℓ ≥ (M/7)^{1/10}`,
this is a size lower bound `2^{Ω(m^{1/10})}` in the number `m` of vertices, which is
superpolynomial in `m` (and in the number `m(m-1)/2` of input edges).

Both disjuncts of the Razborov–Alon–Boppana inequality are ruled out for `s < 2^ℓ`:
* positive side: `C(M,K) · C(K,ℓ+1) = C(M,ℓ+1) · C(M-ℓ-1,K-ℓ-1)` and
  `(M-ℓ)^{ℓ+1} ≤ (ℓ+1)! C(M,ℓ+1)`, `(ℓ+1)! C(K,ℓ+1) ≤ K^{ℓ+1}`, so the first
  disjunct forces `(2ℓ⁴K)^{ℓ+1} ≤ s · ℓ^{4ℓ} · K^{ℓ+1}`;
* negative side: with `r = 2ℓ⁶`, `r^M - ℓ² r^{M-1} = r^ℓ (r - ℓ²) r^{M-ℓ-1}` and
  `r^ℓ = 2^ℓ ℓ^{6ℓ}`, so the second disjunct forces
  `2^ℓ ℓ^{6ℓ} (2ℓ⁶ - ℓ²) ≤ s · ℓ^{4ℓ} · ℓ^{2ℓ+2}`.
-/

namespace Pnp.Monotone

open Finset

/-- Clique size used in the explicit lower bound: `K ℓ = 2 ℓ⁶ + 1`. -/
def cliqueK (ℓ : ℕ) : ℕ := 2 * ℓ ^ 6 + 1

/-- Number of vertices used in the explicit lower bound: `M ℓ = 2 ℓ⁴ · K ℓ + ℓ`. -/
def cliqueM (ℓ : ℕ) : ℕ := 2 * ℓ ^ 4 * cliqueK ℓ + ℓ

lemma cliqueM_le (ℓ : ℕ) : cliqueM ℓ ≤ 7 * ℓ ^ 10 := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp [cliqueM]
  · have h1 : ℓ ≤ ℓ ^ 10 := Nat.le_self_pow (by norm_num) ℓ
    have h2 : ℓ ^ 4 ≤ ℓ ^ 10 := Nat.pow_le_pow_right hℓ (by norm_num)
    have : cliqueM ℓ = 4 * ℓ ^ 10 + 2 * ℓ ^ 4 + ℓ := by unfold cliqueM cliqueK; ring
    omega

lemma two_le_cliqueK {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 2 ≤ cliqueK ℓ := by
  have : 1 ≤ ℓ ^ 6 := Nat.one_le_pow _ _ hℓ
  unfold cliqueK; omega

lemma cliqueK_le_cliqueM {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : cliqueK ℓ ≤ cliqueM ℓ := by
  have : 1 ≤ ℓ ^ 4 := Nat.one_le_pow _ _ hℓ
  unfold cliqueM
  nlinarith

/-- **Explicit monotone lower bound for CLIQUE (Razborov; Alon–Boppana).** For `ℓ ≥ 2`,
every monotone circuit (AND/OR gates, fan-in 2) that computes `CLIQUE(M ℓ, K ℓ)`
— whether a graph on `M ℓ = 2ℓ⁴(2ℓ⁶+1) + ℓ` vertices has a clique of size
`K ℓ = 2ℓ⁶ + 1` — reading the graph through any off-diagonal edge labelling, has at
least `2^ℓ` gates. As `M ℓ ≤ 7 ℓ¹⁰` (`cliqueM_le`), this is a lower bound of
`2^{Ω(m^{1/10})}` gates in the number `m` of vertices: superpolynomial in the input
size. (Non-vacuity: such circuits exist, see `exists_computesClique`.) -/
theorem monotone_clique_lower_bound {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {N s : ℕ}
    {lab : Fin N → Fin (cliqueM ℓ) × Fin (cliqueM ℓ)} (hlab : OffDiag lab)
    (C : MCircuit N s) (hC : ComputesClique lab (cliqueK ℓ) C) : 2 ^ ℓ ≤ s := by
  by_contra hs
  push Not at hs
  set a := ℓ ^ ℓ with ha_def
  have ha : 0 < a := Nat.pow_pos (by omega)
  have hL : ℓ.factorial * (ℓ + 1 - 1) ^ ℓ ≤ a * a := by
    rw [Nat.add_sub_cancel]
    exact Nat.mul_le_mul_right _ (Nat.factorial_le_pow ℓ)
  have hK2 := two_le_cliqueK (by omega : 1 ≤ ℓ)
  have hKM := cliqueK_le_cliqueM (by omega : 1 ≤ ℓ)
  have hℓ4 : 1 ≤ ℓ ^ 4 := Nat.one_le_pow _ _ (by omega)
  rcases razborov_alon_boppana_gen (by omega) hℓ (by omega : 2 ≤ ℓ + 1) hL hlab C hC with h | h
  · -- positive side
    set M := cliqueM ℓ with hM
    set K := cliqueK ℓ with hK
    have hqK : ℓ + 1 ≤ K := by
      have : ℓ ≤ ℓ ^ 6 := Nat.le_self_pow (by norm_num) ℓ
      rw [hK]; unfold cliqueK; omega
    have hcm := Nat.choose_mul (n := M) (k := K) hqK
    have hB : 0 < (M - (ℓ + 1)).choose (K - (ℓ + 1)) := Nat.choose_pos (by omega)
    generalize (M - (ℓ + 1)).choose (K - (ℓ + 1)) = B at h hcm hB
    have h1 : M.choose (ℓ + 1) * B ≤ (s * (a * a) ^ 2 * K.choose (ℓ + 1)) * B := by
      rw [← hcm]
      calc M.choose K * K.choose (ℓ + 1) ≤ s * ((a * a) ^ 2 * B) * K.choose (ℓ + 1) :=
            Nat.mul_le_mul_right _ h
        _ = (s * (a * a) ^ 2 * K.choose (ℓ + 1)) * B := by ring
    have h2 := Nat.le_of_mul_le_mul_right h1 hB
    have d1 := Nat.pow_sub_le_descFactorial M (ℓ + 1)
    rw [Nat.descFactorial_eq_factorial_mul_choose] at d1
    have d2 := Nat.descFactorial_le_pow K (ℓ + 1)
    rw [Nat.descFactorial_eq_factorial_mul_choose] at d2
    have hM1 : M + 1 - (ℓ + 1) = 2 * ℓ ^ 4 * K := by simp only [hM, hK, cliqueM]; omega
    rw [hM1, show (2 * ℓ ^ 4 * K) ^ (ℓ + 1) = 2 * 2 ^ ℓ * (a ^ 4 * ℓ ^ 4) * K ^ (ℓ + 1) by
      rw [ha_def]; ring] at d1
    have hKq : 0 < K ^ (ℓ + 1) := Nat.pow_pos (by omega)
    have key : 2 * 2 ^ ℓ * (a ^ 4 * ℓ ^ 4) * K ^ (ℓ + 1) ≤ s * a ^ 4 * K ^ (ℓ + 1) :=
      calc _ ≤ (ℓ + 1).factorial * M.choose (ℓ + 1) := d1
        _ ≤ (ℓ + 1).factorial * (s * (a * a) ^ 2 * K.choose (ℓ + 1)) :=
            Nat.mul_le_mul_left _ h2
        _ = s * a ^ 4 * ((ℓ + 1).factorial * K.choose (ℓ + 1)) := by ring
        _ ≤ s * a ^ 4 * K ^ (ℓ + 1) := Nat.mul_le_mul_left _ d2
    have ha4 : 0 < a ^ 4 := Nat.pow_pos ha
    generalize a ^ 4 = A at key ha4
    generalize K ^ (ℓ + 1) = X at key hKq
    generalize (2 : ℕ) ^ ℓ = T at key hs
    have : s * A * X < T * A * X :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hs ha4) hKq
    have : T * A * X ≤ 2 * T * (A * ℓ ^ 4) * X := by
      have h5 : T * A * 1 ≤ T * A * ℓ ^ 4 := Nat.mul_le_mul_left _ hℓ4
      have : T * A ≤ 2 * T * (A * ℓ ^ 4) := by nlinarith
      exact Nat.mul_le_mul_right _ this
    omega
  · -- negative side
    set M := cliqueM ℓ with hM
    have hr : cliqueK ℓ - 1 = 2 * ℓ ^ 6 := by unfold cliqueK; omega
    rw [hr] at h
    have hMq : ℓ + 1 ≤ M := by rw [hM]; unfold cliqueM cliqueK; nlinarith
    obtain ⟨t, ht⟩ : ∃ t, M = t + (ℓ + 1) := ⟨M - (ℓ + 1), by omega⟩
    rw [ht, show t + (ℓ + 1) - 1 = t + ℓ by omega, Nat.add_sub_cancel] at h
    have e1 : (2 * ℓ ^ 6) ^ (t + (ℓ + 1)) = 2 ^ ℓ * ((a ^ 6 * (2 * ℓ ^ 6) ^ t) * ℓ ^ 2) * (2 * ℓ ^ 4) := by
      rw [ha_def]; ring
    have e2 : ℓ ^ 2 * (2 * ℓ ^ 6) ^ (t + ℓ) = 2 ^ ℓ * ((a ^ 6 * (2 * ℓ ^ 6) ^ t) * ℓ ^ 2) := by
      rw [ha_def]; ring
    have e3 : s * ((a * a) ^ 2 * ((ℓ ^ 2) ^ (ℓ + 1) * (2 * ℓ ^ 6) ^ t)) =
        s * ((a ^ 6 * (2 * ℓ ^ 6) ^ t) * ℓ ^ 2) := by
      rw [ha_def]; ring
    rw [e1, e2, e3] at h
    have hY : 0 < (a ^ 6 * (2 * ℓ ^ 6) ^ t) * ℓ ^ 2 :=
      Nat.mul_pos (Nat.mul_pos (Nat.pow_pos ha) (Nat.pow_pos (by positivity)))
        (by positivity)
    generalize (a ^ 6 * (2 * ℓ ^ 6) ^ t) * ℓ ^ 2 = Y at h hY
    generalize (2 : ℕ) ^ ℓ = T at h hs
    have h3 : T * Y * (2 * ℓ ^ 4) ≥ T * Y * 2 := Nat.mul_le_mul_left _ (by omega)
    have h4 : s * Y < T * Y := Nat.mul_lt_mul_of_pos_right hs hY
    omega

/-- Non-vacuity for the parameters of `monotone_clique_lower_bound`: for every `ℓ ≥ 1`
there is a monotone circuit computing `CLIQUE(M ℓ, K ℓ)` through an off-diagonal
labelling (namely `stdLab`). So `monotone_clique_lower_bound` is not vacuously true. -/
theorem exists_circuit_clique_MK {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∃ (N s : ℕ) (lab : Fin N → Fin (cliqueM ℓ) × Fin (cliqueM ℓ)) (C : MCircuit N s),
      OffDiag lab ∧ ComputesClique lab (cliqueK ℓ) C :=
  exists_offDiag_computesClique (two_le_cliqueK hℓ) (cliqueK_le_cliqueM hℓ)

/-- Polynomials are eventually beaten by `2^ℓ`: for all `c d` some `ℓ ≥ 2` has
`c · 7^d · ℓ^{10d} < 2^ℓ`. -/
lemma exists_poly_lt_two_pow (c d : ℕ) : ∃ ℓ, 2 ≤ ℓ ∧ c * 7 ^ d * ℓ ^ (10 * d) < 2 ^ ℓ := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt (10 * d) (by norm_num : (1 : ℝ) < 2)
  have hε : (0 : ℝ) < 1 / ((c * 7 ^ d : ℕ) + 1 : ℝ) := by positivity
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (h.eventually (gt_mem_nhds hε))
  refine ⟨max n₀ 2, le_max_right _ _, ?_⟩
  have h1 := hn₀ (max n₀ 2) (le_max_left _ _)
  set ℓ := max n₀ 2
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity), one_mul] at h1
  have h3 : ((c * 7 ^ d * ℓ ^ (10 * d) : ℕ) : ℝ) < ((2 ^ ℓ : ℕ) : ℝ) := by
    push_cast at h1 ⊢
    nlinarith [pow_nonneg (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ) (10 * d)]
  exact_mod_cast h3

/-- **Monotone circuits for CLIQUE are superpolynomial.** No polynomial bound in the
number of vertices holds: for all `c d` there is `ℓ ≥ 2` such that every monotone
circuit computing `CLIQUE(M ℓ, K ℓ)` (through any off-diagonal labelling) has more than
`c · (M ℓ)^d` gates; and such circuits exist (`exists_circuit_clique_MK`). -/
theorem monotone_clique_superpolynomial (c d : ℕ) :
    ∃ ℓ, 2 ≤ ℓ ∧ ∀ {N s : ℕ} {lab : Fin N → Fin (cliqueM ℓ) × Fin (cliqueM ℓ)},
      OffDiag lab → ∀ C : MCircuit N s, ComputesClique lab (cliqueK ℓ) C →
        c * cliqueM ℓ ^ d < s := by
  obtain ⟨ℓ, hℓ, hlt⟩ := exists_poly_lt_two_pow c d
  refine ⟨ℓ, hℓ, fun hlab C hC => ?_⟩
  have hs := monotone_clique_lower_bound hℓ hlab C hC
  have hM : c * cliqueM ℓ ^ d ≤ c * 7 ^ d * ℓ ^ (10 * d) := by
    calc c * cliqueM ℓ ^ d ≤ c * (7 * ℓ ^ 10) ^ d :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (cliqueM_le ℓ) d)
      _ = c * 7 ^ d * ℓ ^ (10 * d) := by ring
  omega

end Pnp.Monotone
