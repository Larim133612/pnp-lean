import Pnp.AC0.Approx
import Pnp.AC0.Smolensky

/-!
# PARITY ∉ AC⁰ (M4c)

Combining the Razborov–Smolensky approximation (`ac0_approx`) with Smolensky's lemma
(`Smolensky.smolensky_tail`) and the central binomial bound
`C(n, ⌊n/2⌋)² · (n+1) ≤ 4ⁿ` (`choose_half_sq_mul_le`):

* `parity_ac0_lower_bound`: a formula `F` computing PARITY on `n` bits satisfies
  `2^ℓ ≤ 4 · size F` whenever `16 · ((2ℓ)^{depth F} + 1)² ≤ n + 1`;
* `parity_ac0_lower_bound_of_depth_le`: same with `depth F ≤ d` and `ℓ ≥ 1`, i.e.
  depth-`d` formulas for PARITY have size `2^{Ω(n^{1/(2d)})}`;
* `parity_not_in_AC0`: for fixed depth `d` and polynomial `c · n^k`, for all large `n`
  every depth-`≤ d` formula computing PARITY has more than `c · n^k` gates;
* `exists_parity_formula`: non-vacuity, a depth-`≤ 2` DNF computes PARITY for every `n`.
-/

namespace Pnp.AC0

open Finset MvPolynomial

variable {n : ℕ}

/-- The two `eval01`s (from `Approx` and `Smolensky`) agree. -/
lemma eval01_eq_smolensky (P : MvPolynomial (Fin n) (ZMod 3)) (x : Fin n → Bool) :
    eval01 P x = Smolensky.eval01 P x := rfl

/-- PARITY as a Boolean function. -/
def parityFn (x : Fin n → Bool) : Bool :=
  decide ((univ.filter fun i => x i = true).card % 2 = 1)

lemma ind_parityFn (x : Fin n → Bool) :
    (if parityFn x then 1 else 0 : ZMod 3) = Smolensky.parityVal x := by
  unfold parityFn Smolensky.parityVal
  by_cases h : (univ.filter fun i => x i = true).card % 2 = 1 <;> simp [h]

/-! ### Central binomial coefficient -/

/-- `C(2m, m)² · (2m+1) ≤ 16^m`. -/
lemma centralBinom_sq_mul_le (m : ℕ) : m.centralBinom ^ 2 * (2 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    have hq : (2 * m + 1) * (2 * m + 3) ≤ (2 * m + 2) ^ 2 := by nlinarith
    have key : (m + 1) ^ 2 * ((m + 1).centralBinom ^ 2 * (2 * (m + 1) + 1)) ≤
        (m + 1) ^ 2 * 16 ^ (m + 1) := by
      generalize (m + 1).centralBinom = b at h ⊢
      generalize m.centralBinom = a at h ih
      calc (m + 1) ^ 2 * (b ^ 2 * (2 * (m + 1) + 1))
          = ((m + 1) * b) ^ 2 * (2 * m + 3) := by ring
        _ = (2 * (2 * m + 1) * a) ^ 2 * (2 * m + 3) := by rw [h]
        _ = 4 * ((2 * m + 1) * (2 * m + 3)) * (a ^ 2 * (2 * m + 1)) := by ring
        _ ≤ 4 * (2 * m + 2) ^ 2 * 16 ^ m :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hq) ih
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- **Central binomial bound:** `C(n, ⌊n/2⌋)² · (n+1) ≤ 4ⁿ`, i.e.
`C(n, ⌊n/2⌋) ≤ 2ⁿ / √(n+1)`. -/
theorem choose_half_sq_mul_le (n : ℕ) : (n.choose (n / 2)) ^ 2 * (n + 1) ≤ 4 ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * m / 2 = m by omega, ← Nat.centralBinom_eq_two_mul_choose, pow_mul]
    simpa using centralBinom_sq_mul_le m
  · rw [show (2 * m + 1) / 2 = m by omega]
    have h2 : 2 * (2 * m + 1).choose m = (m + 1).centralBinom := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = (2 * m + 1) + 1 by ring,
        Nat.choose_succ_succ', Nat.choose_symm_half]
      ring
    have h := centralBinom_sq_mul_le (m + 1)
    rw [← h2] at h
    have h4 : (4 : ℕ) ^ (2 * m + 1) * 4 = 16 ^ (m + 1) := by
      rw [pow_succ, pow_mul, pow_succ]; norm_num; ring
    generalize (2 * m + 1).choose m = a at h ⊢
    generalize (4 : ℕ) ^ (2 * m + 1) = X at h4 ⊢
    generalize (16 : ℕ) ^ (m + 1) = Y at h4 h
    nlinarith

/-- `4 (D+1) C(n, ⌊n/2⌋) ≤ 2ⁿ` once `16 (D+1)² ≤ n+1`. -/
lemma four_mul_choose_half_le {D : ℕ} (h : 16 * (D + 1) ^ 2 ≤ n + 1) :
    4 * ((D + 1) * n.choose (n / 2)) ≤ 2 ^ n := by
  have hc := choose_half_sq_mul_le n
  have h4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4] at hc
  have : (4 * ((D + 1) * n.choose (n / 2))) ^ 2 ≤ (2 ^ n) ^ 2 := by
    calc (4 * ((D + 1) * n.choose (n / 2))) ^ 2
        = (16 * (D + 1) ^ 2) * (n.choose (n / 2)) ^ 2 := by ring
      _ ≤ (n + 1) * (n.choose (n / 2)) ^ 2 := Nat.mul_le_mul_right _ h
      _ = (n.choose (n / 2)) ^ 2 * (n + 1) := by ring
      _ ≤ (2 ^ n) ^ 2 := hc
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this

/-! ### The lower bound -/

/-- **PARITY ∉ AC⁰, explicit form.** If `F` computes PARITY on `n` bits and
`16 · ((2ℓ)^{depth F} + 1)² ≤ n + 1`, then `F` has at least `2^ℓ / 4` gates. -/
theorem parity_ac0_lower_bound (F : Formula n) (hF : ∀ x, F.eval x = parityFn x) (ℓ : ℕ)
    (hℓ : 16 * ((2 * ℓ) ^ F.depth + 1) ^ 2 ≤ n + 1) : 2 ^ ℓ ≤ 4 * F.size := by
  classical
  obtain ⟨P, E, hdeg, hE, hagree⟩ := ac0_approx ℓ F
  have hS := Smolensky.smolensky_tail P _ hdeg
  have hC := four_mul_choose_half_le hℓ
  set A := univ.filter (fun x : Fin n → Bool => Smolensky.eval01 P x = Smolensky.parityVal x)
  have hsub : univ \ E ⊆ A := by
    intro x hx
    simp only [mem_sdiff, mem_univ, true_and] at hx
    simp only [A, mem_filter, mem_univ, true_and]
    rw [← eval01_eq_smolensky, hagree x hx, hF x, ind_parityFn]
  have hcompl : (univ \ E).card = 2 ^ n - E.card := by
    rw [← compl_eq_univ_sdiff, card_compl]; simp
  have hA : 2 ^ n - E.card ≤ A.card := hcompl ▸ card_le_card hsub
  by_contra hlt
  push Not at hlt
  have hE4 : 4 * E.card < 2 ^ n := by
    by_contra h'
    push Not at h'
    have h1 := Nat.mul_le_mul_right (2 ^ ℓ) h'
    have h2 := Nat.mul_lt_mul_of_pos_right hlt (show 0 < 2 ^ n by positivity)
    generalize (2 : ℕ) ^ n = X at h1 h2 hE
    generalize (2 : ℕ) ^ ℓ = Y at h1 h2 hE
    nlinarith
  generalize ((2 * ℓ) ^ F.depth + 1) * n.choose (n / 2) = Z at hS hC
  generalize (2 : ℕ) ^ n = X at hS hC hA hE4
  omega

/-- **PARITY ∉ AC⁰, depth-`d` form.** A formula of depth `≤ d` computing PARITY on `n` bits
has at least `2^ℓ / 4` gates whenever `ℓ ≥ 1` and `16 · ((2ℓ)^d + 1)² ≤ n + 1`; taking
`ℓ ≈ n^{1/(2d)}/2` gives size `2^{Ω(n^{1/(2d)})}`. -/
theorem parity_ac0_lower_bound_of_depth_le {d ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (F : Formula n)
    (hd : F.depth ≤ d) (hF : ∀ x, F.eval x = parityFn x)
    (hℓ : 16 * ((2 * ℓ) ^ d + 1) ^ 2 ≤ n + 1) : 2 ^ ℓ ≤ 4 * F.size := by
  refine parity_ac0_lower_bound F hF ℓ (le_trans ?_ hℓ)
  have : (2 * ℓ) ^ F.depth ≤ (2 * ℓ) ^ d := Nat.pow_le_pow_right (by omega) hd
  have := Nat.pow_le_pow_left (Nat.add_le_add_right this 1) 2
  omega

/-! ### Asymptotic corollary -/

/-- Polynomials are eventually beaten by `2^ℓ`. -/
lemma eventually_poly_lt_two_pow (A e : ℕ) : ∃ L, ∀ ℓ ≥ L, A * ℓ ^ e < 2 ^ ℓ := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt e (by norm_num : (1 : ℝ) < 2)
  have hε : (0 : ℝ) < 1 / ((A : ℝ) + 1) := by positivity
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.1 (h.eventually (gt_mem_nhds hε))
  refine ⟨L, fun ℓ hℓ => ?_⟩
  have h1 := hL ℓ hℓ
  have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity), one_mul] at h1
  have h3 : ((A * ℓ ^ e : ℕ) : ℝ) < ((2 ^ ℓ : ℕ) : ℝ) := by
    push_cast at h1 ⊢
    nlinarith [pow_nonneg (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ) e]
  exact_mod_cast h3

/-- The threshold `16 · ((2ℓ)^d + 1)²` of `parity_ac0_lower_bound_of_depth_le`. -/
def parityThreshold (d ℓ : ℕ) : ℕ := 16 * ((2 * ℓ) ^ d + 1) ^ 2

lemma lt_parityThreshold (d ℓ : ℕ) : ℓ + 1 < parityThreshold (d + 1) ℓ := by
  unfold parityThreshold
  have h1 : (2 * ℓ) ^ (d + 1) + 1 ≤ ((2 * ℓ) ^ (d + 1) + 1) ^ 2 := by nlinarith
  have h2 : 2 * ℓ ≤ (2 * ℓ) ^ (d + 1) := by
    rcases Nat.eq_zero_or_pos ℓ with rfl | hl
    · simp
    · exact Nat.le_self_pow (by omega) _
  omega

lemma parityThreshold_succ_le {d ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    parityThreshold d (ℓ + 1) ≤ 64 * 16 ^ d * ℓ ^ (2 * d) := by
  unfold parityThreshold
  have h1 : (2 * (ℓ + 1)) ^ d ≤ (4 * ℓ) ^ d := Nat.pow_le_pow_left (by omega) d
  have h2 : 1 ≤ (4 * ℓ) ^ d := Nat.one_le_pow _ _ (by omega)
  have h3 : ((2 * (ℓ + 1)) ^ d + 1) ^ 2 ≤ (2 * (4 * ℓ) ^ d) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h4 : 16 * (2 * (4 * ℓ) ^ d) ^ 2 = 64 * 16 ^ d * ℓ ^ (2 * d) := by
    rw [mul_comm 2 d, pow_mul, show (16 : ℕ) ^ d = (4 ^ d) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]; ring
  omega

/-- **PARITY ∉ AC⁰.** For every depth `d` and polynomial `c · n^k`, for all large `n`,
every formula of depth `≤ d` computing PARITY on `n` bits has more than `c · n^k` gates. -/
theorem parity_not_in_AC0 (d c k : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ F : Formula n, F.depth ≤ d → (∀ x, F.eval x = parityFn x) →
      c * n ^ k < F.size := by
  obtain ⟨L, hL⟩ := eventually_poly_lt_two_pow (4 * c * (64 * 16 ^ (d + 1)) ^ k)
    (2 * (d + 1) * k)
  refine ⟨parityThreshold (d + 1) (max L 1), fun n hn F hd hF => ?_⟩
  have hLn : max L 1 ≤ n := by have := lt_parityThreshold d (max L 1); omega
  set ℓ := Nat.findGreatest (fun ℓ => parityThreshold (d + 1) ℓ ≤ n + 1) n with hℓdef
  have hspec : parityThreshold (d + 1) ℓ ≤ n + 1 :=
    Nat.findGreatest_spec (P := fun ℓ => parityThreshold (d + 1) ℓ ≤ n + 1) hLn (by omega)
  have hge : max L 1 ≤ ℓ := Nat.le_findGreatest hLn (by omega)
  have hmax : n + 1 < parityThreshold (d + 1) (ℓ + 1) := by
    by_contra h
    push Not at h
    have hle : ℓ + 1 ≤ n := by have := lt_parityThreshold d (ℓ + 1); omega
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self ℓ) hle h
  have hlb := parity_ac0_lower_bound_of_depth_le (d := d + 1) (ℓ := ℓ) (by omega) F
    (by omega) hF hspec
  have hpoly := parityThreshold_succ_le (d := d + 1) (ℓ := ℓ) (by omega)
  have hLℓ := hL ℓ (by omega)
  have hnk : c * n ^ k ≤ c * (64 * 16 ^ (d + 1)) ^ k * ℓ ^ (2 * (d + 1) * k) := by
    calc c * n ^ k ≤ c * (64 * 16 ^ (d + 1) * ℓ ^ (2 * (d + 1))) ^ k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
      _ = c * (64 * 16 ^ (d + 1)) ^ k * ℓ ^ (2 * (d + 1) * k) := by
          rw [mul_pow, pow_mul]; ring
  have hLℓ' : 4 * (c * (64 * 16 ^ (d + 1)) ^ k * ℓ ^ (2 * (d + 1) * k)) < 2 ^ ℓ :=
    calc 4 * (c * (64 * 16 ^ (d + 1)) ^ k * ℓ ^ (2 * (d + 1) * k))
        = 4 * c * (64 * 16 ^ (d + 1)) ^ k * ℓ ^ (2 * (d + 1) * k) := by ring
      _ < 2 ^ ℓ := hLℓ
  generalize c * (64 * 16 ^ (d + 1)) ^ k * ℓ ^ (2 * (d + 1) * k) = Z at hnk hLℓ'
  omega

/-! ### Non-vacuity: a depth-2 DNF for PARITY -/

/-- The AND of the `n` literals matching the point `y`. -/
def pointTerm (y : Fin n → Bool) : Formula n := .and n fun i => .lit i (y i)

/-- The constant `false` (empty OR). -/
def falseF : Formula n := .or 0 Fin.elim0

lemma eval_pointTerm (y x : Fin n → Bool) : (pointTerm y).eval x = decide (x = y) := by
  simp [pointTerm, funext_iff]

lemma depth_pointTerm (y : Fin n → Bool) : (pointTerm y).depth ≤ 1 := by
  show (univ.sup fun i => (Formula.lit i (y i)).depth) + 1 ≤ 1
  have : (univ.sup fun i => (Formula.lit (n := n) i (y i)).depth) ≤ 0 :=
    Finset.sup_le fun i _ => le_rfl
  omega

/-- The DNF `⋁_{y odd} ⋀_i (xᵢ = yᵢ)` (even points contribute the constant `false`). -/
noncomputable def parityDNF (n : ℕ) : Formula n :=
  .or _ fun j => if parityFn ((Fintype.equivFin (Fin n → Bool)).symm j)
    then pointTerm ((Fintype.equivFin (Fin n → Bool)).symm j) else falseF

/-- **Non-vacuity:** for every `n`, some formula of depth `≤ 2` computes PARITY. -/
theorem exists_parity_formula (n : ℕ) :
    ∃ F : Formula n, F.depth ≤ 2 ∧ ∀ x, F.eval x = parityFn x := by
  refine ⟨parityDNF n, ?_, fun x => ?_⟩
  · show (univ.sup fun j => _) + 1 ≤ 2
    have : (univ.sup fun j : Fin (Fintype.card (Fin n → Bool)) =>
        (if parityFn ((Fintype.equivFin (Fin n → Bool)).symm j)
          then pointTerm ((Fintype.equivFin (Fin n → Bool)).symm j) else falseF).depth) ≤ 1 := by
      refine Finset.sup_le fun j _ => ?_
      split_ifs
      · exact depth_pointTerm _
      · exact le_of_eq rfl
    exact Nat.add_le_add_right this 1
  · simp only [parityDNF, Formula.eval_or]
    by_cases hx : parityFn x = true
    · rw [hx, decide_eq_true_iff]
      refine ⟨Fintype.equivFin _ x, ?_⟩
      rw [Equiv.symm_apply_apply, if_pos hx, eval_pointTerm, decide_eq_true_iff]
    · simp only [Bool.not_eq_true] at hx
      rw [hx, decide_eq_false_iff_not]
      rintro ⟨j, hj⟩
      split_ifs at hj with hp
      · rw [eval_pointTerm, decide_eq_true_iff] at hj
        rw [← hj] at hp
        simp_all
      · exact absurd hj (by simp [falseF])

end Pnp.AC0
