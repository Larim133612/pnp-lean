import Pnp.Derandomization.NisanWigderson

/-!
# Average-case hard functions exist (M19)

The hypothesis of the Nisan–Wigderson theorem (M18) is not vacuous: by counting, most Boolean
functions are hard on average.

* `card_agree_le` (Hoeffding/Chernoff bound by the exponential-moment method, proved
  elementarily with `cosh x ≤ exp (x²/2)`): for any fixed `g : X → Bool`, at most
  `2^N · exp (−2ε²N)` of the `2^N` functions `f : X → Bool` (`N = |X|`) agree with `g` on more
  than a `1/2 + ε` fraction of `X`.
* `exists_avgHard`: if `(#circuits with ≤ s gates) · exp (−2ε²·2^m) < 1`, some
  `f : {0,1}^m → {0,1}` is `(s, ε)`-hard on average.
* `exists_nw_secure`: hence, unconditionally, for every finite field `K` (`q` elements) there
  is an `f` for which the Nisan–Wigderson generator `q²` bits → `q^k` bits fools all tests with
  `sD` gates up to `q^k · ε`, as soon as the counting condition holds. (`f` is not explicit:
  this is the non-uniform existence of pseudorandom generators, not a derandomization of BPP.)
-/

namespace Pnp.Derand

open Pnp.Circuits Pnp.NaturalProofs Classical Real

noncomputable section

/-! ## The tail bound -/

section Tail

variable {X : Type} [Fintype X]

/-- Number of agreements of `f` with `g`. -/
def agree (g f : X → Bool) : ℕ := (Finset.univ.filter (fun x => g x = f x)).card

theorem prob_agree (g f : X → Bool) :
    prob (fun x => g x = f x) = (agree g f : ℝ) / Fintype.card X := by
  simp only [prob, agree]
  congr

/-- Exponential weight of `f`. -/
def wt (l : ℝ) (g f : X → Bool) : ℝ :=
  ∏ x, Real.exp (l * ((if g x = f x then 1 else 0) - 1 / 2))

theorem wt_eq (l : ℝ) (g f : X → Bool) :
    wt l g f = Real.exp (l * ((agree g f : ℝ) - Fintype.card X / 2)) := by
  rw [wt, ← Real.exp_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_boole]
  simp [agree, Finset.card_univ, div_eq_mul_inv]

theorem sum_wt (l : ℝ) (g : X → Bool) :
    ∑ f : X → Bool, wt l g f = (2 * Real.cosh (l / 2)) ^ Fintype.card X := by
  have h := Finset.sum_prod_piFinset (ι := X) (Finset.univ : Finset Bool)
    (fun x b => Real.exp (l * ((if g x = b then 1 else 0) - 1 / 2)))
  rw [Fintype.piFinset_univ] at h
  simp only [wt]
  rw [h]
  have hx : ∀ x, ∑ j : Bool, Real.exp (l * ((if g x = j then 1 else 0) - 1 / 2)) =
      2 * Real.cosh (l / 2) := by
    intro x
    rw [Fintype.sum_bool, Real.cosh_eq]
    cases g x <;> simp <;> ring_nf
  simp only [hx, Finset.prod_const, Finset.card_univ]

theorem sum_wt_le (l : ℝ) (g : X → Bool) :
    ∑ f : X → Bool, wt l g f ≤ 2 ^ Fintype.card X * Real.exp (l ^ 2 / 8 * Fintype.card X) := by
  rw [sum_wt]
  have h1 : 2 * Real.cosh (l / 2) ≤ 2 * Real.exp (l ^ 2 / 8) := by
    have := Real.cosh_le_exp_half_sq (l / 2)
    have h : (l / 2) ^ 2 / 2 = l ^ 2 / 8 := by ring
    rw [h] at this; linarith
  have h0 : 0 ≤ 2 * Real.cosh (l / 2) := by positivity
  calc (2 * Real.cosh (l / 2)) ^ Fintype.card X ≤ (2 * Real.exp (l ^ 2 / 8)) ^ Fintype.card X :=
        pow_le_pow_left₀ h0 h1 _
    _ = 2 ^ Fintype.card X * Real.exp (l ^ 2 / 8 * Fintype.card X) := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_comm (Fintype.card X : ℝ)]

/-- **Tail bound.** At most `2^N · exp(−2ε²N)` functions agree with `g` on more than a
`1/2 + ε` fraction. -/
theorem card_agree_le (g : X → Bool) {ε : ℝ} (hε : 0 ≤ ε) :
    ((Finset.univ.filter (fun f : X → Bool => 1 / 2 + ε < prob (fun x => g x = f x))).card : ℝ)
      ≤ 2 ^ Fintype.card X * Real.exp (-2 * ε ^ 2 * Fintype.card X) := by
  set N : ℝ := (Fintype.card X : ℝ)
  set B := Finset.univ.filter (fun f : X → Bool => 1 / 2 + ε < prob (fun x => g x = f x))
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hlow : ∀ f ∈ B, Real.exp (4 * ε ^ 2 * N) ≤ wt (4 * ε) g f := by
    intro f hf
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, prob_agree] at hf
    rw [wt_eq]
    apply Real.exp_le_exp.mpr
    rcases (Nat.cast_nonneg (Fintype.card X) : (0 : ℝ) ≤ _).eq_or_lt with h0 | hpos
    · rw [← h0, div_zero] at hf; linarith [sq_nonneg ε]
    · rw [lt_div_iff₀ hpos] at hf
      have : ε * N ≤ (agree g f : ℝ) - N / 2 := by simp only [N]; linarith
      nlinarith
  have hsum : (B.card : ℝ) * Real.exp (4 * ε ^ 2 * N) ≤ ∑ f : X → Bool, wt (4 * ε) g f := by
    calc (B.card : ℝ) * Real.exp (4 * ε ^ 2 * N) = ∑ _f ∈ B, Real.exp (4 * ε ^ 2 * N) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ f ∈ B, wt (4 * ε) g f := Finset.sum_le_sum hlow
      _ ≤ ∑ f : X → Bool, wt (4 * ε) g f :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun f _ _ => Finset.prod_nonneg fun x _ => (Real.exp_pos _).le)
  have h2 := hsum.trans (sum_wt_le (4 * ε) g)
  have he : Real.exp ((4 * ε) ^ 2 / 8 * N) =
      Real.exp (4 * ε ^ 2 * N) * Real.exp (-2 * ε ^ 2 * N) := by
    rw [← Real.exp_add]; ring_nf
  rw [he] at h2
  have hp := Real.exp_pos (4 * ε ^ 2 * N)
  have h3 : (B.card : ℝ) * Real.exp (4 * ε ^ 2 * N) ≤
      (2 ^ Fintype.card X * Real.exp (-2 * ε ^ 2 * N)) * Real.exp (4 * ε ^ 2 * N) := by
    calc _ ≤ _ := h2
      _ = _ := by ring
  exact le_of_mul_le_mul_right h3 hp

end Tail

/-! ## Most functions are hard on average -/

theorem card_biUnion_real {α β : Type} [Fintype α] [DecidableEq β] (T : α → Finset β) (E : ℝ)
    (h : ∀ a, ((T a).card : ℝ) ≤ E) :
    ((Finset.univ.biUnion T).card : ℝ) ≤ Fintype.card α * E := by
  calc ((Finset.univ.biUnion T).card : ℝ) ≤ ∑ a, ((T a).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _a : α, E := Finset.sum_le_sum fun a _ => h a
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The bound on the number of circuits with at most `s` gates on `m` inputs. -/
def circCount (m s : ℕ) : ℕ := (s + 1) * ((m + s) * (16 * (m + s) ^ 2) ^ s)

/-- Functions agreeing with some circuit of size `≤ s` on more than `1/2 + ε`. -/
def badSet (m s : ℕ) (ε : ℝ) : Finset ((Fin m → Bool) → Bool) :=
  (Finset.range (s + 1)).biUnion fun t => Finset.univ.biUnion fun C : Circuit m t =>
    Finset.univ.filter (fun f => 1 / 2 + ε < prob (fun x => C.eval x = f x))

theorem card_badSet_le (m s : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ((badSet m s ε).card : ℝ) ≤
      (circCount m s : ℝ) * (2 ^ 2 ^ m * Real.exp (-2 * ε ^ 2 * 2 ^ m)) := by
  set E : ℝ := 2 ^ 2 ^ m * Real.exp (-2 * ε ^ 2 * 2 ^ m)
  have hE : 0 ≤ E := by positivity
  have hT : ∀ t ∈ Finset.range (s + 1), ((Finset.univ.biUnion fun C : Circuit m t =>
      Finset.univ.filter (fun f : (Fin m → Bool) → Bool =>
        1 / 2 + ε < prob (fun x => C.eval x = f x))).card : ℝ) ≤
      (((m + s) * (16 * (m + s) ^ 2) ^ s : ℕ) : ℝ) * E := by
    intro t ht
    refine (card_biUnion_real _ E fun C => ?_).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_circuit_le m t s (by simp at ht; omega)) hE)
    have := card_agree_le (X := Fin m → Bool) (Circuit.eval C) hε
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    push_cast at this
    refine le_of_eq_of_le ?_ this
    congr 2
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, prob]
  calc ((badSet m s ε).card : ℝ) ≤ ∑ t ∈ Finset.range (s + 1),
        ((Finset.univ.biUnion fun C : Circuit m t =>
          Finset.univ.filter (fun f : (Fin m → Bool) → Bool =>
            1 / 2 + ε < prob (fun x => C.eval x = f x))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ Finset.range (s + 1), (((m + s) * (16 * (m + s) ^ 2) ^ s : ℕ) : ℝ) * E :=
        Finset.sum_le_sum hT
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, circCount]
        push_cast; ring

/-- **Average-case hard functions exist.** If `circCount m s · exp(−2ε²·2^m) < 1`, some
`f : {0,1}^m → {0,1}` is `(s, ε)`-hard on average. -/
theorem exists_avgHard {m s : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : (circCount m s : ℝ) * Real.exp (-2 * ε ^ 2 * 2 ^ m) < 1) :
    ∃ f : (Fin m → Bool) → Bool, AvgHard f s ε := by
  have hc : (badSet m s ε).card < Fintype.card ((Fin m → Bool) → Bool) := by
    have h1 := card_badSet_le m s hε
    have hpos : (0 : ℝ) < 2 ^ 2 ^ m := by positivity
    have h2 : ((badSet m s ε).card : ℝ) < 2 ^ 2 ^ m := by
      calc _ ≤ _ := h1
        _ = ((circCount m s : ℝ) * Real.exp (-2 * ε ^ 2 * 2 ^ m)) * 2 ^ 2 ^ m := by ring
        _ < 1 * 2 ^ 2 ^ m := mul_lt_mul_of_pos_right h hpos
        _ = _ := one_mul _
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    exact_mod_cast h2
  obtain ⟨f, hf⟩ : ∃ f, f ∉ badSet m s ε := by
    by_contra hne
    push Not at hne
    have : badSet m s ε = Finset.univ := Finset.eq_univ_of_forall hne
    rw [this, Finset.card_univ] at hc
    exact lt_irrefl _ hc
  refine ⟨f, ?_⟩
  rintro B ⟨t, ht, C, rfl⟩
  by_contra hlt
  push Not at hlt
  apply hf
  simp only [badSet, Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, Finset.mem_filter,
    true_and]
  exact ⟨t, by omega, C, hlt⟩

/-- **Pseudorandom generators exist (non-uniformly).** For every finite field `K` with `q`
elements, if the counting condition holds for `s = q^k · juntaSize (k−1) + sD + 1`, some
`f : {0,1}^q → {0,1}` makes the Nisan–Wigderson generator (`q²` seed bits, `q^k` output bits)
fool every test with `sD` gates up to advantage `q^k · ε`. No hardness assumption. -/
theorem exists_nw_secure (K : Type) [Field K] [Fintype K] (k sD : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : (circCount (Fintype.card K) (Fintype.card K ^ k * juntaSize (k - 1) + sD + 1) : ℝ) *
      Real.exp (-2 * ε ^ 2 * 2 ^ Fintype.card K) < 1) :
    ∃ f : (Fin (Fintype.card K) → Bool) → Bool, ∀ D : (Fin (Fintype.card K ^ k) → Bool) → Bool,
      HasCircuitOfSize D sD →
      |ex (fun w : Fin (Fintype.card K ^ k) → Bool => bv (D w)) -
        ex (fun z : Fin (Fintype.card K * Fintype.card K) → Bool =>
          bv (D (nw f (polyDesign K k).S z)))| ≤ (Fintype.card K ^ k : ℕ) * ε := by
  obtain ⟨f, hf⟩ := exists_avgHard hε h
  exact ⟨f, fun D hD => nw_poly_secure K k f hf hD⟩

/-! ## An explicit parameter choice -/

theorem eight_mul_le (k : ℕ) (hk : 1 ≤ k) : 8 * k ≤ 2 * 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem lin_lt_sixteen_pow (k : ℕ) (hk : 1 ≤ k) : 8 * k + 11 < 2 * 16 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- The number of circuits with `4^k` gates on `8k` inputs is below `2^(2·64^k)`. -/
theorem circCount_lt (k : ℕ) (hk : 1 ≤ k) : circCount (8 * k) (4 ^ k) < 2 ^ (2 * 64 ^ k) := by
  have h1 := eight_mul_le k hk
  have h2 := lin_lt_sixteen_pow k hk
  have hS : 4 ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have hS1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hle : circCount (8 * k) (4 ^ k) ≤
      (2 * 4 ^ k) * ((4 * 4 ^ k) * (16 * (4 * 4 ^ k) ^ 2) ^ 4 ^ k) := by
    unfold circCount
    have h3 : 8 * k + 4 ^ k ≤ 4 * 4 ^ k := by omega
    gcongr
    omega
  have heq : (2 * 4 ^ k) * ((4 * 4 ^ k) * (16 * (4 * 4 ^ k) ^ 2) ^ 4 ^ k) =
      2 ^ ((2 * k + 1) + ((2 * k + 2) + (4 * k + 8) * 4 ^ k)) := by
    have e1 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, hS]; ring
    have e2 : 2 ^ (2 * k + 2) = 4 * 4 ^ k := by rw [pow_add, hS]; ring
    have e3 : 2 ^ (4 * k + 8) = 16 * (4 * 4 ^ k) ^ 2 := by
      rw [show 4 * k + 8 = 2 * k + 2 * k + 8 by ring, pow_add, pow_add, ← hS]; ring
    rw [pow_add 2 (2 * k + 1), pow_add 2 (2 * k + 2), pow_mul 2 (4 * k + 8), e1, e2, e3]
  have h64 : 64 ^ k = 4 ^ k * 16 ^ k := by rw [← mul_pow]; norm_num
  have hexp : (2 * k + 1) + ((2 * k + 2) + (4 * k + 8) * 4 ^ k) < 2 * 64 ^ k := by
    rw [h64]
    have : (4 * k + 3) ≤ (4 * k + 3) * 4 ^ k := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  calc _ ≤ _ := hle
    _ = _ := heq
    _ < _ := Nat.pow_lt_pow_right (by norm_num) hexp

theorem two_pow_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
  rw [← Real.exp_one_pow]
  have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  exact pow_le_pow_left₀ (by norm_num) this n

/-- **Explicit instance.** For every `k ≥ 1` some `f : {0,1}^(8k) → {0,1}` is hard on average
for circuits with `4^k = 2^(m/4)` gates, with advantage `ε = 2^(-k) = 2^(-m/8)`. -/
theorem exists_avgHard_explicit (k : ℕ) (hk : 1 ≤ k) :
    ∃ f : (Fin (8 * k) → Bool) → Bool, AvgHard f (4 ^ k) (1 / 2 ^ k) := by
  refine exists_avgHard (by positivity) ?_
  have hc : (circCount (8 * k) (4 ^ k) : ℝ) < 2 ^ (2 * 64 ^ k) := by
    exact_mod_cast circCount_lt k hk
  have he : -2 * (1 / (2 : ℝ) ^ k) ^ 2 * 2 ^ (8 * k) = -((2 * 64 ^ k : ℕ) : ℝ) := by
    have : (2 : ℝ) ^ (8 * k) = ((2 : ℝ) ^ k) ^ 2 * 64 ^ k := by
      rw [← pow_mul, show (64 : ℝ) = 2 ^ 6 by norm_num, ← pow_mul, ← pow_add]; ring_nf
    rw [this]; push_cast
    field_simp
  rw [he, Real.exp_neg]
  have hpos := Real.exp_pos ((2 * 64 ^ k : ℕ) : ℝ)
  rw [← div_eq_mul_inv, div_lt_one hpos]
  calc _ < (2 : ℝ) ^ (2 * 64 ^ k) := hc
    _ ≤ _ := two_pow_le_exp _

end

end Pnp.Derand
