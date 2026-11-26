import Pnp.PPoly.PPoly

/-!
# Non-vacuity of `InPPoly`

* `exists_not_inPPoly`: over every alphabet with at least two symbols there is a language
  outside `P/poly` (Shannon counting on the strings over two fixed symbols).
* `inPPoly_true`: the trivial language is in `P/poly`.
-/

namespace Pnp.PPoly

open Pnp.Circuits Filter

/-- Polynomials grow slower than `2^n`. -/
lemma eventually_mul_pow_le_two_pow (C e : ℕ) : ∀ᶠ n : ℕ in atTop, C * n ^ e ≤ 2 ^ n := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt e (by norm_num : (1 : ℝ) < 2)).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (C + 1) by positivity))
  filter_upwards [h] with n hn
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity), one_mul] at hn
  have : ((C * n ^ e : ℕ) : ℝ) ≤ 2 ^ n := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) ^ e by positivity]
  exact_mod_cast this

/-- A polynomial over `ℕ` is bounded by `c * n ^ d` for `n ≥ 1`. -/
lemma eval_le_mul_pow (p : Polynomial ℕ) :
    ∃ c d : ℕ, ∀ n : ℕ, 1 ≤ n → p.eval n ≤ c * n ^ d := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun n hn => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hn (by simp at hi; omega))

/-- For every polynomial `p` and constant `k`, some `n ≥ 5` has `(p(n) + n k) · 10 n ≤ 2^n`. -/
lemma exists_poly_small (p : Polynomial ℕ) (k : ℕ) :
    ∃ n, 5 ≤ n ∧ (p.eval n + n * k) * (10 * n) ≤ 2 ^ n := by
  obtain ⟨c, d, hcd⟩ := eval_le_mul_pow p
  obtain ⟨n, hn⟩ := ((eventually_mul_pow_le_two_pow (10 * (c + k)) (2 * (d + 1))).and
    (eventually_ge_atTop 5)).exists
  refine ⟨n, hn.2, le_trans ?_ hn.1⟩
  have h1 : 1 ≤ n := by omega
  have hnd : n ^ d ≤ n ^ (d + 1) := Nat.pow_le_pow_right h1 (by omega)
  have hn1 : n ≤ n ^ (d + 1) := by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ (d + 1) := Nat.pow_le_pow_right h1 (by omega)
  have hp := hcd n h1
  calc (p.eval n + n * k) * (10 * n)
      ≤ (c * n ^ (d + 1) + n ^ (d + 1) * k) * (10 * n ^ (d + 1)) := by
        gcongr
        exact hp.trans (Nat.mul_le_mul_left _ hnd)
    _ = 10 * (c + k) * n ^ (2 * (d + 1)) := by ring

/-- Monotonicity of the circuit count: `N` inputs and `s` gates are dominated by `n` inputs and
`N + s` gates. -/
lemma count_mono {n N s : ℕ} (hn : 1 ≤ n) :
    (s + 1) * ((N + s) * (16 * (N + s) ^ 2) ^ s) ≤
      (N + s + 1) * ((n + (N + s)) * (16 * (n + (N + s)) ^ 2) ^ (N + s)) := by
  have ha : N + s ≤ n + (N + s) := by omega
  have hb : 16 * (N + s) ^ 2 ≤ 16 * (n + (N + s)) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha 2)
  have h1 : (16 * (N + s) ^ 2) ^ s ≤ (16 * (n + (N + s)) ^ 2) ^ (N + s) :=
    (Nat.pow_le_pow_left hb s).trans
      (Nat.pow_le_pow_right (by positivity) (by omega))
  exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul ha h1)

/-- Strings of length `n` over two symbols `a`, `b`, indexed by bit patterns. -/
def word {α : Type} (a b : α) (n : ℕ) (x : Fin n → Bool) : List α :=
  List.ofFn fun i => if x i then a else b

lemma length_word {α : Type} (a b : α) (n : ℕ) (x : Fin n → Bool) :
    (word a b n x).length = n := by simp [word]

lemma word_injective {α : Type} {a b : α} (hab : a ≠ b) (n : ℕ) :
    Function.Injective (word a b n) := by
  intro x y h
  have h' := List.ofFn_injective h
  funext i
  have := congrFun h' i
  cases hx : x i <;> cases hy : y i <;> simp only [hx, hy] at this
  · rfl
  · exact absurd this.symm hab
  · exact absurd this hab
  · rfl

/-- The bit pattern `g` cannot be matched (on the strings `word a b n x`) by circuits of size
`≤ s` on the one-hot inputs. -/
def Hard {α : Type} [Fintype α] [DecidableEq α] (a b : α) (n s : ℕ)
    (g : (Fin n → Bool) → Bool) : Prop :=
  ∀ f : (Fin (n * Fintype.card α) → Bool) → Bool, HasCircuitOfSize f s →
    ∃ x, f (oneHot n (word a b n x)) ≠ g x

lemma exists_hard {α : Type} [Fintype α] [DecidableEq α] (a b : α) {n s : ℕ} (hn : 5 ≤ n)
    (hs : (n * Fintype.card α + s) * (10 * n) ≤ 2 ^ n) :
    ∃ g, Hard a b n s g := by
  classical
  set N := n * Fintype.card α
  let S : Finset ((Fin n → Bool) → Bool) :=
    (Finset.range (s + 1)).biUnion fun t => Finset.univ.image
      fun C : Circuit N t => fun x => C.eval (oneHot n (word a b n x))
  have hS : S.card < Fintype.card ((Fin n → Bool) → Bool) := by
    calc S.card ≤ ∑ t ∈ Finset.range (s + 1), (Finset.univ.image
          fun C : Circuit N t => fun x => C.eval (oneHot n (word a b n x))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ t ∈ Finset.range (s + 1), (N + s) * (16 * (N + s) ^ 2) ^ s := by
          apply Finset.sum_le_sum
          intro t ht
          exact Finset.card_image_le.trans
            (by rw [Finset.card_univ]; exact card_circuit_le N t s (by simp at ht; omega))
      _ = (s + 1) * ((N + s) * (16 * (N + s) ^ 2) ^ s) := by simp
      _ ≤ (N + s + 1) * ((n + (N + s)) * (16 * (n + (N + s)) ^ 2) ^ (N + s)) :=
          count_mono (by omega)
      _ < 2 ^ 2 ^ n := count_lt hn hs
      _ = Fintype.card ((Fin n → Bool) → Bool) := by
          rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  obtain ⟨g, hg⟩ : ∃ g, g ∉ S := by
    by_contra hc
    push Not at hc
    have : S = Finset.univ := Finset.eq_univ_of_forall hc
    rw [this, Finset.card_univ] at hS
    exact lt_irrefl _ hS
  refine ⟨g, fun f hf => ?_⟩
  obtain ⟨t, ht, C, rfl⟩ := hf
  by_contra hc
  push Not at hc
  apply hg
  simp only [S, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact ⟨t, by omega, C, funext hc⟩

/-- **Languages outside `P/poly` exist** (Shannon counting): over any alphabet with at least two
symbols, some language has no polynomial-size circuit family. -/
theorem exists_not_inPPoly (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α] :
    ∃ L : Millennium.Language (List α), ¬ InPPoly L := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  set k := Fintype.card α
  let s : ℕ → ℕ := fun n => 2 ^ n / (10 * n) - n * k
  let G : (n : ℕ) → (Fin n → Bool) → Bool := fun n =>
    if h : ∃ g, Hard a b n (s n) g then h.choose else fun _ => false
  let L : Millennium.Language (List α) := fun w => ∃ n, ∃ x, word a b n x = w ∧ G n x = true
  have hL : ∀ n x, L (word a b n x) ↔ G n x = true := by
    intro n x
    constructor
    · rintro ⟨m, y, hy, hG⟩
      have hm : m = n := by
        have := congrArg List.length hy
        rwa [length_word, length_word] at this
      subst hm
      rwa [word_injective hab m hy] at hG
    · exact fun h => ⟨n, x, rfl, h⟩
  refine ⟨L, ?_⟩
  rintro ⟨p, hp⟩
  obtain ⟨n, hn5, hn⟩ := exists_poly_small p k
  have h10 : 0 < 10 * n := by omega
  have hle : p.eval n + n * k ≤ 2 ^ n / (10 * n) := (Nat.le_div_iff_mul_le h10).2 hn
  have hps : p.eval n ≤ s n := by simp only [s]; omega
  have hks : n * k + s n = 2 ^ n / (10 * n) := by simp only [s]; omega
  have hex : ∃ g, Hard a b n (s n) g :=
    exists_hard a b hn5 (by rw [hks]; exact Nat.div_mul_le_self _ _)
  have hG : Hard a b n (s n) (G n) := by
    simp only [G, dif_pos hex]
    exact hex.choose_spec
  obtain ⟨f, ⟨t, ht, C, hC⟩, hf⟩ := hp n (by omega)
  obtain ⟨x, hx⟩ := hG f ⟨t, ht.trans hps, C, hC⟩
  have := (hf (word a b n x) (length_word a b n x)).trans (hL n x)
  apply hx
  cases h1 : f (oneHot n (word a b n x)) <;> cases h2 : G n x <;> simp_all

/-- Sanity check: the trivial language is in `P/poly` (constant circuits). -/
theorem inPPoly_true (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] :
    InPPoly (fun _ : List α => True) := by
  refine ⟨Polynomial.C 1, fun n hn => ⟨fun _ => true, ?_, fun w _ => by simp⟩⟩
  rw [Polynomial.eval_C]
  exact hasCircuitOfSize_const (Nat.mul_pos hn Fintype.card_pos) true

end Pnp.PPoly
