import Pnp.NaturalProofs.GGM
import Pnp.Circuits.Majority

/-!
# The Goldreich–Levin hardcore bit (M16)

Goldreich–Levin (1989): for every function `f`, the inner product `⟨x, r⟩ mod 2` is a hardcore
bit of `(x, r) ↦ (f x, r)`. A circuit `B` that predicts `⟨x, r⟩` from `(f x, r)` noticeably
better than a coin flip yields a circuit of comparable size that recovers `x` from `f x`.

Main results:

* `ip_rsum` (linearity), `ex_rsum`, `ex_rsum_mul` (the subset sums `r_S = ⊕_{a ∈ S} r_a` of
  independent uniform `r_a` are uniform and pairwise independent).
* `prob_maj_wrong_le` (Chebyshev for the pairwise-independent votes).
* `goldreich_levin` (one input length, explicit parameters): if
  `Pr_{x,r}[B(f x, r) = ⟨x, r⟩] ≥ 1/2 + ε` and `(2^l − 1) ε² ≥ 2n`, there is a circuit `I`
  with `glInvSize n (2^l − 1) |B|` gates and `Pr_x[I(f x) = x] ≥ ε / 2^{l+2}`.
  The inverter is non-uniform: the random strings `r_1, …, r_l` *and* the guesses for
  `⟨x, r_a⟩` are fixed by averaging, so no evaluation of `f` is needed inside `I`.
* `OWF.HardAlong` (one-wayness against circuits of size polynomial in `2ⁿ`, the regime of the
  Razborov–Rudich barrier) and `OWF.hardcore_ip`: for a one-way function the inner product is
  a hardcore predicate in the same regime.
-/

namespace Pnp.NaturalProofs

open Pnp.Circuits Classical

noncomputable section

/-! ## Parities -/

/-- `false ↦ 0`, `true ↦ 1` in `ZMod 2`. -/
def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem toZ_injective : Function.Injective toZ := by
  intro a b h; cases a <;> cases b <;> simp_all [toZ]

theorem toZ_xor (a b : Bool) : toZ (xor a b) = toZ a + toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_decide (z : ZMod 2) : toZ (decide (z = 1)) = z := by
  fin_cases z <;> decide

/-- Parity of the bits `f a`, `a ∈ S`. -/
def bsum {α : Type} (S : Finset α) (f : α → Bool) : Bool :=
  decide ((∑ a ∈ S, toZ (f a)) = 1)

theorem toZ_bsum {α : Type} (S : Finset α) (f : α → Bool) :
    toZ (bsum S f) = ∑ a ∈ S, toZ (f a) := toZ_decide _

/-- Inner product mod 2. -/
def ip {n : ℕ} (x r : Seed n) : Bool := bsum Finset.univ (fun i => x i && r i)

/-- Bitwise xor. -/
def vxor {n : ℕ} (r r' : Seed n) : Seed n := fun i => xor (r i) (r' i)

/-- The unit vector `e_i`. -/
def unitv {n : ℕ} (i : Fin n) : Seed n := fun j => decide (j = i)

theorem ip_vxor {n : ℕ} (x r r' : Seed n) : ip x (vxor r r') = xor (ip x r) (ip x r') := by
  apply toZ_injective
  simp only [ip, toZ_xor, toZ_bsum, vxor, toZ_and, mul_add, Finset.sum_add_distrib]

theorem ip_unitv {n : ℕ} (x : Seed n) (i : Fin n) : ip x (unitv i) = x i := by
  apply toZ_injective
  rw [ip, toZ_bsum, Finset.sum_eq_single i]
  · simp [unitv]
  · intro j _ hj; simp [unitv, hj, toZ]
  · simp

/-- Subset sums `r_S = ⊕_{a ∈ S} r_a`. -/
def rsum {l n : ℕ} (R : Fin l → Seed n) (S : Finset (Fin l)) : Seed n :=
  fun t => bsum S (fun a => R a t)

/-- **Linearity**: `⟨x, r_S⟩ = ⊕_{a ∈ S} ⟨x, r_a⟩`. -/
theorem ip_rsum {l n : ℕ} (x : Seed n) (R : Fin l → Seed n) (S : Finset (Fin l)) :
    ip x (rsum R S) = bsum S (fun a => ip x (R a)) := by
  apply toZ_injective
  simp only [ip, rsum, toZ_bsum, toZ_and, toZ_bsum, Finset.mul_sum]
  exact Finset.sum_comm

theorem rsum_update_of_mem {l n : ℕ} (R : Fin l → Seed n) {S : Finset (Fin l)} {a : Fin l}
    (ha : a ∈ S) (u : Seed n) :
    rsum (Function.update R a u) S = vxor u (rsum R (S.erase a)) := by
  funext t
  apply toZ_injective
  simp only [rsum, vxor, toZ_xor, toZ_bsum]
  rw [← Finset.add_sum_erase S _ ha, Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]

theorem rsum_update_of_notMem {l n : ℕ} (R : Fin l → Seed n) {S : Finset (Fin l)} {a : Fin l}
    (ha : a ∉ S) (u : Seed n) :
    rsum (Function.update R a u) S = rsum R S := by
  funext t
  apply toZ_injective
  simp only [rsum, toZ_bsum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Function.update_of_ne (show b ≠ a from fun h => ha (h ▸ hb))]

/-! ## Expectations -/

/-- Uniform expectation. -/
def ex {α : Type} [Fintype α] (f : α → ℝ) : ℝ := (∑ a, f a) / Fintype.card α

/-- Indicator of an event. -/
def ind {α : Type} (P : α → Prop) (a : α) : ℝ := if P a then 1 else 0

theorem prob_eq_ex {α : Type} [Fintype α] (P : α → Prop) : prob P = ex (ind P) := by
  rw [prob_eq_sum]; rfl

theorem ex_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    ex (fun a => f (e a)) = ex f := by
  rw [ex, ex, Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e f

theorem ex_prod {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    ex f = ex (fun a => ex (fun b => f (a, b))) := by
  rw [ex, ex, Fintype.sum_prod_type, Fintype.card_prod]
  simp only [ex]
  rw [← Finset.sum_div, Nat.cast_mul, div_div, mul_comm (Fintype.card β : ℝ)]

theorem ex_const {α : Type} [Fintype α] [Nonempty α] (c : ℝ) : ex (fun _ : α => c) = c := by
  have : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [ex, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem ex_fst {α β : Type} [Fintype α] [Fintype β] [Nonempty β] (f : α → ℝ) :
    ex (fun p : α × β => f p.1) = ex f := by
  rw [ex_prod]; simp only [ex_const]

theorem ex_add {α : Type} [Fintype α] (f g : α → ℝ) :
    ex (fun a => f a + g a) = ex f + ex g := by
  rw [ex, ex, ex, Finset.sum_add_distrib, add_div]

theorem ex_sub {α : Type} [Fintype α] (f g : α → ℝ) :
    ex (fun a => f a - g a) = ex f - ex g := by
  rw [ex, ex, ex, Finset.sum_sub_distrib, sub_div]

theorem ex_mul_const {α : Type} [Fintype α] (f : α → ℝ) (c : ℝ) :
    ex (fun a => f a * c) = ex f * c := by
  rw [ex, ex, ← Finset.sum_mul, div_mul_eq_mul_div]

theorem ex_sum {α ι : Type} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    ex (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, ex (f i) := by
  rw [ex, Finset.sum_comm, Finset.sum_div]; rfl

theorem ex_mono {α : Type} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : ex f ≤ ex g := by
  rw [ex, ex]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

theorem ex_nonneg {α : Type} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ ex f := by
  rw [ex]; exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (Nat.cast_nonneg _)

/-- Resampling one coordinate. -/
theorem ex_update {ι B : Type} [Fintype ι] [DecidableEq ι] [Fintype B] [Nonempty B] (a : ι)
    (F : (ι → B) → ℝ) :
    ex F = ex (fun R => ex (fun u => F (Function.update R a u))) := by
  let σ : (ι → B) × B → (ι → B) × B := fun q => (Function.update q.1 a q.2, q.1 a)
  have hσ : Function.Involutive σ := by
    rintro ⟨R, u⟩
    simp only [σ, Function.update_self, Function.update_idem, Function.update_eq_self]
  rw [← ex_prod (fun q : (ι → B) × B => F (Function.update q.1 a q.2))]
  have := ex_equiv (hσ.toPerm σ) (fun q : (ι → B) × B => F q.1)
  rw [ex_fst] at this
  rw [← this]
  rfl

/-- Translation invariance on `{0,1}ⁿ`. -/
theorem ex_vxor {n : ℕ} (c : Seed n) (g : Seed n → ℝ) : ex (fun u => g (vxor u c)) = ex g := by
  have hinv : Function.Involutive (fun u : Seed n => vxor u c) := by
    intro u; funext t; simp [vxor]
  exact ex_equiv (hinv.toPerm _) g

/-- `r_S` is uniform for nonempty `S`. -/
theorem ex_rsum {l n : ℕ} {S : Finset (Fin l)} (hS : S.Nonempty) (g : Seed n → ℝ) :
    ex (fun R : Fin l → Seed n => g (rsum R S)) = ex g := by
  obtain ⟨a, ha⟩ := hS
  rw [ex_update a]
  simp only [rsum_update_of_mem _ ha, ex_vxor]
  exact ex_const _

/-- **Pairwise independence** of `r_S`, `r_T` for distinct nonempty `S`, `T`. -/
theorem ex_rsum_mul {l n : ℕ} {S T : Finset (Fin l)} (hS : S.Nonempty) (hT : T.Nonempty)
    (hST : S ≠ T) (g h : Seed n → ℝ) :
    ex (fun R : Fin l → Seed n => g (rsum R S) * h (rsum R T)) = ex g * ex h := by
  by_cases hsub : S ⊆ T
  · -- some `a ∈ T \ S`
    have : ¬ T ⊆ S := fun h' => hST (Finset.Subset.antisymm hsub h')
    obtain ⟨a, haT, haS⟩ := Finset.not_subset.mp this
    rw [ex_update a]
    simp only [rsum_update_of_mem _ haT, rsum_update_of_notMem _ haS]
    have : ∀ R : Fin l → Seed n, ex (fun u => g (rsum R S) * h (vxor u (rsum R (T.erase a)))) =
        g (rsum R S) * ex h := by
      intro R
      rw [show (fun u => g (rsum R S) * h (vxor u (rsum R (T.erase a)))) =
        fun u => h (vxor u (rsum R (T.erase a))) * g (rsum R S) from funext fun _ => mul_comm _ _,
        ex_mul_const, ex_vxor, mul_comm]
    simp only [this]
    rw [ex_mul_const, ex_rsum hS]
  · obtain ⟨a, haS, haT⟩ := Finset.not_subset.mp hsub
    rw [ex_update a]
    simp only [rsum_update_of_mem _ haS, rsum_update_of_notMem _ haT]
    have : ∀ R : Fin l → Seed n, ex (fun u => g (vxor u (rsum R (S.erase a))) * h (rsum R T)) =
        ex g * h (rsum R T) := by
      intro R
      rw [ex_mul_const, ex_vxor]
    simp only [this]
    rw [show (fun R : Fin l → Seed n => ex g * h (rsum R T)) =
      fun R => h (rsum R T) * ex g from funext fun _ => mul_comm _ _, ex_mul_const, ex_rsum hT,
      mul_comm]

/-! ## Chebyshev for pairwise-independent votes -/

theorem ind_mul_self {α : Type} (P : α → Prop) (a : α) : ind P a * ind P a = ind P a := by
  unfold ind; split_ifs <;> norm_num

theorem ex_ind_le_one {α : Type} [Fintype α] (P : α → Prop) : ex (ind P) ≤ 1 := by
  rw [← prob_eq_ex, prob]
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
  · rw [h]; simp
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_le_univ _

/-- **Votes on pairwise-independent samples.** Let `sub j` (`j < m`) be distinct nonempty sets
and `g` an event of probability `≥ 1/2 + δ`. The probability that at most half of the samples
`r_{sub j}` satisfy `g` is at most `1 / (4 m δ²)`. -/
theorem prob_vote_fail {l n m : ℕ} (sub : Fin m → Finset (Fin l))
    (hsub : Function.Injective sub) (hne : ∀ j, (sub j).Nonempty) (g : Seed n → Prop)
    {δ : ℝ} (hδ : 0 ≤ δ) (hp : 1 / 2 + δ ≤ prob g) :
    prob (fun R : Fin l → Seed n =>
        ¬ m < 2 * (Finset.univ.filter (fun j => g (rsum R (sub j)))).card) *
      (4 * m * δ ^ 2) ≤ 1 := by
  set p := prob g with hpdef
  have hpe : ex (ind g) = p := (prob_eq_ex g).symm
  let z : Seed n → ℝ := fun r => ind g r - p
  have hz0 : ex z = 0 := by rw [ex_sub, hpe, ex_const, sub_self]
  have hz2 : ex (fun r => z r * z r) ≤ 1 / 4 := by
    have : (fun r => z r * z r) = fun r => ind g r * (1 - 2 * p) + p ^ 2 := by
      funext r; simp only [z]; rw [sub_mul, mul_sub, ind_mul_self]; ring
    rw [this, ex_add, ex_mul_const, ex_const, hpe]
    nlinarith [sq_nonneg (p - 1 / 2)]
  let X : (Fin l → Seed n) → ℝ := fun R => ∑ j, z (rsum R (sub j))
  have hX : ex (fun R => X R * X R) ≤ m / 4 := by
    have : (fun R => X R * X R) =
        fun R => ∑ j, ∑ j', z (rsum R (sub j)) * z (rsum R (sub j')) := by
      funext R; simp only [X, Finset.sum_mul_sum]
    rw [this, ex_sum]
    calc ∑ j, ex (fun R => ∑ j', z (rsum R (sub j)) * z (rsum R (sub j')))
        = ∑ j : Fin m, ex (fun r => z r * z r) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ex_sum, Finset.sum_eq_single j]
          · exact ex_rsum (hne j) (fun r => z r * z r)
          · intro j' _ hj'
            rw [ex_rsum_mul (hne j) (hne j') (fun h => hj' (hsub h).symm), hz0, zero_mul]
          · simp
      _ ≤ ∑ _j : Fin m, (1 / 4 : ℝ) := Finset.sum_le_sum fun j _ => hz2
      _ = m / 4 := by simp [Finset.sum_const]; ring
  -- Markov on `X²`
  have hpt : ∀ R : Fin l → Seed n,
      ind (fun R : Fin l → Seed n =>
        ¬ m < 2 * (Finset.univ.filter (fun j => g (rsum R (sub j)))).card) R *
        ((m : ℝ) * δ) ^ 2 ≤ X R * X R := by
    intro R
    unfold ind
    split_ifs with h
    · have hc : ((Finset.univ.filter (fun j => g (rsum R (sub j)))).card : ℝ) =
          ∑ j, ind g (rsum R (sub j)) := by
        rw [Finset.card_filter]; push_cast; rfl
      have hle : 2 * ((Finset.univ.filter (fun j => g (rsum R (sub j)))).card : ℝ) ≤ m := by
        exact_mod_cast not_lt.mp h
      have hXv : X R = (∑ j, ind g (rsum R (sub j))) - m * p := by
        simp only [X, z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      have : X R ≤ -(m * δ) := by
        rw [hXv, ← hc]
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      have h0 : 0 ≤ (m : ℝ) * δ := mul_nonneg (Nat.cast_nonneg m) hδ
      nlinarith
    · rw [zero_mul]; exact mul_self_nonneg _
  have := ex_mono hpt
  rw [ex_mul_const, ← prob_eq_ex] at this
  have h4 : prob (fun R : Fin l → Seed n =>
        ¬ m < 2 * (Finset.univ.filter (fun j => g (rsum R (sub j)))).card) *
      (4 * m * δ ^ 2) * m ≤ 4 * (m / 4) := by nlinarith
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    nlinarith

/-! ## Small probability facts -/

theorem ex_ind_not {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) :
    ex (ind (fun a => ¬ P a)) = 1 - ex (ind P) := by
  rw [← ex_const (α := α) 1, ← ex_sub]
  congr 1; funext a; unfold ind; split_ifs <;> simp_all

/-- Union bound. -/
theorem ex_ind_exists_le {α ι : Type} [Fintype α] [Fintype ι] (P : ι → α → Prop) :
    ex (ind (fun a => ∃ i, P i a)) ≤ ∑ i, ex (ind (P i)) := by
  rw [← ex_sum]
  refine ex_mono fun a => ?_
  unfold ind
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    calc (1 : ℝ) = if P i a then 1 else 0 := by rw [if_pos hi]
      _ ≤ ∑ j, if P j a then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if P j a then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

theorem ex_comm {α β : Type} [Fintype α] [Fintype β] (F : α → β → ℝ) :
    ex (fun a => ex (fun b => F a b)) = ex (fun b => ex (fun a => F a b)) := by
  simp only [ex, ← Finset.sum_div]
  rw [Finset.sum_comm, div_div, div_div, mul_comm (Fintype.card α : ℝ)]

/-- Some point is at least the average. -/
theorem exists_le_of_le_ex {α : Type} [Fintype α] [Nonempty α] {f : α → ℝ} {c : ℝ}
    (h : c ≤ ex f) : ∃ a, c ≤ f a := by
  by_contra hne
  push Not at hne
  have : ex f < ex (fun _ : α => c) := by
    have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    rw [ex, ex]
    exact div_lt_div_of_pos_right
      (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun a _ => hne a) hα
  rw [ex_const] at this
  linarith

/-- An event containing a given point has probability `≥ 1 / |α|`. -/
theorem inv_card_le_ex_ind {α : Type} [Fintype α] {P : α → Prop} {a : α} (ha : P a) :
    1 / (Fintype.card α : ℝ) ≤ ex (ind P) := by
  rw [ex]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  calc (1 : ℝ) = ind P a := by simp [ind, ha]
    _ ≤ ∑ b, ind P b :=
      Finset.single_le_sum (f := ind P) (fun b _ => by unfold ind; split_ifs <;> norm_num)
        (Finset.mem_univ a)

/-- Averaging (Markov for `[0,1]` values): if the mean of `N ≤ 1` is `≥ 1/2 + ε`, then
`N ≥ 1/2 + ε/2` on a set of probability `≥ ε/2`. -/
theorem good_set {α : Type} [Fintype α] [Nonempty α] (N : α → ℝ) (hN : ∀ a, N a ≤ 1) {ε : ℝ}
    (h : 1 / 2 + ε ≤ ex N) : ε / 2 ≤ ex (ind (fun a => 1 / 2 + ε / 2 ≤ N a)) := by
  have hpt : ∀ a, N a ≤ ind (fun a => 1 / 2 + ε / 2 ≤ N a) a * (1 / 2 - ε / 2) +
      (1 / 2 + ε / 2) := by
    intro a
    unfold ind
    split_ifs with h'
    · linarith [hN a]
    · push Not at h'; linarith
  have := ex_mono hpt
  rw [ex_add, ex_mul_const, ex_const] at this
  have h1 := ex_ind_le_one (fun a => 1 / 2 + ε / 2 ≤ N a)
  have h0 := ex_nonneg (f := ind (fun a => 1 / 2 + ε / 2 ≤ N a))
    (fun a => by unfold ind; split_ifs <;> norm_num)
  nlinarith

/-! ## The Goldreich–Levin theorem (one input length) -/

section GoldreichLevinSec

variable {k n l m : ℕ}

/-- The predictor `B` on input `(y, r)`. -/
def pred (B : (Fin (k + n) → Bool) → Bool) (y : Seed k) (r : Seed n) : Bool :=
  B (Fin.append y r)

/-- The inverter with random strings `R` and guesses `γ` for `⟨x, R a⟩`. -/
def glCand (B : (Fin (k + n) → Bool) → Bool) (sub : Fin m → Finset (Fin l))
    (R : Fin l → Seed n) (γ : Fin l → Bool) : Seed k → Seed n :=
  glInv B (fun i j => vxor (rsum R (sub j)) (unitv i)) (fun j => bsum (sub j) γ)

theorem maj_eq_of_lt {w : Fin m → Bool} {b : Bool}
    (h : m < 2 * (Finset.univ.filter (fun j => w j = b)).card) : maj w = b := by
  cases b
  · have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin m))) (fun j => w j = true)
    simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at hsum
    simp only [maj, decide_eq_false_iff_not, not_lt]
    omega
  · simpa [maj] using h

/-- With the correct guesses, coordinate `i` is recovered unless the vote fails. -/
theorem glCand_correct (B : (Fin (k + n) → Bool) → Bool) (sub : Fin m → Finset (Fin l))
    (R : Fin l → Seed n) (x : Seed n) (y : Seed k) (i : Fin n)
    (h : m < 2 * (Finset.univ.filter (fun j =>
      (fun r => pred B y (vxor r (unitv i)) = ip x (vxor r (unitv i))) (rsum R (sub j)))).card) :
    glCand B sub R (fun a => ip x (R a)) y i = x i := by
  apply maj_eq_of_lt
  convert h using 4 with j
  beta_reduce
  rw [← ip_rsum, ip_vxor, ip_unitv]
  unfold pred
  cases B (Fin.append y (vxor (rsum R (sub j)) (unitv i))) <;>
    cases ip x (rsum R (sub j)) <;> cases x i <;> decide

/-- For a good `x`, the candidate with the correct guesses is right with probability `≥ 1/2`. -/
theorem glCand_good (B : (Fin (k + n) → Bool) → Bool) (sub : Fin m → Finset (Fin l))
    (hsub : Function.Injective sub) (hne : ∀ j, (sub j).Nonempty) (f : Seed n → Seed k)
    {ε : ℝ} (hε : 0 < ε) (hm : 2 * n ≤ m * ε ^ 2) (x : Seed n)
    (hx : 1 / 2 + ε / 2 ≤ prob (fun r => pred B (f x) r = ip x r)) :
    1 / 2 ≤ ex (ind (fun R : Fin l → Seed n =>
      glCand B sub R (fun a => ip x (R a)) (f x) = x)) := by
  have hfail : ∀ i : Fin n, ex (ind (fun R : Fin l → Seed n => ¬ m < 2 *
      (Finset.univ.filter (fun j => (fun r => pred B (f x) (vxor r (unitv i)) =
        ip x (vxor r (unitv i))) (rsum R (sub j)))).card)) * (m * ε ^ 2) ≤ 1 := by
    intro i
    have hpi : prob (fun r => pred B (f x) (vxor r (unitv i)) = ip x (vxor r (unitv i))) =
        prob (fun r => pred B (f x) r = ip x r) := by
      rw [prob_eq_ex, prob_eq_ex]
      exact ex_vxor (unitv i) (ind fun r => pred B (f x) r = ip x r)
    have := prob_vote_fail sub hsub hne
      (fun r => pred B (f x) (vxor r (unitv i)) = ip x (vxor r (unitv i)))
      (δ := ε / 2) (by linarith) (by rw [hpi]; linarith)
    rw [prob_eq_ex, show (4 * (m : ℝ) * (ε / 2) ^ 2) = m * ε ^ 2 by ring] at this
    beta_reduce
    convert this
  have hunion := ex_ind_exists_le (fun (i : Fin n) (R : Fin l → Seed n) => ¬ m < 2 *
      (Finset.univ.filter (fun j => (fun r => pred B (f x) (vxor r (unitv i)) =
        ip x (vxor r (unitv i))) (rsum R (sub j)))).card)
  have hmε : 0 < (m : ℝ) * ε ^ 2 ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact Or.inr h0
    · left
      have : (0 : ℝ) < 2 * n := by positivity
      linarith
  have hsum : ∑ i : Fin n, ex (ind (fun R : Fin l → Seed n => ¬ m < 2 *
      (Finset.univ.filter (fun j => (fun r => pred B (f x) (vxor r (unitv i)) =
        ip x (vxor r (unitv i))) (rsum R (sub j)))).card)) ≤ 1 / 2 := by
    rcases hmε with hpos | h0
    · calc _ ≤ ∑ _i : Fin n, 1 / ((m : ℝ) * ε ^ 2) :=
            Finset.sum_le_sum fun i _ => by rw [le_div_iff₀ hpos]; exact hfail i
        _ = n / ((m : ℝ) * ε ^ 2) := by simp [Finset.sum_const]; ring
        _ ≤ 1 / 2 := by rw [div_le_iff₀ hpos]; linarith
    · subst h0; simp
  have hcorr : ∀ R : Fin l → Seed n, ind (fun R : Fin l → Seed n => ¬ ∃ i : Fin n, ¬ m < 2 *
      (Finset.univ.filter (fun j => (fun r => pred B (f x) (vxor r (unitv i)) =
        ip x (vxor r (unitv i))) (rsum R (sub j)))).card) R ≤
      ind (fun R : Fin l → Seed n => glCand B sub R (fun a => ip x (R a)) (f x) = x) R := by
    intro R
    unfold ind
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso; apply h2; push Not at h1
      funext i; exact glCand_correct B sub R x (f x) i (h1 i)
    · norm_num
    · exact le_rfl
  have := ex_mono hcorr
  rw [ex_ind_not] at this
  linarith

/-- An enumeration of the `2^l − 1` nonempty subsets of `Fin l`. -/
theorem exists_sub_enum (l : ℕ) : ∃ sub : Fin (2 ^ l - 1) → Finset (Fin l),
    Function.Injective sub ∧ ∀ j, (sub j).Nonempty := by
  have hc : Fintype.card {S : Finset (Fin l) // S.Nonempty} = 2 ^ l - 1 := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun S : Finset (Fin l) => S.Nonempty) =
        Finset.univ.erase ∅ := by
      ext S; simp [Finset.nonempty_iff_ne_empty]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin]
  let e := (Fintype.equivFinOfCardEq hc).symm
  exact ⟨fun j => (e j).1, fun a b h => e.injective (Subtype.ext h), fun j => (e j).2⟩

/-- **Goldreich–Levin** (one input length, explicit parameters). If the circuit `B` (size `sB`)
predicts `⟨x, r⟩` from `(f x, r)` with probability `≥ 1/2 + ε` over uniform `x, r`, and
`(2^l − 1) ε² ≥ 2n`, then some circuit `I` with `glInvSize n (2^l − 1) sB` gates recovers `x`
from `f x` with probability `≥ ε / 2^{l+2}`. -/
theorem goldreich_levin {k n l sB : ℕ} (hk : 0 < k) (hl : 0 < l) {f : Seed n → Seed k}
    {B : (Fin (k + n) → Bool) → Bool} (hB : HasCircuitOfSize B sB) {ε : ℝ} (hε : 0 < ε)
    (hm : 2 * n ≤ ((2 ^ l - 1 : ℕ) : ℝ) * ε ^ 2)
    (hpred : 1 / 2 + ε ≤ prob (fun p : Seed n × Seed n => pred B (f p.1) p.2 = ip p.1 p.2)) :
    ∃ I : Seed k → Seed n, HasMCircuitOfSize I (glInvSize n (2 ^ l - 1) sB) ∧
      ε / 2 ^ (l + 2) ≤ prob (fun x => I (f x) = x) := by
  obtain ⟨sub, hsub, hne⟩ := exists_sub_enum l
  have hm0 : 0 < 2 ^ l - 1 := by
    have : 2 ≤ 2 ^ l := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    omega
  let N : Seed n → ℝ := fun x => prob (fun r => pred B (f x) r = ip x r)
  have hN1 : ∀ x, N x ≤ 1 := fun x => by
    show prob _ ≤ 1; rw [prob_eq_ex]; exact ex_ind_le_one _
  have hexN : 1 / 2 + ε ≤ ex N := by
    rw [prob_prod] at hpred; exact hpred
  have hG := good_set N hN1 hexN
  let F : Seed n → (Fin l → Seed n) × (Fin l → Bool) → ℝ := fun x q =>
    ind (fun x => glCand B sub q.1 q.2 (f x) = x) x
  have hcard : (Fintype.card (Fin l → Bool) : ℝ) = 2 ^ l := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; rfl
  have hstep : ∀ x, ind (fun a => 1 / 2 + ε / 2 ≤ N a) x * (1 / 2 * (1 / 2 ^ l)) ≤
      ex (fun q => F x q) := by
    intro x
    rw [ex_prod]
    have h1 : ∀ R : Fin l → Seed n,
        ind (fun R : Fin l → Seed n => glCand B sub R (fun a => ip x (R a)) (f x) = x) R *
          (1 / 2 ^ l) ≤ ex (fun γ => F x (R, γ)) := by
      intro R
      unfold ind
      split_ifs with h
      · rw [one_mul, ← hcard]
        exact inv_card_le_ex_ind (P := fun γ => glCand B sub R γ (f x) = x) h
      · rw [zero_mul]
        exact ex_nonneg fun γ => by simp only [F, ind]; split_ifs <;> norm_num
    refine le_trans ?_ (ex_mono h1)
    rw [ex_mul_const]
    unfold ind
    split_ifs with hx
    · rw [one_mul]
      have := glCand_good B sub hsub hne f hε (by exact_mod_cast hm) x hx
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · rw [zero_mul]
      exact mul_nonneg (ex_nonneg fun R => by split_ifs <;> norm_num) (by positivity)
  have hall : ε / 2 ^ (l + 2) ≤ ex (fun x => ex (fun q => F x q)) := by
    refine le_trans ?_ (ex_mono hstep)
    rw [ex_mul_const]
    have : ε / 2 ^ (l + 2) = ε / 2 * (1 / 2 * (1 / 2 ^ l)) := by
      rw [pow_add]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hG (by positivity)
  rw [ex_comm] at hall
  obtain ⟨q, hq⟩ := exists_le_of_le_ex hall
  refine ⟨glCand B sub q.1 q.2, hasMCircuitOfSize_glInv hk hm0 hB _ _, ?_⟩
  rw [prob_eq_ex]
  exact hq

end GoldreichLevinSec

/-! ## Asymptotic version: one-way functions have the inner product as a hardcore bit -/

/-- A family of length-preserving functions `f ℓ : {0,1}^ℓ → {0,1}^ℓ`. -/
structure OWF where
  f : ∀ ℓ, Seed ℓ → Seed ℓ

/-- **One-wayness along input lengths `μ(n)`** (an explicit hypothesis, in the regime of
`PRG.SecureAlong`): for all polynomials `q`, `r` and all large `n`, every circuit with `q(2ⁿ)`
gates finds a preimage of `f(x)`, `x` uniform of length `μ(n)`, only with probability
`< 1 / r(2ⁿ)`. -/
def OWF.HardAlong (F : OWF) (μ : Polynomial ℕ) : Prop :=
  ∀ q r : Polynomial ℕ, ∃ N, ∀ n ≥ N, ∀ I : Seed (μ.eval n) → Seed (μ.eval n),
    HasMCircuitOfSize I (q.eval (2 ^ n)) →
      prob (fun x => F.f _ (I (F.f _ x)) = F.f _ x) * r.eval (2 ^ n) < 1

theorem prob_mono {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    prob P ≤ prob Q := by
  rw [prob_eq_ex, prob_eq_ex]
  exact ex_mono fun a => by unfold ind; split_ifs with h1 h2 <;> simp_all

/-- **Goldreich–Levin at one length, in the form used asymptotically.** If no circuit with
`S` gates inverts `f` with probability `≥ 1/R`, where `S`, `R` dominate explicit polynomials in
`L ≥ a`, `ρ` and `sB`, then every predictor with `sB` gates has advantage `< 1/ρ`. -/
theorem hardcore_at {a sB ρ L S R : ℕ} (ha : 0 < a) (hL : a ≤ L) (f : Seed a → Seed a)
    {B : (Fin (a + a) → Bool) → Bool} (hB : HasCircuitOfSize B sB)
    (hS : 102 * L * (2 * (2 * L * ρ ^ 2 + 1)) ^ 2 * (L + sB + 1) ≤ S)
    (hR : 8 * ρ * (2 * L * ρ ^ 2 + 1) ≤ R)
    (hard : ∀ I : Seed a → Seed a, HasMCircuitOfSize I S →
      prob (fun x => f (I (f x)) = f x) * R < 1) :
    (prob (fun p : Seed a × Seed a => pred B (f p.1) p.2 = ip p.1 p.2) - 1 / 2) * ρ < 1 := by
  by_contra hcon
  push Not at hcon
  have hρ0 : 0 < ρ := by
    rcases Nat.eq_zero_or_pos ρ with h | h
    · rw [h] at hcon; norm_num at hcon
    · exact h
  have hρR : (0 : ℝ) < ρ := by exact_mod_cast hρ0
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / ρ := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hpred : 1 / 2 + ε ≤ prob (fun p : Seed a × Seed a => pred B (f p.1) p.2 = ip p.1 p.2) := by
    have : ε ≤ prob (fun p : Seed a × Seed a => pred B (f p.1) p.2 = ip p.1 p.2) - 1 / 2 := by
      rw [hεdef, div_le_iff₀ hρR]; linarith
    linarith
  obtain ⟨A, hA⟩ : ∃ A, 2 * a * ρ ^ 2 + 1 = A := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, Nat.log 2 A + 1 = l := ⟨_, rfl⟩
  have hAl : A < 2 ^ l := by rw [← hl]; exact Nat.lt_pow_succ_log_self (by norm_num) A
  have hlA : 2 ^ l ≤ 2 * A := by
    rw [← hl, pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
  have hm : 2 * ((a : ℕ) : ℝ) ≤ ((2 ^ l - 1 : ℕ) : ℝ) * ε ^ 2 := by
    have h1 : 2 * a * ρ ^ 2 ≤ 2 ^ l - 1 := by omega
    have h2 : ((2 * a * ρ ^ 2 : ℕ) : ℝ) ≤ ((2 ^ l - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    rw [hεdef, div_pow, one_pow, mul_one_div, le_div_iff₀ (by positivity)]
    exact h2
  have hl0 : 0 < l := by omega
  obtain ⟨I, hI, hsucc⟩ := goldreich_levin ha hl0 hB hε hm hpred
  have hm0 : 0 < 2 ^ l - 1 := by omega
  have hAL : A ≤ 2 * L * ρ ^ 2 + 1 := by rw [← hA]; gcongr
  have hsize : glInvSize a (2 ^ l - 1) sB ≤ S := by
    refine (glInvSize_le hm0).trans (le_trans ?_ hS)
    have hm1 : 2 ^ l - 1 ≤ 2 * (2 * L * ρ ^ 2 + 1) := by omega
    gcongr
  have hinv := hard I (hI.mono hsize)
  have hmono : prob (fun x => I (f x) = x) ≤ prob (fun x => f (I (f x)) = f x) :=
    prob_mono fun x h => by rw [h]
  have hR' : (8 * ρ * (2 * L * ρ ^ 2 + 1) : ℝ) ≤ R := by exact_mod_cast hR
  have hA' : (A : ℝ) ≤ 2 * L * ρ ^ 2 + 1 := by exact_mod_cast hAL
  have hlA' : (2 : ℝ) ^ l ≤ 2 * A := by exact_mod_cast hlA
  have hkey : 1 ≤ ε / 2 ^ (l + 2) * (8 * ρ * (2 * L * ρ ^ 2 + 1)) := by
    rw [hεdef, pow_add]
    have h2l : (0 : ℝ) < 2 ^ l := by positivity
    rw [div_div, one_div_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  have h0 : (0 : ℝ) ≤ 8 * ρ * (2 * L * ρ ^ 2 + 1) := by positivity
  have hp0 : 0 ≤ prob (fun x => f (I (f x)) = f x) := prob_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right (hsucc.trans hmono) h0,
    mul_le_mul_of_nonneg_left hR' hp0]

/-- **Goldreich–Levin, asymptotic form.** If `F` is one-way along `μ(n) > 0`, then the inner
product is a hardcore predicate of `(x, r) ↦ (F x, r)`: every circuit with `q(2ⁿ)` gates
predicts `⟨x, r⟩` with advantage `< 1 / r(2ⁿ)` over a coin flip, for all large `n`. -/
theorem OWF.hardcore_ip (F : OWF) (μ : Polynomial ℕ) (hμ : ∀ n, 0 < μ.eval n)
    (hF : F.HardAlong μ) (q r : Polynomial ℕ) : ∃ N, ∀ n ≥ N,
      ∀ B : (Fin (μ.eval n + μ.eval n) → Bool) → Bool, HasCircuitOfSize B (q.eval (2 ^ n)) →
        (prob (fun p : Seed (μ.eval n) × Seed (μ.eval n) =>
          pred B (F.f _ p.1) p.2 = ip p.1 p.2) - 1 / 2) * r.eval (2 ^ n) < 1 := by
  open Polynomial in
  obtain ⟨N, hN⟩ := hF (102 * μ * (2 * (2 * μ * r ^ 2 + 1)) ^ 2 * (μ + q + 1))
    (8 * r * (2 * μ * r ^ 2 + 1))
  refine ⟨N, fun n hn B hB => ?_⟩
  refine hardcore_at (hμ n) (polynomial_eval_mono μ Nat.lt_two_pow_self.le) _ hB ?_ ?_
    (hN n hn)
  · simp
  · simp

end

end Pnp.NaturalProofs
