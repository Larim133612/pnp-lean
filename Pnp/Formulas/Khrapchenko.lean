import Mathlib

/-!
# Khrapchenko's formula lower bound (M2)

De Morgan formulas: leaves are literals `xᵢ` / `¬xᵢ`, internal nodes are binary
`∧` / `∨`. The size measure is the number of leaves.

Khrapchenko (1971): if `F` is `1` on `A` and `0` on `B`, and `E(A,B)` is the set of
pairs `(a,b) ∈ A × B` at Hamming distance `1`, then `|E|² ≤ L(F) · |A| · |B|`.
Corollary: every de Morgan formula for PARITY on `n` variables has `≥ n²` leaves.
-/

namespace Pnp.Formulas

inductive Formula (n : ℕ) where
  | lit : Fin n → Bool → Formula n   -- `lit i c` is true at `x` iff `x i = c`
  | and : Formula n → Formula n → Formula n
  | or  : Formula n → Formula n → Formula n

namespace Formula

variable {n : ℕ}

def eval : Formula n → (Fin n → Bool) → Bool
  | lit i c, x => x i == c
  | and F G, x => F.eval x && G.eval x
  | or F G, x => F.eval x || G.eval x

/-- Formula size: number of leaves. -/
def leaves : Formula n → ℕ
  | lit _ _ => 1
  | and F G => F.leaves + G.leaves
  | or F G => F.leaves + G.leaves

end Formula

open Formula Finset

variable {n : ℕ}

/-- Pairs `(a, b) ∈ A × B` at Hamming distance exactly `1`. -/
def edges (A B : Finset (Fin n → Bool)) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  (A ×ˢ B).filter fun ab => hammingDist ab.1 ab.2 = 1

lemma eq_of_hammingDist_one {a b : Fin n → Bool} (h : hammingDist a b = 1) {i : Fin n}
    (hi : a i ≠ b i) {j : Fin n} (hj : j ≠ i) : a j = b j := by
  by_contra hne
  have hsub : ({i, j} : Finset (Fin n)) ⊆ univ.filter fun k => a k ≠ b k := by
    intro k hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp [*]
  have := card_le_card hsub
  rw [card_pair (Ne.symm hj)] at this
  unfold hammingDist at h
  omega

/-- If `b` is at distance one from `a` and differs at `i`, `b` is `a` with bit `i` flipped. -/
lemma eq_flip {a b : Fin n → Bool} (h : hammingDist a b = 1) {i : Fin n} (hi : a i ≠ b i) :
    b = Function.update a i (!a i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self]; revert hi; cases a j <;> cases b j <;> simp
  · rw [Function.update_of_ne hj]; exact (eq_of_hammingDist_one h hi hj).symm

lemma edges_split (A B : Finset (Fin n → Bool)) (p : (Fin n → Bool) → Prop) [DecidablePred p] :
    (edges A B).card = (edges A (B.filter p)).card + (edges A (B.filter fun b => ¬ p b)).card := by
  rw [← card_filter_add_card_filter_not (fun ab : _ × _ => p ab.2)]
  congr 2 <;> ext ⟨a, b⟩ <;> simp [edges] <;> tauto

lemma edges_split_left (A B : Finset (Fin n → Bool)) (p : (Fin n → Bool) → Prop)
    [DecidablePred p] :
    (edges A B).card = (edges (A.filter p) B).card + (edges (A.filter fun a => ¬ p a) B).card := by
  rw [← card_filter_add_card_filter_not (fun ab : _ × _ => p ab.1)]
  congr 2 <;> ext ⟨a, b⟩ <;> simp [edges] <;> tauto

/-- Cauchy–Schwarz-type step used at internal nodes. -/
lemma sq_add_le {e₁ e₂ L₁ L₂ X₁ X₂ : ℕ} (h₁ : e₁ ^ 2 ≤ L₁ * X₁) (h₂ : e₂ ^ 2 ≤ L₂ * X₂) :
    (e₁ + e₂) ^ 2 ≤ (L₁ + L₂) * (X₁ + X₂) := by
  have key : (2 * (e₁ * e₂)) ^ 2 ≤ (L₁ * X₂ + L₂ * X₁) ^ 2 := by
    have hm : (e₁ * e₂) ^ 2 ≤ (L₁ * X₁) * (L₂ * X₂) := by
      rw [mul_pow]; exact Nat.mul_le_mul h₁ h₂
    nlinarith [sq_nonneg ((L₁ * X₂ : ℤ) - L₂ * X₁)]
  have : 2 * (e₁ * e₂) ≤ L₁ * X₂ + L₂ * X₁ := by
    by_contra hc
    push Not at hc
    have := Nat.pow_lt_pow_left hc (two_ne_zero)
    omega
  nlinarith

/-- **Khrapchenko's theorem.** -/
theorem khrapchenko (F : Formula n) :
    ∀ A B : Finset (Fin n → Bool), (∀ a ∈ A, F.eval a = true) → (∀ b ∈ B, F.eval b = false) →
      (edges A B).card ^ 2 ≤ F.leaves * (A.card * B.card) := by
  induction F with
  | lit i c =>
    intro A B hA hB
    simp only [eval, beq_iff_eq, beq_eq_false_iff_ne] at hA hB
    -- every edge differs exactly at coordinate `i`, so each endpoint determines the edge
    have hdiff : ∀ ab ∈ edges A B, ab.1 i ≠ ab.2 i := by
      intro ab hab
      simp only [edges, mem_filter, mem_product] at hab
      rw [hA _ hab.1.1]; exact (hB _ hab.1.2).symm
    have hdist : ∀ ab ∈ edges A B, hammingDist ab.1 ab.2 = 1 := by
      intro ab hab; exact (mem_filter.1 hab).2
    have hleA : (edges A B).card ≤ A.card := by
      apply card_le_card_of_injOn Prod.fst
      · intro ab hab; exact (mem_product.1 (mem_filter.1 hab).1).1
      · intro ab hab ab' hab' he
        have e1 := eq_flip (hdist ab hab) (hdiff ab hab)
        have e2 := eq_flip (hdist ab' hab') (hdiff ab' hab')
        rw [he] at e1
        exact Prod.ext he (e1.trans e2.symm)
    have hleB : (edges A B).card ≤ B.card := by
      apply card_le_card_of_injOn Prod.snd
      · intro ab hab; exact (mem_product.1 (mem_filter.1 hab).1).2
      · intro ab hab ab' hab' he
        have h1 := hdist ab hab
        have h1' := hdist ab' hab'
        rw [hammingDist_comm] at h1 h1'
        have e1 := eq_flip h1 (Ne.symm (hdiff ab hab))
        have e2 := eq_flip h1' (Ne.symm (hdiff ab' hab'))
        rw [he] at e1
        exact Prod.ext (e1.trans e2.symm) he
    simp only [leaves, one_mul, sq]
    exact Nat.mul_le_mul hleA hleB
  | and F G ihF ihG =>
    intro A B hA hB
    simp only [eval, Bool.and_eq_true] at hA
    rw [edges_split A B (fun b => F.eval b = false)]
    have h1 := ihF A (B.filter fun b => F.eval b = false) (fun a ha => (hA a ha).1)
      (fun b hb => (mem_filter.1 hb).2)
    have h2 := ihG A (B.filter fun b => ¬ F.eval b = false) (fun a ha => (hA a ha).2)
      (fun b hb => by
        have := hB b (mem_filter.1 hb).1
        have hF := (mem_filter.1 hb).2
        simp only [eval] at this
        simp_all)
    have hc := card_filter_add_card_filter_not (s := B) (fun b => F.eval b = false)
    calc _ ≤ (F.leaves + G.leaves) * (A.card * (B.filter fun b => F.eval b = false).card +
            A.card * (B.filter fun b => ¬ F.eval b = false).card) := sq_add_le h1 h2
      _ = _ := by rw [leaves, ← mul_add, hc]
  | or F G ihF ihG =>
    intro A B hA hB
    simp only [eval, Bool.or_eq_false_iff] at hB
    rw [edges_split_left A B (fun a => F.eval a = true)]
    have h1 := ihF (A.filter fun a => F.eval a = true) B (fun a ha => (mem_filter.1 ha).2)
      (fun b hb => (hB b hb).1)
    have h2 := ihG (A.filter fun a => ¬ F.eval a = true) B
      (fun a ha => by
        have := hA a (mem_filter.1 ha).1
        have hF := (mem_filter.1 ha).2
        simp only [eval] at this
        simp_all)
      (fun b hb => (hB b hb).2)
    have hc := card_filter_add_card_filter_not (s := A) (fun a => F.eval a = true)
    calc _ ≤ (F.leaves + G.leaves) * ((A.filter fun a => F.eval a = true).card * B.card +
            (A.filter fun a => ¬ F.eval a = true).card * B.card) := sq_add_le h1 h2
      _ = _ := by rw [leaves, ← add_mul, hc]

/-! ## PARITY needs `n²` leaves -/

/-- Parity of the number of `true` bits, in `ZMod 2`. -/
def parity (x : Fin n → Bool) : ZMod 2 := ∑ i, if x i then 1 else 0

lemma parity_flip (a : Fin n → Bool) (i : Fin n) :
    parity (Function.update a i (!a i)) = parity a + 1 := by
  unfold parity
  have hu : (fun j => if Function.update a i (!a i) j then (1 : ZMod 2) else 0) =
      Function.update (fun j => if a j then (1 : ZMod 2) else 0) i (if !a i then 1 else 0) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hu, Finset.sum_update_of_mem (mem_univ i), ← Finset.add_sum_erase _ _ (mem_univ i),
    sdiff_singleton_eq_erase]
  have key : ∀ (c : Bool) (S : ZMod 2),
      (if (!c) = true then 1 else 0) + S = (if c = true then 1 else 0) + S + 1 := by decide
  exact key _ _

lemma hammingDist_flip (a : Fin n → Bool) (i : Fin n) :
    hammingDist a (Function.update a i (!a i)) = 1 := by
  unfold hammingDist
  rw [card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- In the full cube, the neighbours of `a` are exactly the `n` one-bit flips of `a`. -/
lemma card_neighbours (a : Fin n → Bool) :
    (univ.filter fun b : Fin n → Bool => hammingDist a b = 1).card = n := by
  have : (univ.filter fun b : Fin n → Bool => hammingDist a b = 1) =
      univ.image fun i => Function.update a i (!a i) := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      have : (univ.filter fun k => a k ≠ b k).Nonempty := by
        rw [← card_pos]; unfold hammingDist at h; omega
      obtain ⟨i, hi⟩ := this
      exact ⟨i, (eq_flip h (mem_filter.1 hi).2).symm⟩
    · rintro ⟨i, rfl⟩; exact hammingDist_flip a i
  rw [this, card_image_of_injective, card_univ, Fintype.card_fin]
  intro i j hij
  by_contra hne
  have := congrFun hij i
  dsimp only at this
  rw [Function.update_self, Function.update_of_ne hne] at this
  cases h : a i <;> simp [h] at this

lemma parity_eq_of_dist_one {a b : Fin n → Bool} (h : hammingDist a b = 1) :
    parity b = parity a + 1 := by
  have : (univ.filter fun k => a k ≠ b k).Nonempty := by
    rw [← card_pos]; unfold hammingDist at h; omega
  obtain ⟨i, hi⟩ := this
  rw [eq_flip h (mem_filter.1 hi).2, parity_flip]

/-- Counting edges from one side: if every neighbour of every `a ∈ A` lies in `B`, then
`|E(A,B)| = n · |A|`. -/
lemma card_edges_of_closed (A B : Finset (Fin n → Bool))
    (hAB : ∀ a ∈ A, ∀ b, hammingDist a b = 1 → b ∈ B) :
    (edges A B).card = n * A.card := by
  rw [edges, card_filter, sum_product]
  have h : ∀ a ∈ A, (∑ b ∈ B, if hammingDist a b = 1 then 1 else 0) = n := by
    intro a ha
    rw [← card_filter]
    have : B.filter (fun b => hammingDist a b = 1) = univ.filter fun b => hammingDist a b = 1 := by
      ext b
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hAB a ha b h, h⟩⟩
    rw [this, card_neighbours]
  rw [sum_congr rfl h, sum_const, smul_eq_mul, mul_comm]

lemma card_edges_comm (A B : Finset (Fin n → Bool)) :
    (edges A B).card = (edges B A).card := by
  apply card_nbij' Prod.swap Prod.swap
  · intro ab hab
    simp only [edges, coe_filter, mem_product, Set.mem_setOf_eq] at hab ⊢
    exact ⟨⟨hab.1.2, hab.1.1⟩, by rw [Prod.fst_swap, Prod.snd_swap, hammingDist_comm]; exact hab.2⟩
  · intro ab hab
    simp only [edges, coe_filter, mem_product, Set.mem_setOf_eq] at hab ⊢
    exact ⟨⟨hab.1.2, hab.1.1⟩, by rw [Prod.fst_swap, Prod.snd_swap, hammingDist_comm]; exact hab.2⟩
  · intro ab _; simp
  · intro ab _; simp

/-- The PARITY function on `n` bits. -/
def parityFn (x : Fin n → Bool) : Bool := decide (parity x = 1)

/-- **Khrapchenko's corollary.** Every de Morgan formula computing PARITY on `n ≥ 1`
variables has at least `n²` leaves. -/
theorem parity_formula_lower_bound (hn : 1 ≤ n) (F : Formula n)
    (hF : ∀ x, F.eval x = parityFn x) : n ^ 2 ≤ F.leaves := by
  set A := univ.filter fun x : Fin n → Bool => parity x = 1 with hAdef
  set B := univ.filter fun x : Fin n → Bool => parity x = 0 with hBdef
  have hA : ∀ a ∈ A, F.eval a = true := by
    intro a ha; rw [hF, parityFn]; simpa [A] using ha
  have hB : ∀ b ∈ B, F.eval b = false := by
    intro b hb; rw [hF, parityFn]; simp only [B, mem_filter, mem_univ, true_and] at hb; simp [hb]
  have hEA : (edges A B).card = n * A.card := by
    apply card_edges_of_closed
    intro a ha b hab
    simp only [A, B, mem_filter, mem_univ, true_and] at ha ⊢
    rw [parity_eq_of_dist_one hab, ha]; decide
  have hEB : (edges A B).card = n * B.card := by
    rw [card_edges_comm]
    apply card_edges_of_closed
    intro b hb a hab
    simp only [A, B, mem_filter, mem_univ, true_and] at hb ⊢
    rw [parity_eq_of_dist_one hab, hb]; decide
  have hK := khrapchenko F A B hA hB
  have h0 : parity (fun _ : Fin n => false) = 0 := by simp [parity]
  have hApos : 0 < A.card := by
    rw [card_pos]
    refine ⟨Function.update (fun _ => false) ⟨0, hn⟩ (!false), ?_⟩
    simp only [A, mem_filter, mem_univ, true_and]
    have := parity_flip (fun _ : Fin n => false) ⟨0, hn⟩
    rw [this, h0]; decide
  have hBpos : 0 < B.card := by
    rw [card_pos]; exact ⟨fun _ => false, by simp [B, h0]⟩
  have hsq : (edges A B).card ^ 2 = n ^ 2 * (A.card * B.card) := by
    rw [sq, sq]; nth_rewrite 1 [hEA]; rw [hEB]; ring
  rw [hsq] at hK
  exact Nat.le_of_mul_le_mul_right hK (Nat.mul_pos hApos hBpos)

end Pnp.Formulas
