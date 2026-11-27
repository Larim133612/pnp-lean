import Pnp.Karp.SubsetSum

/-!
# SUBSET SUM: no carries in base `2^b`

A selection of the item rows sums to the target iff it is an exact cover (`ss_iff_excov`),
provided every digit lies in fewer than `2^b` items.
-/

namespace Pnp.Karp.SubsetSum

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Rows of `SS w` -/

theorem sa_sep_not_mem_digRow (b D : ℕ) (S : ℕ → Bool) : sep ∉ digRow b D S := by
  simp only [digRow, List.mem_flatMap, List.mem_range, not_exists, not_and]
  intro p _
  split <;> simp [List.mem_replicate]

theorem sa_clauses_SS (w : List SatSym) : clauses (SS w) = target w :: itemRows w := by
  apply Pnp.Karp.Clique.clauses_flatMap
  intro c hc
  simp only [List.mem_cons, itemRows, List.mem_map] at hc
  rcases hc with rfl | ⟨S, _, rfl⟩
  · exact sa_sep_not_mem_digRow _ _ _
  · exact sa_sep_not_mem_digRow _ _ _

/-! ## Values of rows -/

theorem sa_bv_append (A B : List SatSym) : bv (A ++ B) = bv A + 2 ^ A.length * bv B := by
  induction A with
  | nil => simp [bv]
  | cons s A ih => simp only [List.cons_append, bv, ih, List.length_cons, pow_succ]; ring

theorem sa_bv_replicate (n : ℕ) : bv (List.replicate n zero) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bv, ih]

theorem sa_blk_length (b : ℕ) (hb : 1 ≤ b) (s : Bool) :
    (if s then pos :: List.replicate (b - 1) zero else List.replicate b zero).length = b := by
  cases s <;> simp; omega

theorem sa_bv_blk (b : ℕ) (s : Bool) :
    bv (if s then pos :: List.replicate (b - 1) zero else List.replicate b zero) =
      if s then 1 else 0 := by
  cases s <;> simp [bv, sa_bv_replicate]

theorem sa_digRow_succ (b D : ℕ) (S : ℕ → Bool) : digRow b (D + 1) S = digRow b D S ++
    (if S D then pos :: List.replicate (b - 1) zero else List.replicate b zero) := by
  simp [digRow, List.range_succ, List.flatMap_append]

theorem sa_digRow_length (b D : ℕ) (hb : 1 ≤ b) (S : ℕ → Bool) :
    (digRow b D S).length = b * D := by
  induction D with
  | zero => simp [digRow]
  | succ D ih => rw [sa_digRow_succ, List.length_append, ih, sa_blk_length b hb]; ring

theorem sa_bv_digRow (b D : ℕ) (hb : 1 ≤ b) (S : ℕ → Bool) :
    bv (digRow b D S) = ∑ p ∈ Finset.range D, (if S p then 1 else 0) * 2 ^ (b * p) := by
  induction D with
  | zero => simp [digRow, bv]
  | succ D ih =>
    rw [sa_digRow_succ, sa_bv_append, ih, sa_digRow_length b D hb, sa_bv_blk b,
      Finset.sum_range_succ]
    ring

theorem sa_selSum (b D : ℕ) (hb : 1 ≤ b) :
    ∀ (Ss : List (ℕ → Bool)) (y : List Bool),
      selSum (Ss.map (digRow b D)) y = ∑ p ∈ Finset.range D, cnt Ss y p * 2 ^ (b * p)
  | [], y => by simp [selSum, cnt]
  | S :: Ss, y => by
    rw [List.map_cons, selSum, sa_selSum b D hb Ss y.tail]
    simp only [cnt, add_mul, Finset.sum_add_distrib]
    congr 1
    cases y.headD false <;> simp [sa_bv_digRow b D hb]

/-! ## Uniqueness of digits -/

theorem sa_sum_lt (B : ℕ) (c : ℕ → ℕ) :
    ∀ D, (∀ p < D, c p < B) → ∑ p ∈ Finset.range D, c p * B ^ p < B ^ D
  | 0, _ => by simp
  | D + 1, h => by
    rw [Finset.sum_range_succ, pow_succ]
    have ih := sa_sum_lt B c D (fun p hp => h p (by omega))
    have hD : c D + 1 ≤ B := h D (by omega)
    calc ∑ p ∈ Finset.range D, c p * B ^ p + c D * B ^ D
        < B ^ D + c D * B ^ D := by omega
      _ = (c D + 1) * B ^ D := by ring
      _ ≤ B * B ^ D := Nat.mul_le_mul_right _ hD
      _ = B ^ D * B := by ring

theorem sa_digits_eq (B : ℕ) (c d : ℕ → ℕ) :
    ∀ D, (∀ p < D, c p < B) → (∀ p < D, d p < B) →
      (∑ p ∈ Finset.range D, c p * B ^ p = ∑ p ∈ Finset.range D, d p * B ^ p ↔
        ∀ p < D, c p = d p)
  | 0, _, _ => by simp
  | D + 1, hc, hd => by
    have hc' : ∀ p < D, c p < B := fun p hp => hc p (by omega)
    have hd' : ∀ p < D, d p < B := fun p hp => hd p (by omega)
    have ih := sa_digits_eq B c d D hc' hd'
    have lc := sa_sum_lt B c D hc'
    have ld := sa_sum_lt B d D hd'
    have hBD : 0 < B ^ D := by
      rcases Nat.eq_zero_or_pos (B ^ D) with h0 | h0
      · omega
      · exact h0
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    constructor
    · intro he
      have h1 := congrArg (· / B ^ D) he
      have h2 := congrArg (· % B ^ D) he
      rw [Nat.add_mul_div_right _ _ hBD, Nat.add_mul_div_right _ _ hBD,
        Nat.div_eq_of_lt lc, Nat.div_eq_of_lt ld] at h1
      rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt lc,
        Nat.mod_eq_of_lt ld] at h2
      have hr := ih.1 h2
      intro p hp
      rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · exact hr p hp
      · omega
    · intro h
      rw [ih.2 (fun p hp => h p (by omega)), h D (by omega)]

/-! ## No carries -/

theorem ss_iff_excov (w : List SatSym) (hc : ∀ y p, cnt (itemsP w) y p < 2 ^ BW w) :
    SSLang (SS w) ↔ ExCov w := by
  have hb : 1 ≤ BW w := by unfold BW; omega
  have h1 : 1 < 2 ^ BW w := by
    have : 2 ^ 1 ≤ 2 ^ BW w := Nat.pow_le_pow_right (by norm_num) hb
    have : 2 ^ 2 ≤ 2 ^ BW w := Nat.pow_le_pow_right (by norm_num) (by unfold BW NV; omega)
    omega
  have hS : SSLang (SS w) ↔ ∃ y, selSum (itemRows w) y = bv (target w) := by
    unfold SSLang
    rw [sa_clauses_SS]
    constructor
    · rintro ⟨t, as, he, y, hy⟩
      cases he
      exact ⟨y, hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨_, _, rfl, y, hy⟩
  rw [hS, ExCov]
  apply exists_congr
  intro y
  rw [itemRows, target, sa_selSum _ _ hb, sa_bv_digRow _ _ hb]
  simp only [pow_mul, if_true]
  exact sa_digits_eq (2 ^ BW w) (cnt (itemsP w) y) (fun _ => 1) _ (fun p _ => hc y p)
    (fun _ _ => h1)

end Pnp.Karp.SubsetSum
