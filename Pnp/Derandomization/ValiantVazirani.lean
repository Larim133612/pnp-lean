import Pnp.Derandomization.Lautemann

/-!
# The Valiant–Vazirani isolation lemma (M23)

A random affine hash `h(x) = (⟨aᵢ, x⟩ ⊕ bᵢ)ᵢ₌₁..ₘ` over `GF(2)` is pairwise independent:
`Pr[h x = 0] = 2^{-m}` and `Pr[h x = 0 ∧ h x' = 0] = 4^{-m}` for `x ≠ x'`
(`prob_hashZero`, `prob_hashZero_pair`). Consequently (`isolation`), if
`2^j ≤ |S| ≤ 2^{j+1}` and `m = j + 2`, then with probability `≥ 1/8` exactly one element of
`S` survives the constraint `h x = 0`.

Applied to the satisfying assignments of a circuit `C` (`valiant_vazirani`): if `C` is
satisfiable, then for a suitable `m ≤ n + 2`, with probability `≥ 1/8` the circuit
`C'(x) = C(x) ∧ h(x) = 0` (with `s + m (n + 3)` gates) has exactly one satisfying assignment;
if `C` is unsatisfiable, so is every `C'`. This is the randomized reduction from `SAT` to
"unique `SAT`" (`NP ⊆ RP^{UP-promise}`), in circuit form.
-/

namespace Pnp.Derand

open Pnp.Circuits Pnp.NaturalProofs Classical

noncomputable section

/-! ## Inner products -/

theorem ip_comm {n : ℕ} (x r : Seed n) : ip x r = ip r x := by
  unfold ip; congr 1; funext i; exact Bool.and_comm _ _

theorem ip_vxor_left {n : ℕ} (x x' r : Seed n) : ip (vxor x x') r = xor (ip x r) (ip x' r) := by
  rw [ip_comm, ip_vxor, ip_comm r, ip_comm r]

/-- For `d ≠ 0`, `⟨d, a⟩` is an unbiased bit. -/
theorem prob_ip_false {n : ℕ} {d : Seed n} (hd : d ≠ fun _ => false) :
    prob (fun a : Seed n => ip d a = false) = 1 / 2 := by
  obtain ⟨i, hi⟩ : ∃ i, d i = true := by
    by_contra h; push Not at h; exact hd (funext fun i => by simpa using h i)
  have h1 := prob_vxor (unitv i) (fun a : Seed n => ip d a = false)
  have h2 : (fun a : Seed n => ip d (vxor a (unitv i)) = false) =
      fun a => ¬ (ip d a = false) := by
    funext a; rw [ip_vxor, ip_unitv, hi]; cases ip d a <;> simp
  rw [h2, prob_eq_ex, prob_eq_ex, ex_ind_not] at h1
  rw [prob_eq_ex]; linarith

/-! ## Random affine hashing -/

/-- A hash function: `m` rows `(aᵢ, bᵢ)`. -/
abbrev Hash (n m : ℕ) := Fin m → Seed n × Bool

/-- `h x = 0`: every row is satisfied, `⟨x, aᵢ⟩ = bᵢ`. -/
def hashZero {n m : ℕ} (h : Hash n m) (x : Seed n) : Prop := ∀ i, ip x (h i).1 = (h i).2

theorem prob_row {n : ℕ} (x : Seed n) :
    prob (fun p : Seed n × Bool => ip x p.1 = p.2) = 1 / 2 := by
  rw [prob_eq_ex, ex_prod]
  have : ∀ a : Seed n, ex (fun c : Bool => ind (fun p : Seed n × Bool => ip x p.1 = p.2) (a, c))
      = 1 / 2 := by
    intro a
    rw [ex_bool]; unfold ind
    cases h : ip x a <;> simp [h]
  simp only [this, ex_const]

theorem prob_row_pair {n : ℕ} {x x' : Seed n} (hx : x ≠ x') :
    prob (fun p : Seed n × Bool => ip x p.1 = p.2 ∧ ip x' p.1 = p.2) = 1 / 4 := by
  rw [prob_eq_ex, ex_prod]
  have : ∀ a : Seed n,
      ex (fun c : Bool => ind (fun p : Seed n × Bool => ip x p.1 = p.2 ∧ ip x' p.1 = p.2) (a, c))
      = 1 / 2 * ind (fun a : Seed n => ip (vxor x x') a = false) a := by
    intro a
    rw [ex_bool]; unfold ind
    simp only [ip_vxor_left]
    split_ifs <;> simp_all
  simp only [this]
  rw [ex_const_mul, ← prob_eq_ex, prob_ip_false]
  · norm_num
  · intro h
    apply hx; funext i
    have := congrFun h i
    simp only [vxor] at this
    cases hx1 : x i <;> cases hx2 : x' i <;> simp_all

/-- **Pairwise independence, part 1.** `Pr_h[h x = 0] = 2^{-m}`. -/
theorem prob_hashZero {n m : ℕ} (x : Seed n) :
    prob (fun h : Hash n m => hashZero h x) = (1 / 2) ^ m := by
  rw [← prob_row x]
  exact prob_forall_pi m (fun p : Seed n × Bool => ip x p.1 = p.2)

/-- **Pairwise independence, part 2.** `Pr_h[h x = 0 ∧ h x' = 0] = 4^{-m}` for `x ≠ x'`. -/
theorem prob_hashZero_pair {n m : ℕ} {x x' : Seed n} (hx : x ≠ x') :
    prob (fun h : Hash n m => hashZero h x ∧ hashZero h x') = (1 / 4) ^ m := by
  rw [← prob_row_pair hx, ← prob_forall_pi m]
  congr 1; funext h
  simp only [hashZero, forall_and]

/-! ## Isolation -/

/-- `x` is the unique element of `S` with `h x = 0`. -/
def Unique' {n m : ℕ} (S : Finset (Seed n)) (h : Hash n m) (x : Seed n) : Prop :=
  hashZero h x ∧ ∀ x' ∈ S, hashZero h x' → x' = x

theorem ind_exists_unique_eq {n m : ℕ} (S : Finset (Seed n)) (h : Hash n m) :
    ind (fun h => ∃ x ∈ S, Unique' S h x) h = ∑ x ∈ S, ind (fun h => Unique' S h x) h := by
  by_cases hex : ∃ x ∈ S, Unique' S h x
  · obtain ⟨x, hx, hU⟩ := hex
    rw [Finset.sum_eq_single (f := fun y => ind (fun h => Unique' S h y) h) x
      (fun y hy hyx => by
        unfold ind; exact if_neg fun (hUy : Unique' S h y) => hyx (hU.2 y hy hUy.1))
      (fun hx' => absurd hx hx')]
    unfold ind; rw [if_pos ⟨x, hx, hU⟩, if_pos hU]
  · unfold ind
    rw [if_neg hex, Finset.sum_eq_zero fun x hx => if_neg fun hu => hex ⟨x, hx, hu⟩]

theorem ind_unique_ge {n m : ℕ} (S : Finset (Seed n)) (x : Seed n) (h : Hash n m) :
    ind (fun h => hashZero h x) h -
      ∑ x' ∈ S.erase x, ind (fun h => hashZero h x ∧ hashZero h x') h ≤
      ind (fun h => Unique' S h x) h := by
  have hnn : 0 ≤ ∑ x' ∈ S.erase x, ind (fun h => hashZero h x ∧ hashZero h x') h :=
    Finset.sum_nonneg fun _ _ => by unfold ind; split_ifs <;> norm_num
  have hU0 : 0 ≤ ind (fun h => Unique' S h x) h := by unfold ind; split_ifs <;> norm_num
  by_cases hz : hashZero h x
  · by_cases hu : ∀ x' ∈ S, hashZero h x' → x' = x
    · have : ∑ x' ∈ S.erase x, ind (fun h => hashZero h x ∧ hashZero h x') h = 0 :=
        Finset.sum_eq_zero fun x' hx' => if_neg fun hp =>
          (Finset.ne_of_mem_erase hx') (hu x' (Finset.mem_of_mem_erase hx') hp.2)
      rw [this]; unfold ind; rw [if_pos hz, if_pos ⟨hz, hu⟩]; norm_num
    · push Not at hu
      obtain ⟨x', hx'S, hz', hne⟩ := hu
      have : (1 : ℝ) ≤ ∑ x' ∈ S.erase x, ind (fun h => hashZero h x ∧ hashZero h x') h := by
        calc (1 : ℝ) = ind (fun h => hashZero h x ∧ hashZero h x') h := by
              unfold ind; rw [if_pos ⟨hz, hz'⟩]
          _ ≤ _ := Finset.single_le_sum (f := fun x' => ind (fun h => hashZero h x ∧
              hashZero h x') h) (fun _ _ => by unfold ind; split_ifs <;> norm_num)
              (Finset.mem_erase.2 ⟨hne, hx'S⟩)
      have h1 : ind (fun h => hashZero h x) h ≤ 1 := by unfold ind; split_ifs <;> norm_num
      linarith
  · have : ind (fun h => hashZero h x) h = 0 := if_neg hz
    linarith

/-- **Isolation lemma.** If `2^j ≤ |S| ≤ 2^{j+1}` then a random hash with `m = j + 2` rows
isolates exactly one element of `S` with probability `≥ 1/8`. -/
theorem isolation {n j : ℕ} (S : Finset (Seed n)) (h1 : 2 ^ j ≤ S.card)
    (h2 : S.card ≤ 2 ^ (j + 1)) :
    1 / 8 ≤ prob (fun h : Hash n (j + 2) => ∃ x ∈ S, Unique' S h x) := by
  set q : ℝ := (1 / 2) ^ (j + 2)
  have hpair : ∀ x ∈ S, ∀ x' ∈ S.erase x,
      ex (ind (fun h : Hash n (j + 2) => hashZero h x ∧ hashZero h x')) = q ^ 2 := by
    intro x _ x' hx'
    rw [← prob_eq_ex, prob_hashZero_pair (Finset.ne_of_mem_erase hx').symm]
    simp only [q]; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hx : ∀ x ∈ S, q - (S.card - 1) * q ^ 2 ≤
      ex (ind (fun h : Hash n (j + 2) => Unique' S h x)) := by
    intro x hxS
    have := ex_mono (ind_unique_ge (m := j + 2) S x)
    rw [ex_sub, ex_sum] at this
    rw [← prob_eq_ex, prob_hashZero, Finset.sum_congr rfl (hpair x hxS), Finset.sum_const,
      Finset.card_erase_of_mem hxS, nsmul_eq_mul] at this
    have hc : ((S.card - 1 : ℕ) : ℝ) = S.card - 1 := by
      have : 1 ≤ S.card := Finset.card_pos.2 ⟨x, hxS⟩
      push_cast [this]; ring
    rw [hc] at this
    exact this
  rw [prob_eq_ex]
  have hE : ex (ind (fun h : Hash n (j + 2) => ∃ x ∈ S, Unique' S h x)) =
      ∑ x ∈ S, ex (ind (fun h : Hash n (j + 2) => Unique' S h x)) := by
    rw [← ex_sum]; congr 1; funext h; exact ind_exists_unique_eq S h
  rw [hE]
  have hsum := Finset.sum_le_sum hx
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  refine le_trans ?_ hsum
  -- p = |S| q ∈ [1/4, 1/2]
  have hq : q = 1 / 4 * (1 / 2) ^ j := by
    simp only [q]; rw [pow_add]; ring
  have hj : (0 : ℝ) < 2 ^ j := by positivity
  have hp1 : 1 / 4 ≤ (S.card : ℝ) * q := by
    have : ((2 : ℝ) ^ j) ≤ S.card := by exact_mod_cast h1
    rw [hq, one_div_pow]
    rw [show (S.card : ℝ) * (1 / 4 * (1 / 2 ^ j)) = S.card / 2 ^ j / 4 by ring]
    rw [le_div_iff₀ (by norm_num), le_div_iff₀ hj]; linarith
  have hp2 : (S.card : ℝ) * q ≤ 1 / 2 := by
    have : (S.card : ℝ) ≤ 2 ^ (j + 1) := by exact_mod_cast h2
    rw [hq, one_div_pow]
    rw [show (S.card : ℝ) * (1 / 4 * (1 / 2 ^ j)) = S.card / 2 ^ j / 4 by ring]
    rw [div_le_iff₀ (by norm_num), div_le_iff₀ hj]; rw [pow_succ] at this; linarith
  have hq0 : 0 ≤ q := by positivity
  nlinarith

/-! ## Circuit form -/

/-- One hash row `x ↦ ⟨x, a⟩ ⊕ b` with `a, b` hard-wired: `2n + 4` gates. -/
theorem hasCircuitOfSize_row {n : ℕ} (hn : 0 < n) (a : Seed n) (b : Bool) :
    HasCircuitOfSize (fun x : Seed n => xor (ip x a) b) (2 * n + 4) := by
  have h1 := (hasMCircuitOfSize_append_const hn a).comp_single
    (hasCircuitOfSize_ip (n := n + n) (by omega) (Fin.castAdd n) (Fin.natAdd n))
  have h2 := (h1.toM 1).comp_single (hasCircuitOfSize_xor_const b)
  convert h2.mono (s' := 2 * n + 4) (by unfold ipSize; omega) using 2 with x
  simp only [Function.comp, Fin.append_left, Fin.append_right]

/-- The final gate block: `v₀ ∧ ¬(v₁ ∨ … ∨ v_{k+1})` with `k + 1` gates. -/
theorem hasCircuitOfSize_andNotAny (k : ℕ) :
    HasCircuitOfSize (fun v : Fin (k + 2) → Bool => v 0 && !decide (∃ i : Fin (k + 1),
      v i.succ = true)) (k + 1) := by
  have ht := (hasMCircuitOfSize_rewire (n := k + 2) (m := k + 1) Fin.succ).comp_single
    (hasCircuitOfSize_any k)
  have h2 := ((hasCircuitOfSize_var (n := k + 2) 0).cons (ht.toM 1)).comp_single
    (hasCircuitOfSize_gate2 (fun u w => u && !w))
  convert h2.mono (s' := k + 1) (by omega) using 2 with v
  rfl

/-- `C'(x) = C(x) ∧ h(x) = 0`. -/
def hashed {n m : ℕ} (C : Seed n → Bool) (h : Hash n m) (x : Seed n) : Bool :=
  C x && decide (hashZero h x)

/-- `C'` has `s + m (2n + 5)` gates. -/
theorem hasCircuitOfSize_hashed {n s k : ℕ} (hn : 0 < n) {C : Seed n → Bool}
    (hC : HasCircuitOfSize C s) (h : Hash n (k + 1)) :
    HasCircuitOfSize (hashed C h) (s + (k + 1) * (2 * n + 5)) := by
  have hrows := hasMCircuitOfSize_of_forall (fun x (i : Fin (k + 1)) => xor (ip x (h i).1) (h i).2)
    fun i => hasCircuitOfSize_row hn (h i).1 (h i).2
  have h3 := (hC.cons hrows).comp_single (hasCircuitOfSize_andNotAny k)
  convert h3.mono (s' := s + (k + 1) * (2 * n + 5)) (by nlinarith) using 1
  funext x
  show (C x && decide (hashZero h x)) =
    (C x && !decide (∃ i : Fin (k + 1), xor (ip x (h i).1) (h i).2 = true))
  congr 1
  unfold hashZero
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_exists]
  refine forall_congr' fun i => ?_
  cases ip x (h i).1 <;> cases (h i).2 <;> simp

/-- **Valiant–Vazirani** (circuit form). Let `C` be a circuit with `s` gates on `n > 0`
inputs.
* If `C` is unsatisfiable, so is every `C' = C ∧ (h = 0)`.
* If `C` is satisfiable, there is `j ≤ n` such that for a random hash `h` with `m = j + 2`
  rows, with probability `≥ 1/8` the circuit `C'` (with `s + m (2n + 5)` gates) has exactly one
  satisfying assignment. -/
theorem valiant_vazirani {n s : ℕ} (hn : 0 < n) {C : Seed n → Bool}
    (hC : HasCircuitOfSize C s) :
    ((∀ x, C x = false) → ∀ (m : ℕ) (h : Hash n m) x, hashed C h x = false) ∧
    ((∃ x, C x = true) → ∃ j ≤ n,
      1 / 8 ≤ prob (fun h : Hash n (j + 2) => ∃! x, hashed C h x = true) ∧
      ∀ h : Hash n (j + 2), HasCircuitOfSize (hashed C h) (s + (j + 2) * (2 * n + 5))) := by
  refine ⟨fun hno m h x => by simp [hashed, hno x], fun ⟨x₀, hx₀⟩ => ?_⟩
  set S := Finset.univ.filter (fun x : Seed n => C x = true)
  have hS0 : S.card ≠ 0 := Finset.card_ne_zero.2 ⟨x₀, by simp [S, hx₀]⟩
  have hSn : S.card ≤ 2 ^ n := by
    calc S.card ≤ (Finset.univ : Finset (Seed n)).card := Finset.card_filter_le _ _
      _ = 2 ^ n := by simp
  set j := Nat.log 2 S.card
  have h1 : 2 ^ j ≤ S.card := Nat.pow_log_le_self 2 hS0
  have h2 : S.card < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hjn : j ≤ n := by
    have : 2 ^ j < 2 ^ (n + 1) := lt_of_le_of_lt (h1.trans hSn) (by
      rw [pow_succ]; have := Nat.one_le_two_pow (n := n); omega)
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 this
    omega
  refine ⟨j, hjn, ?_, fun h => hasCircuitOfSize_hashed hn hC h⟩
  refine (isolation S h1 h2.le).trans (prob_mono fun h ⟨x, hxS, hU⟩ => ⟨x, ?_, ?_⟩)
  · simp only [hashed, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(Finset.mem_filter.1 hxS).2, hU.1⟩
  · intro y hy
    simp only [hashed, Bool.and_eq_true, decide_eq_true_eq] at hy
    exact hU.2 y (by simp [S, hy.1]) hy.2

end

end Pnp.Derand
