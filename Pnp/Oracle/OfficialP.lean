import Pnp.Oracle.FromTM2
import Pnp.Oracle.Official
import Pnp.Oracle.OfficialNP

/-!
# The official class `P` equals our class `P ∅`, and the bridge to the Clay statement

* `mem_P_empty_of_inPolynomialTime`: every language in the official, Mathlib-based class `P`
  (over the alphabet `Bool`) is decided by one of our stack programs in time `(|x|+2)^K`.
  The program is the compilation `Pnp.Relativize.FromTM2.prog` of the official machine; after
  simulating `time(|x|)` steps it reads the output symbol and halts.
* `mem_P_empty_iff`: together with `Official.inPolynomialTime_of_mem_P_empty`, our `P ∅` *is*
  the official `P` over `Bool`.
* `negativeBranch_of_NP_not_subset_P`: **bridge.**  If some language is in our `NP ∅` but not
  in our `P ∅`, then the official Clay statement `P ≠ NP` (`NegativeBranch`) holds.  So a
  separation proved entirely inside our simple stack-machine model settles the official problem.
-/

namespace Pnp.Relativize.OfficialP

open Turing Function Polynomial Pnp.Relativize.Comb Pnp.Relativize.FromTM2

/-- A polynomial over `ℕ` is bounded by `c * (n + 2) ^ d`. -/
theorem eval_le (p : ℕ[X]) : ∃ c d : ℕ, ∀ n : ℕ, p.eval n ≤ c * (n + 2) ^ d := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun n => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
  simp only [Finset.mem_range] at hi
  calc n ^ i ≤ (n + 2) ^ i := Nat.pow_le_pow_left (by omega) _
    _ ≤ (n + 2) ^ p.natDegree := Nat.pow_le_pow_right (by omega) (by omega)

/-- Constants are absorbed into a larger power of `n + 2`. -/
theorem absorb (a b d n : ℕ) : a * (n + 2) ^ d + b ≤ (n + 2) ^ (a + b + d) := by
  have h1 : 1 ≤ (n + 2) ^ d := Nat.one_le_pow _ _ (by omega)
  have h2 : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
  have h3 : 2 ^ (a + b) ≤ (n + 2) ^ (a + b) := Nat.pow_le_pow_left (by omega) _
  calc a * (n + 2) ^ d + b ≤ (a + b) * (n + 2) ^ d := by nlinarith
    _ ≤ (n + 2) ^ (a + b) * (n + 2) ^ d := Nat.mul_le_mul_right _ (by omega)
    _ = (n + 2) ^ (a + b + d) := by ring

theorem haltList_stk (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ).stk tm.k₁ = s := by
  simp [haltList]

/-- **Official `P` ⊆ our `P ∅`** (alphabet `Bool`). -/
theorem mem_P_empty_of_inPolynomialTime {L : Set Str}
    (h : Millennium.InPolynomialTime (Millennium.fin_encoding_string Bool) (fun x => x ∈ L)) :
    L ∈ P ∅ := by
  classical
  obtain ⟨f, comp, hf⟩ := h
  let tm := comp.tm
  let e₀ : tm.Γ tm.k₀ ≃ Bool := comp.inputAlphabet
  let e₁ : tm.Γ tm.k₁ ≃ Bool := comp.outputAlphabet
  obtain ⟨c, d, hcd⟩ := eval_le comp.time
  let a := c * (Dm tm * B tm e₀)
  let b := Nm tm e₀ + 2
  refine ⟨prog tm e₀ e₁, a + b + d, fun x => ⟨f x, ?_, (hf x).symm⟩⟩
  -- the official run
  let T := comp.time.eval x.length
  let c₀ : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ := initList tm (x.map e₀.symm)
  let g : tm.Γ tm.k₁ := e₁.symm (f x)
  have ho : TM2OutputsInTime tm (x.map e₀.symm) (some [g]) T := comp.outputsFun x
  obtain ⟨hT, -⟩ := Pnp.PPoly.outputsInTime_step' tm ho
  have hS := Pnp.PPoly.iterate_step'_stkInA tm (x.map e₀.symm)
  -- the encoding of the initial configuration is the input
  have hE : Enc tm e₀ c₀.stk (init [x]).stk := by
    intro k
    simp only [c₀]
    rw [Pnp.PPoly.initList_stk]
    by_cases hk : k = tm.k₀
    · subst hk
      simp only [dite_true, sk_k₀, init]
      exact (enc_k₀ tm e₀ x).symm
    · simp only [hk, dite_false, init]
      have := sk_ne_zero tm hk
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hj]; rfl
  obtain ⟨stk₁, t₁, h₁, ht₁, hE₁⟩ := sim_iter tm e₀ e₁ c₀ _ hS hE T
  rw [hT] at h₁ hE₁
  -- final phase: jump to the output reader, read the output symbol, halt
  have hSf := hS T
  rw [hT] at hSf
  have hStop : (haltList tm [g] : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ).stk tm.k₁ = g :: [] :=
    haltList_stk tm [g]
  have hg : g ∈ Pnp.PPoly.A tm tm.k₁ := hSf tm.k₁ g (by rw [hStop]; simp)
  have hrep : rep tm (haltList tm [g]) = .exec .halt tm.initialState := rfl
  rw [hrep] at h₁
  have h₂ := reach_nop (stk := stk₁)
    (nop_of tm e₀ e₁ (exec_mem tm e₀ (halt_mem tm) tm.initialState) rfl)
  have hN := N_le_Nm tm e₀ tm.k₁
  obtain ⟨t₃, ht₃, h₃⟩ := reach_top tm e₀ e₁ (k := tm.k₁) (z := idx tm e₀ (.fin false))
    (R := fun c => idx tm e₀ (.out c)) (T := fun i => idx tm e₀ (.fin (ans tm e₀ e₁ i)))
    (fun c hc => by rw [prog_idx tm e₀ e₁ (out_mem tm e₀ (by omega))]; rfl) hSf hE₁ hStop
  have hans : ans tm e₀ e₁ (ix tm e₀ tm.k₁ g) = f x := by
    simp only [ans, sy_ix tm e₀ hg, g, Equiv.apply_symm_apply]
  rw [hans] at h₃
  have hall := (h₁.trans h₂).trans h₃
  have hfin : runFor ∅ (prog tm e₀ e₁) (t₁ + 1 + t₃ + 1) (.run (init [x])) = .done (f x) := by
    have e0 : init [x] = ⟨idx tm e₀ (rep tm c₀), (init [x]).stk⟩ := by
      have : rep tm c₀ = .exec (tm.m tm.main) tm.initialState := rfl
      rw [this, idx_init]; rfl
    rw [e0, runFor_add]
    unfold Reach at hall
    rw [hall, runFor_succ_run]
    simp [step, prog_idx tm e₀ e₁ (fin_mem tm e₀ _), act]
  refine runFor_mono hfin ?_
  have hTle : T ≤ c * (x.length + 2) ^ d := hcd _
  have := Nat.mul_le_mul_right (Dm tm * B tm e₀) hTle
  have hab := absorb a b d x.length
  simp only [tb]
  have e : c * (x.length + 2) ^ d * (Dm tm * B tm e₀) = a * (x.length + 2) ^ d := by
    simp only [a]; ring
  omega

/-- Our `P ∅` is exactly the official class `P` over the alphabet `Bool`. -/
theorem mem_P_empty_iff {L : Set Str} :
    L ∈ P ∅ ↔
      Millennium.InPolynomialTime (Millennium.fin_encoding_string Bool) (fun x => x ∈ L) :=
  ⟨Official.inPolynomialTime_of_mem_P_empty, mem_P_empty_of_inPolynomialTime⟩

/-- **Bridge to the Clay statement.** A language in our `NP ∅` that is not in our `P ∅`
proves the official `P ≠ NP`. -/
theorem negativeBranch_of_NP_not_subset_P (h : ∃ L : Set Str, L ∈ NP ∅ ∧ L ∉ P ∅) :
    Millennium.ClayPVersusNP.Formulations.NegativeBranch := by
  obtain ⟨L, hN, hP⟩ := h
  intro hclay
  have hNP := OfficialNP.inNP_of_mem_NP_empty hN
  exact hP (mem_P_empty_of_inPolynomialTime ((hclay Bool (fun x => x ∈ L)).2 hNP))

end Pnp.Relativize.OfficialP
