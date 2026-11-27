import Pnp.NaturalProofs.BMCircuits

/-!
# Pseudorandom generators from one-way permutations (M17)

Blum–Micali / Yao with the Goldreich–Levin hardcore bit. For a permutation `f` of `{0,1}^a`,

`G(x, r) = (⟨x,r⟩, ⟨f x,r⟩, …, ⟨f^{T-1} x,r⟩, f^T x, r)`

stretches `2a` bits to `T + 2a`. A distinguisher for `G` gives, by the hybrid argument and
Yao's "distinguisher ⇒ predictor" step, a predictor for `⟨z, r⟩` from `(f z, r)`
(`bm_reduction`); Goldreich–Levin then inverts `f`.
-/

namespace Pnp.NaturalProofs

open Pnp.Circuits Classical

noncomputable section

/-- Real value of a test. -/
def bv (b : Bool) : ℝ := if b then 1 else 0

theorem ex_bool (g : Bool → ℝ) : ex g = (g true + g false) / 2 := by
  rw [ex, Fintype.sum_bool, Fintype.card_bool]; norm_num

section Concrete

variable {a : ℕ}

/-- The sample `(y, r, β)` as a string. -/
def smp (y r : Seed a) (β : Bool) : Fin (a + a + 1) → Bool := Fin.append (Fin.append y r) (fun _ => β)

/-- Hybrid `j` as a function of `(u, x, r)`: the first `j` bits are `u`, the rest are real. -/
def hstr (f : Seed a → Seed a) (T j : ℕ) (u : Fin T → Bool) (x r : Seed a) :
    Fin (T + (a + a)) → Bool :=
  Fin.append (fun i : Fin T => if i.val < j then u i else ip (f^[i.val] x) r)
    (Fin.append (f^[T] x) r)

theorem bmHyb_smp (f : Seed a → Seed a) (T j : ℕ) (u : Fin T → Bool) (y r : Seed a) (β : Bool) :
    bmHyb f T j u (smp y r β) = Fin.append (fun i : Fin T => if i.val < j then u i else
      if i.val = j then β else ip (f^[i.val - j - 1] y) r) (Fin.append (f^[T - j - 1] y) r) := by
  have hl : Fin.last (a + a) = Fin.natAdd (a + a) (0 : Fin 1) := rfl
  simp only [bmHyb, smp, hl, Fin.append_left, Fin.append_right]

theorem iterate_split (f : Seed a → Seed a) {i j : ℕ} (h : j < i) (x : Seed a) :
    f^[i - j - 1] (f (f^[j] x)) = f^[i] x := by
  rw [← Function.iterate_succ_apply' f j x, ← Function.iterate_add_apply]
  congr 1; omega

theorem hstr_eq (f : Seed a → Seed a) {T j : ℕ} (hj : j < T) (u : Fin T → Bool) (x r : Seed a) :
    hstr f T j u x r = bmHyb f T j u (smp (f (f^[j] x)) r (ip (f^[j] x) r)) := by
  rw [bmHyb_smp, hstr, iterate_split f hj]
  congr 1
  funext i
  by_cases h1 : i.val < j
  · simp [h1]
  · by_cases h2 : i.val = j
    · simp [h2]
    · simp only [h1, h2, if_false]
      rw [iterate_split f (by omega)]

theorem hstr_succ_eq (f : Seed a → Seed a) {T j : ℕ} (hj : j < T) (u : Fin T → Bool)
    (x r : Seed a) :
    hstr f T (j + 1) u x r = bmHyb f T j u (smp (f (f^[j] x)) r (u ⟨j, hj⟩)) := by
  rw [bmHyb_smp, hstr, iterate_split f hj]
  congr 1
  funext i
  by_cases h1 : i.val < j
  · simp [h1, show i.val < j + 1 by omega]
  · by_cases h2 : i.val = j
    · have : i = ⟨j, hj⟩ := Fin.ext h2
      simp [this]
    · simp only [h1, h2, if_false, show ¬ i.val < j + 1 by omega]
      rw [iterate_split f (by omega)]

theorem bmHyb_update (f : Seed a → Seed a) {T j : ℕ} (hj : j < T) (u : Fin T → Bool) (β : Bool)
    (w : Fin (a + a + 1) → Bool) :
    bmHyb f T j (Function.update u ⟨j, hj⟩ β) w = bmHyb f T j u w := by
  simp only [bmHyb]
  congr 1
  funext i
  by_cases h1 : i.val < j
  · have : i ≠ ⟨j, hj⟩ := fun h => by rw [h] at h1; exact lt_irrefl _ h1
    simp [h1, Function.update_of_ne this]
  · simp [h1]

variable (f : Seed a → Seed a) (T : ℕ) (D : (Fin (T + (a + a)) → Bool) → Bool)

/-- Acceptance probability on hybrid `j`. -/
def bhyb (j : ℕ) : ℝ :=
  ex (fun ω : (Fin T → Bool) × (Seed a × Seed a) => bv (D (hstr f T j ω.1 ω.2.1 ω.2.2)))

theorem bhyb_zero : bhyb f T D 0 = ex (fun p : Seed a × Seed a => bv (D (bmOut f T p.1 p.2))) := by
  rw [bhyb, ex_prod]
  simp only [hstr, bmOut, Nat.not_lt_zero, if_false, ex_const]

theorem bhyb_T (hf : Function.Bijective f) :
    bhyb f T D T = ex (fun w : Fin (T + (a + a)) → Bool => bv (D w)) := by
  let e : (Fin T → Bool) × (Seed a × Seed a) ≃ (Fin (T + (a + a)) → Bool) :=
    (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.ofBijective _ (hf.iterate T))
      (Equiv.refl _)).trans (Fin.appendEquiv a a))).trans (Fin.appendEquiv T (a + a))
  rw [bhyb, ← ex_equiv e]
  congr 1
  funext ω
  congr 2
  simp only [hstr, e, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    id, Equiv.ofBijective_apply, Fin.appendEquiv]
  congr 1
  funext i
  simp [i.2]

/-- Acceptance probability on the real bit, prefix `u`, at position `j`. -/
def qReal (j : ℕ) (u : Fin T → Bool) : ℝ :=
  ex (fun p : Seed a × Seed a => bv (D (bmHyb f T j u (smp (f p.1) p.2 (ip p.1 p.2)))))

/-- Acceptance probability on a uniform bit. -/
def qRand (j : ℕ) (u : Fin T → Bool) : ℝ :=
  ex (fun p : Seed a × Seed a => ex (fun β : Bool => bv (D (bmHyb f T j u (smp (f p.1) p.2 β)))))

theorem bhyb_eq_qReal (hf : Function.Bijective f) {j : ℕ} (hj : j < T) :
    bhyb f T D j = ex (fun u => qReal f T D j u) := by
  rw [bhyb, ex_prod]
  congr 1; funext u
  let e : Seed a × Seed a ≃ Seed a × Seed a :=
    Equiv.prodCongr (Equiv.ofBijective _ (hf.iterate j)) (Equiv.refl _)
  refine Eq.trans ?_ (ex_equiv e (fun p : Seed a × Seed a =>
    bv (D (bmHyb f T j u (smp (f p.1) p.2 (ip p.1 p.2))))))
  congr 1; funext p
  rw [hstr_eq f hj]
  rfl

theorem bhyb_succ_eq_qRand (hf : Function.Bijective f) {j : ℕ} (hj : j < T) :
    bhyb f T D (j + 1) = ex (fun u => qRand f T D j u) := by
  have h1 : bhyb f T D (j + 1) = ex (fun p : Seed a × Seed a => ex (fun u : Fin T → Bool =>
      bv (D (bmHyb f T j u (smp (f (f^[j] p.1)) p.2 (u ⟨j, hj⟩)))))) := by
    rw [bhyb, ex_prod, ex_comm]
    congr 1; funext p; congr 1; funext u
    rw [hstr_succ_eq f hj]
  have h2 : ∀ p : Seed a × Seed a,
      ex (fun u : Fin T → Bool =>
        bv (D (bmHyb f T j u (smp (f (f^[j] p.1)) p.2 (u ⟨j, hj⟩))))) =
      ex (fun u : Fin T → Bool => ex (fun β : Bool =>
        bv (D (bmHyb f T j u (smp (f (f^[j] p.1)) p.2 β))))) := by
    intro p
    rw [ex_update ⟨j, hj⟩]
    congr 1; funext u; congr 1; funext β
    rw [Function.update_self, bmHyb_update]
  rw [h1, funext h2, ex_comm (fun (p : Seed a × Seed a) (u : Fin T → Bool) => ex (fun β : Bool =>
    bv (D (bmHyb f T j u (smp (f (f^[j] p.1)) p.2 β)))))]
  refine congrArg ex (funext fun u => ?_)
  let e : Seed a × Seed a ≃ Seed a × Seed a :=
    Equiv.prodCongr (Equiv.ofBijective _ (hf.iterate j)) (Equiv.refl _)
  have := ex_equiv e (fun p : Seed a × Seed a => ex (fun β : Bool =>
    bv (D (bmHyb f T j u (smp (f p.1) p.2 β)))))
  rw [qRand, ← this]
  rfl

theorem abs_ex_le {α : Type} [Fintype α] (h : α → ℝ) : |ex h| ≤ ex (fun a => |h a|) := by
  rw [ex, ex, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card α))]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- **Hybrid step.** Some position `j` and prefix `u` carry a `1/T` share of the advantage. -/
theorem exists_step (hf : Function.Bijective f) (hT : 0 < T) : ∃ j < T, ∃ u : Fin T → Bool,
    |ex (fun w : Fin (T + (a + a)) → Bool => bv (D w)) -
      ex (fun p : Seed a × Seed a => bv (D (bmOut f T p.1 p.2)))| / T ≤
      |qReal f T D j u - qRand f T D j u| := by
  rw [← bhyb_T f T D hf, ← bhyb_zero f T D]
  have htel : bhyb f T D T - bhyb f T D 0 =
      ∑ j ∈ Finset.range T, (bhyb f T D (j + 1) - bhyb f T D j) :=
    (Finset.sum_range_sub (bhyb f T D) T).symm
  have hle : ∑ _j ∈ Finset.range T, |bhyb f T D T - bhyb f T D 0| / T ≤
      ∑ j ∈ Finset.range T, |bhyb f T D (j + 1) - bhyb f T D j| := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ _ (by exact_mod_cast hT.ne' : (T : ℝ) ≠ 0), htel]
    exact Finset.abs_sum_le_sum_abs _ _
  obtain ⟨j, hj, hjle⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr hT.ne') hle
  rw [Finset.mem_range] at hj
  refine ⟨j, hj, ?_⟩
  rw [bhyb_succ_eq_qRand f T D hf hj, bhyb_eq_qReal f T D hf hj, ← ex_sub] at hjle
  have h2 := hjle.trans (abs_ex_le _)
  obtain ⟨u, hu⟩ := exists_le_of_le_ex h2
  refine ⟨u, ?_⟩
  rw [abs_sub_comm (qReal f T D j u)]
  exact hu

theorem ex_const_mul {α : Type} [Fintype α] (c : ℝ) (f : α → ℝ) :
    ex (fun a => c * f a) = c * ex f := by
  rw [ex, ex, ← Finset.mul_sum, mul_div_assoc]

theorem yao_pt (h : Bool → Bool) (b e : Bool) :
    ex (fun c : Bool => ind (fun c => xor (h c) (xor c e) = b) c) =
      1 / 2 + (if e then 1 else -1) * (bv (h b) - ex (fun β : Bool => bv (h β))) := by
  rw [ex_bool, ex_bool]
  cases ht : h true <;> cases hf : h false <;> cases b <;> cases e <;>
    simp [ind, ht, hf, bv] <;> norm_num

/-- **Yao: distinguisher ⇒ predictor.** Guess `c`; if the test accepts `(f z, r, c)` answer
`c`, else `¬c` (for `e = true`; `e = false` uses the flipped test). -/
theorem yao (g : Seed a → Seed a → Bool → Bool) (e : Bool) :
    ex (fun p : Seed a × Seed a => ex (fun c : Bool =>
      ind (fun c => xor (g (f p.1) p.2 c) (xor c e) = ip p.1 p.2) c)) =
      1 / 2 + (if e then 1 else -1) *
        (ex (fun p : Seed a × Seed a => bv (g (f p.1) p.2 (ip p.1 p.2))) -
          ex (fun p : Seed a × Seed a => ex (fun β : Bool => bv (g (f p.1) p.2 β)))) := by
  rw [← ex_sub, ← ex_const_mul, ← ex_const (α := Seed a × Seed a) (1 / 2), ← ex_add]
  congr 1; funext p
  exact yao_pt (g (f p.1) p.2) (ip p.1 p.2) e

/-- **Blum–Micali reduction** (one length, explicit parameters). A test `D` with `sD` gates and
advantage `α` against the generator `bmOut f T` (`f` a permutation with `sf` gates) yields a
predictor `B` with `bmHybSize a T sf + sD + 3` gates and success `≥ 1/2 + α/T` for `⟨z, r⟩`
from `(f z, r)`. -/
theorem bm_reduction {sf sD : ℕ} (ha : 0 < a) (hT : 0 < T) (hf : Function.Bijective f)
    (hfc : HasMCircuitOfSize f sf) (hD : HasCircuitOfSize D sD) :
    ∃ B : (Fin (a + a) → Bool) → Bool, HasCircuitOfSize B (bmHybSize a T sf + sD + 3) ∧
      1 / 2 + |ex (fun w : Fin (T + (a + a)) → Bool => bv (D w)) -
        ex (fun p : Seed a × Seed a => bv (D (bmOut f T p.1 p.2)))| / T ≤
      prob (fun p : Seed a × Seed a => pred B (f p.1) p.2 = ip p.1 p.2) := by
  obtain ⟨j, hj, u, hu⟩ := exists_step f T D hf hT
  let g : Seed a → Seed a → Bool → Bool := fun y r c => D (bmHyb f T j u (smp y r c))
  let e : Bool := decide (qRand f T D j u ≤ qReal f T D j u)
  have hy := yao f g e
  have hge : |qReal f T D j u - qRand f T D j u| ≤ (if e then 1 else -1) *
      (ex (fun p : Seed a × Seed a => bv (g (f p.1) p.2 (ip p.1 p.2))) -
        ex (fun p : Seed a × Seed a => ex (fun β : Bool => bv (g (f p.1) p.2 β)))) := by
    show _ ≤ _ * (qReal f T D j u - qRand f T D j u)
    by_cases h : qRand f T D j u ≤ qReal f T D j u
    · simp only [e, h, decide_true, if_true, one_mul]
      exact le_of_eq (abs_of_nonneg (by linarith))
    · simp only [e, h, decide_false, Bool.false_eq_true, if_false]
      rw [abs_of_neg (by linarith)]; linarith
  rw [ex_comm] at hy
  have hall : 1 / 2 + |ex (fun w : Fin (T + (a + a)) → Bool => bv (D w)) -
      ex (fun p : Seed a × Seed a => bv (D (bmOut f T p.1 p.2)))| / T ≤
      ex (fun c : Bool => ex (fun p : Seed a × Seed a =>
        ind (fun c => xor (g (f p.1) p.2 c) (xor c e) = ip p.1 p.2) c)) := by
    rw [hy]; linarith
  obtain ⟨c, hc⟩ := exists_le_of_le_ex hall
  refine ⟨fun v => xor (D (bmHyb f T j u (Fin.append v (fun _ => c)))) (xor c e), ?_, ?_⟩
  · have h1 := (hasMCircuitOfSize_append_const (k := a + a) (by omega) (fun _ : Fin 1 => c)).comp
      (hasMCircuitOfSize_bmHyb ha hfc j u)
    have h2 := (h1.comp_single hD).toM 1
    have h3 := h2.comp_single (hasCircuitOfSize_xor_const (xor c e))
    refine h3.mono (by omega)
  · rw [prob_eq_ex]
    refine hc.trans (le_of_eq ?_)
    rfl

end Concrete

/-! ## Asymptotic version: one-way permutations give secure generators -/

/-- `F` has circuits of size polynomial in the input length. -/
def OWF.InPPoly (F : OWF) : Prop :=
  ∃ p : Polynomial ℕ, ∀ ℓ, HasMCircuitOfSize (F.f ℓ) (p.eval ℓ)

theorem bmLen (ℓ : ℕ) : ℓ + ℓ = (ℓ + ℓ - 2 * (ℓ / 2)) + (ℓ / 2 + ℓ / 2) := by omega

/-- The first `2 ⌊ℓ/2⌋` bits of a seed. -/
def restr (ℓ : ℕ) (s : Seed ℓ) : Fin (ℓ / 2 + ℓ / 2) → Bool :=
  fun t => s ⟨t.val, by have := t.isLt; omega⟩

/-- The Blum–Micali generator at seed length `ℓ ≥ 2`: `a = ⌊ℓ/2⌋`, `T = 2ℓ − 2a` output bits
from `(x, r)` = the first `2a` seed bits (constant `false` for `ℓ < 2`). -/
def OWF.bmFull (F : OWF) (ℓ : ℕ) (s : Seed ℓ) : Fin (ℓ + ℓ) → Bool :=
  if 2 ≤ ℓ then fun i =>
    bmGen (F.f (ℓ / 2)) (ℓ + ℓ - 2 * (ℓ / 2)) (restr ℓ s) (Fin.cast (bmLen ℓ) i)
  else fun _ => false

/-- The Blum–Micali generator as a length-doubling `PRG`. -/
def OWF.bmPRG (F : OWF) : PRG where
  G₀ ℓ s := half false (F.bmFull ℓ s)
  G₁ ℓ s := half true (F.bmFull ℓ s)

theorem OWF.pair_bmPRG (F : OWF) (ℓ : ℕ) (s : Seed ℓ) :
    pair (F.bmPRG.G₀ ℓ) (F.bmPRG.G₁ ℓ) s = F.bmFull ℓ s := by
  simp only [pair, OWF.bmPRG]
  exact Fin.append_castAdd_natAdd

theorem OWF.bmPRG_inPPoly (F : OWF) (hP : F.InPPoly) : F.bmPRG.InPPoly := by
  obtain ⟨p, hp⟩ := hP
  open Polynomial in
  refine ⟨3 * (2 * X + 1) ^ 2 * (p + X + 1) + 1, fun ℓ b => ?_⟩
  have hhalf : ∀ s, sel (F.bmPRG.G₀ ℓ) (F.bmPRG.G₁ ℓ) b s = half b (F.bmFull ℓ s) := by
    intro s; cases b <;> rfl
  by_cases hℓ : 2 ≤ ℓ
  · have h1 := (hasMCircuitOfSize_rewire (fun t : Fin (ℓ / 2 + ℓ / 2) =>
      (⟨t.val, by have := t.isLt; omega⟩ : Fin ℓ))).comp
      (hasMCircuitOfSize_bmGen (by omega) (T := ℓ + ℓ - 2 * (ℓ / 2)) (hp (ℓ / 2)))
    have h2 := h1.comp (hasMCircuitOfSize_rewire (fun k : Fin ℓ =>
      Fin.cast (bmLen ℓ) (if b then Fin.natAdd ℓ k else Fin.castAdd ℓ k)))
    have hsz : 0 + bmGenSize (ℓ / 2) (ℓ + ℓ - 2 * (ℓ / 2)) (p.eval (ℓ / 2)) + 0 ≤
        (3 * (2 * X + 1) ^ 2 * (p + X + 1) + 1 : Polynomial ℕ).eval ℓ := by
      refine (Nat.le_of_eq (by ring)).trans ((bmGenSize_le _ _ _).trans ?_)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
      have hpm : p.eval (ℓ / 2) ≤ p.eval ℓ := polynomial_eval_mono p (Nat.div_le_self ℓ 2)
      have : ℓ + ℓ - 2 * (ℓ / 2) + 1 ≤ 2 * ℓ + 1 := by omega
      have : ℓ / 2 ≤ ℓ := Nat.div_le_self ℓ 2
      calc 3 * (ℓ + ℓ - 2 * (ℓ / 2) + 1) ^ 2 * (p.eval (ℓ / 2) + ℓ / 2 + 1)
          ≤ 3 * (2 * ℓ + 1) ^ 2 * (p.eval ℓ + ℓ + 1) := by gcongr
        _ ≤ _ := Nat.le_add_right _ _
    refine (h2.mono hsz).mono le_rfl |> fun h => ?_
    convert h using 1
    funext s k
    rw [hhalf]
    simp only [half, OWF.bmFull, if_pos hℓ, Function.comp]
    cases b <;> rfl
  · rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · subst h0
      exact (hasMCircuitOfSize_nil _).mono (Nat.zero_le _)
    · have : HasMCircuitOfSize (fun _ : Seed ℓ => fun _ : Fin ℓ => false) (ℓ * 1) :=
        hasMCircuitOfSize_of_forall _ fun _ => hasCircuitOfSize_const h0 false
      have hle : ℓ * 1 ≤ (3 * (2 * Polynomial.X + 1) ^ 2 * (p + Polynomial.X + 1) + 1 :
          Polynomial ℕ).eval ℓ := by
        simp only [Polynomial.eval_add, Polynomial.eval_one, mul_one]
        omega
      convert this.mono hle using 1
      funext s k; rw [hhalf]; simp [half, OWF.bmFull, hℓ]

theorem ex_restr {ℓ m : ℕ} (hm : m ≤ ℓ) (g : (Fin m → Bool) → ℝ) :
    ex (fun s : Seed ℓ => g (fun t => s ⟨t.val, by have := t.isLt; omega⟩)) = ex g := by
  have h : ℓ = m + (ℓ - m) := by omega
  let e : Seed ℓ ≃ (Fin m → Bool) × (Fin (ℓ - m) → Bool) :=
    (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)).trans (Fin.appendEquiv m (ℓ - m)).symm
  rw [← ex_fst (β := Fin (ℓ - m) → Bool) g, ← ex_equiv e.symm]
  congr 1; funext s
  congr 1; funext t
  simp [e, Fin.appendEquiv, Equiv.arrowCongr]
  exact Fin.append_left _ _ t

theorem prob_eq_ex_bv {α : Type} [Fintype α] (D : α → Bool) :
    prob (fun a => D a = true) = ex (fun a => bv (D a)) := by
  rw [prob_eq_ex]; congr 1; funext a; simp [ind, bv]

/-- **Blum–Micali security at one length.** If `f = F.f ⌊ℓ/2⌋` is a permutation with `sf` gates
and no circuit with `S` gates inverts it with probability `≥ 1/R` (`S`, `R` dominating explicit
polynomials), then every test with `sD` gates has advantage `< 1/ρ` against the generator. -/
theorem OWF.bm_secure_at (F : OWF) {ℓ sf sD ρ L S R : ℕ} (hℓ : 2 ≤ ℓ)
    (hbij : Function.Bijective (F.f (ℓ / 2))) (hfc : HasMCircuitOfSize (F.f (ℓ / 2)) sf)
    {D : (Fin (ℓ + ℓ) → Bool) → Bool} (hD : HasCircuitOfSize D sD) (hL : ℓ / 2 ≤ L)
    (hS : 102 * L * (2 * (2 * L * ((ℓ + ℓ - 2 * (ℓ / 2)) * ρ) ^ 2 + 1)) ^ 2 *
      (L + (bmHybSize (ℓ / 2) (ℓ + ℓ - 2 * (ℓ / 2)) sf + sD + 3) + 1) ≤ S)
    (hR : 8 * ((ℓ + ℓ - 2 * (ℓ / 2)) * ρ) *
      (2 * L * ((ℓ + ℓ - 2 * (ℓ / 2)) * ρ) ^ 2 + 1) ≤ R)
    (hard : ∀ I : Seed (ℓ / 2) → Seed (ℓ / 2), HasMCircuitOfSize I S →
      prob (fun x => F.f _ (I (F.f _ x)) = F.f _ x) * R < 1) :
    prgAdv (F.bmPRG.G₀ ℓ) (F.bmPRG.G₁ ℓ) D * ρ < 1 := by
  set T := ℓ + ℓ - 2 * (ℓ / 2) with hTdef
  have hT : 0 < T := by omega
  have ha : 0 < ℓ / 2 := by omega
  let D' : (Fin (T + (ℓ / 2 + ℓ / 2)) → Bool) → Bool := fun w => D (fun i => w (Fin.cast (bmLen ℓ) i))
  have hD' : HasCircuitOfSize D' sD := by
    have := (hasMCircuitOfSize_rewire (fun i : Fin (ℓ + ℓ) => Fin.cast (bmLen ℓ) i)).comp_single hD
    rw [Nat.zero_add] at this; exact this
  obtain ⟨B, hB, hpred⟩ := bm_reduction (F.f (ℓ / 2)) T D' ha hT hbij hfc hD'
  have hadv : prgAdv (F.bmPRG.G₀ ℓ) (F.bmPRG.G₁ ℓ) D =
      |ex (fun w : Fin (T + (ℓ / 2 + ℓ / 2)) → Bool => bv (D' w)) -
        ex (fun p : Seed (ℓ / 2) × Seed (ℓ / 2) => bv (D' (bmOut (F.f _) T p.1 p.2)))| := by
    rw [prgAdv, prob_eq_ex_bv, prob_eq_ex_bv]
    congr 2
    · exact (ex_equiv (Equiv.arrowCongr (finCongr (bmLen ℓ)) (Equiv.refl Bool)).symm
        (fun y => bv (D y))).symm.trans (by rfl)
    · simp only [OWF.pair_bmPRG, OWF.bmFull, if_pos hℓ]
      let g : (Fin (ℓ / 2 + ℓ / 2) → Bool) → ℝ := fun w => bv (D' (bmGen (F.f _) T w))
      calc _ = ex g := ex_restr (m := ℓ / 2 + ℓ / 2) (by omega) g
        _ = ex (fun p => g (Fin.appendEquiv _ _ p)) := (ex_equiv _ g).symm
        _ = _ := by
          congr 1; funext p
          have h2 : ∀ t : Fin (ℓ / 2), Fin.append p.1 p.2 (t.addNat (ℓ / 2)) = p.2 t := by
            intro t
            rw [show t.addNat (ℓ / 2) = Fin.natAdd (ℓ / 2) t from Fin.ext (by simp)]
            exact Fin.append_right _ _ t
          simp [g, bmGen, Fin.appendEquiv, h2]
  have hcore := hardcore_at ha hL (F.f (ℓ / 2)) hB hS hR hard
  rw [hadv]
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have : |ex (fun w : Fin (T + (ℓ / 2 + ℓ / 2)) → Bool => bv (D' w)) -
      ex (fun p : Seed (ℓ / 2) × Seed (ℓ / 2) => bv (D' (bmOut (F.f _) T p.1 p.2)))| ≤
      (prob (fun p : Seed (ℓ / 2) × Seed (ℓ / 2) => pred B (F.f _ p.1) p.2 = ip p.1 p.2) - 1 / 2)
        * T := by
    rw [← div_le_iff₀ hTR]; linarith
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
  push_cast at hcore
  nlinarith [mul_le_mul_of_nonneg_right this hρ0]

theorem hard_congr (F : OWF) {a b S R : ℕ} (h : a = b)
    (H : ∀ I : Seed a → Seed a, HasMCircuitOfSize I S →
      prob (fun x => F.f a (I (F.f a x)) = F.f a x) * R < 1) :
    ∀ I : Seed b → Seed b, HasMCircuitOfSize I S →
      prob (fun x => F.f b (I (F.f b x)) = F.f b x) * R < 1 := by
  subst h; exact H

/-- **One-way permutations give secure generators.** If `F` is a family of permutations in
P/poly that is one-way along `ν(n) > 0`, the Blum–Micali generator is secure along the seed
lengths `2ν(n)`. -/
theorem OWF.bmPRG_secure (F : OWF) (hbij : ∀ ℓ, Function.Bijective (F.f ℓ)) (hP : F.InPPoly)
    (ν : Polynomial ℕ) (hν : ∀ n, 0 < ν.eval n) (hF : F.HardAlong ν) :
    F.bmPRG.SecureAlong (2 * ν) := by
  obtain ⟨p, hp⟩ := hP
  intro q r
  open Polynomial in
  obtain ⟨N, hN⟩ := hF
    (102 * ν * (2 * (2 * ν * ((2 * ν) * r) ^ 2 + 1)) ^ 2 *
      (ν + (3 * (2 * ν + 1) ^ 2 * (p.comp ν + ν + 1) + q + 3) + 1))
    (8 * ((2 * ν) * r) * (2 * ν * ((2 * ν) * r) ^ 2 + 1))
  refine ⟨N, fun n hn D hD => ?_⟩
  have hℓ : (2 * ν).eval n = 2 * ν.eval n := by simp
  have hhalf : (2 * ν).eval n / 2 = ν.eval n := by rw [hℓ]; omega
  have hT : (2 * ν).eval n + (2 * ν).eval n - 2 * ((2 * ν).eval n / 2) = 2 * ν.eval n := by
    rw [hhalf, hℓ]; omega
  have hmono : ν.eval n ≤ ν.eval (2 ^ n) := polynomial_eval_mono ν Nat.lt_two_pow_self.le
  have hsf : p.eval ((2 * ν).eval n / 2) ≤ p.eval (ν.eval (2 ^ n)) :=
    polynomial_eval_mono p (by rw [hhalf]; exact hmono)
  have hT' : (2 * ν).eval n + (2 * ν).eval n - 2 * ((2 * ν).eval n / 2) ≤ 2 * ν.eval (2 ^ n) := by
    rw [hT]; omega
  have hsB : bmHybSize ((2 * ν).eval n / 2) ((2 * ν).eval n + (2 * ν).eval n -
      2 * ((2 * ν).eval n / 2)) (p.eval ((2 * ν).eval n / 2)) + q.eval (2 ^ n) + 3 ≤
      3 * (2 * ν.eval (2 ^ n) + 1) ^ 2 * (p.eval (ν.eval (2 ^ n)) + ν.eval (2 ^ n) + 1) +
        q.eval (2 ^ n) + 3 := by
    have := bmHybSize_le ((2 * ν).eval n / 2) ((2 * ν).eval n + (2 * ν).eval n -
      2 * ((2 * ν).eval n / 2)) (p.eval ((2 * ν).eval n / 2))
    have h2 : (2 * ν).eval n / 2 ≤ ν.eval (2 ^ n) := by rw [hhalf]; exact hmono
    have : 3 * ((2 * ν).eval n + (2 * ν).eval n - 2 * ((2 * ν).eval n / 2) + 1) ^ 2 *
        (p.eval ((2 * ν).eval n / 2) + (2 * ν).eval n / 2 + 1) ≤
        3 * (2 * ν.eval (2 ^ n) + 1) ^ 2 * (p.eval (ν.eval (2 ^ n)) + ν.eval (2 ^ n) + 1) := by
      gcongr
    omega
  have hρ : ((2 * ν).eval n + (2 * ν).eval n - 2 * ((2 * ν).eval n / 2)) * r.eval (2 ^ n) ≤
      2 * ν.eval (2 ^ n) * r.eval (2 ^ n) := Nat.mul_le_mul_right _ hT'
  refine OWF.bm_secure_at F (by rw [hℓ]; have := hν n; omega) (hbij _) (hp _) hD
    (L := ν.eval (2 ^ n)) (by rw [hhalf]; exact hmono) ?_ ?_
    (hard_congr F hhalf.symm (hN n hn))
  · simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_comp]
    rw [hℓ] at hsB
    gcongr
    omega
  · simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    gcongr <;> omega

/-- **Natural proofs barrier from one-way permutations.** If a family of permutations in
P/poly is one-way along `ν(n) > 0` (against circuits of size `poly(2ⁿ)`), then no property of
Boolean functions is constructive, large and useful against P/poly. -/
theorem no_natural_property_of_owp (F : OWF) (hbij : ∀ ℓ, Function.Bijective (F.f ℓ))
    (hP : F.InPPoly) (ν : Polynomial ℕ) (hν : ∀ n, 0 < ν.eval n) (hF : F.HardAlong ν)
    (Γ : ∀ n, Set (BoolFun n)) : ¬ NaturalAgainstPPoly Γ :=
  no_natural_property_of_secure_prg F.bmPRG (2 * ν)
    (fun n => by have := hν n; simp; omega) (F.bmPRG_inPPoly hP)
    (F.bmPRG_secure hbij hP ν hν hF) Γ

/-- Sanity check: the hypotheses `Function.Bijective` and `OWF.InPPoly` are satisfiable (by the
identity, which is of course not one-way). -/
theorem OWF.id_bij_inPPoly :
    (∀ ℓ, Function.Bijective ((OWF.mk fun _ => id).f ℓ)) ∧ (OWF.mk fun _ => id).InPPoly :=
  ⟨fun _ => Function.bijective_id, ⟨0, fun ℓ => (hasMCircuitOfSize_id ℓ).mono (Nat.zero_le _)⟩⟩

end

end Pnp.NaturalProofs
