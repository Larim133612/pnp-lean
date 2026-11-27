import Pnp.NaturalProofs.GoldreichLevin

/-!
# Circuit size of the Blum–Micali generator

For a map `f : Seed a → Seed a` with circuits of size `sf`, the Blum–Micali generator
`bmGen f T : (x, r) ↦ (⟨x,r⟩, ⟨f x,r⟩, …, ⟨f^{T-1} x,r⟩, f^T x, r)` and each of its hybrids
`bmHyb f T j u` have circuits of size polynomial in `T`, `a` and `sf`
(`hasMCircuitOfSize_bmGen`, `hasMCircuitOfSize_bmHyb`, `bmGenSize_le`, `bmHybSize_le`).
Each inner-product output bit is built independently, from the iterate circuit of `f`
followed by an AND/XOR chain (`hasCircuitOfSize_ip`).
-/

namespace Pnp.NaturalProofs

open Pnp.Circuits Classical

noncomputable section

/-- The Blum–Micali generator with `T` output bits:
`(x, r) ↦ (⟨x,r⟩, ⟨f x,r⟩, …, ⟨f^{T-1} x,r⟩, f^T x, r)`. -/
def bmOut {a : ℕ} (f : Seed a → Seed a) (T : ℕ) (x r : Seed a) : Fin (T + (a + a)) → Bool :=
  Fin.append (fun i : Fin T => ip (f^[i.val] x) r) (Fin.append (f^[T] x) r)

/-- The generator as a function of the seed `s = (x, r)`. -/
def bmGen {a : ℕ} (f : Seed a → Seed a) (T : ℕ) (s : Fin (a + a) → Bool) :
    Fin (T + (a + a)) → Bool :=
  bmOut f T (fun t => s (Fin.castAdd a t)) (fun t => s (Fin.natAdd a t))

/-- Hybrid `j` built from a sample `w = (y, r, β)`: bits `< j` are the constants `u`, bit `j`
is `β`, bit `i > j` is `⟨f^{i-j-1} y, r⟩`, followed by `f^{T-j-1} y` and `r`. -/
def bmHyb {a : ℕ} (f : Seed a → Seed a) (T j : ℕ) (u : Fin T → Bool)
    (w : Fin (a + a + 1) → Bool) : Fin (T + (a + a)) → Bool :=
  Fin.append
    (fun i : Fin T => if i.val < j then u i else if i.val = j then w (Fin.last (a + a)) else
      ip (f^[i.val - j - 1] (fun t => w (Fin.castAdd 1 (Fin.castAdd a t))))
        (fun t => w (Fin.castAdd 1 (Fin.natAdd a t))))
    (Fin.append (f^[T - j - 1] (fun t => w (Fin.castAdd 1 (Fin.castAdd a t))))
      (fun t => w (Fin.castAdd 1 (Fin.natAdd a t))))

/-! ## Appending the outputs of two circuits -/

/-- **Parallel combination** of two multi-output circuits on the same inputs, with the
outputs appended. -/
theorem hasMCircuitOfSize_append {n m k : ℕ} {F : (Fin n → Bool) → (Fin m → Bool)}
    {G : (Fin n → Bool) → (Fin k → Bool)} {s₁ s₂ : ℕ}
    (hF : HasMCircuitOfSize F s₁) (hG : HasMCircuitOfSize G s₂) :
    HasMCircuitOfSize (fun x => (Fin.append (F x) (G x) : Fin (m + k) → Bool)) (s₁ + s₂) := by
  obtain ⟨t₁, ht₁, ⟨g, o⟩, rfl⟩ := hF
  obtain ⟨t₂, ht₂, ⟨h, o₂⟩, rfl⟩ := hG
  let σ : Fin n → Fin (n + t₁) := Fin.castAdd t₁
  refine ⟨t₁ + t₂, by omega, (seqGates g σ h,
    Fin.append (fun j => ⟨(o j).val, by have := (o j).2; omega⟩)
      (fun j => ⟨seqWire σ (o₂ j).val, by have := seqWire_lt σ (o₂ j).2; omega⟩)), ?_⟩
  funext x p
  refine Fin.addCases (fun j => ?_) (fun j => ?_) p
  · simp only [MCircuit.eval, Fin.append_left, wires_eq_wv]
    exact wv_seqGates_low x g σ h (o j).2
  · simp only [MCircuit.eval, Fin.append_right, wires_eq_wv]
    rw [wv_seqGates_high x g σ h (o₂ j).2]
    congr 1
    funext k; exact wv_input x t₁ g k.2

/-! ## Inner products -/

/-- Circuit size of an inner product of two `a`-bit strings. -/
def ipSize (a : ℕ) : ℕ := 2 * a + 1

theorem ip_succ {a : ℕ} (x r : Seed (a + 1)) :
    ip x r = xor (x 0 && r 0) (ip (fun i => x i.succ) (fun i => r i.succ)) := by
  apply toZ_injective
  rw [toZ_xor, ip, ip, toZ_bsum, toZ_bsum, Fin.sum_univ_succ]

theorem ip_zero (x r : Seed 0) : ip x r = false := by
  simp [ip, bsum]

/-- `y ↦ (y 0 && y 1) xor y 2`, with two gates. -/
def andXorCircuit : Circuit 3 2 :=
  (mkGates 3 2 (fun i => if i = 0 then (· && ·) else xor)
    (fun i => if i = 0 then 0 else 3)
    (fun i => if i = 0 then 1 else 2)
    (fun i hi => by interval_cases i <;> simp) (fun i hi => by interval_cases i <;> simp),
    Fin.last 4)

theorem andXorCircuit_eval : andXorCircuit.eval = fun y => xor (y 0 && y 1) (y 2) := by
  funext y; revert y; decide

theorem hasCircuitOfSize_ip {n a : ℕ} (hn : 0 < n) (π₁ π₂ : Fin a → Fin n) :
    HasCircuitOfSize (fun z : Fin n → Bool => ip (fun t => z (π₁ t)) (fun t => z (π₂ t)))
      (ipSize a) := by
  induction a with
  | zero =>
    have := hasCircuitOfSize_const hn false
    show HasCircuitOfSize _ 1
    convert this using 2 with z
    exact ip_zero _ _
  | succ a ih =>
    have hg := ih (fun i => π₁ i.succ) (fun i => π₂ i.succ)
    have h3 := (hasCircuitOfSize_var (π₁ 0)).cons ((hasCircuitOfSize_var (π₂ 0)).cons
      (hg.cons (hasMCircuitOfSize_nil (fun _ => Fin.elim0))))
    have hax : HasCircuitOfSize (fun y : Fin 3 → Bool => xor (y 0 && y 1) (y 2)) 2 :=
      ⟨2, le_rfl, andXorCircuit, andXorCircuit_eval⟩
    have hc := (h3.comp (hax.toM 1)).output 0
    have hc' := hc.mono (s' := ipSize (a + 1)) (by unfold ipSize; omega)
    convert hc' using 2 with z
    rw [ip_succ]
    rfl

/-! ## Iterates with the second half passed through -/

theorem hasMCircuitOfSize_iterAppend {n a sf : ℕ} {f : Seed a → Seed a}
    (hf : HasMCircuitOfSize f sf) (k : ℕ) (π₁ π₂ : Fin a → Fin n) :
    HasMCircuitOfSize (fun w : Fin n → Bool =>
      (Fin.append (f^[k] (fun t => w (π₁ t))) (fun t => w (π₂ t)) : Fin (a + a) → Bool))
      (k * sf) := by
  have h1 := (hasMCircuitOfSize_rewire π₁).comp (hf.iterate k)
  have h := hasMCircuitOfSize_append h1 (hasMCircuitOfSize_rewire π₂)
  simpa using h

theorem hasCircuitOfSize_ipIter {n a sf : ℕ} (ha : 0 < a) {f : Seed a → Seed a}
    (hf : HasMCircuitOfSize f sf) {k T : ℕ} (hk : k ≤ T) (π₁ π₂ : Fin a → Fin n) :
    HasCircuitOfSize (fun w : Fin n → Bool => ip (f^[k] (fun t => w (π₁ t))) (fun t => w (π₂ t)))
      (T * sf + ipSize a) := by
  have h := (hasMCircuitOfSize_iterAppend hf k π₁ π₂).comp_single
    (hasCircuitOfSize_ip (n := a + a) (by omega) (Fin.castAdd a) (Fin.natAdd a))
  have h' := h.mono (s' := T * sf + ipSize a) (by have := Nat.mul_le_mul_right sf hk; omega)
  convert h' using 2 with w
  simp only [Function.comp, Fin.append_left, Fin.append_right]

/-! ## The generator and its hybrids -/

/-- Circuit size of the Blum–Micali generator. -/
def bmGenSize (a T sf : ℕ) : ℕ := T * (T * sf + ipSize a) + T * sf

/-- Circuit size of each Blum–Micali hybrid. -/
def bmHybSize (a T sf : ℕ) : ℕ := T * (T * sf + ipSize a) + T * sf

theorem hasMCircuitOfSize_bmGen {a T sf : ℕ} (ha : 0 < a) {f : Seed a → Seed a}
    (hf : HasMCircuitOfSize f sf) : HasMCircuitOfSize (bmGen f T) (bmGenSize a T sf) := by
  have hhead := hasMCircuitOfSize_of_forall (n := a + a)
    (fun s (i : Fin T) => ip (f^[i.val] (fun t => s (Fin.castAdd a t)))
      (fun t => s (Fin.natAdd a t)))
    (s := T * sf + ipSize a)
    (fun i => hasCircuitOfSize_ipIter ha hf i.2.le _ _)
  have htail := hasMCircuitOfSize_iterAppend hf T
    (Fin.castAdd a : Fin a → Fin (a + a)) (Fin.natAdd a)
  exact hasMCircuitOfSize_append hhead htail

theorem hasMCircuitOfSize_bmHyb {a T sf : ℕ} (ha : 0 < a) {f : Seed a → Seed a}
    (hf : HasMCircuitOfSize f sf) (j : ℕ) (u : Fin T → Bool) :
    HasMCircuitOfSize (bmHyb f T j u) (bmHybSize a T sf) := by
  have hn : 0 < a + a + 1 := by omega
  have hhead := hasMCircuitOfSize_of_forall (n := a + a + 1)
    (fun w (i : Fin T) => if i.val < j then u i else if i.val = j then w (Fin.last (a + a)) else
      ip (f^[i.val - j - 1] (fun t => w (Fin.castAdd 1 (Fin.castAdd a t))))
        (fun t => w (Fin.castAdd 1 (Fin.natAdd a t))))
    (s := T * sf + ipSize a) (fun i => by
      by_cases h1 : i.val < j
      · simp only [if_pos h1]
        exact (hasCircuitOfSize_const hn (u i)).mono (by unfold ipSize; omega)
      · simp only [if_neg h1]
        by_cases h2 : i.val = j
        · simp only [if_pos h2]
          exact (hasCircuitOfSize_var _).mono (Nat.zero_le _)
        · simp only [if_neg h2]
          exact hasCircuitOfSize_ipIter ha hf (by have := i.2; omega) _ _)
  have htail := (hasMCircuitOfSize_iterAppend hf (T - j - 1)
    (fun t : Fin a => Fin.castAdd 1 (Fin.castAdd a t)) (fun t => Fin.castAdd 1 (Fin.natAdd a t))).mono
    (s' := T * sf) (Nat.mul_le_mul_right sf (by omega))
  exact hasMCircuitOfSize_append hhead htail

theorem bmGenSize_le (a T sf : ℕ) : bmGenSize a T sf ≤ 3 * (T + 1) ^ 2 * (sf + a + 1) := by
  unfold bmGenSize ipSize
  nlinarith [Nat.zero_le (T * sf), Nat.zero_le (T * a), Nat.zero_le (T * T * sf),
    Nat.zero_le (T * T * a), Nat.zero_le (T * T)]

theorem bmHybSize_le (a T sf : ℕ) : bmHybSize a T sf ≤ 3 * (T + 1) ^ 2 * (sf + a + 1) :=
  bmGenSize_le a T sf

end

end Pnp.NaturalProofs
