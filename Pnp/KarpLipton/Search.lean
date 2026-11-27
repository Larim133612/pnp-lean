import Pnp.Derandomization.Lautemann

/-!
# Search to decision for circuits (self-reducibility)

The hypothesis of the Karp–Lipton theorem, in circuit form:

* `SmallExistentials T`: for every circuit `V(x, z)` with `n ≥ 1` free inputs `x`, `Z` existential
  inputs `z` and `s` gates, the predicate `x ↦ ∃ z, V(x, z)` has a circuit with at most
  `T(n + Z + s)` gates.  This is the non-uniform statement “circuit satisfiability has
  polynomial-size circuits”.  Since circuit satisfiability is in `NP`, it follows from
  `NP ⊆ P/poly` (that implication needs a polynomial-time circuit evaluator and is not formalized
  here); conversely it implies `NP ⊆ P/poly` (`Pnp.KarpLipton.inPPoly_of_smallExistentials`).

* `search_circuit`: under `SmallExistentials T`, every such `V` has a polynomial-size multi-output
  **search circuit** `F` with `(∃ z, V(x, z)) → V(x, F x)`.  The construction is the classical
  self-reduction: the bits of the witness are fixed one at a time, bit `k` being set to `1` iff
  some witness with the already fixed bits `< k` has bit `k` equal to `1`.  Each such question is
  again an existential question about a circuit obtained from `V` by rewiring and one AND gate.
-/

namespace Pnp.KarpLipton

open Pnp.Circuits Classical

noncomputable section

/-- **Circuit satisfiability has polynomial-size circuits** (non-uniform form, bound `T`). -/
def SmallExistentials (T : Polynomial ℕ) : Prop :=
  ∀ (n Z s : ℕ) (V : (Fin (n + Z) → Bool) → Bool), 0 < n → HasCircuitOfSize V s →
    HasCircuitOfSize (fun x : Fin n → Bool => decide (∃ z : Fin Z → Bool, V (Fin.append x z) = true))
      (T.eval (n + Z + s))

section Search

variable {n Z : ℕ}

/-- The first `k` bits from `u`, the remaining ones from `z`. -/
def mix (k : ℕ) (u z : Fin Z → Bool) : Fin Z → Bool := fun j => if j.val < k then u j else z j

theorem mix_zero (u z : Fin Z → Bool) : mix 0 u z = z := by
  funext j; simp [mix]

theorem mix_all (u z : Fin Z → Bool) : mix Z u z = u := by
  funext j; simp [mix, j.2]

/-- The question asked at step `k`: is there a witness that agrees with `u` below `k` and has
bit `k` equal to `1`?  (`xu` holds `x` followed by `u`.) -/
def ask (V : (Fin (n + Z) → Bool) → Bool) (k : Fin Z) (xu : Fin (n + Z) → Bool) : Bool :=
  decide (∃ z : Fin Z → Bool, z k = true ∧
    V (Fin.append (fun i => xu (Fin.castAdd Z i)) (mix k (fun i => xu (Fin.natAdd n i)) z)) = true)

/-- The rewiring `(x, u, z) ↦ (x, mix k u z)`. -/
def askWire (k : ℕ) : Fin (n + Z) → Fin (n + Z + Z) :=
  Fin.append (fun i => Fin.castAdd Z (Fin.castAdd Z i))
    (fun i => if i.val < k then Fin.castAdd Z (Fin.natAdd n i) else Fin.natAdd (n + Z) i)

theorem askWire_spec (k : ℕ) (xu : Fin (n + Z) → Bool) (z : Fin Z → Bool) :
    (fun j => Fin.append xu z (askWire k j)) =
      Fin.append (fun i => xu (Fin.castAdd Z i)) (mix k (fun i => xu (Fin.natAdd n i)) z) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [askWire, Fin.append_left]
  · simp only [askWire, Fin.append_right, mix]
    split_ifs <;> simp only [Fin.append_left, Fin.append_right]

theorem hasCircuitOfSize_ask {T : Polynomial ℕ} (hT : SmallExistentials T) (hn : 0 < n)
    {V : (Fin (n + Z) → Bool) → Bool} {s : ℕ} (hV : HasCircuitOfSize V s) (k : Fin Z) :
    HasCircuitOfSize (ask V k) (T.eval (n + Z + Z + (s + 1))) := by
  -- the circuit `V'(xu, z) = z_k ∧ V(x, mix k u z)`
  let V' : (Fin (n + Z + Z) → Bool) → Bool := fun v =>
    v (Fin.natAdd (n + Z) k) && V (fun j => v (askWire k j))
  have hV' : HasCircuitOfSize V' (s + 1) := by
    have h1 := (hasMCircuitOfSize_rewire (askWire (n := n) (Z := Z) k)).comp_single hV
    have h2 := ((hasCircuitOfSize_var (Fin.natAdd (n + Z) k)).cons (h1.toM 1)).comp_single
      (Pnp.Derand.hasCircuitOfSize_gate2 (· && ·))
    convert h2.mono (s' := s + 1) (by omega) using 1
    funext v; rfl
  have := hT (n + Z) Z (s + 1) V' (by omega) hV'
  convert this using 2 with xu
  simp only [ask, V', Fin.append_right, askWire_spec, Bool.and_eq_true]

/-- One step of the self-reduction: set bit `k` of `u` to the answer of `ask`. -/
def step (V : (Fin (n + Z) → Bool) → Bool) (k : Fin Z) (xu : Fin (n + Z) → Bool) :
    Fin (n + Z) → Bool :=
  Function.update xu (Fin.natAdd n k) (ask V k xu)

theorem hasMCircuitOfSize_step {T : Polynomial ℕ} (hT : SmallExistentials T) (hn : 0 < n)
    {V : (Fin (n + Z) → Bool) → Bool} {s : ℕ} (hV : HasCircuitOfSize V s) (k : Fin Z) :
    HasMCircuitOfSize (step V k) ((n + Z) * T.eval (n + Z + Z + (s + 1))) := by
  refine hasMCircuitOfSize_of_forall _ fun j => ?_
  by_cases hj : j = Fin.natAdd n k
  · subst hj
    simpa [step] using hasCircuitOfSize_ask hT hn hV k
  · simp only [step, Function.update_of_ne hj]
    exact (hasCircuitOfSize_var j).mono (Nat.zero_le _)

/-- The state after `k` steps (started with an arbitrary `u`, here a copy of `x₀`). -/
def st (V : (Fin (n + Z) → Bool) → Bool) (hn : 0 < n) : ℕ → (Fin n → Bool) → Fin (n + Z) → Bool
  | 0, x => Fin.append x (fun _ => x ⟨0, hn⟩)
  | k + 1, x => if h : k < Z then step V ⟨k, h⟩ (st V hn k x) else st V hn k x

theorem hasMCircuitOfSize_st {T : Polynomial ℕ} (hT : SmallExistentials T) (hn : 0 < n)
    {V : (Fin (n + Z) → Bool) → Bool} {s : ℕ} (hV : HasCircuitOfSize V s) :
    ∀ k, HasMCircuitOfSize (st V hn k) (k * ((n + Z) * T.eval (n + Z + Z + (s + 1))))
  | 0 => by
    have := hasMCircuitOfSize_rewire (n := n) (m := n + Z)
      (Fin.append (fun i => i) (fun _ => ⟨0, hn⟩))
    convert this using 2 with x
    · funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [st]
    · simp
  | k + 1 => by
    by_cases h : k < Z
    · have := (hasMCircuitOfSize_st hT hn hV k).comp (hasMCircuitOfSize_step hT hn hV ⟨k, h⟩)
      have e : st V hn (k + 1) = step V ⟨k, h⟩ ∘ st V hn k := by
        funext x; simp only [st, dif_pos h, Function.comp]
      rw [e]
      exact this.mono (le_of_eq (by ring))
    · have e : st V hn (k + 1) = st V hn k := by funext x; simp only [st, dif_neg h]
      rw [e]
      exact (hasMCircuitOfSize_st hT hn hV k).mono (Nat.mul_le_mul_right _ (Nat.le_succ k))

theorem st_left (V : (Fin (n + Z) → Bool) → Bool) (hn : 0 < n) (x : Fin n → Bool) :
    ∀ k, ∀ i : Fin n, st V hn k x (Fin.castAdd Z i) = x i
  | 0, i => by simp [st]
  | k + 1, i => by
    by_cases h : k < Z
    · have hne : Fin.castAdd Z i ≠ Fin.natAdd n (⟨k, h⟩ : Fin Z) := by
        intro e; have := congrArg Fin.val e; simp at this; omega
      simp only [st, dif_pos h, step, Function.update_of_ne hne]
      exact st_left V hn x k i
    · simp only [st, dif_neg h]; exact st_left V hn x k i

/-- **Invariant of the self-reduction.** -/
theorem st_inv (V : (Fin (n + Z) → Bool) → Bool) (hn : 0 < n) (x : Fin n → Bool)
    (hx : ∃ z, V (Fin.append x z) = true) :
    ∀ k, k ≤ Z → ∃ z, V (Fin.append x (mix k (fun i => st V hn k x (Fin.natAdd n i)) z)) = true
  | 0, _ => by simpa [mix_zero] using hx
  | k + 1, hk => by
    have h : k < Z := by omega
    obtain ⟨z₀, hz₀⟩ := st_inv V hn x hx k (by omega)
    set xu := st V hn k x with hxu
    have hleft : (fun i => xu (Fin.castAdd Z i)) = x := funext (st_left V hn x k)
    set u := fun i => xu (Fin.natAdd n i) with hu
    let kk : Fin Z := ⟨k, h⟩
    have hst : st V hn (k + 1) x = step V kk xu := by simp only [st, dif_pos h]; rfl
    have hnew : (fun i => st V hn (k + 1) x (Fin.natAdd n i)) = Function.update u kk (ask V kk xu) := by
      funext i
      rw [hst]
      unfold step
      by_cases hi : i = kk
      · subst hi; rw [Function.update_self, Function.update_self]
      · have hne : Fin.natAdd n i ≠ Fin.natAdd n kk := fun e => hi (Fin.ext (by
          have := congrArg Fin.val e; simp at this; omega))
        rw [Function.update_of_ne hne, Function.update_of_ne hi]
    -- `mix (k+1) u' z = mix k u z` whenever `z k = u' k`
    have hmix : ∀ z : Fin Z → Bool, z kk = ask V kk xu →
        mix (k + 1) (Function.update u kk (ask V kk xu)) z = mix k u z := by
      intro z hz
      funext j
      simp only [mix]
      by_cases hj : j = kk
      · subst hj; simp [kk, hz]
      · have hjk : j.val ≠ k := fun e => hj (Fin.ext e)
        rw [Function.update_of_ne hj]
        by_cases h1 : j.val < k
        · simp [h1, show j.val < k + 1 by omega]
        · simp [h1, show ¬ j.val < k + 1 by omega]
    rw [hnew]
    by_cases ha : ask V kk xu = true
    · have := ha
      simp only [ask, decide_eq_true_eq, hleft] at this
      obtain ⟨z, hzk, hz⟩ := this
      refine ⟨z, ?_⟩
      rw [hmix z (by rw [hzk, ha])]
      exact hz
    · refine ⟨z₀, ?_⟩
      have hzk : z₀ kk = false := by
        by_contra hc
        apply ha
        simp only [ask, decide_eq_true_eq, hleft]
        exact ⟨z₀, by simpa using hc, hz₀⟩
      rw [hmix z₀ (by rw [hzk]; simpa using ha)]
      exact hz₀

/-- **Search to decision.** Under `SmallExistentials T`, every circuit `V(x, z)` of size `s` has a
multi-output search circuit `F` of size `≤ Z (n + Z) T(n + 2Z + s + 1)` that outputs a witness
whenever one exists. -/
theorem search_circuit {T : Polynomial ℕ} (hT : SmallExistentials T) (hn : 0 < n)
    {V : (Fin (n + Z) → Bool) → Bool} {s : ℕ} (hV : HasCircuitOfSize V s) :
    ∃ F : (Fin n → Bool) → (Fin Z → Bool),
      HasMCircuitOfSize F (Z * ((n + Z) * T.eval (n + Z + Z + (s + 1)))) ∧
      ∀ x, (∃ z, V (Fin.append x z) = true) → V (Fin.append x (F x)) = true := by
  refine ⟨fun x i => st V hn Z x (Fin.natAdd n i), ?_, fun x hx => ?_⟩
  · have := (hasMCircuitOfSize_st hT hn hV Z).comp
      (hasMCircuitOfSize_rewire (n := n + Z) (m := Z) (Fin.natAdd n))
    simp only [Nat.add_zero] at this
    exact this
  · obtain ⟨z, hz⟩ := st_inv V hn x hx Z le_rfl
    rwa [mix_all] at hz

end Search

end

end Pnp.KarpLipton
