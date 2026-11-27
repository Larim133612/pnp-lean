import Pnp.PPoly.PPoly
import Pnp.Derandomization.Adleman

/-!
# The official class `BPP` and `BPP ⊆ P/poly` (M21)

`BPP` is defined in the style of the official `NP` of the Clay formalization
(`Millennium.InNondeterministicPolynomialTime`): a language `L` over a finite alphabet `α` is in
`BPP` if some polynomial-time checking relation `R w r` (a Mathlib `TM2` machine running on the
Cook pair encoding `w#r`, correct on *all* pairs) agrees with `L w` for at least `2/3` of the
random strings `r ∈ {0,1}^{|w|^k}`.

* `InBPP L`: the definition.
* `inPPoly_of_inBPP` (**`BPP ⊆ P/poly`**, Adleman 1978): every language in `BPP` has
  polynomial-size circuits. The proof simulates the verifier machine by circuits (the `P ⊆ P/poly`
  construction of `Pnp.PPoly.simulateOn`, which only needs correctness on the well-formed inputs
  `w#r`), prepends a small re-encoding circuit, and hard-wires good random strings with
  `Pnp.Derand.adleman`.
* `not_inBPP_of_not_inPPoly`: a super-polynomial circuit lower bound excludes a language from `BPP`.
-/

namespace Pnp.Derand

open Pnp.Circuits Pnp.NaturalProofs Pnp.PPoly Classical

noncomputable section

/-- **Bounded-error probabilistic polynomial time.** `L ∈ BPP` if there are a polynomial-time
checking relation `R` (official two-stack Turing machines on `w#r`, as for `NP`) and `k` such that
for every `w`, a uniformly random `r ∈ {0,1}^{|w|^k}` gives `R w r ↔ L w` except with
probability `≤ 1/3`. -/
def InBPP {α : Type} [Fintype α] (L : Millennium.Language (List α)) : Prop :=
  ∃ (R : List α → List Bool → Prop) (k : ℕ),
    Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string Bool) R ∧
    ∀ w : List α, prob (fun r : Fin (w.length ^ k) → Bool => ¬ (R w (List.ofFn r) ↔ L w)) ≤ 1 / 3

section Encoding

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The Cook pair string `w#r` over the alphabet `α ⊕ Option Bool`. -/
def pe (w : List α) (y : List Bool) : List (α ⊕ Option Bool) :=
  w.map Sum.inl ++ Sum.inr none :: y.map (fun b => Sum.inr (some b))

omit [DecidableEq α] [Nonempty α] in
theorem pe_eq_encode (w : List α) (y : List Bool) :
    pe w y = (Millennium.pair_encoding (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string Bool)).encode (w, y) := rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] in
theorem length_pe (w : List α) (y : List Bool) : (pe w y).length = w.length + 1 + y.length := by
  simp [pe]; omega

omit [Fintype α] [DecidableEq α] [Nonempty α] in
theorem getElem?_pe (w : List α) (y : List Bool) (i : ℕ) :
    (pe w y)[i]? = if i < w.length then (w[i]?).map Sum.inl
      else if i = w.length then some (Sum.inr none)
      else (y[i - w.length - 1]?).map (fun b => Sum.inr (some b)) := by
  unfold pe
  rw [List.getElem?_append]
  simp only [List.length_map]
  split_ifs with h₁ h₂
  · simp [List.getElem?_map]
  · subst h₂; simp
  · obtain ⟨t, rfl⟩ : ∃ t, i = w.length + 1 + t := ⟨i - w.length - 1, by omega⟩
    rw [show w.length + 1 + t - w.length = t + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_map]
    simp

omit [DecidableEq α] in
theorem length_decWord (n : ℕ) (x : Fin (n * Fintype.card α) → Bool) :
    (decWord n x).length = n := by simp [decWord]

variable (α) in
/-- The re-encoding map: from the one-hot bits of `w` and the random bits `r` to the one-hot
encoding of the pair string `w#r`. -/
def encE (n ℓ : ℕ) (z : Fin (n * Fintype.card α + ℓ) → Bool) :
    Fin ((n + 1 + ℓ) * Fintype.card (α ⊕ Option Bool)) → Bool :=
  oneHot (n + 1 + ℓ) (pe (decWord n fun i => z (Fin.castAdd ℓ i))
    (List.ofFn fun j => z (Fin.natAdd (n * Fintype.card α) j)))

theorem encE_append (n ℓ : ℕ) (x : Fin (n * Fintype.card α) → Bool) (r : Fin ℓ → Bool) :
    encE α n ℓ (Fin.append x r) = oneHot (n + 1 + ℓ) (pe (decWord n x) (List.ofFn r)) := by
  simp only [encE, Fin.append_left, Fin.append_right]

/-- Every output bit of `encE` reads at most `|α| + 1` input bits. -/
theorem hasMCircuitOfSize_encE {n ℓ : ℕ} (hN : 0 < n * Fintype.card α + ℓ) :
    HasMCircuitOfSize (encE α n ℓ) ((n + 1 + ℓ) * Fintype.card (α ⊕ Option Bool) *
      juntaSize (Fintype.card (Fin (Fintype.card α) ⊕ Unit))) := by
  let d0 : Fin (n * Fintype.card α + ℓ) := ⟨0, hN⟩
  let ι : Fin ((n + 1 + ℓ) * Fintype.card (α ⊕ Option Bool)) → Fin (Fintype.card α) ⊕ Unit →
      Fin (n * Fintype.card α + ℓ) := fun j d =>
    let i := (finProdFinEquiv.symm j).1.val
    match d with
    | Sum.inl c => if h : i < n then Fin.castAdd ℓ (finProdFinEquiv (⟨i, h⟩, c)) else d0
    | Sum.inr _ => if h : i - n - 1 < ℓ then Fin.natAdd (n * Fintype.card α) ⟨i - n - 1, h⟩
        else d0
  refine hasMCircuitOfSize_dep hN _ ι fun j x y hxy => ?_
  simp only [encE, oneHot]
  congr 2
  set i := (finProdFinEquiv.symm j).1.val with hi
  rw [getElem?_pe, getElem?_pe, length_decWord, length_decWord]
  split_ifs with h₁ h₂
  · congr 1
    refine decWord_getElem?_congr i fun hi' a => ?_
    have := hxy (Sum.inl (Fintype.equivFin α a))
    simp only [ι, ← hi, dif_pos hi'] at this
    exact this
  · rfl
  · rw [List.getElem?_ofFn, List.getElem?_ofFn]
    by_cases h₃ : i - n - 1 < ℓ
    · have := hxy (Sum.inr ())
      simp only [ι, ← hi, dif_pos h₃] at this
      simp only [dif_pos h₃, this]
    · simp only [dif_neg h₃]

end Encoding

/-- **`BPP ⊆ P/poly`** (Adleman). Every language in the official-style class `BPP` has
polynomial-size circuits. -/
theorem inPPoly_of_inBPP {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {L : Millennium.Language (List α)} (h : InBPP L) : InPPoly L := by
  obtain ⟨R, k, ⟨V, comp, hV⟩, herr⟩ := h
  let PE := Millennium.pair_encoding (Millennium.fin_encoding_string α)
    (Millennium.fin_encoding_string Bool)
  let dec : List (α ⊕ Option Bool) → List α × List Bool := fun u => (PE.decode u).getD ([], [])
  have hdec : ∀ w y, dec (pe w y) = (w, y) := fun w y => by
    simp only [dec, pe_eq_encode]
    rw [PE.decode_encode]; rfl
  let S : List (α ⊕ Option Bool) → Prop := fun u => ∃ w y, pe w y = u
  obtain ⟨p₁, hp₁⟩ := simulateOn (α := α ⊕ Option Bool) comp.tm comp.inputAlphabet comp.time
    (fun u => comp.outputAlphabet.symm (V (dec u))) (comp.outputAlphabet.symm true) S
    (by
      intro u hS
      have e := hS.choose_spec.choose_spec
      rw [← e, hdec]
      exact comp.outputsFun (hS.choose, hS.choose_spec.choose))
  let c := Fintype.card (α ⊕ Option Bool)
  let J := juntaSize (Fintype.card (Fin (Fintype.card α) ⊕ Unit))
  let a := Fintype.card α
  let mp : Polynomial ℕ := Polynomial.X + 1 + Polynomial.X ^ k
  let tp : Polynomial ℕ := 12 * (Polynomial.X * Polynomial.C a + 1)
  refine ⟨tp * (p₁.comp mp + mp * Polynomial.C (c * J) + 2) + ((2 * tp + 1) + tp * ((2 * tp + 1) * 32)),
    fun n hn => ?_⟩
  have ha : 0 < a := Fintype.card_pos
  have hN : 0 < n * a := Nat.mul_pos hn ha
  set ℓ := n ^ k
  set m := n + 1 + ℓ
  obtain ⟨g, hg, hgw⟩ := hp₁ m (by omega)
  let C : (Fin (n * a + ℓ) → Bool) → Bool := g ∘ encE α n ℓ
  have hC : HasCircuitOfSize C (m * c * J + p₁.eval m) :=
    (hasMCircuitOfSize_encE (α := α) (n := n) (ℓ := ℓ) (Nat.add_pos_left hN _)).comp_single hg
  let F : (Fin (n * a) → Bool) → Bool := fun x => decide (L (decWord n x))
  have hCx : ∀ x r, C (Fin.append x r) = true ↔ R (decWord n x) (List.ofFn r) := by
    intro x r
    simp only [C, Function.comp_apply, encE_append]
    rw [hgw _ ⟨_, _, rfl⟩ (by rw [length_pe, length_decWord, List.length_ofFn]), hdec,
      Equiv.apply_eq_iff_eq]
    exact (hV (decWord n x, List.ofFn r)).symm
  have herr' : ∀ x, prob (fun r : Fin ℓ → Bool => C (Fin.append x r) ≠ F x) ≤ 1 / 3 := by
    intro x
    have hw := herr (decWord n x)
    have key : ∀ (t : ℕ) (ht : (decWord n x).length = t),
        prob (fun r : Fin ((decWord n x).length ^ k) → Bool =>
          ¬ (R (decWord n x) (List.ofFn r) ↔ L (decWord n x))) =
        prob (fun r : Fin (t ^ k) → Bool =>
          ¬ (R (decWord n x) (List.ofFn r) ↔ L (decWord n x))) := by
      intro t ht; subst ht; rfl
    rw [key n (length_decWord n x)] at hw
    refine le_trans (le_of_eq ?_) hw
    congr 1
    funext r
    apply propext
    rw [← hCx]
    simp only [F, ne_eq]
    cases C (Fin.append x r) <;> by_cases hL : L (decWord n x) <;> simp [hL]
  have hA := adleman hN hC F herr'
  refine ⟨F, hA.mono (le_of_eq ?_), fun w hw => ?_⟩
  · simp only [tp, mp, majSize, m, ℓ, a, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_ofNat]
    ring
  · simp only [F, decWord_oneHot w hw, decide_eq_true_eq]

/-- A language without polynomial-size circuits is not in `BPP`. -/
theorem not_inBPP_of_not_inPPoly {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {L : Millennium.Language (List α)} (h : ¬ InPPoly L) : ¬ InBPP L :=
  fun hL => h (inPPoly_of_inBPP hL)

end

end Pnp.Derand
