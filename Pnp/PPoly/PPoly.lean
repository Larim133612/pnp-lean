import Pnp.Upstream.Millennium
import Pnp.PPoly.Simulate

/-!
# `P ⊆ P/poly` and circuit lower bounds for `NP` imply `P ≠ NP`

* `InPPoly L`: `L` has polynomial-size circuits (one per input length, inputs encoded one-hot,
  see `Pnp.PPoly.oneHot` in `Pnp.PPoly.Encode`).
* `inPPoly_of_inPolynomialTime`: every language in the upstream class `P` is in `P/poly`.
* `ppoly_of_clayPVersusNP`, `negativeBranch_of_not_inPPoly`: a super-polynomial circuit lower
  bound for a language in `NP` proves the official negative branch `P ≠ NP`.
-/

namespace Pnp.PPoly

/-- Non-uniform polynomial size: for every input length `n ≥ 1` some circuit of size `≤ p(n)`
decides `L` on all strings of length `n` (encoded one-hot). -/
def InPPoly {α : Type} [Fintype α] [DecidableEq α] (L : Millennium.Language (List α)) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, 0 < n → ∃ f : (Fin (n * Fintype.card α) → Bool) → Bool,
    Pnp.Circuits.HasCircuitOfSize f (p.eval n) ∧
      ∀ w : List α, w.length = n → (f (oneHot n w) = true ↔ L w)

/-- **`P ⊆ P/poly`.** -/
theorem inPPoly_of_inPolynomialTime {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {L : Millennium.Language (List α)}
    (h : Millennium.InPolynomialTime (Millennium.fin_encoding_string α) L) : InPPoly L := by
  obtain ⟨f, comp, hf⟩ := h
  obtain ⟨p, hp⟩ := simulate (α := α) comp.tm comp.inputAlphabet comp.time
    (fun w => comp.outputAlphabet.symm (f w)) (comp.outputAlphabet.symm true)
    fun w => comp.outputsFun w
  refine ⟨p, fun n hn => ?_⟩
  obtain ⟨g, hg, hgw⟩ := hp n hn
  refine ⟨g, hg, fun w hw => ?_⟩
  rw [hgw w hw, Equiv.apply_eq_iff_eq]
  exact (hf w).symm

theorem ppoly_of_clayPVersusNP (hPNP : Millennium.ClayPVersusNP) {α : Type} [Fintype α]
    [DecidableEq α] [Nontrivial α] {L : Millennium.Language (List α)}
    (hL : Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string α) L) :
    InPPoly L :=
  inPPoly_of_inPolynomialTime ((hPNP α L).2 hL)

/-- Circuit lower bounds for NP imply the official negative branch `P ≠ NP`. -/
theorem negativeBranch_of_not_inPPoly {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
    {L : Millennium.Language (List α)}
    (hL : Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string α) L)
    (hL' : ¬ InPPoly L) : Millennium.ClayPVersusNP.Formulations.NegativeBranch :=
  fun hPNP => hL' (ppoly_of_clayPVersusNP hPNP hL)

end Pnp.PPoly
