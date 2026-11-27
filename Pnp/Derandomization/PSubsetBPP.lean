import Pnp.Derandomization.BPP
import Pnp.TM2.Projection

/-!
# `P ⊆ BPP` for the official classes (M24)

A polynomial-time decider for `L` is turned, with `Pnp.TM2Proj.projComp`, into a polynomial-time
checking relation on `w#r` that ignores the random string `r`; it then never errs. Together with
`Pnp.Derand.inPPoly_of_inBPP` this gives the chain `P ⊆ BPP ⊆ P/poly` for the official
(Mathlib `TM2`) classes.

* `inBPP_of_inPolynomialTime`: **`P ⊆ BPP`**.
* `not_inPolynomialTime_of_not_inBPP`: the contrapositive.
-/

namespace Pnp.Derand

open Pnp.NaturalProofs Millennium

/-- **`P ⊆ BPP`**: every language decided in polynomial time by a Mathlib `TM2` machine is in the
official-style class `BPP` (with error probability `0`). -/
theorem inBPP_of_inPolynomialTime {α : Type} [Fintype α] [Nonempty α] {L : Millennium.Language (List α)}
    (hL : InPolynomialTime (fin_encoding_string α) L) : InBPP L :=
  ⟨fun w _ => L w, 0, Pnp.TM2Proj.polynomialTimeCheckingRelation_fst _ hL,
    fun w => by rw [prob_eq_zero fun r h => h Iff.rfl]; norm_num⟩

theorem not_inPolynomialTime_of_not_inBPP {α : Type} [Fintype α] [Nonempty α]
    {L : Millennium.Language (List α)} (hL : ¬ InBPP L) : ¬ InPolynomialTime (fin_encoding_string α) L :=
  fun h => hL (inBPP_of_inPolynomialTime h)

end Pnp.Derand
