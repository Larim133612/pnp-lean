import Pnp.CookLevin.NPComplete

/-!
# Karp reductions: transitivity and transfer of NP-completeness

* `np_complete_of_sat_reduces`: a language in `NP` to which `SATLang` reduces is NP-complete
  (Cook–Levin `sat_np_complete` (M33) + `Pnp.TM2Comp.npComplete_transfer` (M25)).
-/

namespace Pnp.Karp

open Millennium Computability

/-- If `L ∈ NP` and `SATLang ≤ₚ L`, then `L` is NP-complete. -/
theorem np_complete_of_sat_reduces {α : Type} {ea : FinEncoding α} {L : Millennium.Language α}
    (hL : InNondeterministicPolynomialTime ea L)
    (hred : PolynomialTimeReducible (fin_encoding_string Pnp.CookLevin.SatSym) ea
      Pnp.CookLevin.SATLang L) :
    NondeterministicPolynomialTimeComplete ea L :=
  Pnp.TM2Comp.npComplete_transfer _ _ _ _ Pnp.CookLevin.NPC.sat_np_complete hL hred

end Pnp.Karp
