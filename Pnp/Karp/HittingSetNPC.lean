import Pnp.Karp.HittingSetRed
import Pnp.Karp.HittingSetProg
import Pnp.Karp.HittingSetNP
import Pnp.Karp.Basic

/-!
# HITTING SET is NP-complete (official definitions)

`HSLang` (`Pnp/Karp/HittingSet.lean`) is NP-complete:

* `hs_in_np` (`Pnp/Karp/HittingSetNP.lean`): membership in NP;
* `sat_iff_hs` (`Pnp/Karp/HittingSetRed.lean`): a formula is satisfiable iff its instance `HSI w`
  (literal elements, a pair `{x_j, ¬x_j}` per variable, a set per clause, budget `N`) has a
  hitting set;
* `sat_le_hs_of` (`Pnp/Karp/HittingSetProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.HittingSet

open Pnp.CookLevin

/-- **SAT ≤ₚ HITTING SET** (official polynomial-time many-one reducibility). -/
theorem sat_le_hs :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang HSLang :=
  sat_le_hs_of sat_iff_hs

/-- **HITTING SET is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem hs_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) HSLang :=
  Pnp.Karp.np_complete_of_sat_reduces hs_in_np sat_le_hs

end Pnp.Karp.HittingSet
