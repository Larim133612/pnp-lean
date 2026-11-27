import Pnp.Karp.SetCoverRed
import Pnp.Karp.SetCoverProg
import Pnp.Karp.SetCoverNP
import Pnp.Karp.ThreeDMNPC

/-!
# SET COVER is NP-complete (official definitions)

`SCLang` (`Pnp/Karp/SetCover.lean`) is NP-complete:

* `sc_in_np` (`Pnp/Karp/SetCoverNP.lean`): membership in NP (a verifier checking that the
  selected rows are at most the budget and cover the ground set);
* `x3c_iff_sc` (`Pnp/Karp/SetCoverRed.lean`): the X3C instance `X3I w` of a formula has an exact
  cover iff the SET COVER instance `SCI w` (the same triples, budget `q`) has a cover;
  with `sat_iff_x3c` (M46) the formula is satisfiable iff `SCI w ∈ SCLang`;
* `sat_le_sc_of` (`Pnp/Karp/SetCoverProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.SetCover

open Pnp.CookLevin Pnp.Karp.ThreeDM

/-- The SET COVER reduction is correct. -/
theorem sat_iff_sc (w : List SatSym) : SATLang w ↔ SCLang (SCI w) :=
  (sat_iff_x3c w).trans (x3c_iff_sc w)

/-- **SAT ≤ₚ SET COVER** (official polynomial-time many-one reducibility). -/
theorem sat_le_sc :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang SCLang :=
  sat_le_sc_of sat_iff_sc

/-- **SET COVER is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem sc_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) SCLang :=
  Pnp.Karp.np_complete_of_sat_reduces sc_in_np sat_le_sc

end Pnp.Karp.SetCover
