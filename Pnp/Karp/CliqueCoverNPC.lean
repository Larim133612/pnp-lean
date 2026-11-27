import Pnp.Karp.CliqueCoverRed
import Pnp.Karp.CliqueCoverProg
import Pnp.Karp.CliqueCoverNP
import Pnp.Karp.Basic

/-!
# CLIQUE COVER is NP-complete (official definitions)

`CCLang` (`Pnp/Karp/CliqueCover.lean`) is NP-complete:

* `cc_in_np` (`Pnp/Karp/CliqueCoverNP.lean`): membership in NP (a class block per vertex);
* `sat_iff_cc` (`Pnp/Karp/CliqueCoverRed.lean`): a formula is satisfiable iff the complement of
  the symmetrized 3-COLORING graph (M36) can be covered by 3 cliques;
* `sat_le_cc_of` (`Pnp/Karp/CliqueCoverProg.lean`): the reduction program (composition of the
  3-COLORING program, symmetrization with header, and complementation);
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.CliqueCover

open Pnp.CookLevin

/-- **SAT ≤ₚ CLIQUE COVER** (official polynomial-time many-one reducibility). -/
theorem sat_le_cc :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang CCLang :=
  sat_le_cc_of sat_iff_cc

/-- **CLIQUE COVER is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem cc_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) CCLang :=
  Pnp.Karp.np_complete_of_sat_reduces cc_in_np sat_le_cc

end Pnp.Karp.CliqueCover
