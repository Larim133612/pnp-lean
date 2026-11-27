import Pnp.Karp.FeedbackVSRed
import Pnp.Karp.FeedbackVSProg
import Pnp.Karp.FeedbackVSNP
import Pnp.Karp.Basic

/-!
# FEEDBACK VERTEX SET (directed) is NP-complete (official definitions)

`FVSLang` (`Pnp/Karp/FeedbackVS.lean`) is NP-complete:

* `fvs_in_np` (`Pnp/Karp/FeedbackVSNP.lean`): membership in NP (certificate: the set `F` and a
  rank per vertex strictly increasing along every arc outside `F`);
* `sat_iff_fvs` (`Pnp/Karp/FeedbackVSRed.lean`): on the symmetric VERTEX COVER instance
  `cmap (GV w)` (M35) feedback vertex sets are exactly vertex covers;
* `sat_le_fvs_of` (`Pnp/Karp/FeedbackVSProg.lean`): the reduction (the VERTEX COVER one);
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.FeedbackVS

open Pnp.CookLevin

/-- **SAT ≤ₚ FEEDBACK VERTEX SET** (official polynomial-time many-one reducibility). -/
theorem sat_le_fvs :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang FVSLang :=
  sat_le_fvs_of sat_iff_fvs

/-- **FEEDBACK VERTEX SET is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem fvs_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) FVSLang :=
  Pnp.Karp.np_complete_of_sat_reduces fvs_in_np sat_le_fvs

end Pnp.Karp.FeedbackVS
