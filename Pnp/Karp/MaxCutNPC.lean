import Pnp.Karp.MaxCutRed
import Pnp.Karp.MaxCutProg
import Pnp.Karp.MaxCutNP
import Pnp.Karp.Basic

/-!
# MAX CUT is NP-complete (official definitions)

`MCLang` (`Pnp/Karp/MaxCut.lean`, simple undirected graphs, unary bound) is NP-complete:

* `mc_in_np` (`Pnp/Karp/MaxCutNP.lean`): membership in NP (certificate: the side of each vertex);
* `sat_iff_mc` (`Pnp/Karp/MaxCutRed.lean`): correctness of the gadget graph `MCI w`
  (triangles = not-all-equal constraints, a running OR along each clause);
* `sat_le_mc_of` (`Pnp/Karp/MaxCutProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.MaxCut

open Pnp.CookLevin

/-- **SAT ≤ₚ MAX CUT** (official polynomial-time many-one reducibility). -/
theorem sat_le_mc :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang MCLang :=
  sat_le_mc_of sat_iff_mc

/-- **MAX CUT is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem mc_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) MCLang :=
  Pnp.Karp.np_complete_of_sat_reduces mc_in_np sat_le_mc

end Pnp.Karp.MaxCut
