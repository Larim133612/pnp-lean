import Pnp.Karp.FeedbackArcRed
import Pnp.Karp.FeedbackArcProg
import Pnp.Karp.FeedbackArcNP
import Pnp.Karp.FeedbackVSNPC
import Pnp.Karp.Basic

/-!
# FEEDBACK ARC SET (directed) is NP-complete (official definitions)

`FASLang` (`Pnp/Karp/FeedbackArc.lean`) is NP-complete:

* `fas_in_np` (`Pnp/Karp/FeedbackArcNP.lean`): membership in NP (certificate: a rank per
  vertex; the arcs not increasing in rank form the feedback arc set);
* `fvs_iff_fas` (`Pnp/Karp/FeedbackArcRed.lean`): vertex splitting `splitW` turns feedback vertex
  sets into feedback arc sets and back;
* `sat_le_fas_of` (`Pnp/Karp/FeedbackArcProg.lean`): the reduction program
  (FEEDBACK VERTEX SET instance, then `splitW`);
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.FeedbackArc

open Pnp.CookLevin

/-- Correctness of the instance `FASI w = splitW (FVSI w)`. -/
theorem sat_iff_fas (w : List SatSym) : SATLang w ↔ FASLang (FASI w) :=
  (FeedbackVS.sat_iff_fvs w).trans (fvs_iff_fas _)

/-- **SAT ≤ₚ FEEDBACK ARC SET** (official polynomial-time many-one reducibility). -/
theorem sat_le_fas :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang FASLang :=
  sat_le_fas_of sat_iff_fas

/-- **FEEDBACK ARC SET is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem fas_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) FASLang :=
  Pnp.Karp.np_complete_of_sat_reduces fas_in_np sat_le_fas

end Pnp.Karp.FeedbackArc
