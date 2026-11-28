import Pnp.Karp.SeqRDRed
import Pnp.Karp.SeqRDProg
import Pnp.Karp.SeqRDNP
import Pnp.Karp.ThreeDMNPC

/-!
# SEQUENCING WITH RELEASE TIMES AND DEADLINES is strongly NP-complete (unary, official)

`SRDLang` (`Pnp/Karp/SeqRD.lean`, every number in unary) is NP-complete, i.e. the problem is
NP-complete *in the strong sense* (Garey–Johnson SS1).

* `srd_in_np` (`Pnp/Karp/SeqRDNP.lean`): membership in NP (certificate: the start times);
* `sat_iff_srd` (`Pnp/Karp/SeqRDRed.lean`): a formula is satisfiable iff `SRDI w` is a
  yes-instance (separator tasks cut the time line into `m` windows of length `B`, so the instance
  is equivalent to the unary BIN PACKING instance `BPUI w` of M65);
* `sat_le_srd_of` (`Pnp/Karp/SeqRDProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.SeqRD

open Pnp.CookLevin

/-- **SAT ≤ₚ unary SEQUENCING WITH RELEASE TIMES AND DEADLINES**. -/
theorem sat_le_srd :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang SRDLang :=
  sat_le_srd_of sat_iff_srd

/-- **SEQUENCING WITH RELEASE TIMES AND DEADLINES is strongly NP-complete** (official
definitions). -/
theorem srd_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) SRDLang :=
  Pnp.Karp.np_complete_of_sat_reduces srd_in_np sat_le_srd

end Pnp.Karp.SeqRD
