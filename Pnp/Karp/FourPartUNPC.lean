import Pnp.Karp.FourPartURed
import Pnp.Karp.FourPartUProg
import Pnp.Karp.FourPartUNP
import Pnp.Karp.ThreeDMNPC

/-!
# 4-PARTITION is strongly NP-complete (unary encoding, official definitions)

`FPULang` (`Pnp/Karp/FourPartU.lean`: 4-PARTITION with every number written in unary) is
NP-complete, i.e. 4-PARTITION is NP-complete *in the strong sense* (Garey–Johnson).

* `fpu_in_np` (`Pnp/Karp/FourPartUNP.lean`): membership in NP;
* `sat_iff_fpu` (`Pnp/Karp/FourPartURed.lean`): a formula is satisfiable iff `FPUI w` is a
  yes-instance (the unary 3-PARTITION instance `TPUI w` of M64 with items `5 N + a`, `m` fillers
  `6 N` and bound `21 N + B`, `N` the instance length; our own construction);
* `sat_le_fpu_of` (`Pnp/Karp/FourPartUProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.FourPartU

open Pnp.CookLevin

/-- **SAT ≤ₚ unary 4-PARTITION** (official polynomial-time many-one reducibility). -/
theorem sat_le_fpu :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang FPULang :=
  sat_le_fpu_of sat_iff_fpu

/-- **4-PARTITION is strongly NP-complete**: the unary version is NP-complete for the official
definitions (`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem fpu_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) FPULang :=
  Pnp.Karp.np_complete_of_sat_reduces fpu_in_np sat_le_fpu

end Pnp.Karp.FourPartU
