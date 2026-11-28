import Pnp.Karp.BinPackURed
import Pnp.Karp.BinPackUProg
import Pnp.Karp.BinPackUNP
import Pnp.Karp.ThreeDMNPC

/-!
# BIN PACKING is strongly NP-complete (unary encoding, official definitions)

`UBPLang` (`Pnp/Karp/BinPackU.lean`: BIN PACKING with every number written in unary) is
NP-complete, i.e. BIN PACKING is NP-complete *in the strong sense* (Garey–Johnson).

* `ubp_in_np` (`Pnp/Karp/BinPackUNP.lean`): membership in NP;
* `sat_iff_bpu` (`Pnp/Karp/BinPackURed.lean`): a formula is satisfiable iff `BPUI w` is a
  yes-instance (`m` bins of capacity `B` for the unary 3-PARTITION instance `TPUI w` of M64, whose
  items always have total size `m B`, `tpu_total` in `ThreePartUTotal.lean`);
* `sat_le_bpu_of` (`Pnp/Karp/BinPackUProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.BinPackU

open Pnp.CookLevin

/-- **SAT ≤ₚ unary BIN PACKING** (official polynomial-time many-one reducibility). -/
theorem sat_le_bpu :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang UBPLang :=
  sat_le_bpu_of sat_iff_bpu

/-- **BIN PACKING is strongly NP-complete**: the unary version is NP-complete for the official
definitions (`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem ubp_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) UBPLang :=
  Pnp.Karp.np_complete_of_sat_reduces ubp_in_np sat_le_bpu

end Pnp.Karp.BinPackU
