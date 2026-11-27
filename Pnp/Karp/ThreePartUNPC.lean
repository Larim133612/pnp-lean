import Pnp.Karp.ThreePartURed
import Pnp.Karp.ThreePartUProg
import Pnp.Karp.ThreePartUNP
import Pnp.Karp.ThreeDMNPC

/-!
# 3-PARTITION is strongly NP-complete (unary encoding, official definitions)

`TPULang` (`Pnp/Karp/ThreePartU.lean`: 3-PARTITION with every number written in unary) is
NP-complete.  Since a unary instance has size at least the sum of its numbers, this is
NP-completeness of 3-PARTITION *in the strong sense* (Garey–Johnson): the problem stays NP-hard
when all numbers are bounded by a polynomial in the instance size.

* `tpu_in_np` (`Pnp/Karp/ThreePartUNP.lean`): membership in NP;
* `sat_iff_tpu` (`Pnp/Karp/ThreePartURed.lean`): a formula is satisfiable iff `TPUI w` is a
  yes-instance (M63's items with every block compressed into one base-`R` digit,
  `R = 27 M + 10`; rigidity `tpu_sum_iff` in `ThreePartUArith.lean`);
* `sat_le_tpu_of` (`Pnp/Karp/ThreePartUProg.lean`): the reduction program (unary printer
  composed with the 3DM printer of M46);
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.ThreePartU

open Pnp.CookLevin

/-- **SAT ≤ₚ unary 3-PARTITION** (official polynomial-time many-one reducibility). -/
theorem sat_le_tpu :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang TPULang :=
  sat_le_tpu_of sat_iff_tpu

/-- **3-PARTITION is strongly NP-complete**: the unary version is NP-complete for the official
definitions (`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem tpu_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) TPULang :=
  Pnp.Karp.np_complete_of_sat_reduces tpu_in_np sat_le_tpu

end Pnp.Karp.ThreePartU
