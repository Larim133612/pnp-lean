import Pnp.Karp.ThreePartRed
import Pnp.Karp.ThreePartProg
import Pnp.Karp.ThreePartNP
import Pnp.Karp.ThreeDMNPC

/-!
# 3-PARTITION is NP-complete (official definitions)

`TPLang` (`Pnp/Karp/ThreePart.lean`: `3 m` items with sizes strictly between `B/4` and `B/2`,
split into `m` groups of total size exactly `B`; numbers in binary) is NP-complete:

* `tp_in_np` (`Pnp/Karp/ThreePartNP.lean`): membership in NP;
* `sat_iff_tp` (`Pnp/Karp/ThreePartRed.lean`): a formula is satisfiable iff `TPI w` is a
  yes-instance (via the 3DM triples of M46 and our base-`4` digit construction:
  `tp_of_cov` (`ThreePartFwd.lean`), `cov_of_tp` (`ThreePartBwd.lean`), the no-carry arithmetic and
  the rigidity of the groups `tp_sum_iff` (`ThreePartArith.lean`));
* `sat_le_tp_of` (`Pnp/Karp/ThreePartProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).

All numbers of `TPI w` have only base-`4` digits `0`, `1` (and a leading `3` for `B`); their
values are exponential in the instance size, so this is NP-completeness for the binary encoding
(strong NP-completeness, i.e. with unary numbers, is not formalised here).
-/

namespace Pnp.Karp.ThreePart

open Pnp.CookLevin

/-- **SAT ≤ₚ 3-PARTITION** (official polynomial-time many-one reducibility). -/
theorem sat_le_tp :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang TPLang :=
  sat_le_tp_of sat_iff_tp

/-- **3-PARTITION is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem tp_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) TPLang :=
  Pnp.Karp.np_complete_of_sat_reduces tp_in_np sat_le_tp

end Pnp.Karp.ThreePart
