import Pnp.Karp.ILPRed
import Pnp.Karp.ILPProg
import Pnp.Karp.ILPNP
import Pnp.Karp.Basic

/-!
# 0-1 INTEGER PROGRAMMING is NP-complete (official definitions)

`ILPLang` (`Pnp/Karp/ILP.lean`: every row is a linear constraint `Σⱼ cⱼ xⱼ ≥ d` with integer
coefficients written in binary as differences of two natural numbers; is there a `0-1` vector
satisfying all of them?) is NP-complete:

* `ilp_in_np` (`Pnp/Karp/ILPNP.lean`): membership in NP;
* `sat_iff_ilp` (`Pnp/Karp/ILPRed.lean`): a formula is satisfiable iff its instance `ILPI w`
  (two variables per variable of the formula, "exactly one of the two" constraints, and
  "some literal is true" per clause) has a `0-1` solution;
* `sat_le_ilp_of` (`Pnp/Karp/ILPProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.ILP

open Pnp.CookLevin

/-- **SAT ≤ₚ 0-1 INTEGER PROGRAMMING** (official polynomial-time many-one reducibility). -/
theorem sat_le_ilp :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang ILPLang :=
  sat_le_ilp_of sat_iff_ilp

/-- **0-1 INTEGER PROGRAMMING is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem ilp_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) ILPLang :=
  Pnp.Karp.np_complete_of_sat_reduces ilp_in_np sat_le_ilp

end Pnp.Karp.ILP
