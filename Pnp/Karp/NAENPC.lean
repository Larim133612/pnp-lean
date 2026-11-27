import Pnp.Karp.NAERed
import Pnp.Karp.NAEProg
import Pnp.Karp.NAENP
import Pnp.Karp.Basic

/-!
# NAE-3SAT is NP-complete (official definitions)

`NAE3Lang` (`Pnp/Karp/NAE.lean`: at most three literals per clause, an assignment under which
every clause has a true and a false literal) is NP-complete:

* `nae_in_np` (`Pnp/Karp/NAENP.lean`): membership in NP;
* `sat_iff_nae` (`Pnp/Karp/NAERed.lean`): a formula is satisfiable iff its instance `naeI w`
  (the prefix-OR chain of 3-SAT with a global variable `b` and one auxiliary variable per input
  position) is NAE-satisfiable;
* `sat_le_nae_of` (`Pnp/Karp/NAEProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.NAE

open Pnp.CookLevin

/-- **SAT ≤ₚ NAE-3SAT** (official polynomial-time many-one reducibility). -/
theorem sat_le_nae :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang NAE3Lang :=
  sat_le_nae_of sat_iff_nae

/-- **NAE-3SAT is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem nae_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) NAE3Lang :=
  Pnp.Karp.np_complete_of_sat_reduces nae_in_np sat_le_nae

end Pnp.Karp.NAE
