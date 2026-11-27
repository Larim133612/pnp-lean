import Pnp.Karp.NAERed
import Pnp.Karp.M2Red
import Pnp.Karp.M2Prog
import Pnp.Karp.M2NP
import Pnp.Karp.Basic

/-!
# MAX 2-SAT is NP-complete (official definitions)

`M2Lang` (`Pnp/Karp/NAE.lean`: clauses with at most two literals followed by a threshold row
`kr`; some assignment satisfies at least `|kr|` of the clauses) is NP-complete:

* `m2_in_np` (`Pnp/Karp/M2NP.lean`): membership in NP;
* `sat_iff_m2`: a formula is satisfiable iff its instance `m2I w` has an assignment satisfying
  at least `thr w` clauses: `sat_iff_ncs` (`Pnp/Karp/NAERed.lean`, SAT ⇔ the NAE clauses `NCs w`
  are NAE-satisfiable) and `m2_iff_ncs` (`Pnp/Karp/M2Red.lean`, every NAE clause on literals
  `ℓ₁, ℓ₂(, ℓ₃)` becomes the 2-clauses `ℓᵢ ∨ ℓₖ`, `¬ℓᵢ ∨ ¬ℓₖ`, of which exactly `2` resp. `5`
  are satisfied iff the NAE clause is, and fewer otherwise);
* `sat_le_m2_of` (`Pnp/Karp/M2Prog.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.NAE

open Pnp.CookLevin

/-- **SAT ≤ MAX 2-SAT**: correctness of the instance `m2I w`. -/
theorem sat_iff_m2 (w : List SatSym) : SATLang w ↔ M2Lang (m2I w) :=
  (sat_iff_ncs w).trans (m2_iff_ncs w).symm

/-- **SAT ≤ₚ MAX 2-SAT** (official polynomial-time many-one reducibility). -/
theorem sat_le_m2 :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang M2Lang :=
  sat_le_m2_of sat_iff_m2

/-- **MAX 2-SAT is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem m2_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) M2Lang :=
  Pnp.Karp.np_complete_of_sat_reduces m2_in_np sat_le_m2

end Pnp.Karp.NAE
