import Pnp.Karp.DomSetRed
import Pnp.Karp.DomSetProg
import Pnp.Karp.DomSetNP
import Pnp.Karp.Basic

/-!
# DOMINATING SET is NP-complete (official definitions)

`DSLang` (`Pnp/Karp/DomSet.lean`: budget row and adjacency matrix; is there a set of at most
`k` vertices such that every vertex is in it or adjacent to it?) is NP-complete:

* `ds_in_np` (`Pnp/Karp/DomSetNP.lean`): membership in NP;
* `sat_iff_ds` (`Pnp/Karp/DomSetRed.lean`): a formula is satisfiable iff its instance `DSI w`
  (a triangle per variable, a vertex per clause adjacent to its literals, budget `N`) has a
  dominating set;
* `sat_le_ds_of` (`Pnp/Karp/DomSetProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.DomSet

open Pnp.CookLevin

/-- **SAT ≤ₚ DOMINATING SET** (official polynomial-time many-one reducibility). -/
theorem sat_le_ds :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang DSLang :=
  sat_le_ds_of sat_iff_ds

/-- **DOMINATING SET is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem ds_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) DSLang :=
  Pnp.Karp.np_complete_of_sat_reduces ds_in_np sat_le_ds

end Pnp.Karp.DomSet
