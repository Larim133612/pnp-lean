import Pnp.Karp.HamNPC
import Pnp.Karp.TspRed
import Pnp.Karp.TspNP
import Pnp.Karp.TspProg

/-!
# TRAVELING SALESMAN (decision version) is NP-complete (official definitions)

`TSPLang` (`Pnp/Karp/Tsp.lean`: a budget and a weight matrix in binary; at least 3 cities and a
tour of cost at most the budget) is NP-complete:

* `tsp_in_np` (`Pnp/Karp/TspNP.lean`): the verifier checks a tour given as one-hot blocks and
  adds up its weights with a binary adder;
* `uham_iff_tsp` (`Pnp/Karp/TspRed.lean`): weight `0` on edges, `1` on non-edges, budget `0`;
* `uham_le_tsp_of` (`Pnp/Karp/TspProg.lean`): the program printing this instance;
* HAMILTONIAN CYCLE is NP-complete (`uham_np_complete`, M40) and
  `Pnp.TM2Comp.npComplete_transfer`.
-/

namespace Pnp.Karp.Tsp

open Pnp.CookLevin Pnp.Karp.Ham

/-- **HAMILTONIAN CYCLE ≤ₚ TSP**. -/
theorem uham_le_tsp :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) UHamLang TSPLang :=
  uham_le_tsp_of uham_iff_tsp

/-- **TRAVELING SALESMAN (decision version) is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem tsp_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) TSPLang :=
  Pnp.TM2Comp.npComplete_transfer _ _ _ _ uham_np_complete tsp_in_np uham_le_tsp

end Pnp.Karp.Tsp
