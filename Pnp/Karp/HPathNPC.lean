import Pnp.Karp.HamNPC
import Pnp.Karp.HPathRed
import Pnp.Karp.HPathNP
import Pnp.Karp.HPathProg

/-!
# HAMILTONIAN PATH is NP-complete (official definitions)

`UHPathLang` (`Pnp/Karp/HPath.lean`: an undirected graph as an adjacency matrix with a path
through all vertices) is NP-complete:

* `uhpath_in_np` (`Pnp/Karp/HPathNP.lean`): the verifier of HAMILTONIAN CYCLE without the
  wrap-around edge;
* `uham_iff_uhpath` (`Pnp/Karp/HPathRed.lean`): copy a vertex and attach a pendant vertex to it
  and to its copy;
* `uham_le_uhpath_of` (`Pnp/Karp/HPathProg.lean`): the program printing this graph;
* HAMILTONIAN CYCLE is NP-complete (`uham_np_complete`, M40) and
  `Pnp.TM2Comp.npComplete_transfer`.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin

/-- **HAMILTONIAN CYCLE ≤ₚ HAMILTONIAN PATH**. -/
theorem uham_le_uhpath :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) UHamLang UHPathLang :=
  uham_le_uhpath_of uham_iff_uhpath

/-- **HAMILTONIAN PATH is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem uhpath_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) UHPathLang :=
  Pnp.TM2Comp.npComplete_transfer _ _ _ _ uham_np_complete uhpath_in_np uham_le_uhpath

end Pnp.Karp.Ham
