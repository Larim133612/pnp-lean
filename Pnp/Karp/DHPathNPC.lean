import Pnp.Karp.HPathNPC
import Pnp.Karp.DHPathRed
import Pnp.Karp.DHPathProg
import Pnp.Karp.DHPathNP

/-!
# DIRECTED HAMILTONIAN PATH is NP-complete (official definitions)

`DHPathLang` (`Pnp/Karp/DHPath.lean`: arc `u → v` iff the entry `(u, v)` is `pos`; is there an
ordering of the vertices along a directed path?) is NP-complete:

* `dhpath_in_np` (`Pnp/Karp/DHPathNP.lean`): membership in NP;
* `uhpath_iff_dhpath` (`Pnp/Karp/DHPathRed.lean`): every undirected edge becomes two arcs
  (`symG`);
* `uhpath_le_dhpath_of` (`Pnp/Karp/DHPathProg.lean`): the symmetrization program;
* the undirected version is NP-complete (`uhpath_np_complete`, M45) and
  `Pnp.TM2Comp.npComplete_transfer`.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin

/-- **HAMILTONIAN PATH ≤ₚ DIRECTED HAMILTONIAN PATH**. -/
theorem uhpath_le_dhpath :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) UHPathLang DHPathLang :=
  uhpath_le_dhpath_of uhpath_iff_dhpath

/-- **DIRECTED HAMILTONIAN PATH is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem dhpath_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) DHPathLang :=
  Pnp.TM2Comp.npComplete_transfer _ _ _ _ uhpath_np_complete dhpath_in_np uhpath_le_dhpath

end Pnp.Karp.Ham
