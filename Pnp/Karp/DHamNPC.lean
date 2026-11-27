import Pnp.Karp.HamNPC
import Pnp.Karp.DHamRed
import Pnp.Karp.DHamNP
import Pnp.Karp.DHamProg

/-!
# DIRECTED HAMILTONIAN CYCLE is NP-complete (official definitions)

`DHamLang` (`Pnp/Karp/DHam.lean`: the rows of the word are an adjacency matrix, arc `u → v` iff
the entry `(u, v)` is `pos`; at least 3 vertices and a directed Hamiltonian cycle) is
NP-complete:

* `dham_in_np` (`Pnp/Karp/DHamNP.lean`): the verifier of `UHamLang` with a one-direction edge
  check;
* `uham_iff_dham` (`Pnp/Karp/DHamRed.lean`): every undirected edge becomes two arcs (`symG`);
* `uham_le_dham_of` (`Pnp/Karp/DHamProg.lean`): the symmetrization program;
* the undirected version is NP-complete (`uham_np_complete`, M40) and
  `Pnp.TM2Comp.npComplete_transfer`.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin

/-- **HAMILTONIAN CYCLE ≤ₚ DIRECTED HAMILTONIAN CYCLE**. -/
theorem uham_le_dham :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) UHamLang DHamLang :=
  uham_le_dham_of uham_iff_dham

/-- **DIRECTED HAMILTONIAN CYCLE is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem dham_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) DHamLang :=
  Pnp.TM2Comp.npComplete_transfer _ _ _ _ uham_np_complete dham_in_np uham_le_dham

end Pnp.Karp.Ham
