import Pnp.Karp.HamFwd
import Pnp.Karp.HamBwd
import Pnp.Karp.HamNP
import Pnp.Karp.HamGen

/-!
# HAMILTONIAN CYCLE is NP-complete (official definitions)

`UHamLang` (`Pnp/Karp/Ham.lean`: a word over `SatSym` whose rows are an adjacency matrix; it is
in the language iff the undirected graph has at least 3 vertices and a Hamiltonian cycle) is
NP-complete:

* `uham_in_np` (`Pnp/Karp/HamNP.lean`): HAMILTONIAN CYCLE ∈ NP;
* `ham_of_sat` (`Pnp/Karp/HamFwd.lean`) and `sat_of_ham` (`Pnp/Karp/HamBwd.lean`): a formula `w`
  is satisfiable iff the graph `H w` (the vertex split of a directed "variable rows + clause
  vertices" graph) has a Hamiltonian cycle;
* `sat_le_ham_of` (`Pnp/Karp/HamGen.lean`): `H` is polynomial-time computable;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.Ham

/-- Correctness of the reduction. -/
theorem sat_iff_ham (w : List Pnp.CookLevin.SatSym) :
    Pnp.CookLevin.SATLang w ↔ UHamLang (H w) :=
  ⟨ham_of_sat w, sat_of_ham w⟩

/-- **SAT ≤ₚ HAMILTONIAN CYCLE** (official polynomial-time many-one reducibility). -/
theorem sat_le_ham :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string Pnp.CookLevin.SatSym)
      (Millennium.fin_encoding_string Pnp.CookLevin.SatSym) Pnp.CookLevin.SATLang UHamLang :=
  sat_le_ham_of sat_iff_ham

/-- **HAMILTONIAN CYCLE is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem uham_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string Pnp.CookLevin.SatSym) UHamLang :=
  Pnp.Karp.np_complete_of_sat_reduces uham_in_np sat_le_ham

end Pnp.Karp.Ham
