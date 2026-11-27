import Pnp.Karp.CliqueNP
import Pnp.Karp.CliqueProg

/-!
# CLIQUE is NP-complete (official definitions)

`CliqueLang` (`Pnp/Karp/Clique.lean`: a word over `SatSym` whose first row gives the bound `k` in
unary and whose remaining rows are an adjacency matrix; it is in the language iff the graph has a
clique of size `≥ k`) is NP-complete:

* `clique_in_np` (`Pnp/Karp/CliqueNP.lean`): CLIQUE ∈ NP;
* `sat_le_clique` (`Pnp/Karp/CliqueProg.lean`): SAT ≤ₚ CLIQUE;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.Clique

/-- **CLIQUE is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem clique_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string Pnp.CookLevin.SatSym) CliqueLang :=
  Pnp.Karp.np_complete_of_sat_reduces clique_in_np sat_le_clique

end Pnp.Karp.Clique
