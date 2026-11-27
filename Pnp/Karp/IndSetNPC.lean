import Pnp.Karp.IndSetNP

/-!
# INDEPENDENT SET is NP-complete (official definitions)

`ISLang` (`Pnp/Karp/IndSet.lean`: a word over `SatSym` whose first row gives the bound `k` in
unary and whose remaining rows are an adjacency matrix; it is in the language iff the graph has an
independent set of size `≥ k`) is NP-complete:

* `is_in_np` (`Pnp/Karp/IndSetNP.lean`): INDEPENDENT SET ∈ NP;
* `sat_le_is` (`Pnp/Karp/IndSet.lean`): SAT ≤ₚ INDEPENDENT SET (complement of the CLIQUE graph);
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.IndSet

/-- **INDEPENDENT SET is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem indSet_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string Pnp.CookLevin.SatSym) ISLang :=
  Pnp.Karp.np_complete_of_sat_reduces is_in_np sat_le_is

end Pnp.Karp.IndSet
