import Pnp.Karp.VertexCoverProg

/-!
# VERTEX COVER is NP-complete (official definitions)

`VCLang` (`Pnp/Karp/VertexCover.lean`: a word over `SatSym` whose first row gives the bound `k`
in unary and whose remaining rows are an adjacency matrix; it is in the language iff the graph has
a vertex cover of size `≤ k`) is NP-complete:

* `vc_in_np` (`Pnp/Karp/VertexCover.lean`): VERTEX COVER ∈ NP;
* `sat_le_vc` (`Pnp/Karp/VertexCoverProg.lean`): SAT ≤ₚ VERTEX COVER (complement of the CLIQUE
  graph, bound `n - k`);
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.VertexCover

/-- **VERTEX COVER is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem vertexCover_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string Pnp.CookLevin.SatSym) VCLang :=
  Pnp.Karp.np_complete_of_sat_reduces vc_in_np sat_le_vc

end Pnp.Karp.VertexCover
