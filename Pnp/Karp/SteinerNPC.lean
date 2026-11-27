import Pnp.Karp.SteinerRed
import Pnp.Karp.SteinerProg
import Pnp.Karp.SteinerNP
import Pnp.Karp.ThreeDMNPC

/-!
# STEINER TREE (in graphs) is NP-complete (official definitions)

`STLang` (`Pnp/Karp/Steiner.lean`: a set of at most `K` edges connecting all terminals, i.e. a
Steiner tree with at most `K` edges) is NP-complete:

* `st_in_np` (`Pnp/Karp/SteinerNP.lean`): membership in NP (a verifier checking the edges, the
  budget and a connectivity certificate);
* `x3c_iff_st` (`Pnp/Karp/SteinerRed.lean`): the X3C instance `X3I w` of a formula (M46) has an
  exact cover iff its STEINER TREE graph `STI w` (root, triple vertices, element vertices,
  budget `4q`) has a Steiner tree; with `sat_iff_x3c` the formula is satisfiable iff
  `STI w ∈ STLang`;
* `sat_le_st_of` (`Pnp/Karp/SteinerProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.Steiner

open Pnp.CookLevin Pnp.Karp.ThreeDM

/-- The STEINER TREE reduction is correct. -/
theorem sat_iff_st (w : List SatSym) : SATLang w ↔ STLang (STI w) :=
  (sat_iff_x3c w).trans (x3c_iff_st w)

/-- **SAT ≤ₚ STEINER TREE** (official polynomial-time many-one reducibility). -/
theorem sat_le_st :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang STLang :=
  sat_le_st_of sat_iff_st

/-- **STEINER TREE is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem st_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) STLang :=
  Pnp.Karp.np_complete_of_sat_reduces st_in_np sat_le_st

end Pnp.Karp.Steiner
