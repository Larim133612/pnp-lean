import Pnp.Karp.SetPackRed
import Pnp.Karp.SetPackProg
import Pnp.Karp.SetPackNP
import Pnp.Karp.ThreeDMNPC

/-!
# SET PACKING is NP-complete (official definitions)

`SPLang` (`Pnp/Karp/SetPacking.lean`) is NP-complete:

* `spk_in_np` (`Pnp/Karp/SetPackNP.lean`): membership in NP (a verifier checking that the
  selected rows are pairwise disjoint and at least as many as the target);
* `x3c_iff_spk` (`Pnp/Karp/SetPackRed.lean`): the X3C instance `X3I w` has an exact cover iff
  `SPI w` (the same triples, target `q`) has `q` pairwise disjoint sets; with `sat_iff_x3c`
  (M46) the formula is satisfiable iff `SPI w ∈ SPLang`;
* `sat_le_spk_of` (`Pnp/Karp/SetPackProg.lean`): the reduction program (that of SET COVER);
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.SetPacking

open Pnp.CookLevin Pnp.Karp.ThreeDM

/-- The SET PACKING reduction is correct. -/
theorem sat_iff_spk (w : List SatSym) : SATLang w ↔ SPLang (SPI w) :=
  (sat_iff_x3c w).trans (x3c_iff_spk w)

/-- **SAT ≤ₚ SET PACKING** (official polynomial-time many-one reducibility). -/
theorem sat_le_spk :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang SPLang :=
  sat_le_spk_of sat_iff_spk

/-- **SET PACKING is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem spk_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) SPLang :=
  Pnp.Karp.np_complete_of_sat_reduces spk_in_np sat_le_spk

end Pnp.Karp.SetPacking
