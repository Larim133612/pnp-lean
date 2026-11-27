import Pnp.Karp.Chromatic
import Pnp.Karp.ChromaticNP
import Pnp.Karp.Basic

/-!
# CHROMATIC NUMBER is NP-complete (official definitions)

`KColLang` (`Pnp/Karp/Chromatic.lean`, `k`-colorability with `k` in the input) is NP-complete:

* `kcol_in_np` (`Pnp/Karp/ChromaticNP.lean`): membership in NP (a color block per vertex);
* `sat_le_kcol` (`Pnp/Karp/Chromatic.lean`): the symmetrized 3-COLORING graph of M36 with
  `k = 3`;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.Chromatic

open Pnp.CookLevin

/-- **CHROMATIC NUMBER is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem kcol_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) KColLang :=
  Pnp.Karp.np_complete_of_sat_reduces kcol_in_np sat_le_kcol

end Pnp.Karp.Chromatic
