import Pnp.Karp.ExactCoverRed
import Pnp.Karp.ExactCoverNP
import Pnp.Karp.Basic

/-!
# EXACT COVER is NP-complete (official definitions)

`ECLang` (`Pnp/Karp/ExactCover.lean`) is NP-complete:

* `ec_in_np` (`Pnp/Karp/ExactCoverNP.lean`): membership in NP (the X3C verifier without the
  three-element check);
* `sat_le_ec` (`Pnp/Karp/ExactCoverRed.lean`): the X3C instance `X3I w` (M46) is also an EXACT
  COVER instance;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.ExactCover

open Pnp.CookLevin

/-- **EXACT COVER is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem ec_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) ECLang :=
  Pnp.Karp.np_complete_of_sat_reduces ec_in_np sat_le_ec

end Pnp.Karp.ExactCover
