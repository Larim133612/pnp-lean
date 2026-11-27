import Pnp.Karp.ThreeDMComb
import Pnp.Karp.ThreeDMRed
import Pnp.Karp.ThreeDMProg
import Pnp.Karp.ThreeDMNP
import Pnp.Karp.X3CNP
import Pnp.Karp.Basic

/-!
# 3-DIMENSIONAL MATCHING and EXACT COVER BY 3-SETS are NP-complete (official definitions)

`DMLang` and `X3CLang` (`Pnp/Karp/ThreeDM.lean`) are NP-complete:

* `dm_in_np` (`Pnp/Karp/ThreeDMNP.lean`), `x3c_in_np` (`Pnp/Karp/X3CNP.lean`): membership in NP
  (verifiers checking the shape of the rows and that the selected rows cover every element
  exactly once);
* `sat_iff_covT` (`Pnp/Karp/ThreeDMComb.lean`): a formula is satisfiable iff its triples
  (Garey–Johnson: a ring of triples per variable, a triple per literal occurrence, garbage
  triples) have an exact cover; `dm_iff_covT`, `x3c_iff_covT` (`Pnp/Karp/ThreeDMRed.lean`): the
  printed instances `DMI w`, `X3I w` are yes-instances iff such a cover exists;
* `sat_le_dm_of`, `sat_le_x3c_of` (`Pnp/Karp/ThreeDMProg.lean`): the reduction programs;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.ThreeDM

open Pnp.CookLevin

/-- The 3DM reduction is correct. -/
theorem sat_iff_dm (w : List SatSym) : SATLang w ↔ DMLang (DMI w) :=
  (sat_iff_covT w).trans (dm_iff_covT w).symm

/-- The X3C reduction is correct. -/
theorem sat_iff_x3c (w : List SatSym) : SATLang w ↔ X3CLang (X3I w) :=
  (sat_iff_covT w).trans (x3c_iff_covT w).symm

/-- **SAT ≤ₚ 3DM** (official polynomial-time many-one reducibility). -/
theorem sat_le_dm :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang DMLang :=
  sat_le_dm_of sat_iff_dm

/-- **SAT ≤ₚ X3C** (official polynomial-time many-one reducibility). -/
theorem sat_le_x3c :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang X3CLang :=
  sat_le_x3c_of sat_iff_x3c

/-- **3-DIMENSIONAL MATCHING is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem dm_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) DMLang :=
  Pnp.Karp.np_complete_of_sat_reduces dm_in_np sat_le_dm

/-- **EXACT COVER BY 3-SETS is NP-complete** for the official definitions. -/
theorem x3c_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) X3CLang :=
  Pnp.Karp.np_complete_of_sat_reduces x3c_in_np sat_le_x3c

end Pnp.Karp.ThreeDM
