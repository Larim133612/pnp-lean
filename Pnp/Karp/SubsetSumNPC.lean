import Pnp.Karp.SubArith
import Pnp.Karp.SubComb
import Pnp.Karp.SubNP
import Pnp.Karp.SubProg

/-!
# SUBSET SUM is NP-complete (official definitions, numbers in binary)

`SSLang` (`Pnp/Karp/SubsetSum.lean`: the first row of the word is the target, the other rows
are the items, all numbers written in binary) is NP-complete:

* `ss_in_np` (`Pnp/Karp/SubNP.lean`): SUBSET SUM ∈ NP (binary-addition verifier);
* `sat_iff_excov` (`Pnp/Karp/SubComb.lean`): a formula is satisfiable iff its exact-cover
  instance has an exact cover; `ss_iff_excov` (`Pnp/Karp/SubArith.lean`): exact cover iff the
  numbers (digits in base `2^b`, no carries by `cnt_lt`) have a subset summing to the target;
* `sat_le_ss_of` (`Pnp/Karp/SubProg.lean`): the reduction program;
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.SubsetSum

open Pnp.CookLevin

/-- The reduction is correct. -/
theorem sat_iff_ss (w : List SatSym) : SATLang w ↔ SSLang (SS w) :=
  (sat_iff_excov w).trans (ss_iff_excov w (cnt_lt w)).symm

/-- **SAT ≤ₚ SUBSET SUM** (official polynomial-time many-one reducibility). -/
theorem sat_le_ss :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang SSLang :=
  sat_le_ss_of sat_iff_ss

/-- **SUBSET SUM is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem ss_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) SSLang :=
  Pnp.Karp.np_complete_of_sat_reduces ss_in_np sat_le_ss

end Pnp.Karp.SubsetSum
