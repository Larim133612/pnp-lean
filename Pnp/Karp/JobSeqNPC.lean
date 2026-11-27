import Pnp.Karp.SubsetSumNPC
import Pnp.Karp.JobSeqRed
import Pnp.Karp.JobSeqNP
import Pnp.Karp.JobSeqProg

/-!
# JOB SEQUENCING is NP-complete (official definitions, numbers in binary)

`JSLang` (`Pnp/Karp/JobSeq.lean`: jobs with execution times, deadlines and penalties can be
ordered on one machine so that the penalties of the late jobs total at most `K`) is
NP-complete:

* `js_in_np` (`Pnp/Karp/JobSeqNP.lean`): membership in NP (a verifier simulating the schedule
  given as a permutation);
* `ss_iff_js` (`Pnp/Karp/JobSeqRed.lean`): target `t`, items `as` with sum `S` ↦ bound `S`, jobs
  `(a, t, a)` and an always-late job `(1, 0, t)`;
* `ss_le_js_of` (`Pnp/Karp/JobSeqProg.lean`): the reduction program;
* SUBSET SUM is NP-complete (`ss_np_complete`, M41) and `Pnp.TM2Comp.npComplete_transfer`.
-/

namespace Pnp.Karp.JobSeq

open Pnp.CookLevin Pnp.Karp.SubsetSum

/-- **SUBSET SUM ≤ₚ JOB SEQUENCING** (official polynomial-time many-one reducibility). -/
theorem ss_le_js :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SSLang JSLang :=
  ss_le_js_of ss_iff_js

/-- **JOB SEQUENCING is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem js_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) JSLang :=
  Pnp.TM2Comp.npComplete_transfer _ _ _ _ ss_np_complete js_in_np ss_le_js

end Pnp.Karp.JobSeq
