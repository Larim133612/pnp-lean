import Pnp.Karp.SubsetSumNPC
import Pnp.Karp.KnapRed
import Pnp.Karp.KnapNP
import Pnp.Karp.KnapProg

/-!
# KNAPSACK (0-1, decision version) is NP-complete (official definitions, numbers in binary)

`KnapLang` (`Pnp/Karp/Knapsack.lean`: capacity `W`, value goal `V`, items (weight, value);
some selection has total weight `≤ W` and total value `≥ V`) is NP-complete:

* `knap_in_np` (`Pnp/Karp/KnapNP.lean`): KNAPSACK ∈ NP (two accumulators and comparisons);
* `ss_iff_knap` (`Pnp/Karp/KnapRed.lean`): target `t`, items `as` ↦ `W = V = t`, items `(a, a)`;
* `ss_le_knap_of` (`Pnp/Karp/KnapProg.lean`): the reduction program (row duplication);
* SUBSET SUM is NP-complete (`ss_np_complete`, M41) and `Pnp.TM2Comp.npComplete_transfer`.
-/

namespace Pnp.Karp.Knapsack

open Pnp.CookLevin Pnp.Karp.SubsetSum

/-- **SUBSET SUM ≤ₚ KNAPSACK** (official polynomial-time many-one reducibility). -/
theorem ss_le_knap :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SSLang KnapLang :=
  ss_le_knap_of ss_iff_knap

/-- **KNAPSACK is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem knap_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) KnapLang :=
  Pnp.TM2Comp.npComplete_transfer _ _ _ _ ss_np_complete knap_in_np ss_le_knap

end Pnp.Karp.Knapsack
