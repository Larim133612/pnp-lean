import Pnp.Karp.SubsetSumNPC
import Pnp.Karp.PartRed
import Pnp.Karp.PartNP
import Pnp.Karp.PartProg

/-!
# PARTITION is NP-complete (official definitions, numbers in binary)

`PartLang` (`Pnp/Karp/Partition.lean`: the rows of the word, binary numbers, can be split into
two parts with equal sums) is NP-complete:

* `part_in_np` (`Pnp/Karp/PartNP.lean`): PARTITION ∈ NP (verifier with two accumulators);
* `ss_iff_part` (`Pnp/Karp/PartRed.lean`): target `t`, items `as` with sum `S` ↦ items
  `as, S, 2t`;
* `ss_le_part_of` (`Pnp/Karp/PartProg.lean`): the reduction program (ripple-carry sum);
* SUBSET SUM is NP-complete (`ss_np_complete`, M41) and `Pnp.TM2Comp.npComplete_transfer`.
-/

namespace Pnp.Karp.Partition

open Pnp.CookLevin Pnp.Karp.SubsetSum

/-- **SUBSET SUM ≤ₚ PARTITION** (official polynomial-time many-one reducibility). -/
theorem ss_le_part :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SSLang PartLang :=
  ss_le_part_of ss_iff_part

/-- **PARTITION is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem part_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) PartLang :=
  Pnp.TM2Comp.npComplete_transfer _ _ _ _ ss_np_complete part_in_np ss_le_part

end Pnp.Karp.Partition
