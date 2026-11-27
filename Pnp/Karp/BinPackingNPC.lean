import Pnp.Karp.BinPackingRed
import Pnp.Karp.BinPackingProg
import Pnp.Karp.BinPackingNP
import Pnp.Karp.PartitionNPC

/-!
# BIN PACKING is NP-complete (official definitions)

`BPLang` (`Pnp/Karp/BinPacking.lean`: items and capacity in binary, number of bins in unary)
is NP-complete:

* `bp_in_np` (`Pnp/Karp/BinPackingNP.lean`): membership in NP;
* `part_iff_bp` (`Pnp/Karp/BinPackingRed.lean`): a PARTITION instance with total `T` is a
  yes-instance iff its items fit into two bins of capacity `⌊T / 2⌋`;
* `part_le_bp_of` (`Pnp/Karp/BinPackingProg.lean`): the reduction program;
* `Pnp.Karp.Partition.part_np_complete` (M42) and `Pnp.TM2Comp.npComplete_transfer`.
-/

namespace Pnp.Karp.BinPacking

open Pnp.CookLevin Pnp.Karp.Partition

/-- **PARTITION ≤ₚ BIN PACKING** (official polynomial-time many-one reducibility). -/
theorem part_le_bp :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) PartLang BPLang :=
  part_le_bp_of part_iff_bp

/-- **BIN PACKING is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem bp_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string SatSym) BPLang :=
  Pnp.TM2Comp.npComplete_transfer _ _ _ _ part_np_complete bp_in_np part_le_bp

end Pnp.Karp.BinPacking
