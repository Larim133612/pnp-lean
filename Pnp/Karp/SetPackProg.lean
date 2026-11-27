import Pnp.Karp.SetPacking
import Pnp.Karp.SetCoverProg

/-!
# The SET PACKING reduction program

The SET PACKING instance `SPI w` is the SET COVER instance `SCI w`, so the SET COVER reduction
program `sp_redCmd` (`Pnp/Karp/SetCoverProg.lean`, computability `sp_computable`) computes it.
-/

namespace Pnp.Karp.SetPacking

open Pnp.CookLevin Pnp.Karp.SetCover

/-- **SAT ≤ₚ SET PACKING** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `SPI`. -/
theorem sat_le_spk_of (h : ∀ w, SATLang w ↔ SPLang (SPI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang SPLang := by
  obtain ⟨hc⟩ := sp_computable
  exact ⟨SPI, hc, h⟩

end Pnp.Karp.SetPacking
