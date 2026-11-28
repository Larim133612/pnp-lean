import Pnp.Karp.ThreePartUProgG
import Pnp.Karp.ThreePartUProgEq

/-!
# The unary 3-PARTITION reduction program and SAT ≤ₚ unary 3-PARTITION

`TPUI w` is computed as the composition of the 3DM printer `DMI` (`mg_computable`,
`Pnp/Karp/ThreeDMProg.lean`) with the unary transformer `tpup_F`
(`tpup_F_computable`, `Pnp/Karp/ThreePartUProgG.lean`), which satisfies
`tpup_F (DMI w) = TPUI w` (`tpup_F_DMI`, `Pnp/Karp/ThreePartUProgEq.lean`).
-/

namespace Pnp.Karp.ThreePartU

open Pnp.CookLevin Pnp.Karp.ThreeDM

theorem sat_le_tpu_of (h : ∀ w, SATLang w ↔ TPULang (TPUI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang TPULang := by
  obtain ⟨hd⟩ := mg_computable 1 (by norm_num) DMI mg_DMI
  obtain ⟨ht⟩ := tpup_F_computable
  refine ⟨tpup_F ∘ DMI, Pnp.TM2Comp.comp hd ht, fun w => ?_⟩
  rw [Function.comp_apply, tpup_F_DMI]
  exact h w

end Pnp.Karp.ThreePartU
