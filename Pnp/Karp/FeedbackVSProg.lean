import Pnp.Karp.FeedbackVS

/-!
# The FEEDBACK VERTEX SET reduction

The instance `FVSI w = cmap (GV w)` is the VERTEX COVER instance, computed by the composition of
the VERTEX COVER reduction program (`VertexCover.GV_computable`) and the complement map
(`IndSet.cmap_computable`).
-/

namespace Pnp.Karp.FeedbackVS

open Pnp.CookLevin

/-- **SAT ≤ₚ FEEDBACK VERTEX SET** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `FVSI`. -/
theorem sat_le_fvs_of (h : ∀ w, SATLang w ↔ FVSLang (FVSI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang FVSLang := by
  obtain ⟨hG⟩ := VertexCover.GV_computable
  obtain ⟨hc⟩ := IndSet.cmap_computable
  exact ⟨IndSet.cmap ∘ VertexCover.GV, Pnp.TM2Comp.comp hG hc, h⟩

end Pnp.Karp.FeedbackVS
