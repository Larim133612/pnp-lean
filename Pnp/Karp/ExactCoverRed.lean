import Pnp.Karp.ExactCover
import Pnp.Karp.SetCoverRed
import Pnp.Karp.ThreeDMNPC

/-!
# EXACT COVER: correctness of the reduction and the reduction program

The X3C instance `X3I w` of a formula (`Pnp/Karp/ThreeDM.lean`) is also the EXACT COVER
instance: its rows are 3-element subsets of `[0, 3q)` (`SetCover.sr_rows`), so on `X3I w` the two
languages agree (`x3c_iff_ec`).  The X3C reduction program (`mg_computable 3`) computes `X3I`.
-/

namespace Pnp.Karp.ExactCover

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.ThreeDM

/-- On the reduction instances, X3C and EXACT COVER agree. -/
theorem x3c_iff_ec (w : List SatSym) : X3CLang (X3I w) ↔ ECLang (X3I w) := by
  refine ⟨x3c_imp_ec, ?_⟩
  rintro ⟨u, rs, hc, -, y, hy⟩
  have hc' := hc
  rw [X3I, dr_clauses] at hc'
  obtain ⟨rfl, rfl⟩ := List.cons.inj hc'
  refine ⟨_, _, hc, fun r hr => ?_, y, hy⟩
  rw [List.length_replicate]; exact SetCover.sr_rows w r hr

/-- SAT reduces to EXACT COVER on the instances `X3I w`. -/
theorem sat_iff_ec (w : List SatSym) : SATLang w ↔ ECLang (X3I w) :=
  (sat_iff_x3c w).trans (x3c_iff_ec w)

/-- **SAT ≤ₚ EXACT COVER** (official polynomial-time many-one reducibility). -/
theorem sat_le_ec :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang ECLang := by
  obtain ⟨hc⟩ := mg_computable 3 (by norm_num) X3I mg_X3I
  exact ⟨X3I, hc, sat_iff_ec⟩

end Pnp.Karp.ExactCover
