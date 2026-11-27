import Pnp.Karp.ColorNP
import Pnp.Karp.ColorRed
import Pnp.Karp.ColorProg

/-!
# 3-COLORING is NP-complete (official definitions)

`ColLang` (`Pnp/Karp/Color.lean`: a word over `SatSym` whose rows are an adjacency matrix; it is
in the language iff the graph has a proper coloring with 3 colors) is NP-complete:

* `col_in_np` (`Pnp/Karp/ColorNP.lean`): 3-COLORING ∈ NP;
* `sat_iff_col` (`Pnp/Karp/ColorRed.lean`) and `sat_le_col_of` (`Pnp/Karp/ColorProg.lean`):
  SAT ≤ₚ 3-COLORING (OR-gadget reduction);
* `Pnp.Karp.np_complete_of_sat_reduces` (`Pnp/Karp/Basic.lean`, using Cook–Levin).
-/

namespace Pnp.Karp.Color

/-- **SAT ≤ₚ 3-COLORING** (official polynomial-time many-one reducibility). -/
theorem sat_le_col :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string Pnp.CookLevin.SatSym)
      (Millennium.fin_encoding_string Pnp.CookLevin.SatSym) Pnp.CookLevin.SATLang ColLang :=
  sat_le_col_of sat_iff_col

/-- **3-COLORING is NP-complete** for the official definitions
(`Millennium.NondeterministicPolynomialTimeComplete`). -/
theorem col_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete
      (Millennium.fin_encoding_string Pnp.CookLevin.SatSym) ColLang :=
  Pnp.Karp.np_complete_of_sat_reduces col_in_np sat_le_col

end Pnp.Karp.Color
