import Pnp.Karp.DHPath
import Pnp.Karp.DHamProg

/-!
# DIRECTED HAMILTONIAN PATH: the reduction program

The symmetrization program `dp_redCmd` (`Pnp/Karp/DHamProg.lean`) computes `symG`; here it is
used for the reduction UNDIRECTED → DIRECTED HAMILTONIAN PATH.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-- **HAMILTONIAN PATH ≤ₚ DIRECTED HAMILTONIAN PATH** (official polynomial-time many-one
reducibility), given the correctness of the reduction instance `symG`. -/
theorem uhpath_le_dhpath_of (h : ∀ w, UHPathLang w ↔ DHPathLang (symG w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) UHPathLang DHPathLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    dp_redCmd 0 15 (fun x => symG (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := dp_exec_redCmd x
      exact ⟨σ', h1.mono (dp_Tred_le _), h2⟩)
    symG (fun t => (congrArg symG (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨symG, hc, h⟩

end Pnp.Karp.Ham
