import Pnp.Karp.DHPath
import Pnp.Karp.DHamRed

/-!
# DIRECTED HAMILTONIAN PATH: correctness of the reduction from the undirected version

`uhpath_iff_dhpath`: `w ∈ UHPathLang ↔ symG w ∈ DHPathLang`.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin SatSym Pnp.Karp.Clique

theorem dpr_path_iff {n : ℕ} {A B : ℕ → ℕ → Prop} (hAB : ∀ u < n, ∀ v < n, A u v ↔ B u v)
    (σ : List ℕ) : IsHamPath n A σ ↔ IsHamPath n B σ := by
  unfold IsHamPath
  refine and_congr_right fun hp => forall_congr' fun i => imp_congr_right fun hi => hAB _ ?_ _ ?_
  all_goals
    apply List.mem_range.1
    refine hp.subset ?_
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _

/-- **Correctness of the reduction** UNDIRECTED → DIRECTED HAMILTONIAN PATH. -/
theorem uhpath_iff_dhpath (w : List SatSym) : UHPathLang w ↔ DHPathLang (symG w) := by
  unfold UHPathLang DHPathLang
  rw [dr_length]
  refine exists_congr fun σ => (dpr_path_iff ?_ σ).symm
  intro u hu v hv; exact dr_ent w hu hv

end Pnp.Karp.Ham
