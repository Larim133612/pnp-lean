import Pnp.Karp.DHam

/-!
# DIRECTED HAMILTONIAN CYCLE: correctness of the reduction from the undirected version

`uham_iff_dham`: `w ∈ UHamLang ↔ symG w ∈ DHamLang`.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin SatSym Pnp.Karp.Clique

theorem dr_sep_symRow (w : List SatSym) (u : ℕ) : sep ∉ symRow w u := by
  simp only [symRow, List.mem_map, List.mem_range, not_exists, not_and]
  intro v _; split_ifs <;> simp

theorem dr_clauses_symG (w : List SatSym) :
    clauses (symG w) = (List.range (clauses w).length).map (symRow w) := by
  refine clauses_flatMap _ fun c hc => ?_
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hc
  exact dr_sep_symRow w u

theorem dr_length (w : List SatSym) : (clauses (symG w)).length = (clauses w).length := by
  rw [dr_clauses_symG]; simp

theorem dr_ent (w : List SatSym) {u v : ℕ} (hu : u < (clauses w).length)
    (hv : v < (clauses w).length) : adjD (symG w) u v ↔ adjU w u v := by
  have e : (clauses (symG w)).getD u [] = symRow w u := by
    rw [dr_clauses_symG, List.getD_eq_getElem _ _ (by simpa using hu)]; simp
  have e2 : (symRow w u).getD v zero =
      if ent w u v = pos ∨ ent w v u = pos then pos else zero := by
    unfold symRow; rw [List.getD_eq_getElem _ _ (by simpa using hv)]; simp
  unfold adjD adjU
  rw [show ent (symG w) u v = (symRow w u).getD v zero by unfold ent; rw [e], e2]
  split_ifs with h <;> simp [h]

theorem dr_cycle_iff {n : ℕ} {A B : ℕ → ℕ → Prop} (hAB : ∀ u < n, ∀ v < n, A u v ↔ B u v)
    (σ : List ℕ) : IsHamCycle n A σ ↔ IsHamCycle n B σ := by
  unfold IsHamCycle
  refine and_congr_right fun hp => forall_congr' fun i => imp_congr_right fun hi => hAB _ ?_ _ ?_
  all_goals
    apply List.mem_range.1
    refine hp.subset ?_
    rw [List.getD_eq_getElem _ _ (by
      first | exact hi | exact Nat.mod_lt _ (by omega))]
    exact List.getElem_mem _

/-- **Correctness of the reduction** UNDIRECTED → DIRECTED HAMILTONIAN CYCLE. -/
theorem uham_iff_dham (w : List SatSym) : UHamLang w ↔ DHamLang (symG w) := by
  unfold UHamLang DHamLang
  rw [dr_length]
  refine and_congr_right fun _ => exists_congr fun σ => (dr_cycle_iff ?_ σ).symm
  intro u hu v hv; exact dr_ent w hu hv

end Pnp.Karp.Ham
