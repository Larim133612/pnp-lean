import Pnp.Karp.Tsp

/-!
# TRAVELING SALESMAN: correctness of the reduction from HAMILTONIAN CYCLE

`uham_iff_tsp`: `w ∈ UHamLang ↔ tspI w ∈ TSPLang`.  The rows of `tspI w` are the empty budget
row and the rows `tRow w u`; the weight of the step `u → v` is `0` on an edge and `1` otherwise
(`tr_wt`), so a tour has cost `≤ 0` iff all its steps are edges, i.e. it is a Hamiltonian cycle.
-/

namespace Pnp.Karp.Tsp

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.Ham Pnp.Karp.SubsetSum

theorem tr_wchunk_app (c r : List SatSym) (hc : neg ∉ c) :
    ∀ j, wchunk (c ++ neg :: r) j = if j = 0 then c else wchunk r (j - 1) := by
  induction c with
  | nil => intro j; cases j <;> simp [wchunk]
  | cons s c ih =>
    intro j
    have hs : s ≠ neg := fun h => hc (h ▸ List.mem_cons_self)
    have hc' : neg ∉ c := fun h => hc (List.mem_cons_of_mem _ h)
    cases j with
    | zero => simp [wchunk, hs, ih hc' 0]
    | succ j => simp [wchunk, hs, ih hc' (j + 1)]

theorem tr_wchunk_flat : ∀ (cs : List (List SatSym)), (∀ c ∈ cs, neg ∉ c) →
    ∀ j, wchunk (cs.flatMap (· ++ [neg])) j = cs.getD j []
  | [], _, j => by cases j <;> simp [wchunk]
  | c :: cs, h, j => by
    rw [List.flatMap_cons, List.append_assoc, List.singleton_append,
      tr_wchunk_app c _ (h c List.mem_cons_self)]
    cases j with
    | zero => simp
    | succ j =>
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, List.getD_cons_succ]
      exact tr_wchunk_flat cs (fun c hc => h c (List.mem_cons_of_mem _ hc)) j

theorem tr_neg_tEnt (w : List SatSym) (u v : ℕ) : neg ∉ tEnt w u v := by
  unfold tEnt; split_ifs <;> simp

theorem tr_sep_tRow (w : List SatSym) (u : ℕ) : sep ∉ tRow w u := by
  simp only [tRow, List.mem_flatMap, List.mem_range, not_exists, not_and]
  intro v _; unfold tEnt; split_ifs <;> simp

theorem tr_clauses (w : List SatSym) :
    clauses (tspI w) = [] :: (List.range (clauses w).length).map (tRow w) := by
  refine clauses_flatMap _ fun c hc => ?_
  rcases List.mem_cons.1 hc with rfl | hc
  · simp
  · obtain ⟨u, -, rfl⟩ := List.mem_map.1 hc
    exact tr_sep_tRow w u

theorem tr_wt (w : List SatSym) {u v : ℕ} (hu : u < (clauses w).length)
    (hv : v < (clauses w).length) :
    wt ((List.range (clauses w).length).map (tRow w)) u v =
      if ent w u v = pos ∨ ent w v u = pos then 0 else 1 := by
  unfold wt
  rw [List.getD_eq_getElem _ _ (by simpa using hu), List.getElem_map, List.getElem_range]
  have e : tRow w u = ((List.range (clauses w).length).map (tEnt w u)).flatMap (· ++ [neg]) := by
    rw [tRow, List.flatMap_map]
  rw [e, tr_wchunk_flat _ (by
      intro c hc; obtain ⟨v, -, rfl⟩ := List.mem_map.1 hc; exact tr_neg_tEnt w u v),
    List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map, List.getElem_range]
  unfold tEnt
  split_ifs <;> simp [bv]

theorem tr_getD_lt {n : ℕ} {σ : List ℕ} (hp : σ.Perm (List.range n)) (i : ℕ) (hi : i < σ.length) :
    σ.getD i 0 < n := by
  apply List.mem_range.1
  refine hp.subset ?_
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

theorem tr_sum_zero (f : ℕ → ℕ) (k : ℕ) :
    ((List.range k).map f).sum ≤ 0 ↔ ∀ i < k, f i = 0 := by
  rw [Nat.le_zero, List.sum_eq_zero_iff]
  simp

/-- **Correctness of the reduction** HAMILTONIAN CYCLE → TSP. -/
theorem uham_iff_tsp (w : List SatSym) : UHamLang w ↔ TSPLang (tspI w) := by
  unfold UHamLang TSPLang IsHamCycle
  rw [tr_clauses]
  constructor
  · rintro ⟨h3, σ, hp, hc⟩
    refine ⟨[], _, rfl, by simpa using h3, σ, by simpa using hp, ?_⟩
    unfold tourCost
    rw [show bv [] = 0 from rfl, tr_sum_zero]
    intro i hi
    have hlen : σ.length = (clauses w).length := by simpa using hp.length_eq
    rw [tr_wt w (tr_getD_lt hp i hi) (tr_getD_lt hp _ (Nat.mod_lt _ (by omega))),
      if_pos (by simpa [adjU] using hc i hi)]
  · rintro ⟨Bd, M, he, h3, σ, hp, hc⟩
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    rw [List.length_map, List.length_range] at h3 hp
    refine ⟨h3, σ, hp, fun i hi => ?_⟩
    have hlen : σ.length = (clauses w).length := by simpa using hp.length_eq
    unfold tourCost at hc
    rw [show bv [] = 0 from rfl, tr_sum_zero] at hc
    have := hc i hi
    rw [tr_wt w (tr_getD_lt hp i hi) (tr_getD_lt hp _ (Nat.mod_lt _ (by omega)))] at this
    by_contra hn
    exact absurd this (by unfold adjU at hn; rw [if_neg hn]; omega)

end Pnp.Karp.Tsp
