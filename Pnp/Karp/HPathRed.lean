import Pnp.Karp.HPath
import Pnp.Karp.HamFwd

/-!
# HAMILTONIAN PATH: correctness of the reduction from HAMILTONIAN CYCLE

`uham_iff_uhpath`: `w ∈ UHamLang ↔ hpI w ∈ UHPathLang`.

Paths and cycles are handled as chains (`List.IsChain`).  A Hamiltonian cycle of `w`, rotated
to start at `0` as `0 :: l`, gives the path `n + 1, 0 :: l, n, n + 2` of `hpI w`.  Conversely,
the pendant vertices `n + 1`, `n + 2` of `hpI w` have a single neighbour each, so they are the
endpoints of every Hamiltonian path, which (reversed if needed) reads `n + 1, 0 :: l, n, n + 2`.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Generic lemmas on chains -/

theorem hr_path_chain {n : ℕ} {adj : ℕ → ℕ → Prop} {σ : List ℕ} :
    IsHamPath n adj σ ↔ σ.Perm (List.range n) ∧ σ.IsChain adj := by
  unfold IsHamPath
  refine and_congr_right fun _ => ?_
  rw [List.isChain_iff_getElem]
  refine forall_congr' fun i => ⟨fun h hi => ?_, fun h hi => ?_⟩
  · have := h hi
    rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi] at this
  · rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]; exact h hi

theorem hr_chain_of_cycle {n : ℕ} {adj : ℕ → ℕ → Prop} {σ : List ℕ} (h : IsHamCycle n adj σ) :
    (σ ++ σ.take 1).IsChain adj := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hl : (σ ++ σ.take 1).length = σ.length + min 1 σ.length := by simp
  have hi' : i < σ.length := by omega
  have h0 : 0 < σ.length := by omega
  have hc := h.2 i hi'
  rw [List.getD_eq_getElem _ _ hi', List.getElem_append_left hi'] at *
  rcases Nat.lt_or_ge (i + 1) σ.length with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, List.getD_eq_getElem _ _ h1] at hc
    rwa [List.getElem_append_left h1]
  · have he : i + 1 = σ.length := by omega
    rw [he, Nat.mod_self, List.getD_eq_getElem _ _ h0] at hc
    rw [List.getElem_append_right (by omega)]
    simpa [he] using hc

theorem hr_rot {R : ℕ → ℕ → Prop} {σ : List ℕ} {x : ℕ} (hx : x ∈ σ)
    (hc : (σ ++ σ.take 1).IsChain R) : ∃ l, (x :: l).Perm σ ∧ (x :: l ++ [x]).IsChain R := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hx
  rcases s with _ | ⟨a, s⟩
  · exact ⟨t, List.Perm.refl _, by simpa using hc⟩
  · refine ⟨t ++ a :: s, ?_, ?_⟩
    · simpa using (List.perm_append_comm (l₁ := x :: t) (l₂ := a :: s))
    · have e1 : a :: s ++ x :: t ++ (a :: s ++ x :: t).take 1 = (a :: s) ++ x :: (t ++ [a]) := by
        simp
      rw [e1, List.isChain_split] at hc
      have e2 : x :: (t ++ a :: s) ++ [x] = (x :: t) ++ a :: (s ++ [x]) := by simp
      rw [e2, List.isChain_split]
      exact ⟨by simpa using hc.2, by simpa using hc.1⟩

theorem hr_end {R : ℕ → ℕ → Prop} {s t : List ℕ} {x c : ℕ}
    (hn : (s ++ x :: t).Nodup) (hc : (s ++ x :: t).IsChain R)
    (hR : ∀ y, R y x ∨ R x y → y = c) : s = [] ∨ t = [] := by
  by_contra hne
  push Not at hne
  obtain ⟨hs, ht⟩ := hne
  obtain ⟨s', y, rfl⟩ : ∃ s' y, s = s' ++ [y] := by
    rcases List.eq_nil_or_concat s with h | ⟨s', y, h⟩
    · exact absurd h hs
    · exact ⟨s', y, by simpa using h⟩
  obtain ⟨z, t', rfl⟩ := List.exists_cons_of_ne_nil ht
  have e : s' ++ [y] ++ x :: z :: t' = s' ++ y :: x :: z :: t' := by simp
  rw [e] at hc hn
  have hc' := (List.isChain_split.1 hc).2
  rw [List.isChain_cons_cons, List.isChain_cons_cons] at hc'
  have hy := hR y (Or.inl hc'.1)
  have hz := hR z (Or.inr hc'.2.1)
  rw [List.nodup_append] at hn
  simp at hn
  omega

theorem hr_transfer {P : ℕ → Prop} {A B : ℕ → ℕ → Prop} (hAB : ∀ u v, P u → P v → A u v → B u v)
    {L : List ℕ} (hL : ∀ x ∈ L, P x) (h : L.IsChain A) : L.IsChain B := by
  rw [List.IsChain.iff_mem] at h
  exact h.imp fun a b hab => hAB a b (hL a hab.1) (hL b hab.2.1) hab.2.2

/-! ## The abstract reduction -/

section Abstract

variable {n : ℕ} {A B : ℕ → ℕ → Prop}
  (hB : ∀ u v, B u v → B v u) (hA : ∀ u v, A u v → A v u)
  (h1 : ∀ v, B (n + 1) v ↔ v = 0) (h2 : ∀ v, B v (n + 2) ↔ v = n)
  (h3 : ∀ u v, u < n → v < n → (B u v ↔ A u v)) (h4 : ∀ z, z < n → (B z n ↔ 1 ≤ z ∧ A 0 z))

include h1 h2 h3 h4 hA in
theorem hr_fwd (hn : 3 ≤ n) {l : List ℕ} (hp : (0 :: l).Perm (List.range n))
    (hc : (0 :: l ++ [0]).IsChain A) :
    IsHamPath (n + 3) B ((n + 1) :: 0 :: l ++ [n, n + 2]) := by
  have hlen := hp.length_eq
  simp only [List.length_cons, List.length_range] at hlen
  have hlt : ∀ x ∈ 0 :: l, x < n := fun x hx => List.mem_range.1 (hp.subset hx)
  rw [hr_path_chain]
  refine ⟨hf_perm_range (fun x hx => ?_) (by simp; omega), ?_⟩
  · rcases Nat.lt_or_ge x n with h | h
    · have := hp.symm.subset (List.mem_range.2 h)
      simp only [List.mem_cons] at this
      simp only [List.cons_append, List.mem_cons, List.mem_append]
      tauto
    · simp; omega
  obtain ⟨l', z, rfl⟩ : ∃ l' z, l = l' ++ [z] := by
    rcases List.eq_nil_or_concat l with h | ⟨l', z, h⟩
    · subst h; simp at hlen; omega
    · exact ⟨l', z, by simpa using h⟩
  have hnd := hp.nodup_iff.2 List.nodup_range
  have hz0 : z ≠ 0 := by
    intro h; subst h; simp at hnd
  have e1 : 0 :: (l' ++ [z]) ++ [0] = (0 :: l') ++ z :: [0] := by simp
  rw [e1, List.isChain_split] at hc
  have hAz : A z 0 := by simpa using hc.2
  have e2 : (n + 1) :: 0 :: (l' ++ [z]) ++ [n, n + 2] = (n + 1) :: ((0 :: l') ++ z :: [n, n + 2]) := by
    simp
  rw [e2]
  have hzn : z < n := hlt z (by simp)
  rcases l' with _ | ⟨b, l'⟩
  · simp at hlen; omega
  · rw [List.cons_append, List.isChain_cons_cons]
    refine ⟨(h1 0).2 rfl, ?_⟩
    rw [← List.cons_append, List.isChain_split]
    refine ⟨hr_transfer (P := (· < n)) (fun u v hu hv h => (h3 u v hu hv).2 h) hlt hc.1, ?_⟩
    simp only [List.isChain_cons_cons]
    exact ⟨(h4 z hzn).2 ⟨by omega, hA _ _ hAz⟩, (h2 n).2 rfl, List.IsChain.singleton _⟩

include hB h1 in
theorem hr_head {P : List ℕ} (hP : IsHamPath (n + 3) B P) :
    ∃ t, IsHamPath (n + 3) B ((n + 1) :: t) := by
  rw [hr_path_chain] at hP
  simp only [hr_path_chain]
  obtain ⟨hp, hc⟩ := hP
  have hnd := hp.nodup_iff.2 List.nodup_range
  obtain ⟨s, t, rfl⟩ :=
    List.append_of_mem (hp.symm.subset (List.mem_range.2 (by omega : n + 1 < n + 3)))
  rcases hr_end hnd hc (fun y hy => (h1 y).1 (hy.elim (hB _ _) id)) with rfl | rfl
  · exact ⟨t, by simpa using hp, by simpa using hc⟩
  · refine ⟨s.reverse, ?_, ?_⟩
    · have := (List.reverse_perm (s ++ [n + 1])).trans hp
      simpa using this
    · have : ((s ++ [n + 1]).reverse).IsChain B :=
        List.isChain_reverse.2 (hc.imp fun a b h => hB _ _ h)
      simpa using this

include hB hA h1 h2 h3 h4 in
theorem hr_bwd (hn : 3 ≤ n) {P : List ℕ} (hP : IsHamPath (n + 3) B P) :
    ∃ σ, IsHamCycle n A σ := by
  obtain ⟨t, ht⟩ := hr_head hB h1 hP
  rw [hr_path_chain] at ht
  obtain ⟨hp, hc⟩ := ht
  have hnd := hp.nodup_iff.2 List.nodup_range
  have hm : n + 2 ∈ t := by
    have := hp.symm.subset (List.mem_range.2 (by omega : n + 2 < n + 3))
    simpa using this
  obtain ⟨s, t', rfl⟩ := List.append_of_mem hm
  have hc' : ((n + 1) :: s ++ (n + 2) :: t').IsChain B := by simpa using hc
  have hnd' : ((n + 1) :: s ++ (n + 2) :: t').Nodup := by simpa using hnd
  rcases hr_end hnd' hc' (fun y hy => (h2 y).1 (hy.elim id (hB _ _))) with h | rfl
  · simp at h
  have hlen := hp.length_eq
  simp at hlen
  obtain ⟨q, r, rfl⟩ := List.exists_cons_of_ne_nil (show s ≠ [] by rintro rfl; simp at hlen)
  obtain ⟨l, e, rfl⟩ : ∃ l e, r = l ++ [e] := by
    rcases List.eq_nil_or_concat r with h | ⟨l, e, h⟩
    · subst h; simp at hlen; omega
    · exact ⟨l, e, by simpa using h⟩
  have E : (n + 1) :: (q :: (l ++ [e]) ++ [n + 2]) = (n + 1) :: q :: (l ++ e :: [n + 2]) := by
    simp
  rw [E] at hc hp hnd
  rw [List.isChain_cons_cons] at hc
  obtain ⟨hq, hc⟩ := hc
  rw [h1] at hq
  subst hq
  rw [← List.cons_append, List.isChain_split] at hc
  have he : e = n := (h2 e).1 (by simpa using hc.2)
  subst e
  simp at hlen
  have hlt : ∀ x ∈ 0 :: l, x < n := by
    intro x hx
    have hx3 : x < n + 3 := List.mem_range.1 (hp.subset (by simp at hx ⊢; tauto))
    simp [List.nodup_append] at hnd
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have := hnd.2.2.2 x hx
      have : x ≠ n + 1 := fun h => hnd.1 (h ▸ hx)
      omega
  refine ⟨0 :: l, hf_ham_of_chain (hf_perm_range (fun x hx => ?_) (by simp; omega)) ?_⟩
  · have := hp.symm.subset (List.mem_range.2 (by omega : x < n + 3))
    simp only [List.mem_cons, List.mem_append] at this ⊢
    rcases this with h | h | h | h | h | h <;>
      first | omega | exact Or.inr h | exact Or.inl h | simp at h
  obtain ⟨L, z, hL⟩ : ∃ L z, 0 :: l = L ++ [z] := by
    rcases List.eq_nil_or_concat (0 :: l) with h | ⟨L, z, h⟩
    · simp at h
    · exact ⟨L, z, by simpa using h⟩
  have hzn : z < n := hlt z (by rw [hL]; simp)
  rw [List.take_succ_cons, List.take_zero, hL]
  have hc1 := hc.1
  rw [hL, List.append_assoc, List.singleton_append, List.isChain_split] at hc1
  rw [List.append_assoc, List.singleton_append, List.isChain_split]
  refine ⟨hr_transfer (P := (· < n)) (fun u v hu hv h => (h3 u v hu hv).1 h)
    (by rw [← hL]; exact hlt) hc1.1, ?_⟩
  have hzn' : B z n := by simpa using hc1.2
  have := ((h4 z hzn).1 hzn').2
  simpa using hA _ _ this

end Abstract

/-! ## The adjacency of `hpI w` -/

theorem hr_path_iff {n : ℕ} {A B : ℕ → ℕ → Prop} (hAB : ∀ u < n, ∀ v < n, A u v ↔ B u v)
    (σ : List ℕ) : IsHamPath n A σ ↔ IsHamPath n B σ := by
  simp only [hr_path_chain]
  refine and_congr_right fun hp => ?_
  have hlt : ∀ x ∈ σ, x < n := fun x hx => List.mem_range.1 (hp.subset hx)
  exact ⟨hr_transfer (P := (· < n)) (fun u v hu hv h => (hAB u hu v hv).1 h) hlt,
    hr_transfer (P := (· < n)) (fun u v hu hv h => (hAB u hu v hv).2 h) hlt⟩

/-- The (symmetrized) adjacency of `hpI w`. -/
def hr_B (w : List SatSym) (u v : ℕ) : Prop := hpE w u v = true ∨ hpE w v u = true

theorem hr_sep_hpRow (w : List SatSym) (u : ℕ) : sep ∉ hpRow w u := by
  simp only [hpRow, List.mem_map, List.mem_range, not_exists, not_and]
  intro v _; split_ifs <;> simp

theorem hr_clauses (w : List SatSym) (h : 3 ≤ (clauses w).length) :
    clauses (hpI w) = (List.range ((clauses w).length + 3)).map (hpRow w) := by
  unfold hpI
  rw [if_neg (by omega)]
  refine clauses_flatMap _ fun c hc => ?_
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hc
  exact hr_sep_hpRow w u

theorem hr_length (w : List SatSym) (h : 3 ≤ (clauses w).length) :
    (clauses (hpI w)).length = (clauses w).length + 3 := by
  rw [hr_clauses w h]; simp

theorem hr_ent (w : List SatSym) (h : 3 ≤ (clauses w).length) {u v : ℕ}
    (hu : u < (clauses w).length + 3) (hv : v < (clauses w).length + 3) :
    ent (hpI w) u v = if hpE w u v then pos else zero := by
  have e : (clauses (hpI w)).getD u [] = hpRow w u := by
    rw [hr_clauses w h, List.getD_eq_getElem _ _ (by simpa using hu)]; simp
  unfold ent
  rw [e]
  unfold hpRow
  rw [List.getD_eq_getElem _ _ (by simpa using hv)]
  simp

theorem hr_adj (w : List SatSym) (h : 3 ≤ (clauses w).length) {u v : ℕ}
    (hu : u < (clauses w).length + 3) (hv : v < (clauses w).length + 3) :
    adjU (hpI w) u v ↔ hr_B w u v := by
  unfold adjU hr_B
  rw [hr_ent w h hu hv, hr_ent w h hv hu]
  cases hpE w u v <;> cases hpE w v u <;> simp

theorem hr_B_symm (w : List SatSym) (u v : ℕ) : hr_B w u v → hr_B w v u := Or.symm

theorem hr_B_n1 (w : List SatSym) (v : ℕ) : hr_B w ((clauses w).length + 1) v ↔ v = 0 := by
  unfold hr_B hpE
  simp only
  split_ifs <;> simp_all

theorem hr_B_n2 (w : List SatSym) (v : ℕ) : hr_B w v ((clauses w).length + 2) ↔ v = (clauses w).length := by
  unfold hr_B hpE
  simp only
  split_ifs <;> simp_all

theorem hr_B_lt (w : List SatSym) {u v : ℕ} (hu : u < (clauses w).length)
    (hv : v < (clauses w).length) : hr_B w u v ↔ adjU w u v := by
  unfold hr_B hpE adjU
  simp only [hu, hv, and_self, if_true, decide_eq_true_eq]
  tauto

theorem hr_B_n (w : List SatSym) {z : ℕ} (hz : z < (clauses w).length) :
    hr_B w z (clauses w).length ↔ 1 ≤ z ∧ adjU w 0 z := by
  unfold hr_B hpE adjU
  simp only [lt_irrefl, and_false, false_and, if_false, hz, and_self, if_true,
    decide_eq_true_eq, Nat.ne_of_lt hz]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

/-! ## Small graphs -/

theorem hr_small (w : List SatSym) (h : ¬ 3 ≤ (clauses w).length) : ¬ UHPathLang (hpI w) := by
  unfold UHPathLang hpI
  rw [if_pos (by omega)]
  rintro ⟨σ, hσ⟩
  have hc : clauses [sep, sep] = [[], []] := rfl
  have he : ∀ u v, ¬ adjU [sep, sep] u v := by
    have : ∀ u v, ent [sep, sep] u v = zero := by
      intro u v
      unfold ent
      rw [hc]
      rcases u with _ | _ | u <;> simp
    intro u v hu
    unfold adjU at hu
    rw [this, this] at hu
    simp at hu
  rw [hc, hr_path_chain] at hσ
  obtain ⟨hp, hch⟩ := hσ
  have hl := hp.length_eq
  match σ, hl, hch with
  | [a, b], _, hch => exact he a b (List.isChain_pair.1 hch)

/-! ## Correctness -/

/-- **Correctness of the reduction** HAMILTONIAN CYCLE → HAMILTONIAN PATH. -/
theorem uham_iff_uhpath (w : List SatSym) : UHamLang w ↔ UHPathLang (hpI w) := by
  by_cases h : 3 ≤ (clauses w).length
  · have hAB : ∀ u < (clauses w).length + 3, ∀ v < (clauses w).length + 3,
        adjU (hpI w) u v ↔ hr_B w u v := fun u hu v hv => hr_adj w h hu hv
    have hA : ∀ u v, adjU w u v → adjU w v u := fun _ _ => Or.symm
    unfold UHamLang UHPathLang
    rw [hr_length w h]
    simp only [h, true_and, hr_path_iff hAB]
    constructor
    · rintro ⟨σ, hσ⟩
      have h0 : 0 ∈ σ := hσ.1.symm.subset (List.mem_range.2 (by omega))
      obtain ⟨l, hl, hc⟩ := hr_rot h0 (hr_chain_of_cycle hσ)
      exact ⟨_, hr_fwd hA (hr_B_n1 w) (hr_B_n2 w) (fun u v hu hv => hr_B_lt w hu hv)
        (fun z hz => hr_B_n w hz) h (hl.trans hσ.1) hc⟩
    · rintro ⟨P, hP⟩
      exact hr_bwd (hr_B_symm w) hA (hr_B_n1 w) (hr_B_n2 w) (fun u v hu hv => hr_B_lt w hu hv)
        (fun z hz => hr_B_n w hz) h hP
  · exact iff_of_false (fun hw => h hw.1) (hr_small w h)

end Pnp.Karp.Ham
