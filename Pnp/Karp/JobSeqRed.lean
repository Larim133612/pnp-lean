import Pnp.Karp.JobSeq
import Pnp.Karp.PartRed

/-!
# JOB SEQUENCING: correctness of the reduction from SUBSET SUM

`ss_iff_js`: a SUBSET SUM instance `w` (target `t`, items `as`, sum `S`) is a yes-instance iff
its JOB SEQUENCING instance `JI w` (bound `S`, jobs `(a, t, a)` for the items and `(1, 0, t)`)
is one.

* (⇒) For a selection summing to `t`, run the selected items first (they all finish by `t`),
  then the other items, then the last job: the penalty is at most `(S - t) + t = S`.
* (⇐) The last job is always late (penalty `t`).  The on-time jobs `O` (`jsr_on`) are items;
  their penalties sum to at least `t` (the penalty is `≤ S`) and their times to at most `t`
  (`jsr_on_T_le`), so the items in `O` sum to exactly `t`.
-/

namespace Pnp.Karp.JobSeq

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.Partition

/-! ## Schedules in general -/

/-- The jobs of `π` that finish by their deadline when the run starts at time `s`. -/
def jsr_on (js : List (List SatSym)) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | s, j :: π =>
      if s + jT js j ≤ jD js j then j :: jsr_on js (s + jT js j) π else jsr_on js (s + jT js j) π

theorem jsr_pen_add_on (js : List (List SatSym)) : ∀ (s : ℕ) (π : List ℕ),
    latePen js s π + ((jsr_on js s π).map (jP js)).sum = (π.map (jP js)).sum
  | _, [] => rfl
  | s, j :: π => by
    have ih := jsr_pen_add_on js (s + jT js j) π
    simp only [latePen, jsr_on, List.map_cons, List.sum_cons]
    split_ifs <;> (try simp only [List.map_cons, List.sum_cons]) <;> omega

theorem jsr_on_T_le (js : List (List SatSym)) (τ : ℕ) : ∀ (s : ℕ) (π : List ℕ),
    (∀ j ∈ π, jD js j ≤ τ) →
    ((jsr_on js s π).map (jT js)).sum = 0 ∨ s + ((jsr_on js s π).map (jT js)).sum ≤ τ
  | _, [], _ => Or.inl rfl
  | s, j :: π, h => by
    have ih := jsr_on_T_le js τ (s + jT js j) π (fun i hi => h i (List.mem_cons_of_mem _ hi))
    have hj := h j (by simp)
    simp only [jsr_on]
    split_ifs
    · simp only [List.map_cons, List.sum_cons]; omega
    · omega

theorem jsr_on_sub (js : List (List SatSym)) : ∀ (s : ℕ) (π : List ℕ), (jsr_on js s π).Sublist π
  | _, [] => List.Sublist.slnil
  | s, j :: π => by
    simp only [jsr_on]; split_ifs
    · exact (jsr_on_sub js _ π).cons_cons j
    · exact (jsr_on_sub js _ π).cons j

theorem jsr_on_ok (js : List (List SatSym)) : ∀ (s : ℕ) (π : List ℕ),
    ∀ j ∈ jsr_on js s π, jT js j ≤ jD js j
  | _, [] => by simp [jsr_on]
  | s, i :: π => by
    intro j hj
    simp only [jsr_on] at hj; split_ifs at hj with h
    · rcases List.mem_cons.1 hj with rfl | hj
      · omega
      · exact jsr_on_ok js _ π j hj
    · exact jsr_on_ok js _ π j hj

theorem jsr_pen_append (js : List (List SatSym)) : ∀ (s : ℕ) (π₁ π₂ : List ℕ),
    latePen js s (π₁ ++ π₂) = latePen js s π₁ + latePen js (s + (π₁.map (jT js)).sum) π₂
  | s, [], π₂ => by simp [latePen]
  | s, j :: π₁, π₂ => by
    simp only [List.cons_append, latePen, List.map_cons, List.sum_cons,
      jsr_pen_append js (s + jT js j) π₁ π₂, Nat.add_assoc]

theorem jsr_pen_zero (js : List (List SatSym)) (τ : ℕ) : ∀ (s : ℕ) (π : List ℕ),
    (∀ j ∈ π, jD js j = τ) → s + (π.map (jT js)).sum ≤ τ → latePen js s π = 0
  | _, [], _, _ => rfl
  | s, j :: π, h, hs => by
    have hj := h j (by simp)
    simp only [List.map_cons, List.sum_cons] at hs
    simp only [latePen]
    rw [jsr_pen_zero js τ (s + jT js j) π (fun i hi => h i (List.mem_cons_of_mem _ hi))
      (by omega)]
    split_ifs <;> omega

/-! ## Sums over lists -/

theorem jsr_sum_filter (f : ℕ → ℕ) (p : ℕ → Bool) : ∀ l : List ℕ,
    ((l.filter p).map f).sum = (l.map fun i => if p i then f i else 0).sum
  | [] => rfl
  | i :: l => by
    have ih := jsr_sum_filter f p l
    rw [List.filter_cons]; cases h : p i <;> simp [h, ih]

theorem jsr_sum_split (f : ℕ → ℕ) (p : ℕ → Bool) : ∀ l : List ℕ,
    ((l.filter p).map f).sum + ((l.filter fun i => !p i).map f).sum = (l.map f).sum
  | [] => rfl
  | i :: l => by
    have ih := jsr_sum_split f p l
    rw [List.filter_cons, List.filter_cons]; cases p i <;> simp <;> omega

theorem jsr_sel_eq : ∀ (L : List (List SatSym)) (y : List Bool),
    selSum L y = ((List.range L.length).map fun i =>
      if y.getD i false then bv (L.getD i []) else 0).sum
  | [], _ => rfl
  | r :: L, y => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      selSum, jsr_sel_eq L y.tail]
    cases y <;> simp [Function.comp_def]

theorem jsr_tot_eq : ∀ L : List (List SatSym),
    totSum L = ((List.range L.length).map fun i => bv (L.getD i [])).sum
  | [] => rfl
  | r :: L => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      totSum, jsr_tot_eq L]
    simp [Function.comp_def]

/-! ## The two directions, for abstract jobs -/

theorem jsr_bwd (js : List (List SatSym)) (n τ : ℕ) (a : ℕ → ℕ)
    (hT : ∀ j < n, jT js j = a j) (hD : ∀ j < n, jD js j = τ) (hP : ∀ j < n, jP js j = a j)
    (hTn : jT js n = 1) (hDn : jD js n = 0) (hPn : jP js n = τ)
    (π : List ℕ) (hπ : π.Perm (List.range (n + 1)))
    (hpen : latePen js 0 π ≤ ((List.range n).map a).sum) :
    ∃ y : List Bool, ((List.range n).map fun i => if y.getD i false then a i else 0).sum = τ := by
  set O := jsr_on js 0 π with hO
  have hmem : ∀ j ∈ π, j < n + 1 := fun j hj => List.mem_range.1 (hπ.subset hj)
  have hOn : ∀ j ∈ O, j < n := by
    intro j hj
    have h1 := hmem j ((jsr_on_sub js 0 π).subset hj)
    have h2 := jsr_on_ok js 0 π j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | rfl
    · exact h
    · rw [hTn, hDn] at h2; omega
  have hsum := jsr_pen_add_on js 0 π
  have hPπ : (π.map (jP js)).sum = ((List.range n).map a).sum + τ := by
    rw [(hπ.map _).sum_eq, List.range_succ, List.map_append, List.sum_append,
      List.map_congr_left (fun j hj => hP j (List.mem_range.1 hj))]
    simp [hPn]
  have hle := jsr_on_T_le js τ 0 π (by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 (hmem j hj) with h | rfl
    · exact (hD j h).le
    · rw [hDn]; omega)
  have hTO : (O.map (jT js)).sum = (O.map a).sum :=
    congrArg List.sum (List.map_congr_left fun j hj => hT j (hOn j hj))
  have hPO : (O.map (jP js)).sum = (O.map a).sum :=
    congrArg List.sum (List.map_congr_left fun j hj => hP j (hOn j hj))
  rw [← hO] at hsum hle
  have hOa : (O.map a).sum = τ := by omega
  refine ⟨(List.range n).map fun i => decide (i ∈ O), ?_⟩
  have hnd : O.Nodup := (jsr_on_sub js 0 π).nodup (hπ.nodup_iff.2 List.nodup_range)
  have hperm : ((List.range n).filter fun i => decide (i ∈ O)).Perm O := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnd]
    intro i
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hOn i h, h⟩⟩
  have hc : ∀ i ∈ List.range n,
      (if ((List.range n).map fun i => decide (i ∈ O)).getD i false then a i else 0) =
        (if decide (i ∈ O) then a i else 0) := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (List.mem_range.1 hi)]
    rfl
  rw [List.map_congr_left hc, ← jsr_sum_filter, (hperm.map a).sum_eq, hOa]

theorem jsr_fwd (js : List (List SatSym)) (n τ : ℕ) (a : ℕ → ℕ)
    (hT : ∀ j < n, jT js j = a j) (hD : ∀ j < n, jD js j = τ) (hP : ∀ j < n, jP js j = a j)
    (hPn : jP js n = τ) (y : List Bool)
    (hy : ((List.range n).map fun i => if y.getD i false then a i else 0).sum = τ) :
    ∃ π : List ℕ, π.Perm (List.range (n + 1)) ∧ latePen js 0 π ≤ ((List.range n).map a).sum := by
  let p : ℕ → Bool := fun i => y.getD i false
  refine ⟨(List.range n).filter p ++ ((List.range n).filter fun i => !p i) ++ [n], ?_, ?_⟩
  · rw [List.range_succ]; exact (List.filter_append_perm p _).append_right [n]
  · rw [List.append_assoc, jsr_pen_append]
    have hsel : (((List.range n).filter p).map a).sum = τ := by rw [jsr_sum_filter]; exact hy
    have hmF : ∀ j ∈ (List.range n).filter p, j < n :=
      fun j hj => List.mem_range.1 (List.mem_filter.1 hj).1
    have hTF : (((List.range n).filter p).map (jT js)).sum = τ := by
      rw [List.map_congr_left fun j hj => hT j (hmF j hj)]; exact hsel
    have h0 : latePen js 0 ((List.range n).filter p) = 0 :=
      jsr_pen_zero js τ 0 _ (fun j hj => hD j (hmF j hj)) (by omega)
    have hup := jsr_pen_add_on js (0 + (((List.range n).filter p).map (jT js)).sum)
      (((List.range n).filter fun i => !p i) ++ [n])
    have hU : ((((List.range n).filter fun i => !p i) ++ [n]).map (jP js)).sum =
        (((List.range n).filter fun i => !p i).map a).sum + τ := by
      rw [List.map_append, List.sum_append, List.map_congr_left fun j hj =>
        hP j (List.mem_range.1 (List.mem_filter.1 hj).1)]
      simp [hPn]
    have hsp := jsr_sum_split a p (List.range n)
    omega

/-! ## The instance -/

theorem jsr_getD_lt (t : List SatSym) (tl : List (List SatSym)) :
    ∀ (as : List (List SatSym)) (j k : ℕ), j < as.length → k < 3 →
    ((as.flatMap fun a => [a, t, a]) ++ tl).getD (3 * j + k) [] =
      [as.getD j [], t, as.getD j []].getD k []
  | [], _, _, h, _ => absurd h (by simp)
  | r :: as, 0, k, _, hk => by
    interval_cases k <;> simp
  | r :: as, j + 1, k, h, hk => by
    have ih := jsr_getD_lt t tl as j k (by simpa using h) hk
    rw [show 3 * (j + 1) + k = 3 * j + k + 1 + 1 + 1 by ring]
    simpa [List.flatMap_cons, List.append_assoc] using ih

theorem jsr_getD_len (t : List SatSym) (tl : List (List SatSym)) :
    ∀ (as : List (List SatSym)) (k : ℕ),
    ((as.flatMap fun a => [a, t, a]) ++ tl).getD (3 * as.length + k) [] = tl.getD k []
  | [], k => by simp
  | r :: as, k => by
    have ih := jsr_getD_len t tl as k
    rw [List.length_cons, show 3 * (as.length + 1) + k = 3 * as.length + k + 1 + 1 + 1 by ring]
    simpa [List.flatMap_cons, List.append_assoc] using ih

theorem jsr_len (t : List SatSym) (tl : List (List SatSym)) :
    ∀ as : List (List SatSym),
    ((as.flatMap fun a => [a, t, a]) ++ tl).length = 3 * as.length + tl.length
  | [] => by simp
  | r :: as => by
    have ih := jsr_len t tl as
    simp only [List.flatMap_cons, List.append_assoc, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

/-- **Correctness of the reduction** SUBSET SUM → JOB SEQUENCING. -/
theorem ss_iff_js (w : List SatSym) : SSLang w ↔ JSLang (JI w) := by
  unfold SSLang JSLang JI
  rcases hw : clauses w with _ | ⟨t, as⟩
  · constructor
    · rintro ⟨_, _, h, _⟩; exact absurd h (by simp)
    · rintro ⟨K, js, h, π, hπ, hpen⟩
      have e : clauses (([[], [pos], [], [pos]] : List (List SatSym)).flatMap (· ++ [sep])) =
          [[], [pos], [], [pos]] := Pnp.Karp.Clique.clauses_flatMap _ (by decide)
      rw [e] at h
      injection h with h1 h2; subst h1; subst h2
      have : π = [0] := List.perm_singleton.1 hπ
      subst this
      simp [latePen, jT, jD, jP, bv] at hpen
  · have hm : ∀ c ∈ t :: as, sep ∉ c := fun c hc => sep_not_mem_clauses w c (hw ▸ hc)
    have hsep : ∀ c ∈ (toRow (accRows [] as) :: (as.flatMap fun a => [a, t, a])) ++
        [[pos], [], t], sep ∉ c := by
      intro c hc
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | ⟨r, hr, rfl | rfl | rfl⟩ | rfl | rfl | rfl
      · exact pr_sep_toRow _
      · exact hm _ (by simp [hr])
      · exact hm _ (by simp)
      · exact hm _ (by simp [hr])
      · decide
      · decide
      · exact hm _ (by simp)
    rw [Pnp.Karp.Clique.clauses_flatMap _ hsep, List.cons_append]
    have hS : bv (toRow (accRows [] as)) = totSum as := by
      rw [pr_bv_toRow, pr_bval_acc]; simp [sv_bval]
    set js := (as.flatMap fun a => [a, t, a]) ++ [[pos], [], t] with hjs
    have hlen : js.length / 3 = as.length + 1 := by
      rw [hjs, jsr_len]; simp only [List.length_cons, List.length_nil]; omega
    have hT : ∀ j < as.length, jT js j = bv (as.getD j []) := fun j hj => by
      have := jsr_getD_lt t [[pos], [], t] as j 0 hj (by omega)
      simp only [Nat.add_zero] at this
      show bv (js.getD (3 * j) []) = _
      rw [hjs, this]; rfl
    have hD : ∀ j < as.length, jD js j = bv t := fun j hj => by
      have := jsr_getD_lt t [[pos], [], t] as j 1 hj (by omega)
      show bv (js.getD (3 * j + 1) []) = _
      rw [hjs, this]; rfl
    have hP : ∀ j < as.length, jP js j = bv (as.getD j []) := fun j hj => by
      have := jsr_getD_lt t [[pos], [], t] as j 2 hj (by omega)
      show bv (js.getD (3 * j + 2) []) = _
      rw [hjs, this]; rfl
    have hTn : jT js as.length = 1 := by
      have := jsr_getD_len t [[pos], [], t] as 0
      simp only [Nat.add_zero] at this
      show bv (js.getD (3 * as.length) []) = _
      rw [hjs, this]; simp [bv]
    have hDn : jD js as.length = 0 := by
      have := jsr_getD_len t [[pos], [], t] as 1
      show bv (js.getD (3 * as.length + 1) []) = _
      rw [hjs, this]; rfl
    have hPn : jP js as.length = bv t := by
      have := jsr_getD_len t [[pos], [], t] as 2
      show bv (js.getD (3 * as.length + 2) []) = _
      rw [hjs, this]; rfl
    constructor
    · rintro ⟨t', as', h, y, hy⟩
      injection h with h1 h2; subst h1; subst h2
      rw [jsr_sel_eq] at hy
      obtain ⟨π, hπ, hpen⟩ := jsr_fwd js as.length (bv t) _ hT hD hP hPn y hy
      refine ⟨_, _, rfl, π, hlen ▸ hπ, ?_⟩
      rw [hS, jsr_tot_eq]; exact hpen
    · rintro ⟨K, js', h, π, hπ, hpen⟩
      injection h with h1 h2; subst h1; subst h2
      rw [hlen] at hπ
      rw [hS, jsr_tot_eq] at hpen
      obtain ⟨y, hy⟩ := jsr_bwd js as.length (bv t) _ hT hD hP hTn hDn hPn π hπ hpen
      exact ⟨t, as, rfl, y, by rw [jsr_sel_eq]; exact hy⟩

end Pnp.Karp.JobSeq
