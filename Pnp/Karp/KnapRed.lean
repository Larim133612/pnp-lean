import Pnp.Karp.Knapsack

/-!
# KNAPSACK: correctness of the reduction from SUBSET SUM

`ss_iff_knap`: a SUBSET SUM instance `w` (target `t`, items `as`) is a yes-instance iff its
KNAPSACK instance `KI w` (capacity `t`, goal `t`, items `(a, a)`) is one.
-/

namespace Pnp.Karp.Knapsack

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum

theorem kr_pairs_dup : ∀ as : List (List SatSym),
    pairs (as.flatMap fun r => [r, r]) = as.map fun r => (r, r)
  | [] => rfl
  | r :: as => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons]
    rw [pairs, kr_pairs_dup as]

/-- **Correctness of the reduction** SUBSET SUM → KNAPSACK. -/
theorem ss_iff_knap (w : List SatSym) : SSLang w ↔ KnapLang (KI w) := by
  unfold SSLang KnapLang KI
  rcases hw : clauses w with _ | ⟨t, as⟩
  · constructor
    · rintro ⟨_, _, h, _⟩; exact absurd h (by simp)
    · rintro ⟨W, V, items, h, y, -, hV⟩
      have e : clauses [sep, pos, sep] = [[], [pos]] := rfl
      rw [e] at h
      injection h with h1 h2; injection h2 with h2 h3
      subst h1; subst h2; subst h3
      simp [pairs, selSum, bv] at hV
  · have hsep : ∀ c ∈ t :: t :: as.flatMap (fun r => [r, r]), sep ∉ c := by
      have hm : ∀ c ∈ t :: as, sep ∉ c := fun c hc => sep_not_mem_clauses w c (hw ▸ hc)
      intro c hc
      simp only [List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | ⟨r, hr, rfl | rfl⟩
      · exact hm _ (by simp)
      · exact hm _ (by simp)
      · exact hm _ (by simp [hr])
      · exact hm _ (by simp [hr])
    rw [Pnp.Karp.Clique.clauses_flatMap _ hsep]
    have hm : ∀ as' : List (List SatSym), ∀ f : List SatSym × List SatSym → List SatSym,
        (∀ r, f (r, r) = r) → (pairs (as'.flatMap fun r => [r, r])).map f = as' := by
      intro as' f hf
      rw [kr_pairs_dup, List.map_map]
      conv_rhs => rw [← List.map_id as']
      exact List.map_congr_left fun r _ => hf r
    constructor
    · rintro ⟨t', as', h, y, hy⟩
      injection h with h1 h2; subst h1; subst h2
      refine ⟨t, t, _, rfl, y, ?_, ?_⟩
      · rw [hm _ _ fun _ => rfl]; exact hy.le
      · rw [hm _ _ fun _ => rfl]; exact hy.ge
    · rintro ⟨W, V, items, h, y, h1, h2⟩
      injection h with e1 h; injection h with e2 e3
      subst e1; subst e2; subst e3
      rw [hm _ _ fun _ => rfl] at h1 h2
      exact ⟨t, as, rfl, y, le_antisymm h1 h2⟩

end Pnp.Karp.Knapsack
