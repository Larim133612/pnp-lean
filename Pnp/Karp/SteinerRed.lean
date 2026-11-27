import Pnp.Karp.Steiner
import Pnp.Karp.SetCoverRed
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# STEINER TREE: the instance `STI w` is a yes-instance iff the X3C instance `X3I w` is

The work is done for arbitrary X3C data `(q, rs)` (rows of length `3q` with exactly three `pos`,
no `sep`) in `str_iff`, then specialized to the triple rows `triRows w` (`x3c_iff_st`).

* (⇒, `str_fwd`) An exact cover selects exactly `q` rows (double counting, `sr_sum_covC`).
  The edge set `F` joins each selected triple vertex `3q + 1 + i` to the root `3q` (`q`
  edges) and to its three elements (`3q` edges: each element lies in exactly one selected row,
  so `(a, p) ↦ p` is injective on these edges).  Every element reaches the root through its
  triple vertex.
* (⇐, `str_bwd`) Let `VS` be the vertices reachable from the root along `F`.  The graph on
  `VS` induced by `F` is connected, so `|VS| ≤ |F| + 1 ≤ 4q + 1` (`str_graph`, via Mathlib's
  `SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`).  `VS` contains the `3q + 1`
  terminals and the `t` reachable triple vertices, so `t ≤ q`.  Element and root rows are
  empty, so the first edge on the path from an element `p` to the root goes to a triple vertex
  whose row contains `p`; hence the `t ≤ q` reachable triples cover `[0, 3q)`, and by double
  counting every point is covered exactly once.
-/

namespace Pnp.Karp.Steiner

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.ThreeDM Pnp.Karp.SetCover

theorem str_len (q : ℕ) (rs : List (List SatSym)) :
    (stRows q rs).length = 3 * q + 1 + rs.length := by
  simp [stRows]

theorem str_row_lo (q : ℕ) (rs : List (List SatSym)) (a : ℕ) (ha : a ≤ 3 * q) :
    (stRows q rs).getD a [] = [] := by
  unfold stRows
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, ha]

theorem str_row_hi (q : ℕ) (rs : List (List SatSym)) (i : ℕ) (hi : i < rs.length) :
    (stRows q rs).getD (3 * q + 1 + i) [] = rs.getD i [] ++ [pos] := by
  unfold stRows
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem str_ent_lo (q : ℕ) (rs : List (List SatSym)) (a b : ℕ) (ha : a ≤ 3 * q) :
    ent (stRows q rs) a b = zero := by
  rw [ent, str_row_lo q rs a ha]; simp

theorem str_getD_app (r : List SatSym) (b : ℕ) :
    (r ++ [pos]).getD b zero = pos ↔ (b < r.length ∧ r.getD b zero = pos) ∨ b = r.length := by
  by_cases hb : b < r.length
  · rw [List.getD_append _ _ _ _ hb]; simp [hb]; omega
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    rcases Nat.lt_or_ge (b - r.length) 1 with h | h
    · have : b - r.length = 0 := by omega
      rw [this]; simp [hb]; omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      simp [hb]; omega

theorem str_ent_hi (q : ℕ) (rs : List (List SatSym))
    (hrs : ∀ r ∈ rs, r.length = 3 * q ∧ r.count pos = 3) (i b : ℕ) (hi : i < rs.length) :
    ent (stRows q rs) (3 * q + 1 + i) b = pos ↔
      (b < 3 * q ∧ (rs.getD i []).getD b zero = pos) ∨ b = 3 * q := by
  have hl := (hrs (rs.getD i []) (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _)).1
  rw [ent, str_row_hi q rs i hi, str_getD_app, hl]

theorem str_term (q : ℕ) (rs : List (List SatSym)) (t : ℕ) :
    IsTerm (List.replicate (3 * q + 1) pos) (stRows q rs) t ↔ t ≤ 3 * q := by
  unfold IsTerm
  rw [str_len, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  by_cases h : t < 3 * q + 1 <;> simp [h] <;> omega

theorem str_clauses (q : ℕ) (rs : List (List SatSym)) (hsep : ∀ r ∈ rs, sep ∉ r) :
    clauses (STW q rs) =
      List.replicate (4 * q) zero :: List.replicate (3 * q + 1) pos :: stRows q rs := by
  refine clauses_flatMap _ fun c hc => ?_
  simp only [stRows, List.mem_cons, List.mem_append, List.mem_map] at hc
  rcases hc with rfl | rfl | hc | ⟨r, hr, rfl⟩
  · simp [List.mem_replicate]
  · simp [List.mem_replicate]
  · rw [List.eq_of_mem_replicate hc]; simp
  · simpa using hsep r hr

theorem str_covC_sum : ∀ (rs : List (List SatSym)) (y : List Bool) (p : ℕ),
    covC rs y p = ∑ i ∈ Finset.range rs.length,
      if y.getD i false = true ∧ (rs.getD i []).getD p zero = pos then 1 else 0
  | [], _, _ => by simp [covC]
  | r :: rs, y, p => by
    rw [covC, List.length_cons, Finset.sum_range_succ', str_covC_sum rs y.tail p, add_comm]
    simp only [sr_getD_succ, List.getD_cons_succ, List.getD_cons_zero, sr_headD]
    congr 1
    by_cases h1 : y.getD 0 false = true <;> simp

theorem str_covC_uniq (rs : List (List SatSym)) (y : List Bool) (p : ℕ)
    (h : covC rs y p = 1) (i j : ℕ) (hi : i < rs.length) (hj : j < rs.length)
    (hi' : y.getD i false = true ∧ (rs.getD i []).getD p zero = pos)
    (hj' : y.getD j false = true ∧ (rs.getD j []).getD p zero = pos) : i = j := by
  rw [str_covC_sum, ← Finset.card_filter] at h
  exact Finset.card_le_one.1 h.le i (Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hi'⟩) j
    (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hj'⟩)

theorem str_rtg_symm (F : Finset (ℕ × ℕ)) {a b : ℕ}
    (h : Relation.ReflTransGen (adjF F) a b) : Relation.ReflTransGen (adjF F) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (Or.symm hbc) ih

theorem str_mem (rs : List (List SatSym)) (i : ℕ) (hi : i < rs.length) : rs.getD i [] ∈ rs := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

/-- (⇒): the selected triples, joined to the root and to their elements, connect all
terminals with `q + 3q` edges. -/
theorem str_fwd (q : ℕ) (rs : List (List SatSym))
    (hrs : ∀ r ∈ rs, r.length = 3 * q ∧ r.count pos = 3) (hsep : ∀ r ∈ rs, sep ∉ r)
    (y : List Bool) (hy : ∀ p < 3 * q, covC rs y p = 1) : STLang (STW q rs) := by
  classical
  let S := (Finset.range rs.length).filter (fun i => y.getD i false = true)
  have hS : S.card = q := by
    have hs := sr_sum_covC _ _ hrs y
    rw [Finset.sum_congr rfl (fun p hp => hy p (Finset.mem_range.1 hp))] at hs
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hs
    rw [Finset.card_filter, ← sr_sel]
    omega
  let A : Finset (ℕ × ℕ) := S.image (fun i => (3 * q + 1 + i, 3 * q))
  let B : Finset (ℕ × ℕ) :=
    ((S ×ˢ Finset.range (3 * q)).filter (fun x => (rs.getD x.1 []).getD x.2 zero = pos)).image
      (fun x => (3 * q + 1 + x.1, x.2))
  have hA : A.card ≤ q := hS ▸ Finset.card_image_le
  have hB : B.card ≤ 3 * q := by
    rw [← Finset.card_range (3 * q)]
    refine Finset.card_le_card_of_injOn (fun e => e.2) ?_ ?_
    · intro e he
      simp only [B, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_product] at he
      obtain ⟨x, ⟨⟨_, hx⟩, _⟩, rfl⟩ := he
      simpa using hx
    · intro e1 he1 e2 he2 h12
      simp only [B, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_product, S, Finset.mem_range] at he1 he2
      obtain ⟨⟨i, p⟩, ⟨⟨⟨hi, hyi⟩, hp⟩, hip⟩, rfl⟩ := he1
      obtain ⟨⟨j, p'⟩, ⟨⟨⟨hj, hyj⟩, hp'⟩, hjp⟩, rfl⟩ := he2
      simp only at h12 hip hjp hp hp' ⊢
      subst h12
      have := str_covC_uniq rs y p (hy p hp) i j hi hj ⟨hyi, hip⟩ ⟨hyj, hjp⟩
      subst this; rfl
  have hroot : ∀ a, a ≤ 3 * q → Relation.ReflTransGen (adjF (A ∪ B)) a (3 * q) := by
    intro a ha
    rcases Nat.lt_or_ge a (3 * q) with ha' | ha'
    · obtain ⟨i, hi, h2, h3⟩ := (sr_covC_pos rs y a).1 (by rw [hy a ha'])
      have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, h2⟩
      have e1 : adjF (A ∪ B) a (3 * q + 1 + i) := Or.inr (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨(i, a), Finset.mem_filter.2
          ⟨Finset.mem_product.2 ⟨hiS, Finset.mem_range.2 ha'⟩, h3⟩, rfl⟩))
      have e2 : adjF (A ∪ B) (3 * q + 1 + i) (3 * q) :=
        Or.inl (Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, hiS, rfl⟩))
      exact Relation.ReflTransGen.head e1 (Relation.ReflTransGen.single e2)
    · have : a = 3 * q := by omega
      subst this; exact .refl
  refine ⟨_, _, _, str_clauses q rs hsep, A ∪ B, ?_, ?_, ?_⟩
  · rw [List.length_replicate]
    have := Finset.card_union_le A B
    omega
  · intro e he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
      have hi' : i < rs.length := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
      refine ⟨by rw [str_len]; omega, by rw [str_len]; omega, by simp only; omega, ?_⟩
      exact (str_ent_hi q rs hrs i _ hi').2 (Or.inr rfl)
    · obtain ⟨⟨i, p⟩, hx, rfl⟩ := Finset.mem_image.1 he
      simp only [Finset.mem_filter, Finset.mem_product, S, Finset.mem_range] at hx
      obtain ⟨⟨⟨hi, _⟩, hp⟩, hip⟩ := hx
      refine ⟨by rw [str_len]; simp only; omega, by rw [str_len]; simp only; omega,
        by simp only; omega, ?_⟩
      exact (str_ent_hi q rs hrs i _ hi).2 (Or.inl ⟨hp, hip⟩)
  · intro a b ha hb
    rw [str_term] at ha hb
    exact (hroot a ha).trans (str_rtg_symm _ (hroot b hb))

open Classical in
/-- A connected graph has at most one vertex more than it has edges: the vertices `< n`
reachable from `r` along `F` number at most `|F| + 1`. -/
theorem str_graph (F : Finset (ℕ × ℕ)) (n r : ℕ) (hr : r < n)
    (hF : ∀ e ∈ F, e.1 < n ∧ e.2 < n) :
    ((Finset.range n).filter (fun v => Relation.ReflTransGen (adjF F) r v)).card ≤
      F.card + 1 := by
  set VS := (Finset.range n).filter (fun v => Relation.ReflTransGen (adjF F) r v) with hVS
  have hrV : r ∈ VS := Finset.mem_filter.2 ⟨Finset.mem_range.2 hr, .refl⟩
  let G : SimpleGraph VS := SimpleGraph.fromRel (fun u v => (u.1, v.1) ∈ F)
  have hreach : ∀ v, Relation.ReflTransGen (adjF F) r v → ∀ hv : v ∈ VS,
      G.Reachable ⟨r, hrV⟩ ⟨v, hv⟩ := by
    intro v h
    induction h with
    | refl => intro _; rfl
    | @tail b c hab hbc ih =>
      intro hc
      have hb : b ∈ VS := by
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hab⟩
        rcases hbc with h | h
        · exact (hF _ h).1
        · exact (hF _ h).2
      by_cases hne : b = c
      · subst hne; exact ih hb
      · refine (ih hb).trans (SimpleGraph.Adj.reachable ?_)
        rw [SimpleGraph.fromRel_adj]
        exact ⟨fun h => hne (congrArg Subtype.val h), hbc⟩
  have hconn : G.Connected := by
    haveI : Nonempty VS := ⟨⟨r, hrV⟩⟩
    refine { preconnected := fun u v => ?_ }
    exact (hreach u.1 (Finset.mem_filter.1 u.2).2 u.2).symm.trans
      (hreach v.1 (Finset.mem_filter.1 v.2).2 v.2)
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_finsetCard] at h1
  have h2 : Nat.card G.edgeSet ≤ F.card := by
    let D := {e : F // e.1.1 ∈ VS ∧ e.1.2 ∈ VS ∧ e.1.1 ≠ e.1.2}
    let f : D → G.edgeSet := fun d => ⟨s(⟨d.1.1.1, d.2.1⟩, ⟨d.1.1.2, d.2.2.1⟩), by
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
      exact ⟨fun h => d.2.2.2 (congrArg Subtype.val h), Or.inl d.1.2⟩⟩
    have hf : Function.Surjective f := by
      rintro ⟨z, hz⟩
      induction z using Sym2.ind with
      | h u v =>
        rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at hz
        obtain ⟨hne, h | h⟩ := hz
        · exact ⟨⟨⟨(u.1, v.1), h⟩, u.2, v.2, fun h' => hne (Subtype.ext h')⟩, rfl⟩
        · refine ⟨⟨⟨(v.1, u.1), h⟩, v.2, u.2, fun h' => hne (Subtype.ext h'.symm)⟩, ?_⟩
          exact Subtype.ext Sym2.eq_swap
    calc Nat.card G.edgeSet ≤ Nat.card D := Nat.card_le_card_of_surjective f hf
      _ ≤ Nat.card F := Finite.card_subtype_le _
      _ = F.card := Nat.card_eq_finsetCard F
  omega

open Classical in
/-- (⇐): the triple vertices reachable from the root number at most `q` and cover every
element, so they form an exact cover. -/
theorem str_bwd (q : ℕ) (rs : List (List SatSym))
    (hrs : ∀ r ∈ rs, r.length = 3 * q ∧ r.count pos = 3) (hsep : ∀ r ∈ rs, sep ∉ r)
    (h : STLang (STW q rs)) : ∃ y : List Bool, ∀ p < 3 * q, covC rs y p = 1 := by
  obtain ⟨kr, tr, rows, hc, F, hF, hE, hT⟩ := h
  rw [str_clauses q rs hsep] at hc
  obtain ⟨rfl, hc'⟩ := List.cons.inj hc
  obtain ⟨rfl, rfl⟩ := List.cons.inj hc'
  rw [List.length_replicate] at hF
  set n := 3 * q + 1 + rs.length with hn
  set VS := (Finset.range n).filter (fun v => Relation.ReflTransGen (adjF F) (3 * q) v)
    with hVS
  have hFn : ∀ e ∈ F, e.1 < n ∧ e.2 < n := by
    intro e he
    obtain ⟨h1, h2, -⟩ := hE e he
    rw [str_len] at h1 h2
    exact ⟨h1, h2⟩
  have hG : VS.card ≤ F.card + 1 := str_graph F n (3 * q) (by omega) hFn
  have hterm : ∀ t, t ≤ 3 * q → t ∈ VS := by
    intro t ht
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
    exact hT _ _ ((str_term q rs _).2 le_rfl) ((str_term q rs _).2 ht)
  have helem : ∀ p < 3 * q, ∃ i < rs.length,
      (rs.getD i []).getD p zero = pos ∧ 3 * q + 1 + i ∈ VS := by
    intro p hp
    have hpr := hT _ _ ((str_term q rs p).2 hp.le) ((str_term q rs _).2 le_rfl)
    rcases Relation.ReflTransGen.cases_head hpr with h | ⟨c, hpc, hcr⟩
    · omega
    rcases hpc with h | h
    · have := (hE _ h).2.2.2
      rw [str_ent_lo q rs _ _ hp.le] at this
      cases this
    · obtain ⟨hc1, -, hne, hent⟩ := hE _ h
      simp only at hc1 hne hent
      rw [str_len] at hc1
      by_cases hc3 : c ≤ 3 * q
      · rw [str_ent_lo q rs _ _ hc3] at hent; cases hent
      obtain ⟨i, rfl⟩ : ∃ i, c = 3 * q + 1 + i := ⟨c - (3 * q + 1), by omega⟩
      have hi : i < rs.length := by omega
      rcases (str_ent_hi q rs hrs i p hi).1 hent with ⟨-, h2⟩ | h2
      · exact ⟨i, hi, h2, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
          str_rtg_symm _ hcr⟩⟩
      · omega
  set U := (Finset.range rs.length).filter (fun i => 3 * q + 1 + i ∈ VS) with hU
  have hUq : U.card ≤ q := by
    have hsub : Finset.range (3 * q + 1) ∪ U.image (fun i => 3 * q + 1 + i) ⊆ VS := by
      intro v hv
      rcases Finset.mem_union.1 hv with hv | hv
      · exact hterm v (by simpa [Nat.lt_succ_iff] using hv)
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
        exact (Finset.mem_filter.1 hi).2
    have hdis : Disjoint (Finset.range (3 * q + 1)) (U.image (fun i => 3 * q + 1 + i)) := by
      rw [Finset.disjoint_left]
      intro v hv hv'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv'
      simp at hv; omega
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, Finset.card_range,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)] at this
    omega
  let y : List Bool := (List.range rs.length).map (fun i => decide (i ∈ U))
  have hy : ∀ i < rs.length, y.getD i false = decide (i ∈ U) := by
    intro i hi
    simp [y, List.getD_eq_getElem?_getD, hi]
  refine ⟨y, ?_⟩
  have hge : ∀ p ∈ Finset.range (3 * q), 1 ≤ covC rs y p := by
    intro p hp
    obtain ⟨i, hi, h1, h2⟩ := helem p (Finset.mem_range.1 hp)
    have hiU : i ∈ U := Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, h2⟩
    exact (sr_covC_pos _ y p).2 ⟨i, hi, by rw [hy i hi]; simpa using hiU, h1⟩
  have hsel : sr_sel y rs.length ≤ q := by
    have : sr_sel y rs.length = U.card := by
      rw [sr_sel, ← Finset.card_filter]
      congr 1
      have hUe : U = (Finset.range rs.length).filter (fun i => 3 * q + 1 + i ∈ VS) := hU
      rw [hUe]
      apply Finset.filter_congr
      intro i hi
      rw [hy i (Finset.mem_range.1 hi), decide_eq_true_iff, hUe, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩
    omega
  have hs := sr_sum_covC _ _ hrs y
  have heq := (Finset.sum_eq_sum_iff_of_le hge).1 (by
    have hle := Finset.sum_le_sum hge
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hle ⊢; omega)
  intro p hp
  exact (heq p (Finset.mem_range.2 hp)).symm

/-- The reduction for arbitrary X3C data: rows of length `3q` with three `pos` each have an
exact cover of `[0, 3q)` iff the Steiner instance `STW q rs` is a yes-instance. -/
theorem str_iff (q : ℕ) (rs : List (List SatSym))
    (hrs : ∀ r ∈ rs, r.length = 3 * q ∧ r.count pos = 3) (hsep : ∀ r ∈ rs, sep ∉ r) :
    (∃ y : List Bool, ∀ p < 3 * q, covC rs y p = 1) ↔ STLang (STW q rs) :=
  ⟨fun ⟨y, hy⟩ => str_fwd q rs hrs hsep y hy, str_bwd q rs hrs hsep⟩

theorem str_sep (w : List SatSym) : ∀ r ∈ triRows w, sep ∉ r := by
  intro r hr
  simp only [triRows, List.mem_map] at hr
  obtain ⟨t, _, rfl⟩ := hr
  exact dr_sep_triRow _ _

/-- **X3C ≤ STEINER TREE** on the reduction instances: `X3I w` has an exact cover iff `STI w`
has a Steiner tree with at most `4q` edges. -/
theorem x3c_iff_st (w : List SatSym) : X3CLang (X3I w) ↔ STLang (STI w) := by
  rw [STI, ← str_iff _ _ (sr_rows w) (str_sep w)]
  constructor
  · rintro ⟨u, rs, hc, -, y, hy⟩
    rw [X3I, dr_clauses] at hc
    obtain ⟨rfl, rfl⟩ := List.cons.inj hc
    exact ⟨y, fun p hp => hy p (by simpa using hp)⟩
  · rintro ⟨y, hy⟩
    refine ⟨_, _, by rw [X3I, dr_clauses], fun r hr => ?_, y, fun p hp => hy p (by simpa using hp)⟩
    rw [List.length_replicate]; exact sr_rows w r hr

end Pnp.Karp.Steiner
