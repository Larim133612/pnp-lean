import Pnp.Karp.Clique

/-!
# The reduction SAT ≤ CLIQUE: the graph and its correctness

For a dense CNF formula `w` (see `Pnp/CookLevin/SAT.lean`) with finished clauses
`c₀, …, c_{m-1}` we build the CLIQUE instance `G w` (encoding: `Pnp/Karp/Clique.lean`).

* The positions of `trunc w` (the finished clauses, each followed by `sep`) are annotated by
  `ann`: position `p` gets `(symbol, clause index, index inside the clause)`; call this list `A`.
* Vertices: `0` is a universal vertex `u`; vertex `p + 1` is position `p` of `trunc w`.
* Edges: `u — p+1` iff position `p` holds a literal (`pos`/`neg`); `p+1 — q+1` iff both positions
  hold literals, lie in different clauses, and are not contradictory (same variable index with
  opposite signs) (`adjB`).  Positions holding `zero` or `sep` are isolated vertices.
* The clique bound is `k = m + 1`.

`sat_iff_clique : SATLang w ↔ CliqueLang (G w)`: a satisfying assignment gives `u` plus one true
literal per clause; conversely, for `m ≥ 1` a clique of size `≥ m + 1` has `≥ m` literal vertices,
in pairwise distinct clauses (an injection into the `m` clauses), hence one in each clause, and
they are pairwise consistent, which defines a satisfying assignment.
-/

namespace Pnp.Karp.Clique

open Function Pnp.CookLevin SatSym

/-! ## The graph -/

/-- Annotate each position with `(symbol, clause index, index inside the clause)`. -/
def ann : List SatSym → ℕ → ℕ → List (SatSym × ℕ × ℕ)
  | [], _, _ => []
  | sep :: r, t, j => (sep, t, j) :: ann r (t + 1) 0
  | zero :: r, t, j => (zero, t, j) :: ann r t (j + 1)
  | pos :: r, t, j => (pos, t, j) :: ann r t (j + 1)
  | neg :: r, t, j => (neg, t, j) :: ann r t (j + 1)

/-- Literal symbols. -/
def isLit : SatSym → Bool
  | pos => true
  | neg => true
  | _ => false

/-- Adjacency of two annotated positions. -/
def adjB (a b : SatSym × ℕ × ℕ) : Bool :=
  isLit a.1 && isLit b.1 && a.2.1 != b.2.1 && !(a.2.2 == b.2.2 && a.1 != b.1)

/-- Matrix entry. -/
def ent (x : Bool) : SatSym := if x then pos else zero

/-- Row of the universal vertex. -/
def litRow (A : List (SatSym × ℕ × ℕ)) : List SatSym := zero :: A.map fun b => ent (isLit b.1)

/-- Row of the vertex of position `a`. -/
def vRow (A : List (SatSym × ℕ × ℕ)) (a : SatSym × ℕ × ℕ) : List SatSym :=
  ent (isLit a.1) :: A.map fun b => ent (adjB a b)

/-- The annotated positions of `trunc w`. -/
def annW (w : List SatSym) : List (SatSym × ℕ × ℕ) := ann (trunc w) 0 0

/-- The adjacency matrix rows. -/
def gRows (w : List SatSym) : List (List SatSym) := litRow (annW w) :: (annW w).map (vRow (annW w))

/-- The row encoding `k = m + 1`. -/
def kRow (w : List SatSym) : List SatSym := List.replicate ((clauses w).length + 1) zero

/-- The CLIQUE instance of the formula `w`. -/
def G (w : List SatSym) : List SatSym := (kRow w :: gRows w).flatMap (· ++ [sep])

/-! ## Rows of `G w` -/

theorem clausesAux_app : ∀ (c r cur : List SatSym), sep ∉ c →
    clausesAux (c ++ sep :: r) cur = (cur.reverse ++ c) :: clausesAux r []
  | [], r, cur, _ => by simp [clausesAux]
  | s :: c, r, cur, h => by
    have hs : s ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := clausesAux_app c r (s :: cur) (fun e => h (List.mem_cons_of_mem _ e))
    cases s <;> simp_all [clausesAux]

theorem clauses_flatMap : ∀ L : List (List SatSym), (∀ c ∈ L, sep ∉ c) →
    clauses (L.flatMap (· ++ [sep])) = L
  | [], _ => rfl
  | c :: L, h => by
    have := clausesAux_app c (L.flatMap (· ++ [sep])) [] (h c (by simp))
    simp only [List.flatMap_cons, List.append_assoc, List.singleton_append, clauses] at this ⊢
    rw [this, List.reverse_nil, List.nil_append]
    exact congrArg _ (clauses_flatMap L fun c hc => h c (by simp [hc]))

theorem sep_not_mem_ent_list {α : Type} (l : List α) (f : α → Bool) :
    sep ∉ l.map fun b => ent (f b) := by
  simp only [List.mem_map, not_exists, not_and]
  intro b _ h; unfold ent at h; split at h <;> cases h

theorem clauses_G (w : List SatSym) : clauses (G w) = kRow w :: gRows w := by
  refine clauses_flatMap _ fun c hc => ?_
  simp only [gRows, List.mem_cons, List.mem_map] at hc
  rcases hc with rfl | rfl | ⟨a, _, rfl⟩
  · simp [kRow]
  · simp only [litRow, List.mem_cons, reduceCtorEq, false_or]; exact sep_not_mem_ent_list _ _
  · simp only [vRow, List.mem_cons, not_or]
    refine ⟨fun e => ?_, sep_not_mem_ent_list _ _⟩
    unfold ent at e; split at e <;> cases e

/-- Entries of the matrix. -/
def E (A : List (SatSym × ℕ × ℕ)) : ℕ → ℕ → Prop
  | 0, 0 => False
  | 0, q + 1 => ∃ b, A[q]? = some b ∧ isLit b.1 = true
  | p + 1, 0 => ∃ a, A[p]? = some a ∧ isLit a.1 = true
  | p + 1, q + 1 => ∃ a b, A[p]? = some a ∧ A[q]? = some b ∧ adjB a b = true

theorem ent_eq_pos (x : Bool) : ent x = pos ↔ x = true := by cases x <;> simp [ent]

theorem getD_map_ent {α : Type} (l : List α) (f : α → Bool) (q : ℕ) :
    (l.map fun b => ent (f b)).getD q zero = pos ↔ ∃ b, l[q]? = some b ∧ f b = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[q]? with
  | none => simp
  | some b => simp [ent_eq_pos]

theorem entry_iff (A : List (SatSym × ℕ × ℕ)) (i j : ℕ) :
    ((litRow A :: A.map (vRow A)).getD i []).getD j zero = pos ↔ E A i j := by
  rcases i with _ | p <;> rcases j with _ | q
  · simp [litRow, E]
  · simp only [List.getD_cons_zero, litRow, List.getD_cons_succ, E]; exact getD_map_ent _ _ _
  · simp only [List.getD_cons_succ, E, List.getD_eq_getElem?_getD (l := A.map _),
      List.getElem?_map]
    rcases h : A[p]? with _ | a
    · simp
    · simp [vRow, ent_eq_pos]
  · simp only [List.getD_cons_succ, E]
    rw [List.getD_eq_getElem?_getD (l := A.map _), List.getElem?_map]
    rcases h : A[p]? with _ | a
    · simp
    · simp only [Option.map_some, Option.getD_some, vRow, List.getD_cons_succ,
        getD_map_ent, Option.some.injEq]
      constructor
      · rintro ⟨b, hb, h⟩; exact ⟨a, b, rfl, hb, h⟩
      · rintro ⟨a', b, rfl, hb, h⟩; exact ⟨b, hb, h⟩

/-! ## Annotations of `trunc w` -/

/-- Annotation of a `sep`-free clause. -/
def annL : List SatSym → ℕ → ℕ → List (SatSym × ℕ × ℕ)
  | [], _, _ => []
  | s :: c, t, j => (s, t, j) :: annL c t (j + 1)

theorem ann_app : ∀ (c r : List SatSym) (t j : ℕ), sep ∉ c →
    ann (c ++ sep :: r) t j = annL c t j ++ (sep, t, j + c.length) :: ann r (t + 1) 0
  | [], r, t, j, _ => by simp [ann, annL]
  | s :: c, r, t, j, h => by
    have hs : s ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := ann_app c r t (j + 1) (fun e => h (List.mem_cons_of_mem _ e))
    have e : j + 1 + c.length = j + (c.length + 1) := by omega
    rw [e] at ih
    cases s <;> simp_all [ann, annL]

theorem mem_annL : ∀ (c : List SatSym) (t j : ℕ) (x : SatSym × ℕ × ℕ),
    x ∈ annL c t j ↔ ∃ i, ∃ h : i < c.length, x = (c.get ⟨i, h⟩, t, j + i)
  | [], t, j, x => by simp [annL]
  | s :: c, t, j, x => by
    rw [annL, List.mem_cons, mem_annL c t (j + 1) x]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨i + 1, by simp; omega, by simp; omega⟩
    · rintro ⟨_ | i, hi, rfl⟩
      · left; simp
      · right; exact ⟨i, by simp at hi; omega, by simp; omega⟩

theorem ann_flatMap : ∀ (L : List (List SatSym)) (t₀ : ℕ), (∀ c ∈ L, sep ∉ c) →
    (∀ t < L.length, ∀ j < (L.getD t []).length, ((L.getD t []).getD j zero, t₀ + t, j) ∈
      ann (L.flatMap (· ++ [sep])) t₀ 0) ∧
    (∀ x ∈ ann (L.flatMap (· ++ [sep])) t₀ 0, isLit x.1 = true →
      ∃ t < L.length, x.2.1 = t₀ + t ∧ (L.getD t []).getD x.2.2 zero = x.1)
  | [], t₀, _ => by simp [ann]
  | c :: L, t₀, h => by
    have ih := ann_flatMap L (t₀ + 1) fun c hc => h c (by simp [hc])
    have e : (c :: L).flatMap (· ++ [sep]) = c ++ sep :: L.flatMap (· ++ [sep]) := by simp
    rw [e, ann_app _ _ _ _ (h c (by simp))]
    refine ⟨fun t ht j hj => ?_, fun x hx hl => ?_⟩
    · rcases t with _ | t
      · simp only [List.mem_append, List.mem_cons]
        left; exact (mem_annL _ _ _ _).2 ⟨j, by simpa using hj, by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hj)]⟩
      · simp only [List.mem_append, List.mem_cons]
        right; right
        have := ih.1 t (by simpa using ht) j (by simpa using hj)
        simpa [Nat.add_assoc, Nat.add_comm 1 t] using this
    · simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · obtain ⟨i, hi, rfl⟩ := (mem_annL _ _ _ _).1 hx
        exact ⟨0, by simp, by simp, by simp [List.getD_eq_getElem?_getD, hi]⟩
      · simp [isLit] at hl
      · obtain ⟨t, ht, h1, h2⟩ := ih.2 x hx hl
        exact ⟨t + 1, by simp; omega, by omega, by simpa using h2⟩

theorem annW_complete (w : List SatSym) (t : ℕ) (ht : t < (clauses w).length) (j : ℕ)
    (hj : j < ((clauses w).getD t []).length) :
    (((clauses w).getD t []).getD j zero, t, j) ∈ annW w := by
  have := (ann_flatMap (clauses w) 0 (sep_not_mem_clauses w)).1 t ht j hj
  simpa [annW, trunc] using this

theorem annW_sound (w : List SatSym) (x : SatSym × ℕ × ℕ) (hx : x ∈ annW w)
    (hl : isLit x.1 = true) :
    x.2.1 < (clauses w).length ∧ ((clauses w).getD x.2.1 []).getD x.2.2 zero = x.1 := by
  obtain ⟨t, ht, h1, h2⟩ := (ann_flatMap (clauses w) 0 (sep_not_mem_clauses w)).2 x
    (by simpa [annW, trunc] using hx) hl
  rw [h1, Nat.zero_add]; exact ⟨ht, h2⟩

/-! ## Correctness -/

theorem isLit_of_litTrue {a : ℕ → Bool} {j : ℕ} {s : SatSym} (h : litTrue a j s) :
    isLit s = true := by cases s <;> simp_all [litTrue, isLit]

theorem litTrue_consistent {a : ℕ → Bool} {j : ℕ} {s s' : SatSym} (h : litTrue a j s)
    (h' : litTrue a j s') : s = s' := by
  cases s <;> cases s' <;> simp_all [litTrue]

/-- SAT ⇒ CLIQUE. -/
theorem clique_of_sat (w : List SatSym) (h : SATLang w) : CliqueLang (G w) := by
  classical
  obtain ⟨a, ha⟩ := (clauses_sat_iff w).1 h
  set A := annW w
  set m := (clauses w).length
  have hpick : ∀ t, ∃ q : ℕ, t < m → ∃ j, A[q]? = some (((clauses w).getD t []).getD j zero, t, j)
      ∧ litTrue a j (((clauses w).getD t []).getD j zero) := by
    intro t
    by_cases ht : t < m
    · obtain ⟨j, hj, hl⟩ := ha ((clauses w)[t]) (List.getElem_mem ht)
      rw [← List.getD_eq_getElem _ [] ht] at hj hl
      have hm := annW_complete w t ht j hj
      obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hm
      exact ⟨q, fun _ => ⟨j, by rw [List.getElem?_eq_getElem hq, hqe], hl⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose q hq using hpick
  -- the clause index of the vertex `q t + 1`
  have hqt : ∀ t < m, ∃ b, A[q t]? = some b ∧ b.2.1 = t ∧ isLit b.1 = true := by
    intro t ht
    obtain ⟨j, h1, h2⟩ := hq t ht
    exact ⟨_, h1, rfl, isLit_of_litTrue h2⟩
  have hinj : Set.InjOn (fun t => q t + 1) (Finset.range m : Set ℕ) := by
    intro t ht t' ht' e
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    obtain ⟨b, hb, hb1, -⟩ := hqt t ht
    obtain ⟨b', hb', hb1', -⟩ := hqt t' ht'
    have : q t = q t' := by simpa using e
    rw [this, hb'] at hb
    cases hb; omega
  set S := insert 0 ((Finset.range m).image fun t => q t + 1)
  have hcard : S.card = m + 1 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injOn hinj,
      Finset.card_range]
  show (match clauses (G w) with
    | [] => False
    | kr :: rows => ∃ S : Finset ℕ, kr.length ≤ S.card ∧ (∀ i ∈ S, i < rows.length) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (rows.getD i []).getD j zero = pos)
  rw [clauses_G]
  refine ⟨S, by simp [kRow, hcard, m], ?_, ?_⟩
  · intro i hi
    simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hi
    rcases hi with rfl | ⟨t, ht, rfl⟩
    · simp [gRows]
    · obtain ⟨b, hb, -⟩ := hqt t ht
      have := (List.getElem?_eq_some_iff.1 hb).1
      simp [gRows, A] at this ⊢; omega
  · intro i hi j hj hij
    rw [gRows, entry_iff]
    simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hi hj
    rcases hi with rfl | ⟨t, ht, rfl⟩ <;> rcases hj with rfl | ⟨t', ht', rfl⟩
    · exact absurd rfl hij
    · obtain ⟨b, hb, -, hl⟩ := hqt t' ht'; exact ⟨b, hb, hl⟩
    · obtain ⟨b, hb, -, hl⟩ := hqt t ht; exact ⟨b, hb, hl⟩
    · have htt : t ≠ t' := by rintro rfl; exact hij rfl
      obtain ⟨j, h1, h2⟩ := hq t ht
      obtain ⟨j', h1', h2'⟩ := hq t' ht'
      refine ⟨_, _, h1, h1', ?_⟩
      simp only [adjB, isLit_of_litTrue h2, isLit_of_litTrue h2', Bool.true_and]
      have hn : (t != t') = true := by simpa using htt
      rw [hn, Bool.true_and]
      by_cases hjj : j = j'
      · subst hjj; have := litTrue_consistent h2 h2'; rw [this]; simp
      · simp [hjj]

/-- CLIQUE ⇒ SAT. -/
theorem sat_of_clique (w : List SatSym) (h : CliqueLang (G w)) : SATLang w := by
  classical
  have h' : ∃ S : Finset ℕ, (kRow w).length ≤ S.card ∧ (∀ i ∈ S, i < (gRows w).length) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((gRows w).getD i []).getD j zero = pos := by
    have := h; unfold CliqueLang at this; rw [clauses_G] at this; exact this
  obtain ⟨S, hS, -, hadj⟩ := h'
  set A := annW w
  set m := (clauses w).length
  have hk : m + 1 ≤ S.card := by
    have := hS; simp only [kRow, List.length_replicate] at this; exact this
  rcases Nat.eq_zero_or_pos m with hm | hm
  · refine (clauses_sat_iff w).2 ⟨fun _ => false, fun c hc => ?_⟩
    rw [List.length_eq_zero_iff.1 hm] at hc; simp at hc
  have E' : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → E A i j := fun i hi j hj hij => by
    have := hadj i hi j hj hij; rwa [gRows, entry_iff] at this
  set T := S.erase 0
  -- every vertex of `T` is a literal position
  have hlit : ∀ i ∈ T, ∃ b, A[i - 1]? = some b ∧ isLit b.1 = true := by
    intro i hi
    obtain ⟨hi0, hiS⟩ := Finset.mem_erase.1 hi
    obtain ⟨i', hi'S, hii'⟩ : ∃ i' ∈ S, i' ≠ i := by
      by_contra hc; push Not at hc
      have : S ⊆ {i} := fun x hx => by simp [hc x hx]
      have := Finset.card_le_card this; simp at this; omega
    have hE := E' i hiS i' hi'S (Ne.symm hii')
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    rcases i' with _ | q
    · simpa [E] using hE
    · obtain ⟨a, b, ha, hb, hab⟩ := hE
      refine ⟨a, by simpa using ha, ?_⟩
      simp only [adjB, Bool.and_eq_true] at hab; exact hab.1.1.1
  -- the clause of a vertex
  let f : ℕ → ℕ := fun i => ((A[i - 1]?).map fun b => b.2.1).getD 0
  have hf : ∀ i ∈ T, ∀ b, A[i - 1]? = some b → f i = b.2.1 := by
    intro i _ b hb; simp [f, hb]
  have hinj : Set.InjOn f (T : Set ℕ) := by
    intro i hi i' hi' e
    by_contra hne
    obtain ⟨b, hb, -⟩ := hlit i hi
    obtain ⟨b', hb', -⟩ := hlit i' hi'
    have h0 := (Finset.mem_erase.1 hi).1
    have h0' := (Finset.mem_erase.1 hi').1
    have hE := E' i (Finset.mem_erase.1 hi).2 i' (Finset.mem_erase.1 hi').2 hne
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    obtain ⟨p', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0'
    obtain ⟨a, a', ha, ha', hab⟩ := hE
    simp only [Nat.succ_sub_one] at hb hb'
    rw [hb] at ha; rw [hb'] at ha'
    cases ha; cases ha'
    rw [hf _ hi b hb, hf _ hi' b' hb'] at e
    simp [adjB, e] at hab
  have hmaps : ∀ i ∈ T, f i ∈ Finset.range m := by
    intro i hi
    obtain ⟨b, hb, hl⟩ := hlit i hi
    rw [hf i hi b hb, Finset.mem_range]
    exact (annW_sound w b (List.mem_of_getElem? hb) hl).1
  have himg : T.image f = Finset.range m := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx; exact hmaps i hi
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      have : S.card - 1 ≤ T.card := Finset.pred_card_le_card_erase
      omega
  -- the assignment
  let a : ℕ → Bool := fun j =>
    decide (∃ i ∈ T, ∃ b, A[i - 1]? = some b ∧ b.1 = pos ∧ b.2.2 = j)
  refine (clauses_sat_iff w).2 ⟨a, fun c hc => ?_⟩
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨i, hi, hit⟩ := Finset.mem_image.1 (himg.symm ▸ Finset.mem_range.2 ht :
    t ∈ T.image f)
  obtain ⟨b, hb, hl⟩ := hlit i hi
  rw [hf i hi b hb] at hit
  obtain ⟨-, hcb⟩ := annW_sound w b (List.mem_of_getElem? hb) hl
  rw [hit, List.getD_eq_getElem _ _ ht] at hcb
  have hj : b.2.2 < (clauses w)[t].length := by
    by_contra hj
    rw [List.getD_eq_default _ _ (by omega)] at hcb
    rw [← hcb] at hl; simp [isLit] at hl
  refine ⟨b.2.2, hj, ?_⟩
  rw [hcb]
  rcases hb1 : b.1 with _ | _ | _ | _
  · simp only [litTrue, a, decide_eq_true_eq]; exact ⟨i, hi, b, hb, hb1, rfl⟩
  · simp only [litTrue, a, decide_eq_false_iff_not, not_exists, not_and]
    intro i' hi' b' hb' hb'1 hb'2
    have hne : i ≠ i' := by rintro rfl; rw [hb] at hb'; cases hb'; rw [hb1] at hb'1; cases hb'1
    have h0 := (Finset.mem_erase.1 hi).1
    have h0' := (Finset.mem_erase.1 hi').1
    have hE := E' i (Finset.mem_erase.1 hi).2 i' (Finset.mem_erase.1 hi').2 hne
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    obtain ⟨p', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0'
    obtain ⟨x, x', hx, hx', hab⟩ := hE
    simp only [Nat.succ_sub_one] at hb hb'
    rw [hb] at hx; rw [hb'] at hx'
    cases hx; cases hx'
    simp [adjB, hb1, hb'1, hb'2] at hab
  · simp [isLit, hb1] at hl
  · simp [isLit, hb1] at hl

/-- **Correctness of the reduction.** -/
theorem sat_iff_clique (w : List SatSym) : SATLang w ↔ CliqueLang (G w) :=
  ⟨clique_of_sat w, sat_of_clique w⟩

end Pnp.Karp.Clique
