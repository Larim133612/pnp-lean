import Pnp.Karp.NAE

namespace Pnp.Karp.NAE

open Pnp.CookLevin SatSym Pnp.Karp.ThreeSAT

/-- Boolean value of a literal symbol at variable `i`. -/
def m2r_lb (a : ℕ → Bool) (i : ℕ) : SatSym → Bool
  | pos => a i
  | neg => !a i
  | _ => false

theorem m2r_litTrue_iff (a : ℕ → Bool) (i : ℕ) (s : SatSym) :
    litTrue a i s ↔ m2r_lb a i s = true := by
  cases s <;> simp [litTrue, m2r_lb]

theorem m2r_sat_zs_cons (a : ℕ → Bool) (u : ℕ) (s : SatSym) (c : List SatSym) :
    ClauseSat a (zs u ++ s :: c) ↔
      m2r_lb a u s = true ∨ ClauseSat (fun i => a (i + 1 + u)) c := by
  rw [clauseSat_zs, clauseSat_cons, litTrue_zero_shift, m2r_litTrue_iff]

theorem m2r_sat_two (a : ℕ → Bool) (u : ℕ) (s : SatSym) (g : ℕ) (t : SatSym) :
    ClauseSat a (two u s g t) ↔ (m2r_lb a u s || m2r_lb a (u + g + 1) t) = true := by
  have e : two u s g t = zs u ++ s :: (zs g ++ t :: []) := by simp [two]
  rw [e, m2r_sat_zs_cons, m2r_sat_zs_cons]
  have : ClauseSat (fun i => a (i + 1 + g + 1 + u)) [] ↔ False := ⟨clauseSat_nil _, False.elim⟩
  rw [this, or_false]
  have h2 : m2r_lb (fun i => a (i + 1 + u)) g t = m2r_lb a (u + g + 1) t := by
    cases t <;> simp [m2r_lb] <;> congr 1 <;> omega
  rw [h2, Bool.or_eq_true]

theorem m2r_sat_tri (a : ℕ → Bool) (u : ℕ) (s : SatSym) (g : ℕ) (t : SatSym) (h : ℕ)
    (r : SatSym) :
    ClauseSat a (NC.tri u s g t h r).dense ↔
      (m2r_lb a u s || m2r_lb a (u + g + 1) t || m2r_lb a (u + g + h + 2) r) = true := by
  have e : (NC.tri u s g t h r).dense = zs u ++ s :: (zs g ++ t :: (zs h ++ r :: [])) := by
    simp [NC.dense]
  rw [e, m2r_sat_zs_cons, m2r_sat_zs_cons, m2r_sat_zs_cons]
  have : ClauseSat (fun i => a (i + 1 + h + 1 + g + 1 + u)) [] ↔ False :=
    ⟨clauseSat_nil _, False.elim⟩
  rw [this, or_false]
  have h2 : m2r_lb (fun i => a (i + 1 + u)) g t = m2r_lb a (u + g + 1) t := by
    cases t <;> simp [m2r_lb] <;> congr 1 <;> omega
  have h3 : m2r_lb (fun i => a (i + 1 + g + 1 + u)) h r = m2r_lb a (u + g + h + 2) r := by
    cases r <;> simp [m2r_lb] <;> congr 1 <;> omega
  rw [h2, h3]
  simp [Bool.or_eq_true, or_assoc]


/-- A literal symbol (`pos` or `neg`). -/
def m2r_pn (s : SatSym) : Prop := s = pos ∨ s = neg

theorem m2r_lb_swp (a : ℕ → Bool) (i : ℕ) {s : SatSym} (hs : m2r_pn s) :
    m2r_lb a i (swp s) = !m2r_lb a i s := by
  rcases hs with rfl | rfl <;> simp [m2r_lb, swp]

theorem m2r_lb_not (a : ℕ → Bool) (i : ℕ) {s : SatSym} (hs : m2r_pn s) :
    m2r_lb (fun i => !a i) i s = !m2r_lb a i s := by
  rcases hs with rfl | rfl <;> simp [m2r_lb]

/-- All literal symbols of an NC are `pos`/`neg`. -/
def m2r_good : NC → Prop
  | .duo _ s _ t => m2r_pn s ∧ m2r_pn t
  | .tri _ s _ t _ r => m2r_pn s ∧ m2r_pn t ∧ m2r_pn r

open Classical in
/-- Number of clauses of `L` satisfied by `a`. -/
noncomputable def m2r_cnt (a : ℕ → Bool) (L : List (List SatSym)) : ℕ :=
  L.countP (fun r => decide (ClauseSat a r))

theorem m2r_gad (a : ℕ → Bool) (c : NC) (hc : m2r_good c) :
    m2r_cnt a c.gad ≤ c.tgt ∧ (m2r_cnt a c.gad = c.tgt ↔ NAESat a c.dense) := by
  cases c with
  | duo u s g t =>
    obtain ⟨hs, ht⟩ := hc
    simp only [NC.gad, NC.tgt, NC.dense, m2r_cnt, List.countP_cons, List.countP_nil,
      NAESat, m2r_sat_two, m2r_lb_swp a _ hs, m2r_lb_swp a _ ht, m2r_lb_not a _ hs,
      m2r_lb_not a _ ht]
    generalize m2r_lb a u s = p
    generalize m2r_lb a (u + g + 1) t = q
    cases p <;> cases q <;> simp
  | tri u s g t h r =>
    obtain ⟨hs, ht, hr⟩ := hc
    have e1 : u + (g + h + 1) + 1 = u + g + h + 2 := by omega
    have e2 : u + g + 1 + h + 1 = u + g + h + 2 := by omega
    simp only [NC.gad, NC.tgt, m2r_cnt, List.countP_cons, List.countP_nil,
      NAESat, m2r_sat_two, m2r_sat_tri, m2r_lb_swp a _ hs, m2r_lb_swp a _ ht,
      m2r_lb_swp a _ hr, m2r_lb_not a _ hs, m2r_lb_not a _ ht, m2r_lb_not a _ hr, e1, e2]
    generalize m2r_lb a u s = p
    generalize m2r_lb a (u + g + 1) t = q
    generalize m2r_lb a (u + g + h + 2) r = x
    cases p <;> cases q <;> cases x <;> simp


theorem m2r_goN_good : ∀ (w : List SatSym) (j d : ℕ), ∀ c ∈ goN w j d, m2r_good c
  | [], _, _ => by simp [goN]
  | s :: w, j, d => by
    by_cases hs : s = sep
    · simp only [goN, hs, if_true, List.mem_cons]
      rintro c (rfl | rfl | hc)
      · simp [sA, m2r_good, m2r_pn]
      · simp [sB, m2r_good, m2r_pn]
      · exact m2r_goN_good w _ _ c hc
    · simp only [goN, hs, if_false, List.mem_cons]
      rintro c (rfl | rfl | hc)
      · unfold c1
        split_ifs with hz
        · simp [m2r_good, m2r_pn]
        · cases s <;> simp_all [m2r_good, m2r_pn]
      · simp [c2, m2r_good, m2r_pn]
      · exact m2r_goN_good w _ _ c hc

theorem m2r_NCs_good (w : List SatSym) : ∀ c ∈ NCs w, m2r_good c := by
  simp only [NCs, List.mem_cons]
  rintro c (rfl | hc)
  · simp [m2r_good, m2r_pn]
  · exact m2r_goN_good w 0 0 c hc

theorem m2r_gad_rows (c : NC) (hc : m2r_good c) :
    ∀ r ∈ c.gad, ∃ u s g t, r = two u s g t ∧ m2r_pn s ∧ m2r_pn t := by
  have hw : ∀ {s}, m2r_pn s → m2r_pn (swp s) := by
    rintro s (rfl | rfl) <;> simp [m2r_pn, swp]
  cases c with
  | duo u s g t =>
    obtain ⟨hs, ht⟩ := hc
    simp only [NC.gad, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact ⟨_, _, _, _, rfl, hs, ht⟩
    · exact ⟨_, _, _, _, rfl, hw hs, hw ht⟩
  | tri u s g t h x =>
    obtain ⟨hs, ht, hx⟩ := hc
    simp only [NC.gad, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨_, _, _, _, rfl, hs, ht⟩
    · exact ⟨_, _, _, _, rfl, hs, hx⟩
    · exact ⟨_, _, _, _, rfl, ht, hx⟩
    · exact ⟨_, _, _, _, rfl, hw hs, hw ht⟩
    · exact ⟨_, _, _, _, rfl, hw hs, hw hx⟩
    · exact ⟨_, _, _, _, rfl, hw ht, hw hx⟩

theorem m2r_two_sep (u : ℕ) {s : SatSym} (g : ℕ) {t : SatSym} (hs : m2r_pn s)
    (ht : m2r_pn t) : sep ∉ two u s g t := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [two, List.mem_replicate]

theorem m2r_two_len (u : ℕ) (s : SatSym) (g : ℕ) (t : SatSym) :
    ((two u s g t).filter (· ≠ zero)).length ≤ 2 := by
  simp only [two, List.filter_append, List.length_append]
  have : ∀ m, ((zs m).filter (· ≠ zero)).length = 0 := by
    intro m; simp
  rw [this, this]
  have : ∀ x : SatSym, ([x].filter (· ≠ zero)).length ≤ 1 := by
    intro x; cases x <;> simp
  have h1 := this s; have h2 := this t
  omega

theorem m2r_cnt_flatMap (a : ℕ → Bool) : ∀ L : List NC,
    m2r_cnt a (L.flatMap NC.gad) = (L.map (fun c => m2r_cnt a c.gad)).sum
  | [] => by simp [m2r_cnt]
  | c :: L => by
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← m2r_cnt_flatMap a L]
    simp [m2r_cnt, List.countP_append]

open Classical in
theorem m2r_card (a : ℕ → Bool) (rs : List (List SatSym)) :
    ((Finset.range rs.length).filter (fun i => ClauseSat a (rs.getD i []))).card =
      m2r_cnt a rs := by
  induction rs using List.reverseRecOn with
  | nil => simp [m2r_cnt]
  | append_singleton rs x ih =>
    rw [List.length_append, List.length_singleton, Finset.range_add_one,
      Finset.filter_insert]
    have hx : (rs ++ [x]).getD rs.length [] = x := by simp
    have hf : (Finset.range rs.length).filter (fun i => ClauseSat a ((rs ++ [x]).getD i [])) =
        (Finset.range rs.length).filter (fun i => ClauseSat a (rs.getD i [])) := by
      apply Finset.filter_congr
      intro i hi
      rw [Finset.mem_range] at hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    rw [hx, hf]
    unfold m2r_cnt at ih ⊢
    rw [List.countP_append]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]; simp [h]
    · rw [ih]; simp [h]


theorem m2r_sum {f g : NC → ℕ} : ∀ L : List NC, (∀ c ∈ L, f c ≤ g c) →
    (L.map f).sum ≤ (L.map g).sum ∧ ((L.map f).sum = (L.map g).sum → ∀ c ∈ L, f c = g c)
  | [], _ => by simp
  | c :: L, h => by
    have hc := h c (List.mem_cons_self ..)
    obtain ⟨ih1, ih2⟩ := m2r_sum L (fun c hc => h c (List.mem_cons_of_mem _ hc))
    simp only [List.map_cons, List.sum_cons, List.mem_cons]
    refine ⟨by omega, fun he c' hc' => ?_⟩
    rcases hc' with rfl | hc'
    · omega
    · exact ih2 (by omega) c' hc'

theorem m2_iff_ncs (w : List SatSym) :
    M2Lang (m2I w) ↔ ∃ a : ℕ → Bool, ∀ c ∈ NCs w, NAESat a c.dense := by
  classical
  have hrows : ∀ r ∈ (NCs w).flatMap NC.gad, ∃ u s g t, r = two u s g t ∧ m2r_pn s ∧ m2r_pn t := by
    intro r hr
    obtain ⟨c, hc, hr⟩ := List.mem_flatMap.1 hr
    exact m2r_gad_rows c (m2r_NCs_good w c hc) r hr
  have hcl : clauses (m2I w) = (NCs w).flatMap NC.gad ++ [zs (thr w)] := by
    apply clauses_flatMap
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨u, s, g, t, rfl, hs, ht⟩ := hrows r hr
      exact m2r_two_sep u g hs ht
    · rw [List.mem_singleton] at hr; subst hr; simp [List.mem_replicate]
  have key : ∀ a : ℕ → Bool,
      m2r_cnt a ((NCs w).flatMap NC.gad) ≤ thr w ∧
      (m2r_cnt a ((NCs w).flatMap NC.gad) = thr w ↔ ∀ c ∈ NCs w, NAESat a c.dense) := by
    intro a
    rw [m2r_cnt_flatMap, thr]
    obtain ⟨h1, h2⟩ := m2r_sum (f := fun c => m2r_cnt a c.gad) (g := NC.tgt) (NCs w)
      (fun c hc => (m2r_gad a c (m2r_NCs_good w c hc)).1)
    refine ⟨h1, fun he c hc => ?_, fun hn => ?_⟩
    · exact ((m2r_gad a c (m2r_NCs_good w c hc)).2).1 (h2 he c hc)
    · congr 1
      apply List.map_congr_left
      intro c hc
      exact ((m2r_gad a c (m2r_NCs_good w c hc)).2).2 (hn c hc)
  constructor
  · rintro ⟨rs, kr, h, -, a, S, hK, hS⟩
    rw [hcl] at h
    obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
    have hkr : kr = zs (thr w) := (List.singleton_inj.1 h2).symm
    subst hkr
    refine ⟨a, (key a).2.1 (le_antisymm (key a).1 ?_)⟩
    rw [← m2r_card]
    refine le_trans (by simpa using hK) (Finset.card_le_card ?_)
    intro i hi
    obtain ⟨h1, h2⟩ := hS i hi
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩
  · rintro ⟨a, ha⟩
    refine ⟨_, _, hcl, ?_, a,
      (Finset.range ((NCs w).flatMap NC.gad).length).filter
        (fun i => ClauseSat a (((NCs w).flatMap NC.gad).getD i [])), ?_, ?_⟩
    · intro r hr
      obtain ⟨u, s, g, t, rfl, -, -⟩ := hrows r hr
      exact m2r_two_len u s g t
    · rw [m2r_card, (key a).2.2 ha]; simp
    · intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hi
      exact ⟨Finset.mem_range.1 h1, h2⟩

end Pnp.Karp.NAE
