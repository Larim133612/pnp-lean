import Pnp.Karp.NAE

namespace Pnp.Karp.NAE

open Pnp.CookLevin SatSym Pnp.Karp.ThreeSAT

theorem nr_lt_shift (a : ℕ → Bool) (f : ℕ → ℕ) (s : SatSym) :
    litTrue (fun i => a (f i)) 0 s ↔ litTrue a (f 0) s := by
  cases s <;> rfl

theorem nr_lt_congr {a b : ℕ → Bool} {k m : ℕ} (h : a k = b m) (s : SatSym) :
    litTrue a k s ↔ litTrue b m s := by
  cases s <;> simp [litTrue, h]

theorem nr_cs_duo (a : ℕ → Bool) (u : ℕ) (s : SatSym) (g : ℕ) (t : SatSym) :
    ClauseSat a (NC.duo u s g t).dense ↔ litTrue a u s ∨ litTrue a (u + g + 1) t := by
  simp only [NC.dense, two, List.append_assoc, clauseSat_zs,
    clauseSat_cons, nr_lt_shift, clauseSat_nil, or_false, List.cons_append, List.nil_append]
  rw [show 0 + g + 1 + u = u + g + 1 by omega, Nat.zero_add]

theorem nr_cs_tri (a : ℕ → Bool) (u : ℕ) (s : SatSym) (g : ℕ) (t : SatSym) (h : ℕ)
    (r : SatSym) : ClauseSat a (NC.tri u s g t h r).dense ↔
      litTrue a u s ∨ litTrue a (u + g + 1) t ∨ litTrue a (u + g + h + 2) r := by
  simp only [NC.dense, List.append_assoc, clauseSat_zs,
    clauseSat_cons, nr_lt_shift, clauseSat_nil, or_false, List.cons_append, List.nil_append]
  rw [show 0 + g + 1 + u = u + g + 1 by omega,
    show 0 + h + 1 + g + 1 + u = u + g + h + 2 by omega, Nat.zero_add]

theorem nr_cs_c2 (a : ℕ → Bool) (j d : ℕ) : ClauseSat a (c2 j d).dense ↔
    a 0 = true ∨ a (3 * (j + d) + 3) = false ∨ a (3 * (j + d) + 5) = false := by
  rw [c2, nr_cs_tri]; simp only [litTrue]
  ring_nf

theorem nr_cs_c1z (a : ℕ → Bool) (j d : ℕ) : ClauseSat a (c1 zero j d).dense ↔
    a 0 = true ∨ a (3 * (j + d) + 2) = true ∨ a (3 * (j + d) + 3) = true := by
  rw [c1, if_pos rfl, nr_cs_tri]; simp only [litTrue]
  ring_nf

theorem nr_cs_c1 (a : ℕ → Bool) {s : SatSym} (hs : s ≠ zero) (j d : ℕ) :
    ClauseSat a (c1 s j d).dense ↔
      litTrue a (3 * j + 1) s ∨ a (3 * (j + d) + 2) = true ∨ a (3 * (j + d) + 3) = true := by
  rw [c1, if_neg hs, nr_cs_tri]; simp only [litTrue]
  ring_nf

theorem nr_cs_sA (a : ℕ → Bool) (j d : ℕ) : ClauseSat a (sA j d).dense ↔
    a 0 = true ∨ a (3 * (j + d) + 2) = true := by
  rw [sA, nr_cs_duo]; simp only [litTrue]
  ring_nf

theorem nr_cs_sB (a : ℕ → Bool) (j d : ℕ) : ClauseSat a (sB j d).dense ↔
    a 0 = true ∨ a (3 * (j + d) + 5) = false := by
  rw [sB, nr_cs_duo]; simp only [litTrue]
  ring_nf

theorem nr_cs_st (a : ℕ → Bool) : ClauseSat a (NC.duo 0 pos 1 neg).dense ↔
    a 0 = true ∨ a 2 = false := by
  rw [nr_cs_duo]; simp only [litTrue]

theorem nr_nae_not (a : ℕ → Bool) (c : List SatSym) :
    NAESat (fun i => !a i) c ↔ NAESat a c := by
  simp only [NAESat, Bool.not_not]; exact And.comm

/-! ## Shapes -/

theorem nr_goN_shape : ∀ (w : List SatSym) (j d : ℕ), ∀ c ∈ goN w j d,
    sep ∉ c.dense ∧ (c.dense.filter (· ≠ zero)).length ≤ 3
  | [], _, _ => by simp [goN]
  | s :: w, j, d => by
    intro c hc
    have ih := nr_goN_shape w
    by_cases hs : s = sep
    · subst hs
      simp only [goN, if_true, List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · simp [sA, NC.dense, two]
      · simp [sB, NC.dense, two]
      · exact ih _ _ c hc
    · simp only [goN, hs, if_false, List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · cases s <;> simp_all [c1, NC.dense]
      · simp [c2, NC.dense]
      · exact ih _ _ c hc

theorem nr_NCs_shape (w : List SatSym) : ∀ c ∈ NCs w,
    sep ∉ c.dense ∧ (c.dense.filter (· ≠ zero)).length ≤ 3 := by
  intro c hc
  simp only [NCs, List.mem_cons] at hc
  rcases hc with rfl | hc
  · simp [NC.dense, two]
  · exact nr_goN_shape w 0 0 c hc

theorem clauses_naeI (w : List SatSym) : clauses (naeI w) = (NCs w).map NC.dense :=
  clauses_flatMap _ fun c hc => by
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact (nr_NCs_shape w c' hc').1

theorem is3_naeI (w : List SatSym) : Is3 (naeI w) := by
  intro c hc
  rw [clauses_naeI] at hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  exact (nr_NCs_shape w c' hc').2

/-! ## Forward direction -/

/-- The truth value of the literal at input position `q` of `w` (`j`: position inside the
current clause); `false` for `zero` and `sep`. -/
def nr_lAux (a : ℕ → Bool) : List SatSym → ℕ → ℕ → Bool
  | [], _, _ => false
  | s :: _, j, 0 => litB a j s
  | s :: w, j, q + 1 => if s = sep then nr_lAux a w 0 q else nr_lAux a w (j + 1) q

theorem nr_fwd (a A : ℕ → Bool) (h0 : A 0 = false) (hx : ∀ i, A (3 * i + 1) = a i) :
    ∀ (w : List SatSym) (j d : ℕ) (F : Bool),
      (∀ q, A (3 * (j + d + q) + 2) = yAux a w j F q) →
      (∀ q, A (3 * (j + d + q) + 3) = !(nr_lAux a w j q || yAux a w j F q)) →
      evalF a w j F = true → ∀ c ∈ goN w j d, NAESat A c.dense
  | [], _, _, _, _, _, _ => by simp [goN]
  | s :: w, j, d, F, H, Z, he => by
    intro c hc
    have H0 : A (3 * (j + d) + 2) = F := by simpa [yAux] using H 0
    have H1 : A (3 * (j + d) + 5) = yAux a (s :: w) j F 1 := by
      rw [← H 1]; congr 1
    have Z0 : A (3 * (j + d) + 3) = !(litB a j s || F) := by simpa [nr_lAux, yAux] using Z 0
    by_cases hs : s = sep
    · subst hs
      simp only [evalF, Bool.and_eq_true] at he
      simp only [goN, if_true, List.mem_cons] at hc
      simp only [yAux, if_true] at H1
      rcases hc with rfl | rfl | hc
      · simp [NAESat, nr_cs_sA, h0, H0, he.1]
      · simp [NAESat, nr_cs_sB, h0, H1]
      · refine nr_fwd a A h0 hx w 0 (j + d + 1) false (fun q => ?_) (fun q => ?_) he.2 c hc
        · rw [show 3 * (0 + (j + d + 1) + q) + 2 = 3 * (j + d + (q + 1)) + 2 by ring, H]
          simp [yAux]
        · rw [show 3 * (0 + (j + d + 1) + q) + 3 = 3 * (j + d + (q + 1)) + 3 by ring, Z]
          simp [yAux, nr_lAux]
    · rw [evalF_cons_ne a hs] at he
      simp only [goN, hs, if_false, List.mem_cons] at hc
      simp only [yAux, hs, if_false] at H1
      rcases hc with rfl | rfl | hc
      · cases s with
        | sep => exact absurd rfl hs
        | zero =>
          simp only [NAESat, nr_cs_c1z, h0, H0, Z0, litB]
          cases F <;> simp
        | pos =>
          simp only [NAESat, nr_cs_c1 _ (by decide : pos ≠ zero), litTrue, hx, H0, Z0, litB]
          cases a j <;> cases F <;> simp
        | neg =>
          simp only [NAESat, nr_cs_c1 _ (by decide : neg ≠ zero), litTrue, hx, H0, Z0, litB]
          cases a j <;> cases F <;> simp
      · simp only [NAESat, nr_cs_c2, h0, H1, Z0]
        cases F <;> cases litB a j s <;> simp
      · refine nr_fwd a A h0 hx w (j + 1) d _ (fun q => ?_) (fun q => ?_) he c hc
        · rw [show 3 * (j + 1 + d + q) + 2 = 3 * (j + d + (q + 1)) + 2 by ring, H]
          simp [yAux, hs]
        · rw [show 3 * (j + 1 + d + q) + 3 = 3 * (j + d + (q + 1)) + 3 by ring, Z]
          simp [yAux, nr_lAux, hs]

/-! ## Backward direction -/

/-- The 3-SAT assignment read off an NAE assignment: `x_j ↦ 2j`, `y_p ↦ 2p + 1`. -/
def nr_pr (A : ℕ → Bool) (i : ℕ) : Bool :=
  if i % 2 = 0 then A (3 * (i / 2) + 1) else A (3 * (i / 2) + 2)

theorem nr_pr_even (A : ℕ → Bool) (i : ℕ) : nr_pr A (2 * i) = A (3 * i + 1) := by
  simp [nr_pr]

theorem nr_pr_odd (A : ℕ → Bool) (i : ℕ) : nr_pr A (2 * i + 1) = A (3 * i + 2) := by
  simp only [nr_pr]; rw [if_neg (by omega)]; congr 2; omega

theorem nr_bwd (A : ℕ → Bool) (h0 : A 0 = false) : ∀ (w : List SatSym) (j d : ℕ),
    (∀ c ∈ goN w j d, ClauseSat A c.dense) → ∀ c ∈ goC w j d, ClauseSat (nr_pr A) c
  | [], _, _, _ => by simp [goC]
  | s :: w, j, d, hc => by
    have e1 : nr_pr A (2 * (j + d) + 1) = A (3 * (j + d) + 2) := nr_pr_odd A _
    have e3 : nr_pr A (2 * (j + d) + 3) = A (3 * (j + d) + 5) := by
      rw [show 2 * (j + d) + 3 = 2 * (j + d + 1) + 1 by ring, nr_pr_odd]; congr 1
    by_cases hs : s = sep
    · subst hs
      simp only [goN, if_true, List.mem_cons, forall_eq_or_imp] at hc
      obtain ⟨h1, h2, h3⟩ := hc
      rw [nr_cs_sA, h0] at h1
      rw [nr_cs_sB, h0] at h2
      simp only [goC, if_true, List.mem_cons, forall_eq_or_imp]
      refine ⟨?_, ?_, nr_bwd A h0 w 0 (j + d + 1) h3⟩
      · rw [clauseSat_uPos, e1]; simpa using h1
      · rw [clauseSat_uNeg, e3]; simpa using h2
    · simp only [goN, hs, if_false, List.mem_cons, forall_eq_or_imp] at hc
      obtain ⟨h1, h2, h3⟩ := hc
      simp only [goC, hs, if_false, List.mem_cons, forall_eq_or_imp]
      refine ⟨?_, nr_bwd A h0 w (j + 1) d h3⟩
      rw [clauseSat_stp, e1, e3, nr_lt_congr (nr_pr_even A j)]
      rw [nr_cs_c2, h0] at h2
      have h1' : litTrue A (3 * j + 1) s ∨ A (3 * (j + d) + 2) = true ∨
          A (3 * (j + d) + 3) = true := by
        by_cases hz : s = zero
        · subst hz; rw [nr_cs_c1z, h0] at h1; simpa [litTrue] using h1
        · rwa [nr_cs_c1 _ hz] at h1
      cases hA : A (3 * (j + d) + 3)
      · rcases h1' with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · simp [hA] at h
      · rw [hA] at h2; simp at h2
        exact Or.inr (Or.inr h2)

/-! ## Main theorems -/

theorem sat_iff_ncs (w : List SatSym) :
    SATLang w ↔ ∃ a : ℕ → Bool, ∀ c ∈ NCs w, NAESat a c.dense := by
  constructor
  · rintro ⟨a, ha⟩
    let A : ℕ → Bool := fun i =>
      if i % 3 = 1 then a (i / 3) else if i % 3 = 2 then yAux a w 0 false (i / 3)
      else if i = 0 then false
      else !(nr_lAux a w 0 ((i - 1) / 3) || yAux a w 0 false ((i - 1) / 3))
    have h0 : A 0 = false := by simp [A]
    have hx : ∀ i, A (3 * i + 1) = a i := fun i => by
      simp only [A]; rw [if_pos (by omega)]; congr 1; omega
    have hy : ∀ q, A (3 * (0 + 0 + q) + 2) = yAux a w 0 false q := fun q => by
      simp only [A]; rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega
    have hz : ∀ q, A (3 * (0 + 0 + q) + 3) =
        !(nr_lAux a w 0 q || yAux a w 0 false q) := fun q => by
      simp only [A]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have : (3 * (0 + 0 + q) + 3 - 1) / 3 = q := by omega
      rw [this]
    refine ⟨A, ?_⟩
    simp only [NCs, List.mem_cons, forall_eq_or_imp]
    refine ⟨?_, nr_fwd a A h0 hx w 0 0 false hy hz ha⟩
    have h2 : A 2 = false := by simpa [yAux] using hy 0
    simp [NAESat, nr_cs_st, h0, h2]
  · rintro ⟨A, hA⟩
    obtain ⟨B, hB0, hB⟩ : ∃ B : ℕ → Bool, B 0 = false ∧ ∀ c ∈ NCs w, NAESat B c.dense := by
      cases h : A 0
      · exact ⟨A, h, hA⟩
      · exact ⟨fun i => !A i, by simp [h], fun c hc => (nr_nae_not A _).2 (hA c hc)⟩
    rw [← sat_red_iff, clauses_sat_iff, clauses_red]
    refine ⟨nr_pr B, ?_⟩
    simp only [NCs, List.mem_cons, forall_eq_or_imp] at hB
    obtain ⟨hs, hB⟩ := hB
    simp only [TC, List.mem_cons, forall_eq_or_imp]
    refine ⟨?_, nr_bwd B hB0 w 0 0 fun c hc => (hB c hc).1⟩
    have h2 : B 2 = false := by
      have := hs.1; rw [nr_cs_st, hB0] at this; simpa using this
    rw [clauseSat_cons]; right
    rw [clauseSat_cons]; left
    simp only [litTrue]
    exact (nr_pr_odd B 0).trans h2

theorem sat_iff_nae (w : List SatSym) : SATLang w ↔ NAE3Lang (naeI w) := by
  rw [sat_iff_ncs]
  simp only [NAE3Lang, clauses_naeI, List.forall_mem_map]
  exact ⟨fun h => ⟨is3_naeI w, h⟩, fun h => h.2⟩

end Pnp.Karp.NAE
