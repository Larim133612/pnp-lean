import Pnp.Karp.DomSetVer
import Pnp.Karp.HittingSetNP

/-!
# DOMINATING SET ∈ NP (official definition)

The checking relation is `dsv_vres w y = true` (`Pnp/Karp/DomSetVer.lean`): the certificate
`y` is the indicator list of the dominating set `D = {u < n | y_u}` (`n` the number of rows).

* `dsv_or_getD`, `dsv_dm_getD`: the column vector `dsv_dm rows y []` has bit `v` set iff some
  row `u < n` with `y_u` has `pos` at position `v`;
* `dsv_go_iff`: the second pass accepts iff every row `v` has its bit set in one of the two
  vectors, or a hit (`hsv_hit_iff`, from HITTING SET);
* `dsv_dsLang_iff`: `DSLang w ↔ ∃ y, |y| ≤ |w| ∧ dsv_vres w y`;
* `ds_in_np`: `DSLang ∈ NP`, via `dsv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.DomSet

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.HittingSet

/-! ## The column vector -/

theorem dsv_or_cons (s : SatSym) (r : List SatSym) (D : Str) :
    dsv_or (s :: r) D = (D.headD false || decide (s = pos)) :: dsv_or r D.tail := by
  simp [dsv_or, dsv_orP, List.drop_tail]

theorem dsv_or_getD : ∀ (r : List SatSym) (D : Str) (p : ℕ),
    (dsv_or r D).getD p false = (D.getD p false || decide (r.getD p zero = pos))
  | [], D, p => by simp [dsv_or, dsv_orP]
  | s :: r, D, 0 => by cases D <;> simp [dsv_or_cons]
  | s :: r, D, p + 1 => by
    rw [dsv_or_cons, List.getD_cons_succ, dsv_or_getD r D.tail p]
    cases D <;> simp

theorem dsv_dm_getD : ∀ (rows : List (List SatSym)) (R D : Str) (p : ℕ),
    (dsv_dm rows R D).getD p false = true ↔ D.getD p false = true ∨
      ∃ u < rows.length, R.getD u false = true ∧ (rows.getD u []).getD p zero = pos
  | [], R, D, p => by simp [dsv_dm]
  | r :: rows, R, D, p => by
    rw [dsv_dm, dsv_dm_getD rows R.tail _ p]
    have hD : (if R.headD false = true then dsv_or r D else D).getD p false =
        (D.getD p false || (R.getD 0 false && decide (r.getD p zero = pos))) := by
      cases R with
      | nil => simp
      | cons b R =>
        have := dsv_or_getD r D p
        cases b <;> simp_all
    rw [hD]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.length_cons]
    constructor
    · rintro ((h | ⟨h1, h2⟩) | ⟨u, hu, h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨0, by omega, h1, by simpa using h2⟩
      · refine Or.inr ⟨u + 1, by omega, ?_, by simpa using h2⟩
        cases R <;> simp_all
    · rintro (h | ⟨_ | u, hu, h1, h2⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨h1, by simpa using h2⟩)
      · refine Or.inr ⟨u, by omega, ?_, by simpa using h2⟩
        cases R <;> simp_all

/-! ## The second pass -/

theorem dsv_go_iff (V : Str) : ∀ (rows : List (List SatSym)) (D E : Str),
    dsv_go V rows D E = true ↔ ∀ v < rows.length, D.getD v false = true ∨
      E.getD v false = true ∨ hsv_hit (rows.getD v []) V = true
  | [], _, _ => by simp [dsv_go]
  | r :: rows, D, E => by
    rw [dsv_go, Bool.and_eq_true, dsv_go_iff V rows D.tail E.tail]
    simp only [Bool.or_eq_true, List.length_cons]
    constructor
    · rintro ⟨h0, hs⟩ v hv
      rcases v with _ | v
      · cases D <;> cases E <;> simpa [or_assoc] using h0
      · have := hs v (by omega)
        cases D <;> cases E <;> simpa [or_assoc] using this
    · intro h
      refine ⟨?_, fun v hv => ?_⟩
      · have := h 0 (by omega)
        cases D <;> cases E <;> simpa [or_assoc] using this
      · have := h (v + 1) (by omega)
        cases D <;> cases E <;> simpa [or_assoc] using this

/-! ## Correctness -/

theorem dsv_dsLang_iff (w : List SatSym) :
    DSLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ dsv_vres w y = true := by
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have htr := length_trunc_le w
  unfold DSLang dsv_vres
  rcases hc : clauses w with _ | ⟨kr, rows⟩
  · simp
  · rw [hc] at hsum
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    simp only [List.cons.injEq, Bool.and_eq_true, decide_eq_true_eq, dsv_go_iff]
    constructor
    · rintro ⟨_, _, ⟨rfl, rfl⟩, D, hcard, hD, hdom⟩
      let y : Str := (List.range rows.length).map fun p => decide (p ∈ D)
      have hy : ∀ p, y.getD p false = decide (p ∈ D) := by
        intro p
        by_cases hp : p < rows.length
        · rw [List.getD_eq_getElem _ _ (by simpa [y] using hp)]
          simp [y]
        · rw [List.getD_eq_default _ _ (by simpa [y] using hp)]
          have : p ∉ D := fun h => hp (hD p h)
          simp [this]
      have hpad : ∀ p, (hsv_pad y rows.length).getD p false = decide (p ∈ D) := by
        intro p
        rw [hsv_pad_getD, hy]
        by_cases h : p ∈ D
        · simp [h, hD p h]
        · simp [h]
      have hfil : ((Finset.range rows.length).filter fun p => y.getD p false = true) = D := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_range, hy, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun h => ⟨hD p h, h⟩⟩
      refine ⟨y, by simp [y]; omega, ?_, fun v hv => ?_⟩
      · rw [hsv_count_pad, hfil]; exact hcard
      · rcases hdom v hv with h | ⟨u, hu, h | h⟩
        · exact Or.inr (Or.inl (by rw [hpad]; simpa using h))
        · exact Or.inl ((dsv_dm_getD _ _ _ _).2
            (Or.inr ⟨u, hD u hu, by rw [hy]; simpa using hu, h⟩))
        · exact Or.inr (Or.inr ((hsv_hit_iff _ _).2 ⟨u, by rw [hpad]; simpa using hu, h⟩))
    · rintro ⟨y, -, hcnt, hall⟩
      refine ⟨kr, rows, ⟨rfl, rfl⟩,
        (Finset.range rows.length).filter fun p => y.getD p false = true, ?_, ?_, ?_⟩
      · rw [← hsv_count_pad]; exact hcnt
      · intro p hp; simpa using (Finset.mem_filter.1 hp).1
      · intro v hv
        rcases hall v hv with h | h | h
        · rcases (dsv_dm_getD _ _ _ _).1 h with h | ⟨u, hu, h1, h2⟩
          · simp at h
          · exact Or.inr ⟨u, Finset.mem_filter.2 ⟨Finset.mem_range.2 hu, h1⟩, Or.inl h2⟩
        · rw [hsv_pad_getD, Bool.and_eq_true, decide_eq_true_eq] at h
          exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_range.2 h.1, h.2⟩)
        · obtain ⟨p, h1, h2⟩ := (hsv_hit_iff _ _).1 h
          rw [hsv_pad_getD, Bool.and_eq_true, decide_eq_true_eq] at h1
          exact Or.inr ⟨p, Finset.mem_filter.2 ⟨Finset.mem_range.2 h1.1, h1.2⟩, Or.inr h2⟩

/-! ## Transfer to the official class -/

/-- **DOMINATING SET ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem ds_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym) DSLang := by
  classical
  have hrun := fun z => ((dsv_exec_ver z).mono (dsv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg dsv_ver) (tb 7 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg dsv_ver, 7, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => dsv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => dsv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [dsv_dsLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.DomSet
