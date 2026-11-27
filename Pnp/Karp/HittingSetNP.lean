import Pnp.Karp.HittingSetVer
import Pnp.Karp.CliqueNP

/-!
# HITTING SET ∈ NP (official definition)

The checking relation is `hsv_vres w y = true` (`Pnp/Karp/HittingSetVer.lean`): the certificate
`y` is the indicator list of the hitting set `H = {p < |u| | y_p}`.

* `hsv_pad_getD`, `hsv_count_pad`: the padded prefix `hsv_pad y n` is the indicator vector of
  `H`, and its number of `true` bits is `|H|`;
* `hsv_hit_iff`: the row scan accepts iff the row has `pos` at a position of `H`;
* `hsv_hsLang_iff`: `HSLang w ↔ ∃ y, |y| ≤ |w| ∧ hsv_vres w y`;
* `hs_in_np`: `HSLang ∈ NP`, via `hsv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.HittingSet

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

/-! ## The indicator vector -/

theorem hsv_pad_getD : ∀ (n : ℕ) (R : Str) (p : ℕ),
    (hsv_pad R n).getD p false = (decide (p < n) && R.getD p false)
  | 0, R, p => by simp [hsv_pad]
  | n + 1, R, 0 => by cases R <;> simp [hsv_pad]
  | n + 1, R, p + 1 => by
    rw [hsv_pad, List.getD_cons_succ, hsv_pad_getD n R.tail p]
    cases R <;> simp

theorem hsv_pad_succ : ∀ (n : ℕ) (R : Str), hsv_pad R (n + 1) = hsv_pad R n ++ [R.getD n false]
  | 0, R => by cases R <;> simp [hsv_pad]
  | n + 1, R => by
    rw [hsv_pad, hsv_pad_succ n R.tail, hsv_pad]
    cases R <;> simp

theorem hsv_count_pad (R : Str) : ∀ n : ℕ,
    (hsv_pad R n).count true = ((Finset.range n).filter fun p => R.getD p false = true).card
  | 0 => rfl
  | n + 1 => by
    rw [hsv_pad_succ, List.count_append, hsv_count_pad R n, Finset.range_add_one,
      Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), h]; simp
    · rw [Bool.not_eq_true] at h; rw [h]; simp

/-! ## The row scan -/

theorem hsv_hit_iff : ∀ (r : List SatSym) (V : Str),
    hsv_hit r V = true ↔ ∃ p, V.getD p false = true ∧ r.getD p zero = pos
  | [], V => by simp [hsv_hit]
  | s :: r, [] => by simp
  | s :: r, v :: V => by
    rw [hsv_hit, Bool.or_eq_true, hsv_hit_iff r V]
    constructor
    · rintro (h | ⟨p, h1, h2⟩)
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨0, by simp [h.1], by simp [h.2]⟩
      · exact ⟨p + 1, by simpa using h1, by simpa using h2⟩
    · rintro ⟨_ | p, h1, h2⟩
      · left; simp_all
      · right; exact ⟨p, by simpa using h1, by simpa using h2⟩

/-! ## Correctness -/

theorem hsv_len_le (w : List SatSym) (c : List SatSym) (hc : c ∈ clauses w) :
    c.length ≤ w.length := by
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have h1 : c.length ≤ ((clauses w).map List.length).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hc)
  have := length_trunc_le w
  omega

theorem hsv_hsLang_iff (w : List SatSym) :
    HSLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ hsv_vres w y = true := by
  have hlen := hsv_len_le w
  unfold HSLang hsv_vres
  rcases hc : clauses w with _ | ⟨u, _ | ⟨kr, rs⟩⟩
  · simp
  · simp
  · rw [hc] at hlen
    simp only [List.cons.injEq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    constructor
    · rintro ⟨_, _, _, ⟨rfl, rfl, rfl⟩, H, hcard, hH, hrs⟩
      let y : Str := (List.range u.length).map fun p => decide (p ∈ H)
      have hy : ∀ p, y.getD p false = decide (p ∈ H) := by
        intro p
        by_cases hp : p < u.length
        · rw [List.getD_eq_getElem _ _ (by simpa [y] using hp)]
          simp [y]
        · rw [List.getD_eq_default _ _ (by simpa [y] using hp)]
          have : p ∉ H := fun h => hp (hH p h)
          simp [this]
      have hpad : ∀ p, (hsv_pad y u.length).getD p false = decide (p ∈ H) := by
        intro p
        rw [hsv_pad_getD, hy]
        by_cases h : p ∈ H
        · simp [h, hH p h]
        · simp [h]
      have hfil : ((Finset.range u.length).filter fun p => y.getD p false = true) = H := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_range, hy, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun h => ⟨hH p h, h⟩⟩
      refine ⟨y, by simpa [y] using hlen u (by simp), ?_, fun r hr => ?_⟩
      · rw [hsv_count_pad, hfil]; exact hcard
      · obtain ⟨p, hp, hpos⟩ := hrs r hr
        exact (hsv_hit_iff _ _).2 ⟨p, by rw [hpad]; simpa using hp, hpos⟩
    · rintro ⟨y, -, hcnt, hall⟩
      refine ⟨u, kr, rs, ⟨rfl, rfl, rfl⟩,
        (Finset.range u.length).filter fun p => y.getD p false = true, ?_, ?_, ?_⟩
      · rw [← hsv_count_pad]; exact hcnt
      · intro p hp; simpa using (Finset.mem_filter.1 hp).1
      · intro r hr
        obtain ⟨p, h1, h2⟩ := (hsv_hit_iff _ _).1 (hall r hr)
        rw [hsv_pad_getD, Bool.and_eq_true, decide_eq_true_eq] at h1
        exact ⟨p, Finset.mem_filter.2 ⟨Finset.mem_range.2 h1.1, h1.2⟩, h2⟩

/-! ## Transfer to the official class -/

/-- **HITTING SET ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem hs_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym) HSLang := by
  classical
  have hrun := fun z => ((hsv_exec_ver z).mono (hsv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg hsv_ver) (tb 5 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg hsv_ver, 5, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => hsv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => hsv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [hsv_hsLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.HittingSet
