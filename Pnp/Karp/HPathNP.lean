import Pnp.Karp.HPathVer
import Pnp.Karp.HamNP

/-!
# HAMILTONIAN PATH ∈ NP (official definition)

The checking relation is `pv2_vres w y = true` (`Pnp/Karp/HPathVer.lean`): with
`n = |clauses w|`, the verifier accepts if `n = 0`; otherwise the certificate `y` is read as the
blocks `B_i = hv_B n y i` of `n` bits, and the verifier checks that every block has exactly one
`true` bit, at a position no earlier block has (`hv_permOk` against `hv_Sacc`, as in
`Pnp/Karp/HamNP.lean`), and that consecutive blocks `B_i`, `B_{i+1}` (`i + 1 < n`, no
wrap-around) are joined by a `pos` entry (`hv_edgeB`).

* `pv2_vres_iff`: this characterization of `pv2_vres`;
* `uhpathLang_iff`: `UHPathLang w ↔ ∃ y, |y| ≤ |w|^2 ∧ pv2_vres w y`;
* `uhpath_in_np`: `UHPathLang ∈ NP`, via `pv2_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.Ham

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

theorem pv2_mainF_iff (rows : List (List SatSym)) (n : ℕ) (y : Str) : ∀ (k j : ℕ),
    pv2_mainF rows n k (y.drop ((j + 1) * n)) (hv_B n y j) (hv_Sacc n y j) = true ↔
      ∀ i, j ≤ i → i ≤ j + k → hv_permOk (hv_B n y i) (hv_Sacc n y i) = true ∧
        (i < j + k → hv_edgeB rows (hv_B n y i) (hv_B n y (i + 1)) = true)
  | 0, j => by
    rw [pv2_mainF]
    constructor
    · rintro h1 i hi1 hi2
      obtain rfl : i = j := by omega
      exact ⟨h1, fun h => by omega⟩
    · intro h
      exact (h j le_rfl (by omega)).1
  | k + 1, j => by
    have ih := pv2_mainF_iff rows n y k (j + 1)
    have e1 : (y.drop ((j + 1) * n)).drop n = y.drop ((j + 1 + 1) * n) := by
      rw [List.drop_drop]; congr 1; ring
    have e2 : hv_tk n (y.drop ((j + 1) * n)) = hv_B n y (j + 1) := rfl
    have e3 : hv_orV (hv_B n y j) (hv_Sacc n y j) = hv_Sacc n y (j + 1) := rfl
    rw [pv2_mainF, e1, e2, e3, Bool.and_eq_true, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ i hi1 hi2
      rcases Nat.eq_or_lt_of_le hi1 with rfl | hi1
      · exact ⟨h1, fun _ => h2⟩
      · have := h3 i (by omega) (by omega)
        exact ⟨this.1, fun h => this.2 (by omega)⟩
    · intro h
      have h0 := h j le_rfl (by omega)
      refine ⟨⟨h0.1, h0.2 (by omega)⟩, fun i hi1 hi2 => ?_⟩
      have := h i (by omega) (by omega)
      exact ⟨this.1, fun h' => this.2 (by omega)⟩

theorem pv2_vres_iff (w : List SatSym) (y : Str) :
    pv2_vres w y = true ↔ (clauses w).length = 0 ∨ ∀ i < (clauses w).length,
      hv_permOk (hv_B (clauses w).length y i) (hv_Sacc (clauses w).length y i) = true ∧
      (i + 1 < (clauses w).length → hv_edgeB (clauses w) (hv_B (clauses w).length y i)
        (hv_B (clauses w).length y (i + 1)) = true) := by
  unfold pv2_vres
  rw [Bool.or_eq_true, decide_eq_true_iff]
  set n := (clauses w).length
  by_cases hn : n = 0
  · simp [hn]
  simp only [hn, false_or]
  have h := pv2_mainF_iff (clauses w) n y (n - 1) 0
  have e0 : hv_B n y 0 = hv_tk n y := by simp [hv_B]
  have eS : hv_Sacc n y 0 = List.replicate n false := rfl
  rw [e0, eS, show (0 + 1) * n = n by ring] at h
  rw [h]
  constructor
  · intro H i hi
    have := H i (by omega) (by omega)
    exact ⟨this.1, fun h' => this.2 (by omega)⟩
  · intro H i _ hi
    have := H i (by omega)
    exact ⟨this.1, fun h' => this.2 (by omega)⟩

/-! ## Short certificates -/

theorem uhpathLang_iff (w : List SatSym) :
    UHPathLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ pv2_vres w y = true := by
  have hcl := length_clauses_le w
  unfold UHPathLang IsHamPath
  simp only [pv2_vres_iff]
  set n := (clauses w).length
  by_cases hn0 : n = 0
  · refine ⟨fun _ => ⟨[], by simp, Or.inl hn0⟩, fun _ => ⟨[], ?_, by simp⟩⟩
    rw [hn0]; exact List.Perm.refl _
  simp only [hn0, false_or]
  constructor
  · rintro ⟨σ, hp, hadj⟩
    have hlen : σ.length = n := by simpa using hp.length_eq
    have hnd : σ.Nodup := hp.nodup_iff.mpr List.nodup_range
    set sg : ℕ → ℕ := fun i => σ.getD i 0 with hsgdef
    have hsg : ∀ i < n, sg i < n := fun i hi => by
      have hm : σ.getD i 0 ∈ σ := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      exact List.mem_range.1 (hp.subset hm)
    have hinj : ∀ i < n, ∀ j < n, sg i = sg j → i = j := by
      intro i hi j hj h
      simp only [sg, List.getD_eq_getElem _ _ (show i < σ.length by omega),
        List.getD_eq_getElem _ _ (show j < σ.length by omega)] at h
      exact (hnd.getElem_inj_iff).1 h
    set y : Str := (List.range (n * n)).map fun p => decide (sg (p / n) = p % n) with hy
    have hB : ∀ i < n, ∀ v, (hv_B n y i).getD v false = decide (v = sg i) := by
      intro i hi v
      rw [hv_B_bit]
      by_cases hv : v < n
      · have hp' : i * n + v < n * n := by nlinarith
        simp only [y, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp',
          Option.map_some, Option.getD_some]
        have hn0 : 0 < n := by omega
        rw [show (i * n + v) / n = i by
              rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn0, Nat.div_eq_of_lt hv]; simp,
            show (i * n + v) % n = v by
              rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]]
        simp [hv, eq_comm]
      · have := hsg i hi
        simp only [hv, decide_false, Bool.false_and]
        symm; simp only [decide_eq_false_iff_not]; omega
    refine ⟨y, ?_, fun i hi => ⟨?_, fun hi1 => ?_⟩⟩
    · simp only [y, List.length_map, List.length_range]
      have : n * n ≤ w.length * w.length := Nat.mul_le_mul hcl hcl
      nlinarith
    · rw [hv_permOk_iff]
      refine ⟨sg i, hB i hi, ?_⟩
      rcases h : (hv_Sacc n y i).getD (sg i) false
      · rfl
      · obtain ⟨i', hi', h'⟩ := (hv_Sacc_bit n y i (sg i)).1 h
        rw [hB i' (by omega), decide_eq_true_iff] at h'
        have := hinj i hi i' (by omega) h'
        omega
    · rw [hv_edgeB_iff]
      have ha := hadj i (by omega)
      rcases ha with ha | ha
      · exact ⟨sg i, sg (i + 1), ha, Or.inl ⟨by rw [hB i hi]; simp,
          by rw [hB _ hi1]; simp⟩⟩
      · exact ⟨sg (i + 1), sg i, ha, Or.inr ⟨by rw [hB _ hi1]; simp,
          by rw [hB i hi]; simp⟩⟩
  · rintro ⟨y, -, H⟩
    have hex : ∀ i, i < n → ∃ u, (∀ v, (hv_B n y i).getD v false = decide (v = u)) ∧
        (hv_Sacc n y i).getD u false = false := fun i hi => (hv_permOk_iff _ _).1 (H i hi).1
    choose! sg hsg1 hsg2 using hex
    have hlt : ∀ i < n, sg i < n := by
      intro i hi
      have := hsg1 i hi (sg i)
      rw [hv_B_bit] at this
      simp only [decide_true, Bool.and_eq_true, decide_eq_true_iff] at this
      exact this.1
    have hinj : ∀ i < n, ∀ j < n, sg i = sg j → i = j := by
      intro i hi j hj h
      by_contra hne
      wlog hij : j < i generalizing i j
      · exact this j hj i hi h.symm (Ne.symm hne) (by omega)
      have hb : (hv_B n y j).getD (sg i) false = true := by rw [hsg1 j hj, h]; simp
      have := (hv_Sacc_bit n y i (sg i)).2 ⟨j, hij, hb⟩
      rw [hsg2 i hi] at this
      exact absurd this (by simp)
    have hbit : ∀ i < n, ∀ v, (hv_B n y i).getD v false = true ↔ v = sg i := by
      intro i hi v; rw [hsg1 i hi]; simp
    refine ⟨(List.range n).map sg, ?_, ?_⟩
    · have hnd : ((List.range n).map sg).Nodup :=
        List.Nodup.map_on (fun a ha b hb h => hinj a (List.mem_range.1 ha) b
          (List.mem_range.1 hb) h) List.nodup_range
      have hsub : (List.range n).map sg ⊆ List.range n := by
        intro x hx
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        simpa using hlt a ha
      exact (List.subperm_of_subset hnd hsub).perm_of_length_le (by simp)
    · intro i hi
      simp only [List.length_map, List.length_range] at hi ⊢
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_map, List.getElem_range]
      obtain ⟨u, v, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := (hv_edgeB_iff _ _ _).1 ((H i (by omega)).2 hi)
      · rw [hbit i (by omega)] at h1; rw [hbit _ hi] at h2
        subst h1 h2
        exact Or.inl he
      · rw [hbit _ hi] at h1; rw [hbit i (by omega)] at h2
        subst h1 h2
        exact Or.inr he

/-! ## Transfer to the official class -/

/-- **HAMILTONIAN PATH ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem uhpath_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      UHPathLang := by
  classical
  have hrun := fun z => ((pv2_exec_ver z).mono (hv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg pv2_ver) (tb 11 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg pv2_ver, 11, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => pv2_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => pv2_vres w y = true, 2, hR, fun w => ?_⟩
  rw [uhpathLang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.Ham
