import Pnp.Karp.HamVer
import Pnp.Karp.CliqueNP

/-!
# HAMILTONIAN CYCLE ∈ NP (official definition)

The checking relation is `hv_vres w y = true` (`Pnp/Karp/HamVer.lean`): with `n = |clauses w|`,
the certificate `y` is read as the blocks `B_i = hv_B n y i` of `n` bits, and the verifier
checks `n ≥ 3`, that every block has exactly one `true` bit, at a position no earlier block
has (`hv_permOk` against the union `hv_Sacc` of the earlier blocks), and that consecutive
blocks (cyclically) are joined by a `pos` entry (`hv_edgeB`).

* `hv_vres_iff`: this characterization of `hv_vres`;
* `uhamLang_iff`: `UHamLang w ↔ ∃ y, |y| ≤ |w|^2 ∧ hv_vres w y`;
* `uham_in_np`: `UHamLang ∈ NP`, via `hv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.Ham

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Bits -/

theorem hv_getD_cons_succ (b : Bool) (X : Str) (u : ℕ) :
    (b :: X).getD (u + 1) false = X.getD u false := by simp

theorem hv_getD_tail (X : Str) (u : ℕ) : X.tail.getD u false = X.getD (u + 1) false := by
  cases X <;> simp

theorem hv_getD_tk : ∀ (k : ℕ) (L : Str) (u : ℕ),
    (hv_tk k L).getD u false = (decide (u < k) && L.getD u false)
  | 0, L, u => by simp [hv_tk]
  | k + 1, L, 0 => by cases L <;> simp [hv_tk]
  | k + 1, L, u + 1 => by
    rw [hv_tk, hv_getD_cons_succ, hv_getD_tk k L.tail u, hv_getD_tail]
    simp

theorem hv_getD_orV : ∀ (X S : Str) (u : ℕ),
    (hv_orV X S).getD u false = (decide (u < X.length) && (X.getD u false || S.getD u false))
  | [], S, u => by simp [hv_orV]
  | x :: X, S, 0 => by cases S <;> simp [hv_orV]
  | x :: X, S, u + 1 => by
    rw [hv_orV, hv_getD_cons_succ, hv_getD_orV X S.tail u, hv_getD_tail]
    simp

theorem hv_tk_tk : ∀ (k : ℕ) (L : Str), hv_tk k (hv_tk k L) = hv_tk k L
  | 0, _ => rfl
  | k + 1, L => by
    simp only [hv_tk, List.headD_cons, List.tail_cons]
    rw [hv_tk_tk k L.tail]

/-! ## The block checks -/

theorem hv_zok_true : ∀ (X S : Str), hv_zok X S true = true ↔ ∀ v, X.getD v false = false
  | [], S => by simp [hv_zok]
  | false :: X, S => by
    rw [hv_zok, hv_zok_true X S.tail]
    constructor
    · intro h v; cases v
      · rfl
      · rw [List.getD_cons_succ]; exact h _
    · intro h v; have := h (v + 1); rwa [List.getD_cons_succ] at this
  | true :: X, S => by
    simp only [hv_zok, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true,
      false_iff, not_forall]
    exact ⟨0, by simp⟩

theorem hv_permOk_iff : ∀ (X S : Str), hv_permOk X S = true ↔
    ∃ u, (∀ v, X.getD v false = decide (v = u)) ∧ S.getD u false = false
  | [], S => by
    simp only [hv_permOk, hv_zok, hv_anyT, Bool.and_false, Bool.false_eq_true, false_iff,
      not_exists, not_and]
    intro u h; simpa using h u
  | false :: X, S => by
    have ih := hv_permOk_iff X S.tail
    simp only [hv_permOk] at ih
    simp only [hv_permOk, hv_zok, hv_anyT, Bool.false_or, ih]
    constructor
    · rintro ⟨u, h1, h2⟩
      refine ⟨u + 1, fun v => ?_, by rwa [hv_getD_tail] at h2⟩
      cases v
      · simp
      · rw [List.getD_cons_succ, h1]; simp
    · rintro ⟨u, h1, h2⟩
      rcases u with _ | u
      · simpa using h1 0
      · refine ⟨u, fun v => ?_, by rwa [hv_getD_tail]⟩
        have := h1 (v + 1); rw [List.getD_cons_succ] at this; rw [this]; simp
  | true :: X, S => by
    simp only [hv_permOk, hv_zok, hv_anyT, Bool.true_or, Bool.and_true, Bool.not_false,
      Bool.and_true, Bool.and_eq_true, Bool.not_eq_true', hv_zok_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨0, fun v => ?_, by cases S <;> simp_all⟩
      cases v
      · rfl
      · rw [List.getD_cons_succ, h2]; simp
    · rintro ⟨u, h1, h2⟩
      have hu : u = 0 := by have := h1 0; simp at this; omega
      subst hu
      refine ⟨by cases S <;> simp_all, fun v => ?_⟩
      have := h1 (v + 1); rw [List.getD_cons_succ] at this; rw [this]; simp

theorem hv_anyHit_iff : ∀ (r : List SatSym) (C : Str),
    hv_anyHit r C = true ↔ ∃ v, r.getD v zero = pos ∧ C.getD v false = true
  | [], C => by simp [hv_anyHit]
  | x :: r, C => by
    rw [hv_anyHit, Bool.or_eq_true, hv_anyHit_iff r C.tail]
    constructor
    · rintro (h | ⟨v, h1, h2⟩)
      · refine ⟨0, ?_, ?_⟩
        · simp only [Bool.and_eq_true] at h
          have := h.1; cases x <;> simp_all [isPos]
        · simp only [Bool.and_eq_true] at h
          cases C <;> simp_all
      · exact ⟨v + 1, by simpa using h1, by rwa [hv_getD_tail] at h2⟩
    · rintro ⟨v, h1, h2⟩
      rcases v with _ | v
      · left
        simp only [List.getD_cons_zero] at h1
        subst h1
        cases C <;> simp_all [isPos]
      · right; exact ⟨v, by simpa using h1, by rwa [hv_getD_tail]⟩

theorem hv_goS_iff (C : Str) : ∀ (rows : List (List SatSym)) (RF : Str),
    hv_goS C rows RF = true ↔ ∃ u v, RF.getD u false = true ∧ C.getD v false = true ∧
      (rows.getD u []).getD v zero = pos
  | [], RF => by simp [hv_goS]
  | r :: rows, RF => by
    rw [hv_goS, Bool.or_eq_true, hv_goS_iff C rows RF.tail, Bool.and_eq_true, hv_anyHit_iff]
    constructor
    · rintro (⟨h1, v, h2, h3⟩ | ⟨u, v, h1, h2, h3⟩)
      · exact ⟨0, v, by cases RF <;> simp_all, h3, by simpa using h2⟩
      · exact ⟨u + 1, v, by rwa [hv_getD_tail] at h1, h2, by simpa using h3⟩
    · rintro ⟨u, v, h1, h2, h3⟩
      rcases u with _ | u
      · left; exact ⟨by cases RF <;> simp_all, v, by simpa using h3, h2⟩
      · right; exact ⟨u, v, by rwa [hv_getD_tail], h2, by simpa using h3⟩

theorem hv_edgeB_iff (rows : List (List SatSym)) (X Y : Str) :
    hv_edgeB rows X Y = true ↔ ∃ u v, (rows.getD u []).getD v zero = pos ∧
      ((X.getD u false = true ∧ Y.getD v false = true) ∨
        (Y.getD u false = true ∧ X.getD v false = true)) := by
  rw [hv_edgeB, Bool.or_eq_true, hv_goS_iff, hv_goS_iff]
  constructor
  · rintro (⟨u, v, h1, h2, h3⟩ | ⟨u, v, h1, h2, h3⟩)
    · exact ⟨u, v, h3, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨u, v, h3, Or.inr ⟨h1, h2⟩⟩
  · rintro ⟨u, v, h3, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Or.inl ⟨u, v, h1, h2, h3⟩
    · exact Or.inr ⟨u, v, h1, h2, h3⟩

/-! ## Blocks -/

/-- Block `i` of the certificate. -/
def hv_B (n : ℕ) (y : Str) (i : ℕ) : Str := hv_tk n (y.drop (i * n))

/-- The union of the first `i` blocks. -/
def hv_Sacc (n : ℕ) (y : Str) : ℕ → Str
  | 0 => List.replicate n false
  | i + 1 => hv_orV (hv_B n y i) (hv_Sacc n y i)

theorem hv_length_B (n : ℕ) (y : Str) (i : ℕ) : (hv_B n y i).length = n := hv_length_tk _ _

theorem hv_B_bit (n : ℕ) (y : Str) (i u : ℕ) :
    (hv_B n y i).getD u false = (decide (u < n) && y.getD (i * n + u) false) := by
  rw [hv_B, hv_getD_tk]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem hv_Sacc_bit (n : ℕ) (y : Str) : ∀ (i u : ℕ),
    (hv_Sacc n y i).getD u false = true ↔ ∃ i' < i, (hv_B n y i').getD u false = true
  | 0, u => by
    simp only [hv_Sacc, Nat.not_lt_zero, false_and, exists_false, iff_false]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> simp
  | i + 1, u => by
    rw [hv_Sacc, hv_getD_orV, hv_length_B, Bool.and_eq_true, Bool.or_eq_true, hv_Sacc_bit n y i u]
    constructor
    · rintro ⟨-, h | ⟨i', hi', h⟩⟩
      · exact ⟨i, by omega, h⟩
      · exact ⟨i', by omega, h⟩
    · rintro ⟨i', hi', h⟩
      have hu : u < n := by
        rw [hv_B_bit, Bool.and_eq_true, decide_eq_true_iff] at h; exact h.1
      refine ⟨by simpa using hu, ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h' | rfl
      · exact Or.inr ⟨i', h', h⟩
      · exact Or.inl h

theorem hv_mainF_iff (rows : List (List SatSym)) (n : ℕ) (y Z : Str) : ∀ (k j : ℕ),
    hv_mainF rows n Z k (y.drop ((j + 1) * n)) (hv_B n y j) (hv_Sacc n y j) = true ↔
      ∀ i, j ≤ i → i ≤ j + k → hv_permOk (hv_B n y i) (hv_Sacc n y i) = true ∧
        hv_edgeB rows (hv_B n y i) (if i = j + k then hv_tk n Z else hv_B n y (i + 1)) = true
  | 0, j => by
    rw [hv_mainF, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩ i hi1 hi2
      obtain rfl : i = j := by omega
      exact ⟨h1, by simpa using h2⟩
    · intro h
      have := h j le_rfl (by omega)
      exact ⟨this.1, by simpa using this.2⟩
  | k + 1, j => by
    have ih := hv_mainF_iff rows n y Z k (j + 1)
    have e1 : (y.drop ((j + 1) * n)).drop n = y.drop ((j + 1 + 1) * n) := by
      rw [List.drop_drop]; congr 1; ring
    have e2 : hv_tk n (y.drop ((j + 1) * n)) = hv_B n y (j + 1) := rfl
    have e3 : hv_orV (hv_B n y j) (hv_Sacc n y j) = hv_Sacc n y (j + 1) := rfl
    rw [hv_mainF, e1, e2, e3, Bool.and_eq_true, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ i hi1 hi2
      rcases Nat.eq_or_lt_of_le hi1 with rfl | hi1
      · exact ⟨h1, by rw [if_neg (by omega)]; exact h2⟩
      · have := h3 i (by omega) (by omega)
        refine ⟨this.1, ?_⟩
        have e : (i = j + 1 + k) ↔ (i = j + (k + 1)) := by omega
        simpa only [e] using this.2
    · intro h
      have h0 := h j le_rfl (by omega)
      rw [if_neg (by omega)] at h0
      refine ⟨h0, fun i hi1 hi2 => ?_⟩
      have := h i (by omega) (by omega)
      refine ⟨this.1, ?_⟩
      have e : (i = j + 1 + k) ↔ (i = j + (k + 1)) := by omega
      simpa only [e] using this.2

theorem hv_vres_iff (w : List SatSym) (y : Str) :
    hv_vres w y = true ↔ 3 ≤ (clauses w).length ∧ ∀ i < (clauses w).length,
      hv_permOk (hv_B (clauses w).length y i) (hv_Sacc (clauses w).length y i) = true ∧
      hv_edgeB (clauses w) (hv_B (clauses w).length y i)
        (hv_B (clauses w).length y ((i + 1) % (clauses w).length)) = true := by
  set n := (clauses w).length
  unfold hv_vres
  rw [Bool.and_eq_true, decide_eq_true_iff]
  refine and_congr_right fun hn => ?_
  have h := hv_mainF_iff (clauses w) n y (hv_tk n y) (n - 1) 0
  have e0 : hv_B n y 0 = hv_tk n y := by simp [hv_B]
  have eS : hv_Sacc n y 0 = List.replicate n false := rfl
  rw [e0, eS, show (0 + 1) * n = n by ring, hv_tk_tk] at h
  rw [h]
  constructor
  · intro H i hi
    have := H i (by omega) (by omega)
    refine ⟨by simpa [e0] using this.1, ?_⟩
    by_cases hl : i = n - 1
    · rw [if_pos (by omega)] at this
      rw [show (i + 1) % n = 0 by rw [show i + 1 = n by omega, Nat.mod_self], e0]
      simpa [e0] using this.2
    · rw [if_neg (by omega)] at this
      rw [Nat.mod_eq_of_lt (by omega)]
      simpa [e0] using this.2
  · intro H i _ hi
    have := H i (by omega)
    refine ⟨by simpa [e0] using this.1, ?_⟩
    by_cases hl : i = n - 1
    · rw [if_pos (by omega)]
      rw [show (i + 1) % n = 0 by rw [show i + 1 = n by omega, Nat.mod_self], e0] at this
      simpa [e0] using this.2
    · rw [if_neg (by omega)]
      rw [Nat.mod_eq_of_lt (by omega)] at this
      simpa [e0] using this.2

/-! ## Short certificates -/

theorem uhamLang_iff (w : List SatSym) :
    UHamLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ hv_vres w y = true := by
  have hcl := length_clauses_le w
  unfold UHamLang IsHamCycle
  simp only [hv_vres_iff]
  set n := (clauses w).length
  constructor
  · rintro ⟨hn, σ, hp, hadj⟩
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
    refine ⟨y, ?_, hn, fun i hi => ⟨?_, ?_⟩⟩
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
      rw [hlen] at ha
      have hj : (i + 1) % n < n := Nat.mod_lt _ (by omega)
      rcases ha with ha | ha
      · exact ⟨sg i, sg ((i + 1) % n), ha, Or.inl ⟨by rw [hB i hi]; simp,
          by rw [hB _ hj]; simp⟩⟩
      · exact ⟨sg ((i + 1) % n), sg i, ha, Or.inr ⟨by rw [hB _ hj]; simp,
          by rw [hB i hi]; simp⟩⟩
  · rintro ⟨y, -, hn, H⟩
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
    refine ⟨hn, (List.range n).map sg, ?_, ?_⟩
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
      have hj : (i + 1) % n < n := Nat.mod_lt _ (by omega)
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hj)]
      simp only [List.getElem_map, List.getElem_range]
      obtain ⟨u, v, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := (hv_edgeB_iff _ _ _).1 (H i hi).2
      · rw [hbit i hi] at h1; rw [hbit _ hj] at h2
        subst h1 h2
        exact Or.inl he
      · rw [hbit _ hj] at h1; rw [hbit i hi] at h2
        subst h1 h2
        exact Or.inr he

/-! ## Transfer to the official class -/

/-- **HAMILTONIAN CYCLE ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem uham_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      UHamLang := by
  classical
  have hrun := fun z => ((hv_exec_ver z).mono (hv_Tver_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg hv_ver) (tb 11 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg hv_ver, 11, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => hv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => hv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [uhamLang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.Ham
