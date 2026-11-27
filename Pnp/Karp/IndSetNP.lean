import Pnp.Karp.IndSetVer
import Pnp.Karp.CliqueNP

/-!
# INDEPENDENT SET ∈ NP (official definition)

The checking relation is `vresI false w y = true` (`Pnp/Karp/IndSetVer.lean`): the certificate
`y` is the indicator list of the independent set (`S = {i | y_i}`; every set bit must be a
vertex index).

* `goI_iff`: the verifier's main loop accepts iff the selected vertices are vertices, the count
  test holds (`finB`: at least `k` selected rows for `vc = false`, at most `k` unselected rows for
  `vc = true`), and no entry between two distinct selected vertices is `pos`;
* `inNP_of_vresI`: a language described by short certificates checked by `vresI vc` is in NP
  (shared with VERTEX COVER, `Pnp/Karp/VertexCover.lean`);
* `isLang_iff`, `is_in_np`: `ISLang ∈ NP`.
-/

namespace Pnp.Karp.IndSet

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics of the row check -/

theorem checkRowI_nil : ∀ r : List SatSym, checkRowI r [] = true
  | [] => rfl
  | _ :: r => by rw [checkRowI]; exact checkRowI_nil r

theorem checkRowI_iff : ∀ (r : List SatSym) (Y : Str),
    checkRowI r Y = true ↔ ∀ j, Y.getD j false = true → r.getD j zero ≠ pos
  | [], Y => by simp [checkRowI]
  | s :: r, [] => by simp [checkRowI_nil]
  | s :: r, c :: Y => by
    rw [checkRowI, Bool.and_eq_true, checkRowI_iff r Y]
    constructor
    · rintro ⟨h0, h⟩ j hj
      rcases j with _ | j
      · simp only [List.getD_cons_zero] at hj ⊢
        subst hj; cases s <;> simp_all [isPos]
      · simpa using h j (by simpa using hj)
    · intro h
      refine ⟨?_, fun j hj => by simpa using h (j + 1) (by simpa using hj)⟩
      cases c
      · rfl
      · have := h 0 (by simp); simp at this; cases s <;> simp_all [isPos]

/-! ## Counting -/

/-- Number of positions `i₀ ≤ i < i₀ + n` whose bit of `y` differs from `vc` (the selected rows
for `vc = false`, the unselected ones for `vc = true`). -/
def cntB (vc : Bool) (y : Str) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i₀, n + 1 => (if (y.getD i₀ false != vc) = true then 1 else 0) + cntB vc y (i₀ + 1) n

theorem cntB_succ (vc : Bool) (y : Str) : ∀ (n i₀ : ℕ),
    cntB vc y i₀ (n + 1) = cntB vc y i₀ n + (if (y.getD (i₀ + n) false != vc) = true then 1 else 0)
  | 0, i₀ => by simp [cntB]
  | n + 1, i₀ => by
    rw [cntB, cntB_succ vc y n (i₀ + 1), cntB]
    rw [show i₀ + 1 + n = i₀ + (n + 1) by omega]; omega

theorem cntB_clear (vc : Bool) (y : Str) : ∀ (n i₀ : ℕ), (∀ j, i₀ ≤ j → y.getD j false = false) →
    cntB vc y i₀ n = if vc then n else 0
  | 0, _, _ => by cases vc <;> rfl
  | n + 1, i₀, h => by
    rw [cntB, h i₀ le_rfl, cntB_clear vc y n (i₀ + 1) (fun j hj => h j (by omega))]
    cases vc <;> simp; omega

theorem card_filter_eq_cntB (vc : Bool) (y : Str) : ∀ n : ℕ,
    ((Finset.range n).filter fun i => (y.getD i false != vc) = true).card = cntB vc y 0 n
  | 0 => rfl
  | n + 1 => by
    rw [cntB_succ, ← card_filter_eq_cntB vc y n, Finset.range_add_one, Finset.filter_insert,
      Nat.zero_add]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

/-! ## The main loop -/

/-- What the main loop checks, for the rows `i₀, i₀ + 1, …`. -/
def Good (vc : Bool) (K : ℕ) (y : Str) (rows : List (List SatSym)) (i₀ c : ℕ) : Prop :=
  (∀ j, i₀ ≤ j → y.getD j false = true → j < i₀ + rows.length) ∧
  finB vc K (c + cntB vc y i₀ rows.length) = true ∧
  ∀ i, i₀ ≤ i → i < i₀ + rows.length → y.getD i false = true →
    ∀ j, j ≠ i → y.getD j false = true → (rows.getD (i - i₀) []).getD j zero ≠ pos

theorem goI_nilR (vc : Bool) (K : ℕ) : ∀ (rows : List (List SatSym)) (Dn : Str) (c : ℕ),
    goI vc K rows [] Dn c = finB vc K (c + if vc then rows.length else 0)
  | [], Dn, c => by cases vc <;> simp [goI, allF]
  | _ :: rows, Dn, c => by
    rw [goI, goI_nilR vc K rows Dn (inc vc c)]
    congr 1; cases vc <;> simp [inc]; omega

theorem good_of_clearI {vc : Bool} {K : ℕ} {y : Str} {rows : List (List SatSym)} {i₀ c : ℕ}
    (h : ∀ j, i₀ ≤ j → y.getD j false = false) :
    Good vc K y rows i₀ c ↔ finB vc K (c + if vc then rows.length else 0) = true := by
  unfold Good
  rw [cntB_clear vc y _ _ h]
  constructor
  · exact fun h => h.2.1
  · intro hK
    refine ⟨fun j hj hy => (by rw [h j hj] at hy; cases hy), hK, fun i hi _ hy => ?_⟩
    rw [h i hi] at hy; cases hy

theorem goI_iff (vc : Bool) (K : ℕ) (y : Str) : ∀ (rows : List (List SatSym)) (R Dn : Str)
    (c i₀ : ℕ), Dn.reverse ++ R = y → Dn.length ≤ i₀ → (R ≠ [] → Dn.length = i₀) →
    (goI vc K rows R Dn c = true ↔ Good vc K y rows i₀ c)
  | rows, [], Dn, c, i₀, hy, hl, _ => by
    rw [goI_nilR, good_of_clearI]
    intro j hj
    rw [← hy, List.append_nil]
    exact List.getD_eq_default _ _ (by simp; omega)
  | [], b :: R, Dn, c, i₀, hy, _, he => by
    have hl := he (by simp)
    have hyj : ∀ j, i₀ ≤ j → y.getD j false = (b :: R).getD (j - i₀) false := by
      intro j hj; rw [← hy, getD_append_right _ _ _ (by simp; omega), List.length_reverse, hl]
    rw [goI, Bool.and_eq_true, allF_iff]
    unfold Good
    simp only [List.length_nil, Nat.add_zero, cntB]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun j hj hyj' => ?_, h2, fun i hi hi' => absurd hi' (by omega)⟩
      rw [hyj j hj, h1] at hyj'; cases hyj'
    · rintro ⟨h1, h2, -⟩
      refine ⟨fun k => ?_, h2⟩
      have := hyj (i₀ + k) (by omega)
      rw [show i₀ + k - i₀ = k by omega] at this
      cases hk : (b :: R).getD k false
      · rfl
      · have := h1 (i₀ + k) (by omega) (by rw [this, hk]); omega
  | r :: rows, b :: R, Dn, c, i₀, hy, _, he => by
    have hl := he (by simp)
    have hyj : ∀ j, i₀ ≤ j → y.getD j false = (b :: R).getD (j - i₀) false := by
      intro j hj; rw [← hy, getD_append_right _ _ _ (by simp; omega), List.length_reverse, hl]
    have hy0 : y.getD i₀ false = b := by rw [hyj i₀ le_rfl]; simp
    have hrow : ∀ i, i₀ + 1 ≤ i → (r :: rows).getD (i - i₀) [] = rows.getD (i - (i₀ + 1)) [] := by
      intro i hi; rw [show i - i₀ = (i - (i₀ + 1)) + 1 by omega]; simp
    cases b
    · have ih := goI_iff vc K y rows R (false :: Dn) (inc vc c) (i₀ + 1) (by simpa using hy)
        (by simp; omega) (fun _ => by simp; omega)
      have hc : c + cntB vc y i₀ (rows.length + 1) = inc vc c + cntB vc y (i₀ + 1) rows.length := by
        rw [cntB, hy0]; cases vc <;> simp [inc]; omega
      rw [goI, ih]
      unfold Good
      simp only [List.length_cons]
      rw [hc]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun j hj hyj' => ?_, h2, fun i hi hi' hyi j hji hyj' => ?_⟩
        · rcases Nat.eq_or_lt_of_le hj with rfl | hj
          · rw [hy0] at hyj'; cases hyj'
          · have := h1 j hj hyj'; omega
        · rcases Nat.eq_or_lt_of_le hi with rfl | hi
          · rw [hy0] at hyi; cases hyi
          · rw [hrow i hi]; exact h3 i hi (by omega) hyi j hji hyj'
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun j hj hyj' => ?_, h2, fun i hi hi' hyi j hji hyj' => ?_⟩
        · have := h1 j (by omega) hyj'; omega
        · have := h3 i (by omega) (by omega) hyi j hji hyj'
          rwa [hrow i hi] at this
    · have ih := goI_iff vc K y rows R (true :: Dn) (inc (!vc) c) (i₀ + 1) (by simpa using hy)
        (by simp; omega) (fun _ => by simp; omega)
      have hc : c + cntB vc y i₀ (rows.length + 1) =
          inc (!vc) c + cntB vc y (i₀ + 1) rows.length := by
        rw [cntB, hy0]; cases vc <;> simp [inc]; omega
      have hcol : ∀ j, (Dn.reverse ++ false :: R).getD j false =
          (y.getD j false && j != i₀) := by
        intro j
        rcases lt_trichotomy j i₀ with h | rfl | h
        · rw [getD_append_left _ _ _ (by simp; omega), ← hy,
            getD_append_left _ _ _ (by simp; omega)]
          simp [Nat.ne_of_lt h]
        · rw [getD_append_right _ _ _ (by simp; omega), hy0]; simp [hl]
        · rw [getD_append_right _ _ _ (by simp; omega), hyj j h.le, List.length_reverse, hl]
          rw [show j - i₀ = (j - i₀ - 1) + 1 by omega]; simp [Nat.ne_of_gt h]
      rw [goI, Bool.and_eq_true, ih, checkRowI_iff]
      simp only [hcol, Bool.and_eq_true, bne_iff_ne, ne_eq]
      unfold Good
      simp only [List.length_cons]
      rw [hc]
      constructor
      · rintro ⟨hr, h1, h2, h3⟩
        refine ⟨fun j hj hyj' => ?_, h2, fun i hi hi' hyi j hji hyj' => ?_⟩
        · rcases Nat.eq_or_lt_of_le hj with rfl | hj
          · omega
          · have := h1 j hj hyj'; omega
        · rcases Nat.eq_or_lt_of_le hi with rfl | hi
          · simpa using hr j ⟨hyj', hji⟩
          · rw [hrow i hi]; exact h3 i hi (by omega) hyi j hji hyj'
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun j ⟨hyj', hji⟩ => by simpa using h3 i₀ le_rfl (by omega) hy0 j hji hyj',
          fun j hj hyj' => ?_, h2, fun i hi hi' hyi j hji hyj' => ?_⟩
        · have := h1 j (by omega) hyj'; omega
        · have := h3 i (by omega) (by omega) hyi j hji hyj'
          rwa [hrow i hi] at this

theorem vresI_iff (vc : Bool) (w : List SatSym) (y : Str) :
    vresI vc w y = true ↔ match clauses w with
      | [] => False
      | kr :: rows => Good vc kr.length y rows 0 0 := by
  unfold vresI
  rcases clauses w with _ | ⟨kr, rows⟩
  · simp
  · exact goI_iff vc kr.length y rows y [] 0 0 (by simp) le_rfl (fun _ => rfl)

/-! ## Transfer to the official class -/

/-- A language whose members are exactly the words with a certificate of length `≤ |w|`
accepted by `vresI vc` is in the official class `NP`. -/
theorem inNP_of_vresI (vc : Bool) (L : Millennium.Language (List SatSym))
    (hL : ∀ w, L w ↔ ∃ y : Str, y.length ≤ w.length ∧ vresI vc w y = true) :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym) L := by
  classical
  have hrun := fun z => ((exec_verCmdI vc z).mono (TverI_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg (verCmdI vc)) (tb 6 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg (verCmdI vc), 6, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => vresI vc w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => vresI vc w y = true, 1, hR, fun w => ?_⟩
  rw [hL]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

/-! ## Short certificates for INDEPENDENT SET -/

theorem isLang_iff (w : List SatSym) :
    ISLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ vresI false w y = true := by
  classical
  have hcl := length_clauses_le w
  unfold ISLang
  simp only [vresI_iff]
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · simp
  · rw [hcw] at hcl
    simp only [List.length_cons] at hcl
    have hcard : ∀ y : Str, cntB false y 0 rows.length =
        ((Finset.range rows.length).filter fun i => y.getD i false = true).card := by
      intro y; rw [← card_filter_eq_cntB]; simp
    simp only [Good, Nat.zero_add, Nat.sub_zero, Nat.zero_le, true_implies, finB,
      Bool.false_eq_true, if_false, decide_eq_true_eq, hcard]
    constructor
    · rintro ⟨S, hk, hS, hadj⟩
      let y : Str := (List.range rows.length).map fun i => decide (i ∈ S)
      have hy : ∀ i, y.getD i false = decide (i ∈ S) := by
        intro i
        by_cases hi : i < rows.length
        · simp [y, List.getD_eq_getElem?_getD, hi]
        · rw [List.getD_eq_default _ _ (by simp [y]; omega)]
          symm; simp only [decide_eq_false_iff_not]; exact fun h => hi (hS i h)
      refine ⟨y, by simp [y]; omega, fun j hj => ?_, ?_, fun i _ hyi j hji hyj => ?_⟩
      · rw [hy] at hj; exact hS j (by simpa using hj)
      · refine hk.trans (Finset.card_le_card fun i hi => ?_)
        simp only [Finset.mem_filter, Finset.mem_range, hy, decide_eq_true_eq]
        exact ⟨hS i hi, hi⟩
      · rw [hy] at hyi hyj
        exact hadj i (by simpa using hyi) j (by simpa using hyj) (Ne.symm hji)
    · rintro ⟨y, -, h1, h2, h3⟩
      refine ⟨(Finset.range rows.length).filter fun i => y.getD i false = true, h2, ?_, ?_⟩
      · intro i hi; simpa using (Finset.mem_filter.1 hi).1
      · intro i hi j hj hij
        simp only [Finset.mem_filter, Finset.mem_range] at hi hj
        exact h3 i hi.1 hi.2 j (Ne.symm hij) hj.2

/-- **INDEPENDENT SET ∈ NP** for the official class `NP`. -/
theorem is_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      ISLang :=
  inNP_of_vresI false ISLang isLang_iff

end Pnp.Karp.IndSet
