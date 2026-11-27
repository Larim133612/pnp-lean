import Pnp.Karp.CliqueVer

/-!
# CLIQUE ∈ NP (official definition)

The checking relation is `vres w y = true` (`Pnp/Karp/CliqueVer.lean`): the certificate `y`
is the indicator list of the clique (`S = {i | y_i}`; every set bit must be a vertex index).

* `go_iff`: the verifier's main loop accepts iff the selected vertices are vertices, at least
  `k` of them, and pairwise adjacent;
* `cliqueLang_iff`: `CliqueLang w ↔ ∃ y, |y| ≤ |w| ∧ vres w y`;
* `clique_in_np`: `CliqueLang ∈ NP`, via `exec_verCmd` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.Clique

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

/-! ## Semantics of the checks -/

theorem allF_iff : ∀ Y : Str, allF Y = true ↔ ∀ j, Y.getD j false = false
  | [] => by simp [allF]
  | b :: Y => by
    rw [allF, Bool.and_eq_true, allF_iff Y]
    constructor
    · rintro ⟨hb, h⟩ j
      rcases j with _ | j
      · simpa using hb
      · simpa using h j
    · intro h
      exact ⟨by simpa using h 0, fun j => by simpa using h (j + 1)⟩

theorem checkRow_nil : ∀ r : List SatSym, checkRow r [] = true
  | [] => rfl
  | _ :: r => by rw [checkRow]; exact checkRow_nil r

theorem checkRow_iff : ∀ (r : List SatSym) (Y : Str),
    checkRow r Y = true ↔ ∀ j, Y.getD j false = true → r.getD j zero = pos
  | [], Y => by
    rw [checkRow, allF_iff]
    refine ⟨fun h j hj => (by rw [h j] at hj; cases hj), fun h j => ?_⟩
    by_contra hc
    have := h j (by simpa using hc)
    simp at this
  | s :: r, [] => by simp [checkRow_nil]
  | s :: r, c :: Y => by
    rw [checkRow, Bool.and_eq_true, checkRow_iff r Y]
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
      · have := h 0 (by simp); simp at this; subst this; rfl

/-- Number of set bits of `y` at positions `i₀, …, i₀ + n - 1`. -/
def cntI (y : Str) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i₀, n + 1 => (if y.getD i₀ false then 1 else 0) + cntI y (i₀ + 1) n

theorem cntI_succ (y : Str) : ∀ (n i₀ : ℕ),
    cntI y i₀ (n + 1) = cntI y i₀ n + (if y.getD (i₀ + n) false then 1 else 0)
  | 0, i₀ => by simp [cntI]
  | n + 1, i₀ => by
    rw [cntI, cntI_succ y n (i₀ + 1), cntI]
    rw [show i₀ + 1 + n = i₀ + (n + 1) by omega]; omega

theorem cntI_eq_zero (y : Str) : ∀ (n i₀ : ℕ), (∀ j, i₀ ≤ j → y.getD j false = false) →
    cntI y i₀ n = 0
  | 0, _, _ => rfl
  | n + 1, i₀, h => by
    rw [cntI, h i₀ le_rfl, cntI_eq_zero y n (i₀ + 1) (fun j hj => h j (by omega))]; rfl

theorem card_filter_eq_cntI (y : Str) : ∀ n : ℕ,
    ((Finset.range n).filter fun i => y.getD i false = true).card = cntI y 0 n
  | 0 => rfl
  | n + 1 => by
    rw [cntI_succ, ← card_filter_eq_cntI y n, Finset.range_add_one, Finset.filter_insert,
      Nat.zero_add]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl

/-- What the main loop checks, for the rows `i₀, i₀ + 1, …`. -/
def Good (K : ℕ) (y : Str) (rows : List (List SatSym)) (i₀ c : ℕ) : Prop :=
  (∀ j, i₀ ≤ j → y.getD j false = true → j < i₀ + rows.length) ∧
  K ≤ c + cntI y i₀ rows.length ∧
  ∀ i, i₀ ≤ i → i < i₀ + rows.length → y.getD i false = true →
    ∀ j, j ≠ i → y.getD j false = true → (rows.getD (i - i₀) []).getD j zero = pos

theorem go_nilR (K : ℕ) : ∀ (rows : List (List SatSym)) (Dn : Str) (c : ℕ),
    go K rows [] Dn c = decide (K ≤ c)
  | [], Dn, c => by simp [go, allF]
  | _ :: rows, Dn, c => by rw [go]; exact go_nilR K rows Dn c

theorem good_of_clear {K : ℕ} {y : Str} {rows : List (List SatSym)} {i₀ c : ℕ}
    (h : ∀ j, i₀ ≤ j → y.getD j false = false) : Good K y rows i₀ c ↔ K ≤ c := by
  unfold Good
  rw [cntI_eq_zero y _ _ h, Nat.add_zero]
  constructor
  · exact fun h => h.2.1
  · intro hK
    refine ⟨fun j hj hy => (by rw [h j hj] at hy; cases hy), hK, fun i hi _ hy => ?_⟩
    rw [h i hi] at hy; cases hy

theorem getD_append_right (D R : Str) (j : ℕ) (hj : D.length ≤ j) :
    (D ++ R).getD j false = R.getD (j - D.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hj]

theorem getD_append_left (D R : Str) (j : ℕ) (hj : j < D.length) :
    (D ++ R).getD j false = D.getD j false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem go_iff (K : ℕ) (y : Str) : ∀ (rows : List (List SatSym)) (R Dn : Str) (c i₀ : ℕ),
    Dn.reverse ++ R = y → Dn.length ≤ i₀ → (R ≠ [] → Dn.length = i₀) →
    (go K rows R Dn c = true ↔ Good K y rows i₀ c)
  | rows, [], Dn, c, i₀, hy, hl, _ => by
    rw [go_nilR, decide_eq_true_iff, good_of_clear]
    intro j hj
    rw [← hy, List.append_nil]
    exact List.getD_eq_default _ _ (by simp; omega)
  | [], b :: R, Dn, c, i₀, hy, _, he => by
    have hl := he (by simp)
    have hyj : ∀ j, i₀ ≤ j → y.getD j false = (b :: R).getD (j - i₀) false := by
      intro j hj; rw [← hy, getD_append_right _ _ _ (by simp; omega), List.length_reverse, hl]
    rw [go, Bool.and_eq_true, allF_iff, decide_eq_true_iff]
    unfold Good
    simp only [List.length_nil, Nat.add_zero, cntI]
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
    cases b
    · have ih := go_iff K y rows R (false :: Dn) c (i₀ + 1) (by simpa using hy) (by simp; omega)
        (fun _ => by simp; omega)
      rw [go, ih]
      unfold Good
      simp only [List.length_cons, cntI, hy0, Bool.false_eq_true, if_false, Nat.zero_add]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun j hj hyj' => ?_, by rw [show i₀ + 1 = i₀ + 1 from rfl] at h2; omega,
          fun i hi hi' hyi j hji hyj' => ?_⟩
        · rcases Nat.eq_or_lt_of_le hj with rfl | hj
          · rw [hy0] at hyj'; cases hyj'
          · have := h1 j hj hyj'; omega
        · rcases Nat.eq_or_lt_of_le hi with rfl | hi
          · rw [hy0] at hyi; cases hyi
          · have := h3 i hi (by omega) hyi j hji hyj'
            rwa [show i - (i₀ + 1) = (i - i₀) - 1 by omega,
              show (r :: rows).getD (i - i₀) [] = rows.getD (i - i₀ - 1) [] by
                rw [show i - i₀ = (i - i₀ - 1) + 1 by omega]; simp] at *
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun j hj hyj' => ?_, h2, fun i hi hi' hyi j hji hyj' => ?_⟩
        · have := h1 j (by omega) hyj'; omega
        · have := h3 i (by omega) (by omega) hyi j hji hyj'
          rwa [show (r :: rows).getD (i - i₀) [] = rows.getD (i - (i₀ + 1)) [] by
                rw [show i - i₀ = (i - (i₀ + 1)) + 1 by omega]; simp] at this
    · have ih := go_iff K y rows R (true :: Dn) (c + 1) (i₀ + 1) (by simpa using hy)
        (by simp; omega) (fun _ => by simp; omega)
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
      rw [go, Bool.and_eq_true, ih, checkRow_iff]
      simp only [hcol, Bool.and_eq_true, bne_iff_ne, ne_eq]
      unfold Good
      simp only [List.length_cons, cntI, hy0, if_true]
      constructor
      · rintro ⟨hr, h1, h2, h3⟩
        refine ⟨fun j hj hyj' => ?_, by omega, fun i hi hi' hyi j hji hyj' => ?_⟩
        · rcases Nat.eq_or_lt_of_le hj with rfl | hj
          · omega
          · have := h1 j hj hyj'; omega
        · rcases Nat.eq_or_lt_of_le hi with rfl | hi
          · simpa using hr j ⟨hyj', hji⟩
          · have := h3 i hi (by omega) hyi j hji hyj'
            rwa [show (r :: rows).getD (i - i₀) [] = rows.getD (i - (i₀ + 1)) [] by
                rw [show i - i₀ = (i - (i₀ + 1)) + 1 by omega]; simp]
      · rintro ⟨h1, h2, h3⟩
        refine ⟨fun j ⟨hyj', hji⟩ => by simpa using h3 i₀ le_rfl (by omega) hy0 j hji hyj',
          fun j hj hyj' => ?_, by omega, fun i hi hi' hyi j hji hyj' => ?_⟩
        · have := h1 j (by omega) hyj'; omega
        · have := h3 i (by omega) (by omega) hyi j hji hyj'
          rwa [show (r :: rows).getD (i - i₀) [] = rows.getD (i - (i₀ + 1)) [] by
                rw [show i - i₀ = (i - (i₀ + 1)) + 1 by omega]; simp] at this

/-! ## Short certificates -/

theorem vres_iff (w : List SatSym) (y : Str) :
    vres w y = true ↔ match clauses w with
      | [] => False
      | kr :: rows => Good kr.length y rows 0 0 := by
  unfold vres
  rcases clauses w with _ | ⟨kr, rows⟩
  · simp
  · exact go_iff kr.length y rows y [] 0 0 (by simp) le_rfl (fun _ => rfl)

theorem cliqueLang_iff (w : List SatSym) :
    CliqueLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ vres w y = true := by
  classical
  have hcl := length_clauses_le w
  unfold CliqueLang
  simp only [vres_iff]
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · simp
  · rw [hcw] at hcl
    simp only [List.length_cons] at hcl
    simp only [Good, Nat.zero_add, Nat.sub_zero, Nat.zero_le, true_implies]
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
      · rw [← card_filter_eq_cntI]
        refine hk.trans (Finset.card_le_card fun i hi => ?_)
        simp only [Finset.mem_filter, Finset.mem_range, hy, decide_eq_true_eq]
        exact ⟨hS i hi, hi⟩
      · rw [hy] at hyi hyj
        exact hadj i (by simpa using hyi) j (by simpa using hyj) (Ne.symm hji)
    · rintro ⟨y, -, h1, h2, h3⟩
      refine ⟨(Finset.range rows.length).filter fun i => y.getD i false = true, ?_, ?_, ?_⟩
      · rw [card_filter_eq_cntI]; exact h2
      · intro i hi; simpa using (Finset.mem_filter.1 hi).1
      · intro i hi j hj hij
        simp only [Finset.mem_filter, Finset.mem_range] at hi hj
        exact h3 i hi.1 hi.2 j (Ne.symm hij) hj.2

/-! ## Transfer to the official class -/

/-- **CLIQUE ∈ NP** for the official class `NP` (`Millennium.InNondeterministicPolynomialTime`). -/
theorem clique_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      CliqueLang := by
  classical
  have hrun := fun z => ((exec_verCmd z).mono (Tver_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg verCmd) (tb 6 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg verCmd, 6, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => vres w y = true, 1, hR, fun w => ?_⟩
  rw [cliqueLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.Clique
