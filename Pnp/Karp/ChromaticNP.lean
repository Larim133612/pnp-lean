import Pnp.Karp.ChromaticVer
import Pnp.Karp.ColorNP

/-!
# CHROMATIC NUMBER (k-COLORING) ∈ NP (official definition)

The checking relation is `kcv_vres w y = true` (`Pnp/Karp/ChromaticVer.lean`): with
`clauses w = kr :: rows` and `K = |kr|`, vertex `i` owns the `K` certificate bits
`y[iK + p]`, `p < K` (missing bits `false`); every vertex `i < |rows|` needs a set bit, and the
two ends of a `pos` entry `(i, j)` must not share a set bit at the same offset `p`.
The color of `i` is the offset of its first set bit.

* `kcv_go_iff`, `kcv_rowOk_iff`, `kcv_meet_blk`, `kcv_cnt_pos`: semantics of the main loop;
* `kcv_kcol_iff`: `KColLang w ↔ ∃ y, |y| ≤ |w|^2 ∧ kcv_vres w y`;
* `kcol_in_np`: `KColLang ∈ NP`, via `kcv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.Chromatic

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics of the checks -/

theorem kcv_headD (R : Str) : R.headD false = R.getD 0 false := by cases R <;> rfl

theorem kcv_getD_tail (R : Str) (p : ℕ) : R.tail.getD p false = R.getD (p + 1) false := by
  cases R <;> simp

theorem kcv_getD_drop (y : Str) (n p : ℕ) : (y.drop n).getD p false = y.getD (n + p) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem kcv_meet_blk : ∀ (K : ℕ) (R Y : Str), kcv_meet (kcv_blk K R) Y = true ↔
    ∃ p, p < K ∧ R.getD p false = true ∧ Y.getD p false = true
  | 0, R, Y => by simp [kcv_blk, kcv_meet]
  | K + 1, R, Y => by
    rw [kcv_blk, kcv_meet, Bool.or_eq_true, Bool.and_eq_true, kcv_meet_blk K R.tail Y.tail,
      kcv_headD, kcv_headD]
    simp only [kcv_getD_tail]
    constructor
    · rintro (h | ⟨p, hp, h⟩)
      · exact ⟨0, by omega, h⟩
      · exact ⟨p + 1, by omega, h⟩
    · rintro ⟨p, hp, h⟩
      rcases p with _ | p
      · exact Or.inl h
      · exact Or.inr ⟨p, by omega, h⟩

theorem kcv_cnt_pos : ∀ (K : ℕ) (R : Str),
    0 < kcv_cnt K R ↔ ∃ p, p < K ∧ R.getD p false = true
  | 0, R => by simp [kcv_cnt]
  | K + 1, R => by
    have ih := kcv_cnt_pos K R.tail
    simp only [kcv_getD_tail] at ih
    simp only [kcv_cnt, kcv_headD]
    constructor
    · intro h
      by_cases h0 : R.getD 0 false = true
      · exact ⟨0, by omega, h0⟩
      · rw [if_neg h0] at h
        obtain ⟨p, hp, h⟩ := ih.1 (by omega)
        exact ⟨p + 1, by omega, h⟩
    · rintro ⟨p, hp, h⟩
      rcases p with _ | p
      · rw [if_pos h]; omega
      · have := ih.2 ⟨p, by omega, h⟩; omega

theorem kcv_rowOk_iff (B : Str) : ∀ (r : List SatSym) (Y : Str),
    kcv_rowOk B r Y = true ↔
      ∀ j, r.getD j zero = pos → kcv_meet B (Y.drop (j * B.length)) = false
  | [], Y => by simp [kcv_rowOk]
  | s :: r, Y => by
    rw [kcv_rowOk, Bool.and_eq_true, kcv_rowOk_iff B r (Y.drop B.length)]
    simp only [List.drop_drop]
    constructor
    · rintro ⟨h0, h⟩ j hj
      rcases j with _ | j
      · simp only [List.getD_cons_zero] at hj
        subst hj
        simpa [isPos] using h0
      · have := h j (by simpa using hj)
        rwa [show B.length + j * B.length = (j + 1) * B.length by ring] at this
    · intro h
      refine ⟨?_, fun j hj => ?_⟩
      · cases hs : isPos s
        · simp
        · have := h 0 (by simpa [Color.isPos_iff] using hs)
          simpa using this
      · have := h (j + 1) (by simpa using hj)
        rwa [show B.length + j * B.length = (j + 1) * B.length by ring]

theorem kcv_go_iff (K : ℕ) (y : Str) : ∀ (rows : List (List SatSym)) (R : Str),
    kcv_go K y rows R = true ↔ ∀ i < rows.length,
      kcv_rowOk (kcv_blk K (R.drop (i * K))) (rows.getD i []) y = true ∧
        0 < kcv_cnt K (R.drop (i * K))
  | [], R => by simp [kcv_go]
  | r :: rows, R => by
    rw [kcv_go, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff,
      kcv_go_iff K y rows (R.drop K)]
    simp only [List.drop_drop]
    constructor
    · rintro ⟨⟨h1, h2⟩, h⟩ i hi
      rcases i with _ | i
      · simpa using And.intro h1 h2
      · have := h i (by simpa using hi)
        rwa [show K + i * K = (i + 1) * K by ring] at this
    · intro h
      refine ⟨⟨?_, ?_⟩, fun i hi => ?_⟩
      · simpa using (h 0 (by simp)).1
      · simpa using (h 0 (by simp)).2
      · have := h (i + 1) (by simpa using hi)
        rwa [show K + i * K = (i + 1) * K by ring]

/-! ## Short certificates -/

theorem kcv_kcol_iff (w : List SatSym) :
    KColLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ kcv_vres w y = true := by
  unfold KColLang kcv_vres
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · simp
  · rw [hcw] at hsum
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    simp only [kcv_go_iff, kcv_rowOk_iff, kcv_blk_length, Bool.eq_false_iff, ne_eq,
      kcv_meet_blk, kcv_cnt_pos, kcv_getD_drop]
    constructor
    · rintro ⟨c, hcK, hc⟩
      let y : Str := (List.range (rows.length * kr.length)).map
        fun q => decide (c (q / kr.length) = q % kr.length)
      have hy : ∀ i p, p < kr.length →
          (y.getD (i * kr.length + p) false = true ↔ i < rows.length ∧ c i = p) := by
        intro i p hp
        have hK0 : 0 < kr.length := by omega
        have e1 : (i * kr.length + p) / kr.length = i := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK0, Nat.div_eq_of_lt hp, Nat.zero_add]
        have e2 : (i * kr.length + p) % kr.length = p := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
        by_cases hi : i < rows.length
        · have hq : i * kr.length + p < rows.length * kr.length := by
            have : (i + 1) * kr.length ≤ rows.length * kr.length :=
              Nat.mul_le_mul_right _ (by omega)
            rw [Nat.add_mul] at this; omega
          simp only [y, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
            Option.map_some, Option.getD_some, e1, e2, decide_eq_true_eq]
          simp [hi]
        · have hq : rows.length * kr.length ≤ i * kr.length + p := by
            have : rows.length * kr.length ≤ i * kr.length := Nat.mul_le_mul_right _ (by omega)
            omega
          have hn : (List.range (rows.length * kr.length))[i * kr.length + p]? = none :=
            List.getElem?_eq_none (by simpa using hq)
          simp only [y, List.getD_eq_getElem?_getD, List.getElem?_map, hn]
          simp [hi]
      refine ⟨y, ?_, fun i hi => ⟨fun j hj => ?_, ?_⟩⟩
      · simp only [y, List.length_map, List.length_range]
        have h1 : rows.length ≤ w.length := by omega
        have h2 : kr.length ≤ w.length := by omega
        rw [pow_two]; exact Nat.mul_le_mul h1 h2
      · rintro ⟨p, hp, h1, h2⟩
        obtain ⟨-, e1⟩ := (hy i p hp).1 h1
        obtain ⟨hj', e2⟩ := (hy j p hp).1 h2
        exact hc i hi j hj' hj (e1.trans e2.symm)
      · exact ⟨c i, hcK i hi, (hy i (c i) (hcK i hi)).2 ⟨hi, rfl⟩⟩
    · rintro ⟨y, -, h⟩
      classical
      let c : ℕ → ℕ := fun i =>
        if hx : ∃ p, p < kr.length ∧ y.getD (i * kr.length + p) false = true then Nat.find hx
        else 0
      have hcs : ∀ i < rows.length,
          c i < kr.length ∧ y.getD (i * kr.length + c i) false = true := by
        intro i hi
        have hx := (h i hi).2
        simp only [c, dif_pos hx]
        exact Nat.find_spec hx
      refine ⟨c, fun i hi => (hcs i hi).1, fun i hi j hj hij heq => ?_⟩
      exact (h i hi).1 j hij ⟨c i, (hcs i hi).1, (hcs i hi).2, by rw [heq]; exact (hcs j hj).2⟩

/-! ## Transfer to the official class -/

/-- **CHROMATIC NUMBER (k-COLORING) ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem kcol_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      KColLang := by
  classical
  have hrun := fun z => ((kcv_exec_ver z).mono (kcv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg kcv_ver) (tb 7 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg kcv_ver, 7, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => kcv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => kcv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [kcv_kcol_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.Chromatic
