import Pnp.Karp.ColorVer
import Pnp.Karp.CliqueNP

/-!
# 3-COLORING ∈ NP (official definition)

The checking relation is `vresC w y = true` (`Pnp/Karp/ColorVer.lean`): the certificate `y`
gives vertex `v` the color `colAt y v` (bits `2v`, `2v + 1`, missing bits `false`).

* `goC_iff`: the verifier's main loop accepts iff every `pos` entry `(i, j)` joins differently
  colored vertices;
* `entry_lt`: a `pos` entry `(i, j)` of a word `w` has `i, j < |w| - 1`;
* `colLang_iff`: `ColLang w ↔ ∃ y, |y| ≤ |w|^2 ∧ vresC w y`;
* `col_in_np`: `ColLang ∈ NP`, via `exec_verC` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.Color

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics of the checks -/

/-- The color of vertex `v` under the certificate `y`. -/
def colAt (y : Str) (v : ℕ) : Fin 3 := toCol (y.getD (2 * v) false) (y.getD (2 * v + 1) false)

theorem hdC_eq (Y : Str) : hdC Y = colAt Y 0 := rfl

theorem getD_drop2 (Y : Str) (n : ℕ) : (Y.drop 2).getD n false = Y.getD (n + 2) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [Nat.add_comm]

theorem colAt_drop (Y : Str) (v : ℕ) : colAt (Y.drop 2) v = colAt Y (v + 1) := by
  unfold colAt
  rw [getD_drop2, getD_drop2]
  congr 2

theorem isPos_iff (s : SatSym) : isPos s = true ↔ s = pos := by
  cases s <;> simp [isPos]

theorem rowOk_iff (k : Fin 3) : ∀ (r : List SatSym) (Y : Str),
    rowOk k r Y = true ↔ ∀ j, r.getD j zero = pos → colAt Y j ≠ k
  | [], Y => by simp [rowOk]
  | s :: r, Y => by
    rw [rowOk, Bool.and_eq_true, rowOk_iff k r (Y.drop 2)]
    simp only [colAt_drop]
    constructor
    · rintro ⟨h0, h⟩ j hj
      rcases j with _ | j
      · simp only [List.getD_cons_zero] at hj
        subst hj
        intro e
        rw [← hdC_eq] at e
        simp [isPos, e] at h0
      · exact h j (by simpa using hj)
    · intro h
      refine ⟨?_, fun j hj => h (j + 1) (by simpa using hj)⟩
      cases hs : isPos s
      · rfl
      · have := h 0 (by simpa [isPos_iff] using hs)
        rw [← hdC_eq] at this
        simp [Ne.symm this]

theorem goC_iff (y : Str) : ∀ (rows : List (List SatSym)) (R : Str),
    goC y rows R = true ↔ ∀ i j, (rows.getD i []).getD j zero = pos → colAt y j ≠ colAt R i
  | [], R => by simp [goC]
  | r :: rows, R => by
    rw [goC, Bool.and_eq_true, rowOk_iff, goC_iff y rows (R.drop 2)]
    simp only [colAt_drop, hdC_eq]
    constructor
    · rintro ⟨h0, h⟩ i j hij
      rcases i with _ | i
      · exact h0 j (by simpa using hij)
      · exact h i j (by simpa using hij)
    · intro h
      exact ⟨fun j hj => h 0 j (by simpa using hj), fun i j hj => h (i + 1) j (by simpa using hj)⟩

theorem vresC_iff (w : List SatSym) (y : Str) :
    vresC w y = true ↔ ∀ i j, ((clauses w).getD i []).getD j zero = pos → colAt y j ≠ colAt y i :=
  goC_iff y (clauses w) y

/-! ## Short certificates -/

/-- A `pos` entry `(i, j)` has `i + 2 ≤ |w|` and `j + 2 ≤ |w|`. -/
theorem entry_lt (w : List SatSym) (i j : ℕ) (h : ((clauses w).getD i []).getD j zero = pos) :
    i + 2 ≤ w.length ∧ j + 2 ≤ w.length := by
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hi : i < (clauses w).length := by
    by_contra hc
    rw [List.getD_eq_default (clauses w) [] (by omega : (clauses w).length ≤ i)] at h
    simp at h
  have hmem : (clauses w).getD i [] ∈ clauses w := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hj : j < ((clauses w).getD i []).length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at h
    cases h
  have hle : ((clauses w).getD i []).length ≤ ((clauses w).map List.length).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hmem)
  omega

/-- Bits of a color. -/
def cbit (k : Fin 3) (p : ℕ) : Bool := if p = 0 then decide (k = 2) else decide (k = 1)

theorem toCol_cbit (k : Fin 3) : toCol (cbit k 0) (cbit k 1) = k := by
  fin_cases k <;> rfl

theorem colLang_iff (w : List SatSym) :
    ColLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ vresC w y = true := by
  unfold ColLang
  simp only [vresC_iff]
  constructor
  · rintro ⟨c, hc⟩
    let y : Str := (List.range (2 * (w.length - 1))).map fun p => cbit (c (p / 2)) (p % 2)
    have hy : ∀ v, v + 2 ≤ w.length → colAt y v = c v := by
      intro v hv
      have h1 : 2 * v < 2 * (w.length - 1) := by omega
      have h2 : 2 * v + 1 < 2 * (w.length - 1) := by omega
      simp only [colAt, y, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1,
        List.getElem?_range h2, Option.map_some, Option.getD_some]
      rw [show 2 * v / 2 = v by omega, show (2 * v + 1) / 2 = v by omega,
        show 2 * v % 2 = 0 by omega, show (2 * v + 1) % 2 = 1 by omega, toCol_cbit]
    refine ⟨y, ?_, fun i j hij => ?_⟩
    · simp only [y, List.length_map, List.length_range]
      rcases Nat.lt_or_ge w.length 2 with h | h
      · interval_cases w.length <;> simp
      · have : 2 * w.length ≤ w.length ^ 2 := by nlinarith
        omega
    · have hb := entry_lt w i j hij
      rw [hy i hb.1, hy j hb.2]
      exact Ne.symm (hc i j hij)
  · rintro ⟨y, -, h⟩
    exact ⟨colAt y, fun i j hij => Ne.symm (h i j hij)⟩

/-! ## Transfer to the official class -/

/-- **3-COLORING ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem col_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      ColLang := by
  classical
  have hrun := fun z => ((exec_verC z).mono (TverC_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg verC) (tb 6 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg verC, 6, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => vresC w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => vresC w y = true, 2, hR, fun w => ?_⟩
  rw [colLang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.Color
