import Pnp.Karp.CliqueCoverVer
import Pnp.Karp.CliqueNP

/-!
# CLIQUE COVER ∈ NP (official definition)

The checking relation is `ccv_res w y = true` (`Pnp/Karp/CliqueCoverVer.lean`): with
`k = |kr|`, vertex `v` belongs to class `t < k` iff bit `v * k + t` of the certificate `y` is set
(`ccv_mem`, missing bits `false`).

* `ccv_res_iff`: the verifier accepts iff every vertex `i < n` has a class, and any vertex `j ≠ i`
  sharing a class with `i` has the entry `(i, j) = pos`;
* `ccv_lang_iff`: `CCLang w ↔ ∃ y, |y| ≤ |w|^2 ∧ ccv_res w y` (the class of `i` is its first set
  bit; conversely, `y` is the one-hot code of a class map);
* `cc_in_np`: `CCLang ∈ NP`, via `ccv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.CliqueCover

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics of the checks -/

theorem ccv_getD_cons_succ (b : Bool) (Y : Str) (t : ℕ) :
    (b :: Y).getD (t + 1) false = Y.getD t false := by simp

theorem ccv_hits_iff : ∀ (A Y : Str),
    ccv_hits A Y = true ↔ ∃ t < A.length, A.getD t false = true ∧ Y.getD t false = true
  | [], Y => by simp [ccv_hits]
  | a :: A, Y => by
    rw [ccv_hits, Bool.or_eq_true, Bool.and_eq_true, ccv_hits_iff A Y.tail]
    have e0 : Y.headD false = Y.getD 0 false := by rcases Y with _ | ⟨b, Y⟩ <;> simp
    have e1 : ∀ t, Y.tail.getD t false = Y.getD (t + 1) false := by
      intro t; rcases Y with _ | ⟨b, Y⟩ <;> simp
    simp only [e0, e1]
    constructor
    · rintro (⟨ha, hy⟩ | ⟨t, ht, h1, h2⟩)
      · exact ⟨0, by simp, by simpa using ha, hy⟩
      · exact ⟨t + 1, by simp; omega, by simpa using h1, h2⟩
    · rintro ⟨t, ht, h1, h2⟩
      rcases t with _ | t
      · exact Or.inl ⟨by simpa using h1, h2⟩
      · exact Or.inr ⟨t, by simp at ht; omega, by simpa using h1, h2⟩

theorem ccv_hits_nil (A : Str) : ccv_hits A [] = false := by
  cases h : ccv_hits A []
  · rfl
  · obtain ⟨t, -, -, h2⟩ := (ccv_hits_iff A []).1 h
    simp at h2

theorem ccv_drop_succ (Y : Str) (m L : ℕ) : (Y.drop L).drop (m * L) = Y.drop ((m + 1) * L) := by
  rw [List.drop_drop]; congr 1; ring

theorem ccv_rest_iff (A : Str) : ∀ (n : ℕ) (Y : Str), Y.length ≤ n →
    (ccv_rest A Y = true ↔ ∀ m, ccv_hits A (Y.drop (m * A.length)) = false)
  | n, [], _ => by simp [ccv_rest_nil, ccv_hits_nil]
  | 0, b :: Y, h => by simp at h
  | n + 1, b :: Y, hY => by
    by_cases hA : A = []
    · subst hA; rw [ccv_rest]; simp [ccv_hits]
    have hl : 0 < A.length := List.length_pos_of_ne_nil hA
    rw [ccv_rest_cons A hA, Bool.and_eq_true, Bool.not_eq_true',
      ccv_rest_iff A n _ (by simp only [List.length_drop, List.length_cons] at hY ⊢; omega)]
    simp only [ccv_drop_succ]
    constructor
    · rintro ⟨h0, h⟩ m
      rcases m with _ | m
      · simpa using h0
      · exact h m
    · intro h
      exact ⟨by simpa using h 0, fun m => h (m + 1)⟩

theorem ccv_rowOk_iff (A F : Str) : ∀ (r : List SatSym) (Y : Str),
    ccv_rowOk A F r Y = true ↔
      F ≠ [] ∧ ∀ j, ccv_hits A (Y.drop (j * A.length)) = true → r.getD j zero = pos
  | [], Y => by
    rw [ccv_rowOk, Bool.and_eq_true, ccv_rest_iff A Y.length Y le_rfl]
    simp
  | s :: r, Y => by
    rw [ccv_rowOk, Bool.and_eq_true, ccv_rowOk_iff A F r (Y.drop A.length)]
    simp only [ccv_drop_succ]
    constructor
    · rintro ⟨h0, hF, h⟩
      refine ⟨hF, fun j hj => ?_⟩
      rcases j with _ | j
      · simp only [Nat.zero_mul, List.drop_zero] at hj
        rw [hj] at h0
        cases s <;> simp_all [isPos]
      · simpa using h j hj
    · rintro ⟨hF, h⟩
      refine ⟨?_, hF, fun j hj => by simpa using h (j + 1) hj⟩
      cases hh : ccv_hits A Y
      · simp
      · have := h 0 (by simpa using hh)
        simp at this
        simp [this, isPos]

theorem ccv_fp_ne : ∀ (B F : Str), ccv_fp B F ≠ [] ↔ F ≠ [] ∨ true ∈ B
  | [], F => by simp [ccv_fp]
  | b :: B, F => by
    rw [ccv_fp, ccv_fp_ne B]
    cases b <;> simp

theorem ccv_blk_eq : ∀ (m : ℕ) (R : Str), ccv_blk m R = (List.range m).map (fun t => R.getD t false)
  | 0, R => rfl
  | m + 1, R => by
    rw [ccv_blk, ccv_blk_eq m R.tail, List.range_succ_eq_map, List.map_cons, List.map_map]
    rcases R with _ | ⟨b, R⟩
    · simp
    · simp only [List.headD_cons, List.getD_cons_zero, List.tail_cons]
      congr 1

theorem ccv_getD_map_range (m : ℕ) (g : ℕ → Bool) (t : ℕ) :
    ((List.range m).map g).getD t false = if t < m then g t else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_range h]; rfl
  · rw [List.getElem?_eq_none (by simpa using h)]; rfl

theorem ccv_getD_drop (Y : Str) (a t : ℕ) : (Y.drop a).getD t false = Y.getD (a + t) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Membership of vertex `v` in class `t`. -/
def ccv_mem (y : Str) (K v t : ℕ) : Prop := y.getD (v * K + t) false = true

/-- The certificate bits of the first `i` blocks. -/
def ccv_pfx (y : Str) (K i : ℕ) : Str := (List.range (i * K)).map (fun p => y.getD p false)

theorem ccv_getD_Y (y : Str) (K i p : ℕ) :
    (ccv_Y K (y.drop (i * K)) (ccv_pfx y K i).reverse).getD p false =
      if i * K ≤ p ∧ p < i * K + K then false else y.getD p false := by
  unfold ccv_Y
  rw [List.reverse_reverse, List.drop_drop, List.append_assoc]
  have hl : (ccv_pfx y K i).length = i * K := by simp [ccv_pfx]
  by_cases h1 : p < i * K
  · rw [List.getD_append _ _ _ _ (by omega), if_neg (by omega)]
    simp only [ccv_pfx, ccv_getD_map_range, if_pos h1]
  · rw [List.getD_append_right _ _ _ _ (by omega), hl]
    by_cases h2 : p < i * K + K
    · rw [List.getD_append _ _ _ _ (by simp; omega), if_pos ⟨by omega, h2⟩,
        List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by omega)]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by simp; omega), if_neg (by omega), ccv_getD_drop]
      congr 1; simp only [List.length_replicate]; omega

/-- The condition on row `v` (with entries `r`). -/
def ccv_cond (y : Str) (K v : ℕ) (r : List SatSym) : Prop :=
  (∃ t < K, ccv_mem y K v t) ∧
    ∀ j, j ≠ v → (∃ t < K, ccv_mem y K v t ∧ ccv_mem y K j t) → r.getD j zero = pos

theorem ccv_hits_row (y : Str) (K i j : ℕ) :
    ccv_hits (ccv_blk K (y.drop (i * K)))
        ((ccv_Y K (y.drop (i * K)) (ccv_pfx y K i).reverse).drop (j * K)) = true ↔
      j ≠ i ∧ ∃ t < K, ccv_mem y K i t ∧ ccv_mem y K j t := by
  rw [ccv_hits_iff]
  simp only [ccv_blk_eq, List.length_map, List.length_range, ccv_getD_map_range, ccv_getD_drop,
    ccv_getD_Y, ccv_mem]
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    rw [if_pos ht] at h1
    by_cases h3 : i * K ≤ j * K + t ∧ j * K + t < i * K + K
    · rw [if_pos h3] at h2; simp at h2
    · rw [if_neg h3] at h2
      exact ⟨fun e => h3 ⟨by subst e; omega, by subst e; omega⟩, t, ht, h1, h2⟩
  · rintro ⟨hji, t, ht, h1, h2⟩
    refine ⟨t, ht, by rw [if_pos ht]; exact h1, ?_⟩
    rw [if_neg]; · exact h2
    rintro ⟨h3, h4⟩
    rcases Nat.lt_or_gt_of_ne hji with h | h
    · have : (j + 1) * K ≤ i * K := Nat.mul_le_mul_right K h
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    · have : (i + 1) * K ≤ j * K := Nat.mul_le_mul_right K h
      rw [Nat.add_mul, Nat.one_mul] at this; omega

theorem ccv_go_iff (y : Str) (K : ℕ) : ∀ (rows : List (List SatSym)) (i : ℕ),
    ccv_go K rows (y.drop (i * K)) (ccv_pfx y K i).reverse = true ↔
      ∀ i' < rows.length, ccv_cond y K (i + i') (rows.getD i' [])
  | [], i => by simp [ccv_go]
  | r :: rows, i => by
    have eR : (y.drop (i * K)).drop K = y.drop ((i + 1) * K) := by
      rw [List.drop_drop]; congr 1; ring
    have eD : (ccv_blk K (y.drop (i * K))).reverse ++ (ccv_pfx y K i).reverse =
        (ccv_pfx y K (i + 1)).reverse := by
      rw [← List.reverse_append]; congr 1
      simp only [ccv_pfx, ccv_blk_eq, ccv_getD_drop]
      rw [show (i + 1) * K = i * K + K by ring, List.range_add, List.map_append, List.map_map]
      rfl
    rw [ccv_go, eR, eD, Bool.and_eq_true, ccv_go_iff y K rows (i + 1), ccv_rowOk_iff,
      ccv_fp_ne, ccv_length_blk]
    simp only [ccv_hits_row]
    simp only [ne_eq, not_true_eq_false, false_or, ccv_blk_eq, List.mem_map,
      List.mem_range, ccv_getD_drop]
    constructor
    · rintro ⟨⟨⟨t, ht, h1⟩, h2⟩, h3⟩ i' hi'
      rcases i' with _ | i'
      · refine ⟨⟨t, ht, by simpa [ccv_mem] using h1⟩, fun j hj hs => ?_⟩
        simpa using h2 j ⟨hj, hs⟩
      · have := h3 i' (by simp at hi'; omega)
        rwa [show i + 1 + i' = i + (i' + 1) by ring] at this
    · intro h
      obtain ⟨⟨t, ht, h1⟩, h2⟩ := h 0 (by simp)
      refine ⟨⟨⟨t, ht, by simpa [ccv_mem] using h1⟩, fun j ⟨hj, hs⟩ => by simpa using h2 j hj hs⟩,
        fun i' hi' => ?_⟩
      have := h (i' + 1) (by simp; omega)
      rwa [show i + (i' + 1) = i + 1 + i' by ring] at this

theorem ccv_res_iff (w : List SatSym) (y : Str) :
    ccv_res w y = true ↔ ∃ kr rows, clauses w = kr :: rows ∧
      ∀ i < rows.length, ccv_cond y kr.length i (rows.getD i []) := by
  unfold ccv_res
  rcases clauses w with _ | ⟨kr, rows⟩
  · simp
  · have := ccv_go_iff y kr.length rows 0
    simp only [Nat.zero_mul, List.drop_zero, ccv_pfx, List.range_zero, List.map_nil,
      List.reverse_nil, Nat.zero_add] at this
    simp [this]

/-! ## Short certificates -/

theorem ccv_lang_iff (w : List SatSym) :
    CCLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ ccv_res w y = true := by
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  unfold CCLang
  simp only [ccv_res_iff]
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · simp
  rw [hcw] at hsum
  simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
  have hr : rows.length ≤ w.length := by omega
  have hk : kr.length ≤ w.length := by omega
  have e : ∀ y : Str, (∃ kr' rows', kr :: rows = kr' :: rows' ∧
      ∀ i < rows'.length, ccv_cond y kr'.length i (rows'.getD i [])) ↔
      ∀ i < rows.length, ccv_cond y kr.length i (rows.getD i []) :=
    fun y => ⟨fun ⟨_, _, h, hp⟩ => by cases h; exact hp, fun hp => ⟨_, _, rfl, hp⟩⟩
  simp only [e]
  set K := kr.length
  constructor
  · rintro ⟨c, hc, hadj⟩
    let y : Str := (List.range (rows.length * K)).map fun p => decide (c (p / K) = p % K)
    have hy : ∀ v t, t < K → (ccv_mem y K v t ↔ v < rows.length ∧ c v = t) := by
      intro v t ht
      simp only [ccv_mem, y, ccv_getD_map_range]
      have e1 : (v * K + t) / K = v := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < K), Nat.div_eq_of_lt ht, Nat.zero_add]
      have e2 : (v * K + t) % K = t := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
      by_cases hv : v < rows.length
      · have : v * K + t < rows.length * K := by
          have := Nat.mul_le_mul_right K (show v + 1 ≤ rows.length by omega)
          rw [Nat.add_mul, Nat.one_mul] at this; omega
        rw [if_pos this, e1, e2]; simp [hv]
      · have : ¬ v * K + t < rows.length * K := by
          have := Nat.mul_le_mul_right K (show rows.length ≤ v by omega)
          omega
        rw [if_neg this]; simp [hv]
    refine ⟨y, ?_, fun i hi => ⟨⟨c i, hc i hi, (hy i (c i) (hc i hi)).2 ⟨hi, rfl⟩⟩, ?_⟩⟩
    · simp only [y, List.length_map, List.length_range, sq]
      exact Nat.mul_le_mul hr hk
    · rintro j hji ⟨t, ht, h1, h2⟩
      rw [hy i t ht] at h1; rw [hy j t ht] at h2
      exact hadj i hi j h2.1 (Ne.symm hji) (h1.2.trans h2.2.symm)
  · rintro ⟨y, -, h⟩
    classical
    let c : ℕ → ℕ := fun v => if hv : ∃ t, t < K ∧ ccv_mem y K v t then Nat.find hv else 0
    have hc : ∀ v, (∃ t < K, ccv_mem y K v t) → c v < K ∧ ccv_mem y K v (c v) := by
      intro v hv
      have hv' : ∃ t, t < K ∧ ccv_mem y K v t := hv
      simp only [c, dif_pos hv']
      exact Nat.find_spec hv'
    refine ⟨c, fun i hi => (hc i (h i hi).1).1, fun i hi j hj hij hcij => ?_⟩
    refine (h i hi).2 j (Ne.symm hij) ⟨c i, (hc i (h i hi).1).1, (hc i (h i hi).1).2, ?_⟩
    rw [hcij]; exact (hc j (h j hj).1).2

/-! ## Transfer to the official class -/

/-- **CLIQUE COVER ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem cc_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      CCLang := by
  classical
  have hrun := fun z => ((ccv_exec_ver z).mono (ccv_Tver_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg ccv_ver) (tb 6 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg ccv_ver, 6, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => ccv_res w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => ccv_res w y = true, 2, hR, fun w => ?_⟩
  rw [ccv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.CliqueCover
