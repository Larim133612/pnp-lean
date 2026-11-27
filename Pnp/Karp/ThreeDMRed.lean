import Pnp.Karp.ThreeDM
import Pnp.Karp.SubComb

/-!
# 3DM / X3C: the instances `DMI w`, `X3I w` reduce to abstract covering by the triples `tris w`
-/

namespace Pnp.Karp.ThreeDM

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum

/-! ## Bounds on the triples -/

theorem dr_mik {N m i k : ℕ} (hi : i < N) (hk : k < m) : m * i + k < N * m := by
  have : m * (i + 1) ≤ m * N := Nat.mul_le_mul_left m hi
  rw [Nat.mul_comm N m]; rw [Nat.mul_succ] at this; omega

theorem dr_tip_lt {N m i k : ℕ} (v : Bool) (hi : i < N) (hk : k < m) :
    tipI m i k v < 2 * N * m := by
  have := dr_mik hi hk
  unfold tipI; rw [Nat.mul_assoc]; split <;> omega

theorem dr_tris_lt (w : List SatSym) :
    ∀ t ∈ tris w, t.1 < qB w ∧ t.2.1 < qB w ∧ t.2.2 < qB w := by
  intro t ht
  have hN : 1 ≤ NV w := by unfold NV; omega
  have hq : qB w = 2 * (NV w * mC w) := by unfold qB; rw [Nat.mul_assoc]
  simp only [tris, List.mem_append, List.mem_flatMap, List.mem_range] at ht
  rcases ht with (⟨i, hi, k, hk, ht⟩ | ⟨k, hk, j, hj, ht⟩) | ⟨x, hx, ht⟩
  · have h1 := dr_mik hi hk
    have hk' : (k + 1) % mC w < mC w := Nat.mod_lt _ (by omega)
    have h2 := dr_mik hi hk'
    simp only [ringT, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    all_goals exact ⟨dr_tip_lt _ hi hk, by dsimp only; omega, by dsimp only; omega⟩
  · have hj' : j < NV w := lt_of_lt_of_le hj (sc_len_clause_lt w k).le
    have h1 : NV w * mC w + k < qB w := by
      have : mC w ≤ NV w * mC w := Nat.le_mul_of_pos_left _ hN
      omega
    revert ht
    cases sy w k j <;> simp only [clT, List.mem_cons, List.not_mem_nil, or_false] <;>
      (try exact False.elim) <;> rintro rfl <;> exact ⟨dr_tip_lt _ hj' hk, h1, h1⟩
  · simp only [garT, List.mem_map, List.mem_range] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have : mC w * (NV w - 1) + mC w = NV w * mC w := by
      rw [Nat.mul_comm (NV w)]
      conv_rhs => rw [← Nat.sub_add_cancel hN]
      rw [Nat.mul_succ]
    exact ⟨hx, by dsimp only; omega, by dsimp only; omega⟩

/-! ## The rows -/

theorem dr_oh_getD (q a p : ℕ) : (oh q a).getD p zero = if p < q ∧ p = a then pos else zero := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hp : p < q
  · simp [oh, hp]
  · rw [List.getElem?_eq_none (by simp [oh]; omega)]; simp [hp]

theorem dr_oh_len (q a : ℕ) : (oh q a).length = q := by simp [oh]

theorem dr_oh_count (q a : ℕ) : (oh q a).count pos = if a < q then 1 else 0 := by
  induction q with
  | zero => simp [oh]
  | succ q ih =>
    have : oh (q + 1) a = oh q a ++ [if q = a then pos else zero] := by
      simp [oh, List.range_succ]
    rw [this, List.count_append, ih]
    by_cases h : q = a
    · subst h; simp
    · have : (if q = a then pos else zero) = zero := if_neg h
      rw [this]; simp
      split <;> split <;> omega


theorem dr_triRow_getD (q : ℕ) (t : ℕ × ℕ × ℕ) (h1 : t.1 < q) (h2 : t.2.1 < q) (h3 : t.2.2 < q)
    (p : ℕ) : (triRow q t).getD p zero = pos ↔ (p = t.1 ∨ p = q + t.2.1 ∨ p = 2 * q + t.2.2) := by
  unfold triRow
  by_cases hp1 : p < q
  · rw [List.getD_append _ _ _ _ (by simp [dr_oh_len]; omega),
      List.getD_append _ _ _ _ (by simp [dr_oh_len]; omega), dr_oh_getD]
    split <;> simp_all; omega
  by_cases hp2 : p < 2 * q
  · rw [List.getD_append _ _ _ _ (by simp [dr_oh_len]; omega),
      List.getD_append_right _ _ _ _ (by simp [dr_oh_len]; omega), dr_oh_getD, dr_oh_len]
    split <;> simp_all <;> omega
  · rw [List.getD_append_right _ _ _ _ (by simp [dr_oh_len]; omega), dr_oh_getD]
    simp only [List.length_append, dr_oh_len]
    split <;> simp_all <;> omega

theorem dr_triRow_isTri (q : ℕ) (t : ℕ × ℕ × ℕ) (h1 : t.1 < q) (h2 : t.2.1 < q) (h3 : t.2.2 < q) :
    IsTri q (triRow q t) := by
  unfold IsTri triRow
  refine ⟨by simp [dr_oh_len]; omega, ?_, ?_, ?_⟩
  · rw [List.append_assoc, List.take_left' (dr_oh_len _ _), dr_oh_count, if_pos h1]
  · rw [List.append_assoc, List.drop_left' (dr_oh_len _ _), List.take_left' (dr_oh_len _ _),
      dr_oh_count, if_pos h2]
  · rw [List.drop_left' (by simp [dr_oh_len]; omega), dr_oh_count, if_pos h3]

theorem dr_triRow_len (q : ℕ) (t : ℕ × ℕ × ℕ) : (triRow q t).length = 3 * q := by
  simp [triRow, dr_oh_len]; omega

theorem dr_triRow_count (q : ℕ) (t : ℕ × ℕ × ℕ) (h1 : t.1 < q) (h2 : t.2.1 < q) (h3 : t.2.2 < q) :
    (triRow q t).count pos = 3 := by
  simp only [triRow, List.count_append, dr_oh_count, if_pos h1, if_pos h2, if_pos h3]

theorem dr_sep_triRow (q : ℕ) (t : ℕ × ℕ × ℕ) : sep ∉ triRow q t := by
  simp only [triRow, oh, List.mem_append, List.mem_map, List.mem_range, not_or, not_exists, not_and]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro i _ h <;> split at h <;> cases h

theorem dr_clauses (w : List SatSym) (n : ℕ) :
    clauses ((List.replicate n zero :: triRows w).flatMap (· ++ [sep])) =
      List.replicate n zero :: triRows w := by
  refine clauses_flatMap _ fun c hc => ?_
  simp only [List.mem_cons, triRows, List.mem_map] at hc
  rcases hc with rfl | ⟨t, _, rfl⟩
  · simp [List.mem_replicate]
  · exact dr_sep_triRow _ _

/-! ## Covering counts -/

theorem dr_covC_eq (q : ℕ) :
    ∀ (ts : List (ℕ × ℕ × ℕ)), (∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) →
      ∀ y p, covC (ts.map (triRow q)) y p = covT q ts y p
  | [], _, _, _ => rfl
  | t :: ts, h, y, p => by
    obtain ⟨h1, h2, h3⟩ := h t (by simp)
    simp only [List.map_cons, covC, covT]
    rw [dr_covC_eq q ts (fun t ht => h t (by simp [ht])) y.tail p]
    congr 2
    simp only [decide_eq_decide.2 (dr_triRow_getD q t h1 h2 h3 p)]

theorem dr_covC_tris (w : List SatSym) (y : List Bool) (p : ℕ) :
    covC (triRows w) y p = covT (qB w) (tris w) y p :=
  dr_covC_eq _ _ (dr_tris_lt w) y p

/-! ## The main equivalences -/

theorem dm_iff_covT (w : List SatSym) :
    DMLang (DMI w) ↔ ∃ y : List Bool, ∀ p < 3 * qB w, covT (qB w) (tris w) y p = 1 := by
  constructor
  · rintro ⟨u, rs, hc, -, y, hy⟩
    rw [DMI, dr_clauses] at hc
    obtain ⟨rfl, rfl⟩ := List.cons.inj hc
    refine ⟨y, fun p hp => ?_⟩
    rw [← dr_covC_tris]; exact hy p (by simpa using hp)
  · rintro ⟨y, hy⟩
    refine ⟨_, _, by rw [DMI, dr_clauses], fun r hr => ?_, y, fun p hp => ?_⟩
    · simp only [triRows, List.mem_map] at hr
      obtain ⟨t, ht, rfl⟩ := hr
      obtain ⟨h1, h2, h3⟩ := dr_tris_lt w t ht
      rw [List.length_replicate]; exact dr_triRow_isTri _ _ h1 h2 h3
    · rw [dr_covC_tris]; exact hy p (by simpa using hp)

theorem x3c_iff_covT (w : List SatSym) :
    X3CLang (X3I w) ↔ ∃ y : List Bool, ∀ p < 3 * qB w, covT (qB w) (tris w) y p = 1 := by
  constructor
  · rintro ⟨u, rs, hc, -, y, hy⟩
    rw [X3I, dr_clauses] at hc
    obtain ⟨rfl, rfl⟩ := List.cons.inj hc
    refine ⟨y, fun p hp => ?_⟩
    rw [← dr_covC_tris]; exact hy p (by simpa using hp)
  · rintro ⟨y, hy⟩
    refine ⟨_, _, by rw [X3I, dr_clauses], fun r hr => ?_, y, fun p hp => ?_⟩
    · simp only [triRows, List.mem_map] at hr
      obtain ⟨t, ht, rfl⟩ := hr
      obtain ⟨h1, h2, h3⟩ := dr_tris_lt w t ht
      rw [List.length_replicate]
      exact ⟨dr_triRow_len _ _, dr_triRow_count _ _ h1 h2 h3⟩
    · rw [dr_covC_tris]; exact hy p (by simpa using hp)

end Pnp.Karp.ThreeDM
