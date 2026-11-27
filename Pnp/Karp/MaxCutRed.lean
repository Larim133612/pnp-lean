import Pnp.Karp.MaxCut
import Pnp.Karp.ColorRed

namespace Pnp.Karp.MaxCut

open Pnp.CookLevin SatSym Pnp.Karp.Clique

set_option linter.unusedSimpArgs false

/-- `1` if the two sides differ. -/
def mcr_d (x y : Bool) : ℕ := if x = y then 0 else 1

theorem mcr_d_le (x y : Bool) : mcr_d x y ≤ 1 := by unfold mcr_d; split_ifs <;> omega

/-- Default annotation. -/
abbrev mcr_dflt : SatSym × ℕ × ℕ := (zero, 0, 0)

theorem mcr_getD_append (l₁ l₂ : List SatSym) (k : ℕ) :
    (l₁ ++ l₂).getD k zero =
      if k < l₁.length then l₁.getD k zero else l₂.getD (k - l₁.length) zero := by
  split_ifs with h
  · exact List.getD_append _ _ _ _ h
  · exact List.getD_append_right _ _ _ _ (by omega)

/-! ## Row cuts -/

theorem mcr_rc (rows : List (List SatSym)) (c : ℕ → Bool) (i : ℕ) (S : Finset ℕ)
    (hS : ∀ j < i, (((rows.getD i []).getD j zero = pos) ↔ j ∈ S)) (hSi : ∀ j ∈ S, j < i) :
    rowCut rows c i = ∑ j ∈ S, mcr_d (c i) (c j) := by
  unfold rowCut
  rw [Finset.card_filter]
  have : ∑ j ∈ S, mcr_d (c i) (c j) =
      ∑ j ∈ (Finset.range i).filter (· ∈ S), mcr_d (c i) (c j) := by
    congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => ⟨hSi j h, h⟩, fun h => h.2⟩
  rw [this, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have e := hS j hj
  unfold mcr_d
  by_cases h : j ∈ S
  · have e' := e.2 h
    by_cases h' : c i = c j
    · rw [if_neg (fun x => x.2 h'), if_pos h]; simp [h']
    · rw [if_pos ⟨e', h'⟩, if_pos h]; simp [h']
  · have e' : ¬ (rows.getD i []).getD j zero = pos := fun x => h (e.1 x)
    rw [if_neg (fun x => e' x.1), if_neg h]

theorem mcr_rc0 (rows : List (List SatSym)) (c : ℕ → Bool) (i : ℕ)
    (h : ∀ j < i, ¬ (rows.getD i []).getD j zero = pos) : rowCut rows c i = 0 := by
  rw [mcr_rc rows c i ∅ (fun j hj => by simpa using h j hj) (by simp)]; simp

theorem mcr_rc1 (rows : List (List SatSym)) (c : ℕ → Bool) (i x : ℕ) (hx : x < i)
    (h : ∀ j < i, ((rows.getD i []).getD j zero = pos ↔ j = x)) :
    rowCut rows c i = mcr_d (c i) (c x) := by
  rw [mcr_rc rows c i {x} (fun j hj => by simpa using h j hj) (by simpa using hx)]; simp

theorem mcr_rc2 (rows : List (List SatSym)) (c : ℕ → Bool) (i x y : ℕ) (hx : x < i)
    (hy : y < i) (hxy : x ≠ y)
    (h : ∀ j < i, ((rows.getD i []).getD j zero = pos ↔ j = x ∨ j = y)) :
    rowCut rows c i = mcr_d (c i) (c x) + mcr_d (c i) (c y) := by
  rw [mcr_rc rows c i {x, y} (fun j hj => by simpa using h j hj) (by simp [hx, hy])]
  rw [Finset.sum_insert (by simpa using hxy), Finset.sum_singleton]

theorem mcr_rc3 (rows : List (List SatSym)) (c : ℕ → Bool) (i x y z : ℕ) (hx : x < i)
    (hy : y < i) (hz : z < i) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : ∀ j < i, ((rows.getD i []).getD j zero = pos ↔ j = x ∨ j = y ∨ j = z)) :
    rowCut rows c i = mcr_d (c i) (c x) + mcr_d (c i) (c y) + mcr_d (c i) (c z) := by
  rw [mcr_rc rows c i {x, y, z} (fun j hj => by simpa using h j hj) (by simp [hx, hy, hz])]
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simpa using hyz),
    Finset.sum_singleton, add_assoc]

/-! ## Positive entries of the rows -/

theorem mcr_tw_pos (a c k : ℕ) (h : a < c) : (tw a c).getD k zero = pos ↔ k = a ∨ k = c := by
  simp only [tw, List.append_assoc, List.cons_append, Color.getD_rep_append,
    Color.ite_zero_eq_pos, Color.getD_cons_pos_iff, Color.getD_nil_pos]
  simp; omega

theorem mcr_xpRow_pos (j k : ℕ) : (xpRow j).getD k zero = pos ↔ k = 2 + 2 * j := by
  unfold xpRow
  simp only [Color.getD_rep_append, Color.ite_zero_eq_pos, Color.getD_cons_pos_iff,
    Color.getD_nil_pos]
  simp; omega

theorem mcr_nlCol_bd (s : SatSym) (j : ℕ) : 1 ≤ nlCol s j ∧ nlCol s j ≤ 3 + 2 * j := by
  cases s <;> simp [nlCol] <;> omega

theorem mcr_lRow_pos (L p : ℕ) (s : SatSym) (j k : ℕ) (hjp : j ≤ p) (hj : j < L) :
    (lRow s (base L p) j).getD k zero = pos ↔ k = accV L p j ∨ k = nlCol s j := by
  have hn := mcr_nlCol_bd s j
  unfold lRow accV
  split_ifs with h0
  · rw [mcr_tw_pos _ _ _ (by omega)]
  · rw [mcr_tw_pos _ _ _ (by unfold base; omega)]; omega

theorem mcr_cRow_pos (L p : ℕ) (s : SatSym) (j k : ℕ) (hjp : j ≤ p) :
    (cRow s (base L p) j).getD k zero = pos ↔
      k = accV L p j ∨ k = base L p ∨ (s = sep ∧ k = 1) := by
  have hb : 2 ≤ base L p := by unfold base; omega
  unfold cRow accV
  by_cases h0 : j = 0
  · have hb3 : 2 ≤ base L p := hb
    by_cases hs : s = sep <;> simp only [h0, hs, if_true, if_false]
    · simp only [List.append_assoc, List.cons_append, List.nil_append, Color.getD_rep_append,
        Color.ite_zero_eq_pos, Color.getD_cons_pos_iff, Color.getD_nil_pos]
      simp; omega
    · rw [mcr_tw_pos _ _ _ (by omega)]; simp [hs]
  · have hb3 : 5 ≤ base L p := by unfold base; omega
    by_cases hs : s = sep <;> simp only [h0, hs, if_true, if_false]
    · simp only [List.append_assoc, List.cons_append, List.nil_append, Color.getD_rep_append,
        Color.ite_zero_eq_pos, Color.getD_cons_pos_iff, Color.getD_nil_pos]
      simp; omega
    · simp only [List.append_assoc, List.cons_append, List.nil_append, Color.getD_rep_append,
        Color.ite_zero_eq_pos, Color.getD_cons_pos_iff, Color.getD_nil_pos]
      simp; omega

theorem mcr_bRow_pos (s : SatSym) (b k : ℕ) :
    (bRow s b).getD k zero = pos ↔ s ≠ sep ∧ k = b + 1 := by
  unfold bRow
  by_cases hs : s = sep <;> simp only [hs, if_true, if_false]
  · simp
  · simp only [Color.getD_rep_append, Color.ite_zero_eq_pos, Color.getD_cons_pos_iff,
      Color.getD_nil_pos]
    simp [hs]; omega

/-! ## The rows of `gRows w` -/

theorem mcr_length_litRows (L : ℕ) : (litRows L).length = 2 * L := by
  induction L with
  | zero => rfl
  | succ L ih => simp [litRows, List.range_succ, List.flatMap_append] at ih ⊢; omega

theorem mcr_litRows_succ (L : ℕ) : litRows (L + 1) = litRows L ++ [[], xpRow L] := by
  simp [litRows, List.range_succ, List.flatMap_append]

theorem mcr_getD_litRows (L m : ℕ) (hm : m < 2 * L) :
    (litRows L).getD m [] = if m % 2 = 0 then [] else xpRow (m / 2) := by
  induction L with
  | zero => omega
  | succ L ih =>
    rw [mcr_litRows_succ]
    by_cases h : m < 2 * L
    · rw [List.getD_append _ _ _ _ (by rw [mcr_length_litRows]; exact h), ih h]
    · rw [List.getD_append_right _ _ _ _ (by rw [mcr_length_litRows]; omega), mcr_length_litRows]
      have : m - 2 * L = 0 ∨ m - 2 * L = 1 := by omega
      rcases this with e | e <;> rw [e]
      · have h1 : m % 2 = 0 := by omega
        simp [h1]
      · have h1 : m % 2 = 1 := by omega
        have h2 : m / 2 = L := by omega
        simp [h1, h2]

theorem mcr_length_gadAll (L : ℕ) : ∀ (p : ℕ) (A : List (SatSym × ℕ × ℕ)),
    (gadAll L p A).length = 3 * A.length
  | _, [] => rfl
  | p, a :: A => by simp [gadAll, gadRows, mcr_length_gadAll L (p + 1) A]; ring

theorem mcr_getD_gadAll (L : ℕ) : ∀ (A : List (SatSym × ℕ × ℕ)) (p k e : ℕ), k < A.length →
    e < 3 → (gadAll L p A).getD (3 * k + e) [] = (gadRows L (p + k) (A.getD k mcr_dflt)).getD e []
  | [], _, _, _, hk, _ => by simp at hk
  | a :: A, p, 0, e, _, he => by
    simp only [gadAll]
    rw [List.getD_append _ _ _ _ (by simp [gadRows]; omega)]
    simp
  | a :: A, p, k + 1, e, hk, he => by
    simp only [gadAll]
    rw [List.getD_append_right _ _ _ _ (by simp [gadRows]; omega)]
    have : 3 * (k + 1) + e - (gadRows L p a).length = 3 * k + e := by simp [gadRows]; omega
    rw [this, mcr_getD_gadAll L A (p + 1) k e (by simp at hk; omega) he,
      show p + 1 + k = p + (k + 1) by omega]
    simp

theorem mcr_length_pre (L : ℕ) : (preRows ++ litRows L).length = base L 0 := by
  simp [preRows, mcr_length_litRows, base]; omega

theorem mcr_length_gRows (w : List SatSym) :
    (gRows w).length = (2 + 2 * (annW w).length) + 3 * (annW w).length := by
  unfold gRows
  rw [List.length_append, mcr_length_pre, mcr_length_gadAll]; simp [base]

theorem mcr_row_pre (w : List SatSym) (i : ℕ) (hi : i < base (annW w).length 0) :
    (gRows w).getD i [] = (preRows ++ litRows (annW w).length).getD i [] :=
  List.getD_append _ _ _ _ (by rw [mcr_length_pre]; exact hi)

theorem mcr_row0 (w : List SatSym) : (gRows w).getD 0 [] = [] := by
  rw [mcr_row_pre w 0 (by simp [base])]; simp [preRows]

theorem mcr_row1 (w : List SatSym) : (gRows w).getD 1 [] = [pos] := by
  rw [mcr_row_pre w 1 (by unfold base; omega)]; simp [preRows]

theorem mcr_rowX (w : List SatSym) (j : ℕ) (hj : j < (annW w).length) :
    (gRows w).getD (2 + 2 * j) [] = [] := by
  rw [mcr_row_pre w _ (by simp [base]; omega),
    List.getD_append_right _ _ _ _ (by simp [preRows]),
    show 2 + 2 * j - preRows.length = 2 * j by simp [preRows], mcr_getD_litRows _ _ (by omega)]
  simp

theorem mcr_rowXp (w : List SatSym) (j : ℕ) (hj : j < (annW w).length) :
    (gRows w).getD (3 + 2 * j) [] = xpRow j := by
  rw [mcr_row_pre w _ (by simp [base]; omega),
    List.getD_append_right _ _ _ _ (by simp [preRows]; omega),
    show 3 + 2 * j - preRows.length = 2 * j + 1 by simp only [preRows]; simp; omega,
    mcr_getD_litRows _ _ (by omega)]
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp [h1, h2]

theorem mcr_rowG (w : List SatSym) (p e : ℕ) (hp : p < (annW w).length) (he : e < 3) :
    (gRows w).getD (base (annW w).length p + e) [] =
      (gadRows (annW w).length p ((annW w).getD p mcr_dflt)).getD e [] := by
  unfold gRows
  rw [List.getD_append_right _ _ _ _ (by rw [mcr_length_pre]; unfold base; omega),
    mcr_length_pre, show base (annW w).length p + e - base (annW w).length 0 = 3 * p + e by
      unfold base; omega, mcr_getD_gadAll _ _ _ _ _ (by omega) he]
  simp

theorem mcr_ann_le : ∀ (r : List SatSym) (t j k : ℕ), k < r.length →
    ((ann r t j).getD k mcr_dflt).2.2 ≤ j + k
  | [], _, _, _, hk => by simp at hk
  | s :: r, t, j, 0, _ => by rw [Color.ann_cons]; simp
  | s :: r, t, j, k + 1, hk => by
    rw [Color.ann_cons]
    simp only [List.getD_cons_succ]
    have := mcr_ann_le r (if s = sep then t + 1 else t) (if s = sep then 0 else j + 1) k
      (by simp at hk; omega)
    by_cases hs : s = sep <;> simp only [hs, if_true, if_false] at this ⊢ <;> omega

theorem mcr_annW_le (w : List SatSym) (p : ℕ) (hp : p < (annW w).length) :
    ((annW w).getD p mcr_dflt).2.2 ≤ p := by
  have := mcr_ann_le (trunc w) 0 0 p (by rw [← Color.length_annW]; exact hp)
  unfold annW; omega

/-! ## The cut value -/

/-- The cut edges of the gadget of position `p` (annotation `a`). -/
def mcr_gc (L : ℕ) (c : ℕ → Bool) (p : ℕ) (a : SatSym × ℕ × ℕ) : ℕ :=
  (mcr_d (c (base L p)) (c (accV L p a.2.2)) + mcr_d (c (base L p)) (c (nlCol a.1 a.2.2))) +
  (if a.1 = sep then
    mcr_d (c (base L p + 1)) (c (accV L p a.2.2)) + mcr_d (c (base L p + 1)) (c (base L p)) +
      mcr_d (c (base L p + 1)) (c 1)
   else mcr_d (c (base L p + 1)) (c (accV L p a.2.2)) + mcr_d (c (base L p + 1)) (c (base L p))) +
  (if a.1 = sep then 0 else mcr_d (c (base L p + 2)) (c (base L p + 1)))

theorem mcr_gad_cut (w : List SatSym) (c : ℕ → Bool) (p : ℕ) (hp : p < (annW w).length) :
    rowCut (gRows w) c (base (annW w).length p) + rowCut (gRows w) c (base (annW w).length p + 1)
      + rowCut (gRows w) c (base (annW w).length p + 2) =
      mcr_gc (annW w).length c p ((annW w).getD p mcr_dflt) := by
  have r0 := mcr_rowG w p 0 hp (by omega)
  have r1 := mcr_rowG w p 1 hp (by omega)
  have r2 := mcr_rowG w p 2 hp (by omega)
  have hjp := mcr_annW_le w p hp
  generalize (annW w).getD p mcr_dflt = a at hjp r0 r1 r2 ⊢
  obtain ⟨s, t, j⟩ := a
  simp only [gadRows, Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at r0 r1 r2 hjp
  generalize (annW w).length = L at *
  have hjL : j < L := by omega
  have hb : base L p = 2 + 2 * L + 3 * p := rfl
  have hacc : (j = 0 ∧ accV L p j = 0) ∨ (j ≠ 0 ∧ accV L p j = base L p - 1) := by
    unfold accV; split_ifs <;> simp_all
  have hn := mcr_nlCol_bd s j
  rw [mcr_rc2 _ c _ (accV L p j) (nlCol s j) (by omega) (by omega) (by omega)
    (fun k _ => by rw [r0]; exact mcr_lRow_pos L p s j k hjp hjL)]
  unfold mcr_gc
  by_cases hs : s = sep
  · rw [mcr_rc3 _ c _ (accV L p j) (base L p) 1 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (fun k _ => by rw [r1, mcr_cRow_pos L p s j k hjp]; simp [hs]),
      mcr_rc0 _ c _ (fun k _ => by rw [r2, mcr_bRow_pos]; simp [hs])]
    simp [hs]
  · rw [mcr_rc2 _ c _ (accV L p j) (base L p) (by omega) (by omega) (by omega)
      (fun k _ => by rw [r1, mcr_cRow_pos L p s j k hjp]; simp [hs]),
      mcr_rc1 _ c _ (base L p + 1) (by omega) (fun k _ => by rw [r2, mcr_bRow_pos]; simp [hs])]
    simp [hs]

theorem mcr_sum_block (g : ℕ → ℕ) (m : ℕ) : ∀ n : ℕ,
    ∑ k ∈ Finset.range (m * n), g k = ∑ q ∈ Finset.range n, ∑ e ∈ Finset.range m, g (m * q + e)
  | 0 => by simp
  | n + 1 => by
    rw [show m * (n + 1) = m * n + m by ring, Finset.sum_range_add, mcr_sum_block g m n,
      Finset.sum_range_succ]

theorem mcr_cut_eq (w : List SatSym) (c : ℕ → Bool) :
    cutVal (gRows w) c = mcr_d (c 1) (c 0) +
      ∑ j ∈ Finset.range (annW w).length, mcr_d (c (3 + 2 * j)) (c (2 + 2 * j)) +
      ∑ p ∈ Finset.range (annW w).length, mcr_gc (annW w).length c p ((annW w).getD p mcr_dflt) := by
  unfold cutVal
  rw [mcr_length_gRows, Finset.sum_range_add, Finset.sum_range_add, mcr_sum_block _ 2,
    mcr_sum_block _ 3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have e0 : rowCut (gRows w) c 0 = 0 := mcr_rc0 _ _ _ (fun j hj => by omega)
  have e1 : rowCut (gRows w) c 1 = mcr_d (c 1) (c 0) :=
    mcr_rc1 _ _ _ 0 (by omega) (fun j hj => by
      rw [mcr_row1]; obtain rfl : j = 0 := by omega
      simp)
  rw [e0, e1, zero_add]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [show 2 + (2 * j + 0) = 2 + 2 * j by omega, show 2 + (2 * j + 1) = 3 + 2 * j by omega,
      mcr_rc0 _ _ (2 + 2 * j) (fun k _ => by rw [mcr_rowX w j hj]; simp),
      mcr_rc1 _ _ (3 + 2 * j) (2 + 2 * j) (by omega)
        (fun k _ => by rw [mcr_rowXp w j hj]; exact mcr_xpRow_pos j k), zero_add]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_range] at hp
    have hb : base (annW w).length p = 2 + 2 * (annW w).length + 3 * p := rfl
    rw [← mcr_gad_cut w c p hp, hb, Nat.add_zero, Nat.add_assoc _ (3 * p) 1,
      Nat.add_assoc _ (3 * p) 2]

theorem mcr_d_eq_one (x y : Bool) : mcr_d x y = 1 ↔ x ≠ y := by
  unfold mcr_d; split_ifs <;> simp_all

theorem mcr_gc_le (L : ℕ) (c : ℕ → Bool) (p : ℕ) (a : SatSym × ℕ × ℕ) : mcr_gc L c p a ≤ 4 := by
  unfold mcr_gc mcr_d
  generalize c (base L p + 2) = u2
  generalize c (base L p + 1) = u1
  generalize c (base L p) = u0
  generalize c (accV L p a.2.2) = v
  generalize c (nlCol a.1 a.2.2) = n
  generalize c 1 = o
  by_cases hs : a.1 = sep <;> simp only [hs, if_true, if_false] <;> revert u2 u1 u0 v n o <;>
    decide

theorem mcr_gc_five (L : ℕ) (c : ℕ → Bool) (p : ℕ) (a : SatSym × ℕ × ℕ) :
    mcr_gc L c p a = 4 ↔ (c (base L p) ≠ c (nlCol a.1 a.2.2) ∧
      ¬ (c (accV L p a.2.2) = c (base L p) ∧ c (base L p) = c (base L p + 1)) ∧
      (a.1 = sep → c (base L p + 1) ≠ c 1) ∧ (a.1 ≠ sep → c (base L p + 2) ≠ c (base L p + 1))) := by
  unfold mcr_gc mcr_d
  generalize c (base L p + 2) = u2
  generalize c (base L p + 1) = u1
  generalize c (base L p) = u0
  generalize c (accV L p a.2.2) = v
  generalize c (nlCol a.1 a.2.2) = n
  generalize c 1 = o
  by_cases hs : a.1 = sep <;> simp only [hs, if_true, if_false, ne_eq, not_true, not_false_eq_true,
    true_implies, false_implies, and_true, IsEmpty.forall_iff] <;> revert u2 u1 u0 v n o <;>
    decide

theorem mcr_tight (w : List SatSym) (c : ℕ → Bool)
    (h : 5 * (annW w).length + 1 ≤ cutVal (gRows w) c) :
    c 1 ≠ c 0 ∧ (∀ j < (annW w).length, c (3 + 2 * j) ≠ c (2 + 2 * j)) ∧
      ∀ p < (annW w).length, mcr_gc (annW w).length c p ((annW w).getD p mcr_dflt) = 4 := by
  rw [mcr_cut_eq] at h
  have b1 := mcr_d_le (c 1) (c 0)
  have b2 : ∑ j ∈ Finset.range (annW w).length, mcr_d (c (3 + 2 * j)) (c (2 + 2 * j)) ≤
      ∑ j ∈ Finset.range (annW w).length, 1 := Finset.sum_le_sum fun j _ => mcr_d_le _ _
  have b3 : ∑ p ∈ Finset.range (annW w).length,
      mcr_gc (annW w).length c p ((annW w).getD p mcr_dflt) ≤
      ∑ p ∈ Finset.range (annW w).length, 4 := Finset.sum_le_sum fun p _ => mcr_gc_le _ _ _ _
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at b2 b3
  refine ⟨(mcr_d_eq_one _ _).1 (by omega), fun j hj => (mcr_d_eq_one _ _).1 ?_, fun p hp => ?_⟩
  · have e2 : ∑ j ∈ Finset.range (annW w).length, mcr_d (c (3 + 2 * j)) (c (2 + 2 * j)) =
        ∑ j ∈ Finset.range (annW w).length, 1 := by simp; omega
    exact (Finset.sum_eq_sum_iff_of_le fun j _ => mcr_d_le _ _).1 e2 j (Finset.mem_range.2 hj)
  · have e3 : ∑ p ∈ Finset.range (annW w).length,
        mcr_gc (annW w).length c p ((annW w).getD p mcr_dflt) =
        ∑ p ∈ Finset.range (annW w).length, 4 := by
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; omega
    exact (Finset.sum_eq_sum_iff_of_le fun p _ => mcr_gc_le _ _ _ _).1 e3 p (Finset.mem_range.2 hp)

/-! ## Cut ⇒ SAT -/

theorem mcr_accV_succ (L p j : ℕ) : accV L (p + 1) (j + 1) = base L p + 2 := by
  simp [accV, base]; omega

theorem mcr_b_ne_ne : ∀ x y z : Bool, x ≠ y → y ≠ z → x = z := by decide

theorem mcr_b_key : ∀ z x y u v : Bool, x = z → y = z → ¬ (x = y ∧ y = u) → v ≠ u → v = z := by
  decide

theorem mcr_sound (w : List SatSym) (c : ℕ → Bool) (h01 : c 1 ≠ c 0)
    (hlit : ∀ j < (annW w).length, c (3 + 2 * j) ≠ c (2 + 2 * j))
    (hg : ∀ q < (annW w).length, mcr_gc (annW w).length c q ((annW w).getD q mcr_dflt) = 4) :
    ∀ (r : List SatSym) (t j p : ℕ) (F : Bool) (Pre : List (SatSym × ℕ × ℕ)),
    annW w = Pre ++ ann r t j → Pre.length = p → j ≤ p → p + r.length = (annW w).length →
    (F = false → c (accV (annW w).length p j) = c 0) →
    evalF (fun j => c (2 + 2 * j) != c 0) r j F = true
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | s :: r, t, j, p, F, Pre, hA, hP, hjp, hlen, hacc => by
    have hjL : j < (annW w).length := by simp at hlen; omega
    have hpL : p < (annW w).length := by simp at hlen; omega
    rw [Color.ann_cons] at hA
    have hap : (annW w).getD p mcr_dflt = (s, t, j) := by
      rw [hA, List.getD_append_right _ _ _ _ (by omega), hP, Nat.sub_self]; rfl
    have hA' : annW w = (Pre ++ [(s, t, j)]) ++ ann r (if s = sep then t + 1 else t)
        (if s = sep then 0 else j + 1) := by rw [hA]; simp
    have hP' : (Pre ++ [(s, t, j)]).length = p + 1 := by simp [hP]
    have hlen' : p + 1 + r.length = (annW w).length := by simp at hlen; omega
    have ih := fun F => mcr_sound w c h01 hlit hg r _ _ (p + 1) F _ hA' hP'
    obtain ⟨g1, g2, g3, g4⟩ := (mcr_gc_five _ _ _ _).1 (hg p hpL)
    rw [hap] at g1 g2 g3 g4
    simp only at g1 g2 g3 g4
    have hl := hlit j hjL
    cases s
    · -- pos
      simp only [evalF]
      simp only [reduceCtorEq, ↓reduceIte] at ih
      refine ih _ (by omega) hlen' fun hF => ?_
      rw [Bool.or_eq_false_iff] at hF
      rw [mcr_accV_succ]
      have h2 : c (2 + 2 * j) = c 0 := by simpa using hF.2
      have hb : c (base (annW w).length p) = c 0 :=
        h2 ▸ mcr_b_ne_ne _ _ _ (by simpa [nlCol] using g1) hl
      exact mcr_b_key _ _ _ _ _ (hacc hF.1) hb g2 (g4 (by simp))
    · -- neg
      simp only [evalF]
      simp only [reduceCtorEq, ↓reduceIte] at ih
      refine ih _ (by omega) hlen' fun hF => ?_
      rw [Bool.or_eq_false_iff] at hF
      rw [mcr_accV_succ]
      have h2 : c (2 + 2 * j) ≠ c 0 := by simpa using hF.2
      have hb : c (base (annW w).length p) = c 0 :=
        mcr_b_ne_ne _ _ _ (by simpa [nlCol] using g1) h2
      exact mcr_b_key _ _ _ _ _ (hacc hF.1) hb g2 (g4 (by simp))
    · -- zero
      simp only [evalF]
      simp only [reduceCtorEq, ↓reduceIte] at ih
      refine ih _ (by omega) hlen' fun hF => ?_
      rw [mcr_accV_succ]
      have hb : c (base (annW w).length p) = c 0 :=
        mcr_b_ne_ne _ _ _ (by simpa [nlCol] using g1) h01
      exact mcr_b_key _ _ _ _ _ (hacc hF) hb g2 (g4 (by simp))
    · -- sep
      simp only [evalF, Bool.and_eq_true]
      simp only [↓reduceIte] at ih
      refine ⟨?_, ih _ (by omega) hlen' fun _ => by simp [accV]⟩
      cases F
      · exfalso
        have hb : c (base (annW w).length p) = c 0 :=
          mcr_b_ne_ne _ _ _ (by simpa [nlCol] using g1) h01
        have hc : c (base (annW w).length p + 1) = c 0 :=
          mcr_b_ne_ne _ _ _ (g3 rfl) h01
        exact g2 ⟨(hacc rfl).trans hb.symm, hb.trans hc.symm⟩
      · rfl

theorem mcr_sat_of_mc (w : List SatSym) (h : MCLang (MCI w)) : SATLang w := by
  unfold MCLang at h
  rw [clauses_MCI] at h
  obtain ⟨c, hc⟩ := h
  have hk : (kRow w).length = 5 * (annW w).length + 1 := by simp [kRow]
  rw [hk] at hc
  obtain ⟨h01, hlit, hg⟩ := mcr_tight w c hc
  refine ⟨fun j => c (2 + 2 * j) != c 0, ?_⟩
  rw [← Color.evalF_trunc]
  exact mcr_sound w c h01 hlit hg (trunc w) 0 0 0 false [] rfl rfl le_rfl
    (by rw [Color.length_annW]; simp) (fun _ => by simp [accV])

/-! ## SAT ⇒ cut -/

/-- The sides of the gadget vertices (three per position): `Lₚ`, `Cₚ`, `Bₚ`. -/
def mcr_gcol (a : ℕ → Bool) : List SatSym → ℕ → Bool → List Bool
  | [], _, _ => []
  | s :: r, j, F => [Color.lv a s j, !(F || Color.lv a s j), F || Color.lv a s j] ++
      mcr_gcol a r (if s = sep then 0 else j + 1) (if s = sep then false else F || Color.lv a s j)

/-- The cut of the reduction graph from the assignment `a`. -/
def mcr_side (w : List SatSym) (a : ℕ → Bool) (v : ℕ) : Bool :=
  if v = 0 then false else if v = 1 then true
  else if v < base (annW w).length 0 then
    (if v % 2 = 0 then a ((v - 2) / 2) else !a ((v - 2) / 2))
  else (mcr_gcol a (trunc w) 0 false).getD (v - base (annW w).length 0) false

theorem mcr_side_X (w : List SatSym) (a : ℕ → Bool) (j : ℕ) (hj : j < (annW w).length) :
    mcr_side w a (2 + 2 * j) = a j := by
  have h1 : 2 + 2 * j < base (annW w).length 0 := by simp [base]; omega
  have h2 : (2 + 2 * j) % 2 = 0 := by omega
  have h3 : (2 + 2 * j - 2) / 2 = j := by omega
  simp only [mcr_side, h1, h2, h3, if_true, show 2 + 2 * j ≠ 0 by omega,
    show 2 + 2 * j ≠ 1 by omega, if_false]

theorem mcr_side_Xp (w : List SatSym) (a : ℕ → Bool) (j : ℕ) (hj : j < (annW w).length) :
    mcr_side w a (3 + 2 * j) = !a j := by
  have h1 : 3 + 2 * j < base (annW w).length 0 := by simp [base]; omega
  have h2 : ¬ (3 + 2 * j) % 2 = 0 := by omega
  have h3 : (3 + 2 * j - 2) / 2 = j := by omega
  simp only [mcr_side, h1, h2, h3, if_true, show 3 + 2 * j ≠ 0 by omega,
    show 3 + 2 * j ≠ 1 by omega, if_false]

theorem mcr_side_nl (w : List SatSym) (a : ℕ → Bool) (s : SatSym) (j : ℕ)
    (hj : j < (annW w).length) : mcr_side w a (nlCol s j) = !Color.lv a s j := by
  cases s
  · simp only [nlCol, Color.lv]; exact mcr_side_Xp w a j hj
  · simp only [nlCol, Color.lv, mcr_side_X w a j hj, Bool.not_not]
  · rfl
  · rfl

theorem mcr_side_gad (w : List SatSym) (a : ℕ → Bool) (p e : ℕ) (Q l : List Bool)
    (hQ : ∃ R, mcr_gcol a (trunc w) 0 false = Q ++ l ++ R) (hl : Q.length = 3 * p)
    (he : e < l.length) : mcr_side w a (base (annW w).length p + e) = l.getD e false := by
  obtain ⟨R, hR⟩ := hQ
  have h0 : base (annW w).length p + e ≠ 0 := by simp [base]
  have h1 : base (annW w).length p + e ≠ 1 := by simp [base]; omega
  have h2 : ¬ base (annW w).length p + e < base (annW w).length 0 := by simp [base]; omega
  simp only [mcr_side, h0, h1, h2, if_false, hR]
  have : base (annW w).length p + e - base (annW w).length 0 = Q.length + e := by
    simp [base, hl]; omega
  rw [this, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ he]

theorem mcr_compl (w : List SatSym) (a : ℕ → Bool) :
    ∀ (r : List SatSym) (t j p : ℕ) (F : Bool) (Pre : List (SatSym × ℕ × ℕ)) (Q : List Bool),
    annW w = Pre ++ ann r t j → Pre.length = p →
    mcr_gcol a (trunc w) 0 false = Q ++ mcr_gcol a r j F → Q.length = 3 * p →
    j ≤ p → p + r.length = (annW w).length → evalF a r j F = true →
    mcr_side w a (accV (annW w).length p j) = F →
    ∀ q, p ≤ q → q < (annW w).length →
      mcr_gc (annW w).length (mcr_side w a) q ((annW w).getD q mcr_dflt) = 4
  | [], _, _, _, _, _, _, _, _, _, _, _, hlen, _, _, q, hq, hq' => by simp at hlen; omega
  | s :: r, t, j, p, F, Pre, Q, hA, hP, hQ, hQl, hjp, hlen, hev, hacc, q, hq, hq' => by
    have hjL : j < (annW w).length := by simp at hlen; omega
    rw [Color.ann_cons] at hA
    have hap : (annW w).getD p mcr_dflt = (s, t, j) := by
      rw [hA, List.getD_append_right _ _ _ _ (by omega), hP, Nat.sub_self]; rfl
    have hA' : annW w = (Pre ++ [(s, t, j)]) ++ ann r (if s = sep then t + 1 else t)
        (if s = sep then 0 else j + 1) := by rw [hA]; simp
    have hP' : (Pre ++ [(s, t, j)]).length = p + 1 := by simp [hP]
    have hlen' : p + 1 + r.length = (annW w).length := by simp at hlen; omega
    simp only [mcr_gcol] at hQ
    have hQ' := hQ
    rw [← List.append_assoc] at hQ'
    have hQl' : (Q ++ [Color.lv a s j, !(F || Color.lv a s j), F || Color.lv a s j]).length =
        3 * (p + 1) := by simp [hQl]; ring
    have hc : ∀ e < 3, mcr_side w a (base (annW w).length p + e) =
        [Color.lv a s j, !(F || Color.lv a s j), F || Color.lv a s j].getD e false :=
      fun e he => mcr_side_gad w a p e Q _ ⟨_, hQ'⟩ hQl (by simpa using he)
    have c0 := hc 0 (by omega)
    have c1 := hc 1 (by omega)
    have c2 := hc 2 (by omega)
    simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at c0 c1 c2
    rw [Color.evalF_cons] at hev
    by_cases hqp : q = p
    · subst hqp
      rw [hap]
      refine (mcr_gc_five _ _ _ _).2 ?_
      simp only
      rw [c0, c1, c2, hacc, mcr_side_nl w a s j hjL,
        show mcr_side w a 1 = true by simp [mcr_side]]
      refine ⟨by cases Color.lv a s j <;> decide, by cases F <;> cases Color.lv a s j <;> decide,
        fun hs => ?_, fun _ => by cases F <;> cases Color.lv a s j <;> decide⟩
      rw [if_pos hs, Bool.and_eq_true] at hev
      rw [hev.1]; simp
    · refine mcr_compl w a r _ _ (p + 1) _ _ _ hA' hP' hQ' hQl' ?_ hlen' ?_ ?_ q (by omega) hq'
      · split_ifs <;> omega
      · split_ifs at hev ⊢
        · simp only [Bool.and_eq_true] at hev; exact hev.2
        · exact hev
      · by_cases hs : s = sep
        · rw [if_pos hs, if_pos hs]; simp [accV, mcr_side]
        · rw [if_neg hs, if_neg hs, mcr_accV_succ, c2]

theorem mcr_mc_of_sat (w : List SatSym) (h : SATLang w) : MCLang (MCI w) := by
  obtain ⟨a, ha⟩ := h
  unfold MCLang
  rw [clauses_MCI]
  refine ⟨mcr_side w a, ?_⟩
  have hk : (kRow w).length = 5 * (annW w).length + 1 := by simp [kRow]
  rw [hk, mcr_cut_eq]
  have e1 : mcr_d (mcr_side w a 1) (mcr_side w a 0) = 1 := by simp [mcr_side, mcr_d]
  have e2 : ∑ j ∈ Finset.range (annW w).length,
      mcr_d (mcr_side w a (3 + 2 * j)) (mcr_side w a (2 + 2 * j)) =
      ∑ j ∈ Finset.range (annW w).length, 1 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [mcr_side_X w a j hj, mcr_side_Xp w a j hj, mcr_d_eq_one]
    cases a j <;> decide
  have e3 : ∑ p ∈ Finset.range (annW w).length,
      mcr_gc (annW w).length (mcr_side w a) p ((annW w).getD p mcr_dflt) =
      ∑ p ∈ Finset.range (annW w).length, 4 := by
    refine Finset.sum_congr rfl fun p hp => ?_
    exact mcr_compl w a (trunc w) 0 0 0 false [] [] rfl rfl rfl rfl le_rfl
      (by rw [Color.length_annW]; simp) ((Color.evalF_trunc a w).2 ha)
      (by simp [accV, mcr_side]) p (Nat.zero_le _) (Finset.mem_range.1 hp)
  rw [e1, e2, e3]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

/-- **Correctness of the reduction SAT ≤ MAX CUT.** -/
theorem sat_iff_mc (w : List SatSym) : SATLang w ↔ MCLang (MCI w) :=
  ⟨mcr_mc_of_sat w, mcr_sat_of_mc w⟩


end Pnp.Karp.MaxCut
