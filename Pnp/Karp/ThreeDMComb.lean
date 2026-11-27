import Pnp.Karp.ThreeDM
import Pnp.Karp.SubComb

/-!
# 3-DIMENSIONAL MATCHING: correctness of the Garey–Johnson triples

`sat_iff_covT`: the formula `w` is satisfiable iff some selection of the triples `tris w`
covers every element of `X ⊔ Y ⊔ Z` exactly once.

The count `covT` is decomposed over the three blocks of `tris w` into an abstract count
`dc_T` parametrised by selection functions (`dc_decomp`, `dc_construct`), which is then
evaluated on each kind of element (`dc_T_tip`, `dc_T_yr`, `dc_T_zr`, `dc_T_ycl`, `dc_T_zcl`,
`dc_T_yg`, `dc_T_zg`).
-/

namespace Pnp.Karp.ThreeDM

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum

/-! ## `covT` over lists -/

/-- Does the triple `t` contain the element `p`? -/
def dc_h (q p : ℕ) (t : ℕ × ℕ × ℕ) : Bool :=
  decide (p = t.1 ∨ p = q + t.2.1 ∨ p = 2 * q + t.2.2)

theorem dc_cov_append (q : ℕ) : ∀ (A B : List (ℕ × ℕ × ℕ)) (y : List Bool) (p : ℕ),
    covT q (A ++ B) y p = covT q A y p + covT q B (y.drop A.length) p
  | [], B, y, p => by simp [covT]
  | t :: A, B, y, p => by
    simp only [List.cons_append, covT, dc_cov_append q A B y.tail p, List.length_cons]
    have : y.tail.drop A.length = y.drop (A.length + 1) := by cases y <;> simp
    rw [this]; omega

theorem dc_cov_app2 (q : ℕ) : ∀ (A B : List (ℕ × ℕ × ℕ)) (yA yB : List Bool) (p : ℕ),
    yA.length = A.length → covT q (A ++ B) (yA ++ yB) p = covT q A yA p + covT q B yB p
  | [], B, [], yB, p, _ => by simp [covT]
  | t :: A, B, b :: yA, yB, p, h => by
    simp only [List.cons_append, covT, List.headD_cons, List.tail_cons]
    rw [dc_cov_app2 q A B yA yB p (by simpa using h)]; simp [Nat.add_assoc]
  | [], _, _ :: _, _, _, h => by simp at h
  | _ :: _, _, [], _, _, h => by simp at h

theorem dc_cov_fm2 (q : ℕ) (f : ℕ → List (ℕ × ℕ × ℕ)) (g : ℕ → List Bool)
    (hg : ∀ i, (g i).length = (f i).length) (p : ℕ) : ∀ n,
    covT q ((List.range n).flatMap f) ((List.range n).flatMap g) p =
      ∑ i ∈ Finset.range n, covT q (f i) (g i) p
  | 0 => by simp [covT]
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, dc_cov_app2,
      dc_cov_fm2 q f g hg p n, Finset.sum_range_succ]
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · rw [sc_len_fm, sc_len_fm]; simp [hg]

theorem dc_cov_map2 (q : ℕ) (F : ℕ → ℕ × ℕ × ℕ) (b : ℕ → Bool) (p : ℕ) : ∀ n,
    covT q ((List.range n).map F) ((List.range n).map b) p =
      ∑ i ∈ Finset.range n, if b i && dc_h q p (F i) then 1 else 0
  | 0 => by simp [covT]
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, dc_cov_app2,
      dc_cov_map2 q F b p n, Finset.sum_range_succ]
    · simp [covT, dc_h]
    · simp

theorem dc_cov_fm (q : ℕ) (f : ℕ → List (ℕ × ℕ × ℕ)) (y : List Bool) (p : ℕ) : ∀ n,
    covT q ((List.range n).flatMap f) y p =
      ∑ i ∈ Finset.range n, covT q (f i) (y.drop (∑ i' ∈ Finset.range i, (f i').length)) p
  | 0 => by simp [covT]
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, dc_cov_append, dc_cov_fm q f y p n,
      Finset.sum_range_succ, sc_len_fm]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem dc_cov_fm' (q : ℕ) (f : ℕ → List (ℕ × ℕ × ℕ)) (y : List Bool) (n : ℕ) :
    ∃ g : ℕ → List Bool, ∀ p,
      covT q ((List.range n).flatMap f) y p = ∑ i ∈ Finset.range n, covT q (f i) (g i) p :=
  ⟨_, fun p => dc_cov_fm q f y p n⟩

theorem dc_cov_map (q : ℕ) (F : ℕ → ℕ × ℕ × ℕ) (y : List Bool) (p : ℕ) : ∀ n,
    covT q ((List.range n).map F) y p =
      ∑ i ∈ Finset.range n, if (y.drop i).headD false && dc_h q p (F i) then 1 else 0
  | 0 => by simp [covT]
  | n + 1 => by
    rw [List.range_succ, List.map_append, dc_cov_append, dc_cov_map q F y p n,
      Finset.sum_range_succ]
    simp [covT, dc_h]

theorem dc_cov_map' (q : ℕ) (F : ℕ → ℕ × ℕ × ℕ) (y : List Bool) (n : ℕ) :
    ∃ b : ℕ → Bool, ∀ p,
      covT q ((List.range n).map F) y p = ∑ i ∈ Finset.range n, if b i && dc_h q p (F i) then 1 else 0 :=
  ⟨_, fun p => dc_cov_map q F y p n⟩

/-! ## The abstract count -/

/-- Does the clause triple of symbol `sym` at position `j` of clause `k` contain `p`? -/
def dc_clH (N m k j : ℕ) (sym : SatSym) (p : ℕ) : Bool :=
  decide (sym = pos ∨ sym = neg) &&
    dc_h (2 * N * m) p (tipI m j k (decide (sym = pos)), N * m + k, N * m + k)

/-- Selected ring triples containing `p`. -/
def dc_TA (N m : ℕ) (rt rf : ℕ → ℕ → Bool) (p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range m,
    ((if rt i k && dc_h (2 * N * m) p (tipI m i k false, m * i + k, m * i + k) then 1 else 0) +
      (if rf i k && dc_h (2 * N * m) p (tipI m i k true, m * i + (k + 1) % m, m * i + k)
        then 1 else 0))

/-- Selected clause triples containing `p`. -/
def dc_TB (N m : ℕ) (len : ℕ → ℕ) (s : ℕ → ℕ → SatSym) (c : ℕ → ℕ → Bool) (p : ℕ) : ℕ :=
  ∑ k ∈ Finset.range m, ∑ j ∈ Finset.range (len k),
    if c k j && dc_clH N m k j (s k j) p then 1 else 0

/-- Selected garbage triples containing `p`. -/
def dc_TC (N m : ℕ) (g : ℕ → ℕ → Bool) (p : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * N * m), ∑ t ∈ Finset.range (m * (N - 1)),
    if g x t && dc_h (2 * N * m) p (x, N * m + m + t, N * m + m + t) then 1 else 0

/-- The number of selected triples containing `p`. -/
def dc_T (N m : ℕ) (len : ℕ → ℕ) (s : ℕ → ℕ → SatSym) (rt rf c g : ℕ → ℕ → Bool) (p : ℕ) : ℕ :=
  dc_TA N m rt rf p + dc_TB N m len s c p + dc_TC N m g p

theorem dc_cov_ring (q m i k : ℕ) (z : List Bool) (p : ℕ) :
    covT q (ringT m i k) z p =
      (if z.headD false && dc_h q p (tipI m i k false, m * i + k, m * i + k) then 1 else 0) +
        (if z.tail.headD false && dc_h q p (tipI m i k true, m * i + (k + 1) % m, m * i + k)
          then 1 else 0) := by
  simp only [ringT, covT, dc_h, add_zero]; rfl

theorem dc_ringT_len (m i k : ℕ) : (ringT m i k).length = 2 := rfl

theorem dc_cov_cl (N m k j : ℕ) (sym : SatSym) (z : List Bool) (p : ℕ) :
    covT (2 * N * m) (clT N m k j sym) z p =
      if z.headD false && dc_clH N m k j sym p then 1 else 0 := by
  cases sym <;> simp [clT, covT, dc_clH, dc_h]

theorem dc_cov_cl2 (N m k j : ℕ) (sym : SatSym) (b : Bool) (p : ℕ) :
    covT (2 * N * m) (clT N m k j sym) ((clT N m k j sym).map fun _ => b) p =
      if b && dc_clH N m k j sym p then 1 else 0 := by
  cases sym <;> simp [clT, covT, dc_clH, dc_h]

theorem dc_decomp (w : List SatSym) (y : List Bool) : ∃ rt rf c g : ℕ → ℕ → Bool, ∀ p,
    covT (qB w) (tris w) y p = dc_T (NV w) (mC w) (fun k => ((clauses w).getD k []).length)
      (sy w) rt rf c g p := by
  have hA : ∀ y' : List Bool, ∃ g : ℕ → ℕ → List Bool, ∀ p,
      covT (qB w) ((List.range (NV w)).flatMap fun i =>
        (List.range (mC w)).flatMap fun k => ringT (mC w) i k) y' p =
      ∑ i ∈ Finset.range (NV w), ∑ k ∈ Finset.range (mC w),
        covT (qB w) (ringT (mC w) i k) (g i k) p := by
    intro y'
    obtain ⟨g1, h1⟩ := dc_cov_fm' (qB w) (fun i =>
      (List.range (mC w)).flatMap fun k => ringT (mC w) i k) y' (NV w)
    choose g2 h2 using fun i => dc_cov_fm' (qB w) (fun k => ringT (mC w) i k) (g1 i) (mC w)
    exact ⟨g2, fun p => by rw [h1]; exact Finset.sum_congr rfl fun i _ => h2 i p⟩
  have hB : ∀ y' : List Bool, ∃ g : ℕ → ℕ → List Bool, ∀ p,
      covT (qB w) ((List.range (mC w)).flatMap fun k =>
        (List.range ((clauses w).getD k []).length).flatMap fun j =>
          clT (NV w) (mC w) k j (sy w k j)) y' p =
      ∑ k ∈ Finset.range (mC w), ∑ j ∈ Finset.range ((clauses w).getD k []).length,
        covT (qB w) (clT (NV w) (mC w) k j (sy w k j)) (g k j) p := by
    intro y'
    obtain ⟨g1, h1⟩ := dc_cov_fm' (qB w) (fun k =>
      (List.range ((clauses w).getD k []).length).flatMap fun j =>
          clT (NV w) (mC w) k j (sy w k j)) y' (mC w)
    choose g2 h2 using fun k => dc_cov_fm' (qB w) (fun j => clT (NV w) (mC w) k j (sy w k j))
      (g1 k) ((clauses w).getD k []).length
    exact ⟨g2, fun p => by rw [h1]; exact Finset.sum_congr rfl fun i _ => h2 i p⟩
  have hC : ∀ y' : List Bool, ∃ g : ℕ → ℕ → Bool, ∀ p,
      covT (qB w) ((List.range (qB w)).flatMap fun x => garT (NV w) (mC w) x) y' p =
      ∑ x ∈ Finset.range (qB w), ∑ t ∈ Finset.range (mC w * (NV w - 1)),
        if g x t && dc_h (qB w) p (x, NV w * mC w + mC w + t, NV w * mC w + mC w + t)
          then 1 else 0 := by
    intro y'
    obtain ⟨g1, h1⟩ := dc_cov_fm' (qB w) (fun x => garT (NV w) (mC w) x) y' (qB w)
    choose g2 h2 using fun x => dc_cov_map' (qB w)
      (fun t => (x, NV w * mC w + mC w + t, NV w * mC w + mC w + t)) (g1 x) (mC w * (NV w - 1))
    exact ⟨g2, fun p => by rw [h1]; exact Finset.sum_congr rfl fun i _ => h2 i p⟩
  choose gA hgA using hA
  choose gB hgB using hB
  choose gC hgC using hC
  refine ⟨fun i k => (gA y i k).headD false, fun i k => (gA y i k).tail.headD false,
    fun k j => (gB (y.drop ((List.range (NV w)).flatMap fun i =>
        (List.range (mC w)).flatMap fun k => ringT (mC w) i k).length) k j).headD false,
    gC (y.drop (((List.range (NV w)).flatMap fun i =>
        (List.range (mC w)).flatMap fun k => ringT (mC w) i k) ++
      (List.range (mC w)).flatMap fun k =>
        (List.range ((clauses w).getD k []).length).flatMap fun j =>
          clT (NV w) (mC w) k j (sy w k j)).length), fun p => ?_⟩
  unfold tris
  rw [dc_cov_append, dc_cov_append, hgA, hgB, hgC]
  unfold dc_T dc_TA dc_TB dc_TC
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) rfl
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => dc_cov_ring _ _ _ _ _ _
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => dc_cov_cl _ _ _ _ _ _ _

theorem dc_construct (w : List SatSym) (rt rf c g : ℕ → ℕ → Bool) : ∃ y, ∀ p,
    covT (qB w) (tris w) y p = dc_T (NV w) (mC w) (fun k => ((clauses w).getD k []).length)
      (sy w) rt rf c g p := by
  refine ⟨(List.range (NV w)).flatMap (fun i => (List.range (mC w)).flatMap fun k => [rt i k, rf i k]) ++
    (List.range (mC w)).flatMap (fun k => (List.range ((clauses w).getD k []).length).flatMap
      fun j => (clT (NV w) (mC w) k j (sy w k j)).map fun _ => c k j) ++
    (List.range (qB w)).flatMap (fun x => (List.range (mC w * (NV w - 1))).map (g x)),
    fun p => ?_⟩
  unfold tris
  rw [dc_cov_app2, dc_cov_app2, dc_cov_fm2, dc_cov_fm2, dc_cov_fm2]
  · unfold dc_T dc_TA dc_TB dc_TC
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [dc_cov_fm2]
      · exact Finset.sum_congr rfl fun k _ => by rw [dc_cov_ring]; simp [qB]
      · intro k; simp [dc_ringT_len]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [dc_cov_fm2]
      · exact Finset.sum_congr rfl fun j _ => dc_cov_cl2 _ _ _ _ _ _ _
      · intro j; simp
    · exact Finset.sum_congr rfl fun x _ => dc_cov_map2 _ _ _ _ _
  · intro x; simp [garT]
  · intro k; rw [sc_len_fm, sc_len_fm]; simp
  · intro i; rw [sc_len_fm, sc_len_fm]; simp [dc_ringT_len]
  · rw [sc_len_fm, sc_len_fm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sc_len_fm, sc_len_fm]; simp [dc_ringT_len]
  · simp only [List.length_append]; rw [sc_len_fm, sc_len_fm, sc_len_fm, sc_len_fm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_len_fm, sc_len_fm]; simp [dc_ringT_len]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [sc_len_fm, sc_len_fm]; simp

/-! ## Arithmetic of the layout -/

theorem dc_ring_lt {N m i : ℕ} (hi : i < N) : m * i + m ≤ N * m := by
  have := Nat.mul_le_mul_left m (show i + 1 ≤ N from hi)
  rw [Nat.mul_succ, Nat.mul_comm m N] at this; exact this

theorem dc_sep {m i i' : ℕ} (h : i ≠ i') : m * i + m ≤ m * i' ∨ m * i' + m ≤ m * i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left; have := Nat.mul_le_mul_left m (show i + 1 ≤ i' from h)
    rw [Nat.mul_succ] at this; exact this
  · right; have := Nat.mul_le_mul_left m (show i' + 1 ≤ i from h)
    rw [Nat.mul_succ] at this; exact this

theorem dc_ik {m i i' k k' : ℕ} (hk : k < m) (hk' : k' < m) :
    m * i + k = m * i' + k' ↔ i = i' ∧ k = k' := by
  constructor
  · intro h
    by_cases hi : i = i'
    · subst hi; omega
    · have := dc_sep (m := m) hi; omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem dc_G {N m : ℕ} (hN : 1 ≤ N) : m * (N - 1) + m = N * m := by
  rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hN, Nat.mul_comm]

theorem dc_q (N m : ℕ) : 2 * N * m = 2 * (N * m) := Nat.mul_assoc 2 N m

theorem dc_tip_bd (m i k : ℕ) (v : Bool) :
    2 * (m * i + k) ≤ tipI m i k v ∧ tipI m i k v ≤ 2 * (m * i + k) + 1 := by
  unfold tipI; cases v <;> simp

theorem dc_tip_inj {m i i' k k' : ℕ} {v v' : Bool} (hk : k < m) (hk' : k' < m) :
    tipI m i k v = tipI m i' k' v' ↔ i = i' ∧ k = k' ∧ v = v' := by
  constructor
  · intro h
    have h2 : m * i + k = m * i' + k' ∧ v = v' := by
      unfold tipI at h; cases v <;> cases v' <;> simp at h ⊢ <;> omega
    exact ⟨((dc_ik hk hk').1 h2.1).1, ((dc_ik hk hk').1 h2.1).2, h2.2⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem dc_tip_lt {N m i k : ℕ} (hi : i < N) (hk : k < m) (v : Bool) :
    tipI m i k v < 2 * N * m := by
  have := dc_tip_bd m i k v; have := dc_ring_lt (m := m) hi; rw [dc_q]; omega

theorem dc_succ_mod {m k k0 : ℕ} (hk : k < m) (hk0 : k0 < m) :
    k0 = (k + 1) % m ↔ k = if k0 = 0 then m - 1 else k0 - 1 := by
  rcases Nat.lt_or_ge (k + 1) m with h | h
  · rw [Nat.mod_eq_of_lt h]; split_ifs <;> omega
  · have : k + 1 = m := by omega
    rw [this, Nat.mod_self]; split_ifs <;> omega

theorem dc_pred_lt {m k0 : ℕ} (hk0 : k0 < m) : (if k0 = 0 then m - 1 else k0 - 1) < m := by
  split_ifs <;> omega

theorem dc_sum2 {N m i0 k0 : ℕ} {f : ℕ → ℕ → ℕ} (hi0 : i0 < N) (hk0 : k0 < m)
    (h : ∀ i < N, ∀ k < m, ¬(i = i0 ∧ k = k0) → f i k = 0) :
    ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range m, f i k = f i0 k0 := by
  rw [sc_sum_single (i0 := i0) (fun i hi hne => Finset.sum_eq_zero fun k hk =>
    h i hi k (Finset.mem_range.1 hk) fun e => hne e.1), if_pos hi0,
    sc_sum_single (i0 := k0) (fun k hk hne => h i0 hi0 k hk fun e => hne e.2), if_pos hk0]

theorem dc_ite_zero {b x : Bool} (h : x = true → False) : (if b && x then 1 else 0) = 0 := by
  cases x <;> simp_all

theorem dc_hX {q p : ℕ} (hp : p < q) (a b c : ℕ) : dc_h q p (a, b, c) = decide (p = a) := by
  simp only [dc_h, decide_eq_decide]; constructor <;> intro h <;> omega

theorem dc_hY {q a b0 : ℕ} (ha : a < q) (hb0 : b0 < q) (b c : ℕ) :
    dc_h q (q + b0) (a, b, c) = decide (b0 = b) := by
  simp only [dc_h, decide_eq_decide]; constructor <;> intro h <;> omega

theorem dc_hZ {q a b c0 : ℕ} (ha : a < q) (hb : b < q) (c : ℕ) :
    dc_h q (2 * q + c0) (a, b, c) = decide (c0 = c) := by
  simp only [dc_h, decide_eq_decide]; constructor <;> intro h <;> omega

theorem dc_clH_le {N m k j : ℕ} {sym : SatSym} {p : ℕ} (h : dc_clH N m k j sym p = true) :
    p = tipI m j k (decide (sym = pos)) ∨ p = 2 * N * m + (N * m + k) ∨
      p = 2 * (2 * N * m) + (N * m + k) := by
  simp only [dc_clH, dc_h, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

/-! ## Evaluation of the blocks -/

variable {N m : ℕ} {len : ℕ → ℕ} {s : ℕ → ℕ → SatSym} {rt rf c g : ℕ → ℕ → Bool}

theorem dc_A0 {P : ℕ} (hq : 2 * N * m ≤ P)
    (h : ∀ b < N * m, P ≠ 2 * N * m + b ∧ P ≠ 2 * (2 * N * m) + b) : dc_TA N m rt rf P = 0 :=
  Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun k hk => by
    have hi := Finset.mem_range.1 hi
    have hk := Finset.mem_range.1 hk
    have h1 := dc_tip_lt hi hk false
    have h2 := dc_tip_lt hi hk true
    have h3 := dc_ring_lt (m := m) hi
    have h4 : (k + 1) % m < m := Nat.mod_lt _ (by omega)
    have e1 := h (m * i + k) (by omega)
    have e2 := h (m * i + (k + 1) % m) (by omega)
    rw [dc_ite_zero, dc_ite_zero] <;> first | rfl | (simp only [dc_h, decide_eq_true_eq]; omega)

theorem dc_B0 (hlen : ∀ k, len k < N) {P : ℕ} (hq : 2 * N * m ≤ P)
    (h : ∀ k < m, P ≠ 2 * N * m + (N * m + k) ∧ P ≠ 2 * (2 * N * m) + (N * m + k)) :
    dc_TB N m len s c P = 0 :=
  Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun j hj => by
    have hk := Finset.mem_range.1 hk
    have hj : j < N := lt_trans (Finset.mem_range.1 hj) (hlen k)
    have h1 := dc_tip_lt hj hk (decide (s k j = pos))
    have e1 := h k hk
    rw [dc_ite_zero]; intro hc; have := dc_clH_le hc; omega

theorem dc_C0 {P : ℕ} (hq : 2 * N * m ≤ P)
    (h : ∀ t < m * (N - 1), P ≠ 2 * N * m + (N * m + m + t) ∧
      P ≠ 2 * (2 * N * m) + (N * m + m + t)) : dc_TC N m g P = 0 :=
  Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun t ht => by
    have hx := Finset.mem_range.1 hx
    have e1 := h t (Finset.mem_range.1 ht)
    rw [dc_ite_zero]; simp only [dc_h, decide_eq_true_eq]; omega

theorem dc_A_tip {i0 k0 : ℕ} (hi0 : i0 < N) (hk0 : k0 < m) (v : Bool) :
    dc_TA N m rt rf (tipI m i0 k0 v) = if (if v then rf i0 k0 else rt i0 k0) then 1 else 0 := by
  have hp := dc_tip_lt hi0 hk0 v
  unfold dc_TA
  rw [dc_sum2 hi0 hk0]
  · rw [dc_hX hp, dc_hX hp]; cases v <;> simp [dc_tip_inj hk0 hk0]
  · intro i _ k hk hne
    rw [dc_hX hp, dc_hX hp, dc_ite_zero, dc_ite_zero] <;> first | rfl |
      (simp only [decide_eq_true_eq, dc_tip_inj hk0 hk]; rintro ⟨rfl, rfl, -⟩; exact hne ⟨rfl, rfl⟩)

theorem dc_B_tip {i0 k0 : ℕ} (hi0 : i0 < N) (hk0 : k0 < m) (v : Bool) :
    dc_TB N m len s c (tipI m i0 k0 v) =
      if i0 < len k0 ∧ c k0 i0 = true ∧ s k0 i0 = (if v then pos else neg) then 1 else 0 := by
  have hp := dc_tip_lt hi0 hk0 v
  unfold dc_TB
  rw [sc_sum_single (i0 := k0) (fun k hk hne => Finset.sum_eq_zero fun j hj => ?_), if_pos hk0]
  · rw [sc_sum_single (i0 := i0) (fun j hj hne => ?_)]
    · by_cases hl : i0 < len k0
      · rw [if_pos hl]; unfold dc_clH; rw [dc_hX hp]
        cases v <;> cases s k0 i0 <;> simp [dc_tip_inj hk0 hk0, hl]
      · rw [if_neg hl]; simp [hl]
    · rw [dc_ite_zero]; unfold dc_clH; rw [dc_hX hp]
      simp only [Bool.and_eq_true, decide_eq_true_eq, dc_tip_inj hk0 hk0]
      rintro ⟨-, rfl, -⟩; exact hne rfl
  · rw [dc_ite_zero]; unfold dc_clH; rw [dc_hX hp]
    simp only [Bool.and_eq_true, decide_eq_true_eq, dc_tip_inj hk0 hk]
    rintro ⟨-, -, rfl, -⟩; exact hne rfl

theorem dc_C_tip {i0 k0 : ℕ} (hi0 : i0 < N) (hk0 : k0 < m) (v : Bool) :
    dc_TC N m g (tipI m i0 k0 v) =
      ∑ t ∈ Finset.range (m * (N - 1)), if g (tipI m i0 k0 v) t then 1 else 0 := by
  have hp := dc_tip_lt hi0 hk0 v
  unfold dc_TC
  rw [sc_sum_single (i0 := tipI m i0 k0 v) (fun x hx hne => Finset.sum_eq_zero fun t _ => ?_),
    if_pos hp]
  · refine Finset.sum_congr rfl fun t _ => ?_; rw [dc_hX hp]; simp
  · rw [dc_hX hp, dc_ite_zero]; simp only [decide_eq_true_eq]; exact fun e => hne e.symm

theorem dc_A_yr {i0 k0 : ℕ} (hi0 : i0 < N) (hk0 : k0 < m) :
    dc_TA N m rt rf (2 * N * m + (m * i0 + k0)) =
      (if rt i0 k0 then 1 else 0) + (if rf i0 (if k0 = 0 then m - 1 else k0 - 1) then 1 else 0) := by
  have hb0 : m * i0 + k0 < 2 * N * m := by have := dc_ring_lt (m := m) hi0; rw [dc_q]; omega
  have hk0' := dc_pred_lt hk0
  unfold dc_TA
  simp only [Finset.sum_add_distrib]
  rw [dc_sum2 hi0 hk0, dc_sum2 hi0 hk0']
  · rw [dc_hY (dc_tip_lt hi0 hk0 false) hb0, dc_hY (dc_tip_lt hi0 hk0' true) hb0,
      ← (dc_succ_mod hk0' hk0).2 rfl]
    simp
  · intro i hi k hk hne
    have h4 : (k + 1) % m < m := Nat.mod_lt _ (by omega)
    rw [dc_hY (dc_tip_lt hi hk true) hb0, dc_ite_zero]
    simp only [decide_eq_true_eq, dc_ik hk0 h4, dc_succ_mod hk hk0]
    rintro ⟨rfl, rfl⟩; exact hne ⟨rfl, rfl⟩
  · intro i hi k hk hne
    rw [dc_hY (dc_tip_lt hi hk false) hb0, dc_ite_zero]
    simp only [decide_eq_true_eq, dc_ik hk0 hk]
    rintro ⟨rfl, rfl⟩; exact hne ⟨rfl, rfl⟩

theorem dc_A_zr {i0 k0 : ℕ} (hi0 : i0 < N) (hk0 : k0 < m) :
    dc_TA N m rt rf (2 * (2 * N * m) + (m * i0 + k0)) =
      (if rt i0 k0 then 1 else 0) + (if rf i0 k0 then 1 else 0) := by
  unfold dc_TA
  have hb : ∀ i < N, ∀ k < m, m * i + k < 2 * N * m ∧ m * i + (k + 1) % m < 2 * N * m :=
    fun i hi k hk => by
      have := dc_ring_lt (m := m) hi
      have h4 : (k + 1) % m < m := Nat.mod_lt _ (by omega)
      rw [dc_q]; omega
  rw [dc_sum2 hi0 hk0]
  · rw [dc_hZ (dc_tip_lt hi0 hk0 false) (hb i0 hi0 k0 hk0).1,
      dc_hZ (dc_tip_lt hi0 hk0 true) (hb i0 hi0 k0 hk0).2]
    simp
  · intro i hi k hk hne
    rw [dc_hZ (dc_tip_lt hi hk false) (hb i hi k hk).1,
      dc_hZ (dc_tip_lt hi hk true) (hb i hi k hk).2, dc_ite_zero, dc_ite_zero] <;> first | rfl |
      (simp only [decide_eq_true_eq, dc_ik hk0 hk]; rintro ⟨rfl, rfl⟩; exact hne ⟨rfl, rfl⟩)

theorem dc_B_y (hlen : ∀ k, len k < N) {k0 : ℕ} (hk0 : k0 < m) :
    dc_TB N m len s c (2 * N * m + (N * m + k0)) = ∑ j ∈ Finset.range (len k0),
      if c k0 j && decide (s k0 j = pos ∨ s k0 j = neg) then 1 else 0 := by
  have hN : 1 ≤ N := by have := hlen 0; omega
  have hb0 : N * m + k0 < 2 * N * m := by
    have := Nat.le_mul_of_pos_left m hN; rw [dc_q]; omega
  unfold dc_TB
  rw [sc_sum_single (i0 := k0) (fun k hk hne => Finset.sum_eq_zero fun j hj => ?_), if_pos hk0]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj : j < N := lt_trans (Finset.mem_range.1 hj) (hlen k0)
    unfold dc_clH; rw [dc_hY (dc_tip_lt hj hk0 _) hb0]; simp
  · have hj : j < N := lt_trans (Finset.mem_range.1 hj) (hlen k)
    rw [dc_ite_zero]; unfold dc_clH; rw [dc_hY (dc_tip_lt hj hk _) hb0]
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

theorem dc_B_z (hlen : ∀ k, len k < N) {k0 : ℕ} (hk0 : k0 < m) :
    dc_TB N m len s c (2 * (2 * N * m) + (N * m + k0)) = ∑ j ∈ Finset.range (len k0),
      if c k0 j && decide (s k0 j = pos ∨ s k0 j = neg) then 1 else 0 := by
  have hN : 1 ≤ N := by have := hlen 0; omega
  have hb : ∀ k < m, N * m + k < 2 * N * m := fun k hk => by
    have := Nat.le_mul_of_pos_left m hN; rw [dc_q]; omega
  unfold dc_TB
  rw [sc_sum_single (i0 := k0) (fun k hk hne => Finset.sum_eq_zero fun j hj => ?_), if_pos hk0]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj : j < N := lt_trans (Finset.mem_range.1 hj) (hlen k0)
    unfold dc_clH; rw [dc_hZ (dc_tip_lt hj hk0 _) (hb k0 hk0)]; simp
  · have hj : j < N := lt_trans (Finset.mem_range.1 hj) (hlen k)
    rw [dc_ite_zero]; unfold dc_clH; rw [dc_hZ (dc_tip_lt hj hk _) (hb k hk)]
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

theorem dc_C_y (hN : 1 ≤ N) {t0 : ℕ} (ht0 : t0 < m * (N - 1)) :
    dc_TC N m g (2 * N * m + (N * m + m + t0)) =
      ∑ x ∈ Finset.range (2 * N * m), if g x t0 then 1 else 0 := by
  have hb0 : N * m + m + t0 < 2 * N * m := by have := dc_G (m := m) hN; rw [dc_q]; omega
  unfold dc_TC
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx := Finset.mem_range.1 hx
  rw [sc_sum_single (i0 := t0) (fun t _ hne => ?_), if_pos ht0]
  · rw [dc_hY hx hb0]; simp
  · rw [dc_hY hx hb0, dc_ite_zero]; simp only [decide_eq_true_eq]; omega

theorem dc_C_z (hN : 1 ≤ N) {t0 : ℕ} (ht0 : t0 < m * (N - 1)) :
    dc_TC N m g (2 * (2 * N * m) + (N * m + m + t0)) =
      ∑ x ∈ Finset.range (2 * N * m), if g x t0 then 1 else 0 := by
  have hb : ∀ t < m * (N - 1), N * m + m + t < 2 * N * m := fun t ht => by
    have := dc_G (m := m) hN; rw [dc_q]; omega
  unfold dc_TC
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx := Finset.mem_range.1 hx
  rw [sc_sum_single (i0 := t0) (fun t ht hne => ?_), if_pos ht0]
  · rw [dc_hZ hx (hb t0 ht0)]; simp
  · rw [dc_hZ hx (hb t ht), dc_ite_zero]; simp only [decide_eq_true_eq]; omega

/-! ## The count on each kind of element -/

theorem dc_T_tip {i0 k0 : ℕ} (hi0 : i0 < N) (hk0 : k0 < m) (v : Bool) :
    dc_T N m len s rt rf c g (tipI m i0 k0 v) =
      (if (if v then rf i0 k0 else rt i0 k0) then 1 else 0) +
      (if i0 < len k0 ∧ c k0 i0 = true ∧ s k0 i0 = (if v then pos else neg) then 1 else 0) +
      ∑ t ∈ Finset.range (m * (N - 1)), if g (tipI m i0 k0 v) t then 1 else 0 := by
  unfold dc_T; rw [dc_A_tip hi0 hk0, dc_B_tip hi0 hk0, dc_C_tip hi0 hk0]

theorem dc_T_yr (hlen : ∀ k, len k < N) {i0 k0 : ℕ} (hi0 : i0 < N) (hk0 : k0 < m) :
    dc_T N m len s rt rf c g (2 * N * m + (m * i0 + k0)) =
      (if rt i0 k0 then 1 else 0) + (if rf i0 (if k0 = 0 then m - 1 else k0 - 1) then 1 else 0) := by
  have := dc_ring_lt (m := m) hi0; have := dc_q N m
  have := dc_G (m := m) (show 1 ≤ N by have := hlen 0; omega)
  unfold dc_T
  rw [dc_A_yr hi0 hk0, dc_B0 hlen (by omega) (fun k _ => by omega),
    dc_C0 (by omega) (fun t _ => by omega), add_zero, add_zero]

theorem dc_T_zr (hlen : ∀ k, len k < N) {i0 k0 : ℕ} (hi0 : i0 < N) (hk0 : k0 < m) :
    dc_T N m len s rt rf c g (2 * (2 * N * m) + (m * i0 + k0)) =
      (if rt i0 k0 then 1 else 0) + (if rf i0 k0 then 1 else 0) := by
  have := dc_ring_lt (m := m) hi0; have := dc_q N m
  have := dc_G (m := m) (show 1 ≤ N by have := hlen 0; omega)
  unfold dc_T
  rw [dc_A_zr hi0 hk0, dc_B0 hlen (by omega) (fun k _ => by omega),
    dc_C0 (by omega) (fun t _ => by omega), add_zero, add_zero]

theorem dc_T_ycl (hlen : ∀ k, len k < N) {k0 : ℕ} (hk0 : k0 < m) :
    dc_T N m len s rt rf c g (2 * N * m + (N * m + k0)) = ∑ j ∈ Finset.range (len k0),
      if c k0 j && decide (s k0 j = pos ∨ s k0 j = neg) then 1 else 0 := by
  have hN : 1 ≤ N := by have := hlen 0; omega
  have := dc_q N m; have := dc_G (m := m) hN
  unfold dc_T
  rw [dc_A0 (by omega) (fun b _ => by omega), dc_B_y hlen hk0,
    dc_C0 (by omega) (fun t _ => by omega)]
  simp

theorem dc_T_zcl (hlen : ∀ k, len k < N) {k0 : ℕ} (hk0 : k0 < m) :
    dc_T N m len s rt rf c g (2 * (2 * N * m) + (N * m + k0)) = ∑ j ∈ Finset.range (len k0),
      if c k0 j && decide (s k0 j = pos ∨ s k0 j = neg) then 1 else 0 := by
  have hN : 1 ≤ N := by have := hlen 0; omega
  have := dc_q N m; have := dc_G (m := m) hN
  unfold dc_T
  rw [dc_A0 (by omega) (fun b _ => by omega), dc_B_z hlen hk0,
    dc_C0 (by omega) (fun t _ => by omega)]
  simp

theorem dc_T_yg (hlen : ∀ k, len k < N) {t0 : ℕ} (ht0 : t0 < m * (N - 1)) :
    dc_T N m len s rt rf c g (2 * N * m + (N * m + m + t0)) =
      ∑ x ∈ Finset.range (2 * N * m), if g x t0 then 1 else 0 := by
  have hN : 1 ≤ N := by have := hlen 0; omega
  have := dc_q N m; have := dc_G (m := m) hN
  unfold dc_T
  rw [dc_A0 (by omega) (fun b _ => by omega), dc_B0 hlen (by omega) (fun k _ => by omega),
    dc_C_y hN ht0]
  simp

theorem dc_T_zg (hlen : ∀ k, len k < N) {t0 : ℕ} (ht0 : t0 < m * (N - 1)) :
    dc_T N m len s rt rf c g (2 * (2 * N * m) + (N * m + m + t0)) =
      ∑ x ∈ Finset.range (2 * N * m), if g x t0 then 1 else 0 := by
  have hN : 1 ≤ N := by have := hlen 0; omega
  have := dc_q N m; have := dc_G (m := m) hN
  unfold dc_T
  rw [dc_A0 (by omega) (fun b _ => by omega), dc_B0 hlen (by omega) (fun k _ => by omega),
    dc_C_z hN ht0]
  simp

/-! ## Decoding the elements -/

theorem dc_dec_ring {b : ℕ} (hb : b < N * m) : ∃ i < N, ∃ k < m, b = m * i + k := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h] at hb
    · exact h
  exact ⟨b / m, (Nat.div_lt_iff_lt_mul hm).2 hb, b % m, Nat.mod_lt _ hm,
    (Nat.div_add_mod b m).symm⟩

theorem dc_dec_tip {p : ℕ} (hp : p < 2 * N * m) : ∃ i < N, ∃ k < m, ∃ v, p = tipI m i k v := by
  obtain ⟨i, hi, k, hk, e⟩ := dc_dec_ring (N := N) (m := m) (b := p / 2)
    (by rw [dc_q] at hp; omega)
  refine ⟨i, hi, k, hk, decide (p % 2 = 0), ?_⟩
  unfold tipI; rw [← e]
  by_cases h : p % 2 = 0 <;> simp [h] <;> omega

theorem dc_dec_yz (hN : 1 ≤ N) {b : ℕ} (hb : b < 2 * N * m) :
    b < N * m ∨ (∃ k < m, b = N * m + k) ∨ ∃ t < m * (N - 1), b = N * m + m + t := by
  have := dc_G (m := m) hN; rw [dc_q] at hb
  by_cases h1 : b < N * m
  · exact Or.inl h1
  by_cases h2 : b < N * m + m
  · exact Or.inr (Or.inl ⟨b - N * m, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨b - N * m - m, by omega, by omega⟩)

/-! ## The free tips (for the garbage triples) -/

/-- The tips left free by the ring and clause triples of a satisfying assignment. -/
def dc_L (N m : ℕ) (a : ℕ → Bool) (wit : ℕ → ℕ) : List ℕ :=
  (List.range m).flatMap fun k =>
    ((List.range N).filter fun i => i ≠ wit k).map fun i => tipI m i k (a i)

theorem dc_L_mem {a : ℕ → Bool} {wit : ℕ → ℕ} {i k : ℕ} {v : Bool} (hk : k < m) (hi : i < N) :
    tipI m i k v ∈ dc_L N m a wit ↔ i ≠ wit k ∧ v = a i := by
  simp only [dc_L, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨k', hk', i', ⟨_, hne⟩, e⟩
    rw [dc_tip_inj hk' hk] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨hne, rfl⟩
  · rintro ⟨hne, rfl⟩
    exact ⟨k, hk, i, ⟨hi, hne⟩, rfl⟩

theorem dc_L_lt {a : ℕ → Bool} {wit : ℕ → ℕ} {x : ℕ} (hx : x ∈ dc_L N m a wit) :
    x < 2 * N * m := by
  simp only [dc_L, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hx
  obtain ⟨k, hk, i, ⟨hi, _⟩, rfl⟩ := hx
  exact dc_tip_lt hi hk _

theorem dc_L_nodup (a : ℕ → Bool) (wit : ℕ → ℕ) : (dc_L N m a wit).Nodup := by
  unfold dc_L
  rw [List.nodup_flatMap]
  refine ⟨fun k hk => ?_, ?_⟩
  · have hk := List.mem_range.1 hk
    refine List.Nodup.map_on (fun i _ i' _ e => ?_) (List.nodup_range.filter _)
    exact ((dc_tip_inj hk hk).1 e).1
  · refine List.pairwise_lt_range.imp_of_mem fun {k k'} hk hk' hlt => ?_
    have hk := List.mem_range.1 hk
    have hk' := List.mem_range.1 hk'
    simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_filter]
    rintro x ⟨i, _, rfl⟩ ⟨i', _, e⟩
    have := ((dc_tip_inj hk' hk).1 e).2.1
    omega

theorem dc_filter_len : ∀ {N j : ℕ}, j < N → ((List.range N).filter fun i => i ≠ j).length = N - 1
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | N + 1, j, h => by
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hj : j = N
    · subst hj
      have : (List.range j).filter (fun i => i ≠ j) = List.range j :=
        List.filter_eq_self.2 fun i hi => by simpa using (List.mem_range.1 hi).ne
      rw [this]; simp
    · rw [dc_filter_len (by omega)]; simp [Ne.symm hj]; omega

theorem dc_L_len {a : ℕ → Bool} {wit : ℕ → ℕ} (hw : ∀ k < m, wit k < N) :
    (dc_L N m a wit).length = m * (N - 1) := by
  unfold dc_L
  rw [sc_len_fm]
  rw [Finset.sum_congr rfl fun k hk => by
    rw [List.length_map, dc_filter_len (hw k (Finset.mem_range.1 hk))]]
  simp

theorem dc_sum_get : ∀ (L : List ℕ), L.Nodup → ∀ x,
    ∑ t ∈ Finset.range L.length, (if L[t]? = some x then 1 else 0) = if x ∈ L then 1 else 0
  | [], _, x => by simp
  | b :: L, h, x => by
    have e : ∀ t, (if (b :: L)[t + 1]? = some x then 1 else 0) =
        if L[t]? = some x then 1 else 0 := fun t => by simp
    rw [List.length_cons, Finset.sum_range_succ', Finset.sum_congr rfl fun t _ => e t,
      dc_sum_get L (List.nodup_cons.1 h).2 x]
    have hb := (List.nodup_cons.1 h).1
    by_cases hx : x = b
    · subst hx; simp [hb]
    · simp [hx, Ne.symm hx]

/-! ## The correctness theorem -/

theorem sat_iff_covT (w : List SatSym) :
    SATLang w ↔ ∃ y : List Bool, ∀ p < 3 * qB w, covT (qB w) (tris w) y p = 1 := by
  have hlen := sc_len_clause_lt w
  have hN : 1 ≤ NV w := by unfold NV; omega
  have hq := dc_q (NV w) (mC w)
  rw [clauses_sat_iff]
  constructor
  · rintro ⟨a, ha⟩
    have hex : ∀ k, ∃ j, k < mC w →
        j < ((clauses w).getD k []).length ∧ litTrue a j (sy w k j) := by
      intro k
      by_cases hk : k < mC w
      · have hc : (clauses w).getD k [] ∈ clauses w := by
          rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
        obtain ⟨j, hj, hl⟩ := ha _ hc
        exact ⟨j, fun _ => ⟨hj, hl⟩⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose wit hwit using hex
    have hw : ∀ k < mC w, wit k < NV w := fun k hk => lt_trans (hwit k hk).1 (hlen k)
    obtain ⟨y, hy⟩ := dc_construct w (fun i _ => a i) (fun i _ => !a i)
      (fun k j => decide (j = wit k))
      (fun x t => decide ((dc_L (NV w) (mC w) a wit)[t]? = some x))
    refine ⟨y, fun p hp => ?_⟩
    rw [hy]
    unfold qB at hp
    have hLl := dc_L_len (a := a) hw
    -- the garbage elements
    have hgar : ∀ t < mC w * (NV w - 1), (∑ x ∈ Finset.range (2 * NV w * mC w),
        if decide ((dc_L (NV w) (mC w) a wit)[t]? = some x) = true then 1 else 0) = 1 := by
      intro t ht
      have ht' : t < (dc_L (NV w) (mC w) a wit).length := by omega
      rw [sc_sum_single (i0 := (dc_L (NV w) (mC w) a wit)[t]) (fun x _ hne => by
        simp [List.getElem?_eq_getElem ht', Ne.symm hne])]
      rw [if_pos (dc_L_lt (List.getElem_mem ht'))]
      simp [List.getElem?_eq_getElem ht']
    -- the clause elements
    have hcl : ∀ k < mC w, (∑ j ∈ Finset.range ((clauses w).getD k []).length,
        if (decide (j = wit k) && decide (sy w k j = pos ∨ sy w k j = neg)) = true
          then 1 else 0) = 1 := by
      intro k hk
      obtain ⟨hw1, hw2⟩ := hwit k hk
      rw [sc_sum_single (i0 := wit k) (fun j _ hne => by simp [hne]), if_pos hw1]
      simp [sc_lit a _ _ hw2]
    by_cases hp1 : p < 2 * NV w * mC w
    · obtain ⟨i, hi, k, hk, v, rfl⟩ := dc_dec_tip hp1
      rw [dc_T_tip hi hk, ← hLl]
      simp only [decide_eq_true_eq]
      rw [dc_sum_get _ (dc_L_nodup a wit)]
      simp only [dc_L_mem hk hi]
      obtain ⟨hw1, hw2⟩ := hwit k hk
      have hw1' : wit k < ((clauses w)[k]?.getD []).length := by simpa using hw1
      by_cases hiw : i = wit k
      · subst hiw
        cases hs : sy w k (wit k) <;> rw [hs] at hw2 <;> simp only [litTrue] at hw2 <;>
          cases v <;> simp [hw1', hw2]
      · cases v <;> cases a i <;> simp [hiw]
    by_cases hp2 : p < 2 * (2 * NV w * mC w)
    · obtain ⟨b, rfl⟩ : ∃ b, p = 2 * NV w * mC w + b := ⟨p - 2 * NV w * mC w, by omega⟩
      rcases dc_dec_yz hN (show b < 2 * NV w * mC w by omega) with hb | ⟨k, hk, rfl⟩ | ⟨t, ht, rfl⟩
      · obtain ⟨i, hi, k, hk, rfl⟩ := dc_dec_ring hb
        rw [dc_T_yr hlen hi hk]; cases a i <;> simp
      · rw [dc_T_ycl hlen hk]; exact hcl k hk
      · rw [dc_T_yg hlen ht]; exact hgar t ht
    · obtain ⟨b, rfl⟩ : ∃ b, p = 2 * (2 * NV w * mC w) + b :=
        ⟨p - 2 * (2 * NV w * mC w), by omega⟩
      rcases dc_dec_yz hN (show b < 2 * NV w * mC w by omega) with hb | ⟨k, hk, rfl⟩ | ⟨t, ht, rfl⟩
      · obtain ⟨i, hi, k, hk, rfl⟩ := dc_dec_ring hb
        rw [dc_T_zr hlen hi hk]; cases a i <;> simp
      · rw [dc_T_zcl hlen hk]; exact hcl k hk
      · rw [dc_T_zg hlen ht]; exact hgar t ht
  · rintro ⟨y, hy⟩
    obtain ⟨rt, rf, c, g, hd⟩ := dc_decomp w y
    unfold qB at hy hd
    refine ⟨fun i => rt i 0, fun cl hcl => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hcl
    have hk' : k < mC w := hk
    have hZ : ∀ i < NV w, ∀ k < mC w, rf i k = !rt i k := by
      intro i hi k hk
      have := dc_ring_lt (m := mC w) hi
      have h := hy (2 * (2 * NV w * mC w) + (mC w * i + k)) (by omega)
      rw [hd, dc_T_zr hlen hi hk] at h
      revert h; cases rt i k <;> cases rf i k <;> simp
    have hY : ∀ i < NV w, ∀ k, k + 1 < mC w → rt i (k + 1) = !rf i k := by
      intro i hi k hk
      have := dc_ring_lt (m := mC w) hi
      have h := hy (2 * NV w * mC w + (mC w * i + (k + 1))) (by omega)
      rw [hd, dc_T_yr hlen hi hk] at h
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at h
      revert h; cases rt i (k + 1) <;> cases rf i k <;> simp
    have hconst : ∀ i < NV w, ∀ k < mC w, rt i k = rt i 0 := by
      intro i hi k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        rw [hY i hi k hk, hZ i hi k (by omega), ih (by omega)]; simp
    have hcl := hy (2 * NV w * mC w + (NV w * mC w + k))
      (by have := Nat.le_mul_of_pos_left (mC w) hN; omega)
    rw [hd, dc_T_ycl hlen hk'] at hcl
    obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_eq_of_ne hcl one_ne_zero)
    have hj : j < ((clauses w).getD k []).length := Finset.mem_range.1 hj
    have hb : c k j = true := by by_contra hc; simp [hc] at hne
    have hs : sy w k j = pos ∨ sy w k j = neg := by by_contra hc; simp [hc] at hne
    have hjN : j < NV w := lt_trans hj (hlen k)
    have hj' : j < ((clauses w)[k]?.getD []).length := by simpa using hj
    rw [← List.getD_eq_getElem _ [] hk]
    refine ⟨j, hj, ?_⟩
    show litTrue (fun i => rt i 0) j (sy w k j)
    have htip := hy (tipI (mC w) j k (decide (sy w k j = pos)))
      (by have := dc_tip_lt hjN hk' (decide (sy w k j = pos)); omega)
    rw [hd, dc_T_tip hjN hk'] at htip
    rcases hs with hs | hs
    · rw [hs] at htip ⊢
      simp only [litTrue]
      have h1 : rf j k = false := by
        revert htip; cases rf j k <;> simp [hj', hb]; omega
      rw [← hconst j hjN k hk', ← Bool.not_not (rt j k), ← hZ j hjN k hk', h1]; rfl
    · rw [hs] at htip ⊢
      simp only [litTrue]
      have h1 : rt j k = false := by
        revert htip; cases rt j k <;> simp [hj', hb]; omega
      rw [← hconst j hjN k hk', h1]

end Pnp.Karp.ThreeDM
