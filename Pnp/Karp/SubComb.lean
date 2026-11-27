import Pnp.Karp.SubsetSum

/-!
# SUBSET SUM: the combinatorics of the exact-cover instance

* `cnt_lt`: every digit is contained in fewer than `2 ^ BW w` items (no carries);
* `sat_iff_excov`: the formula is satisfiable iff the items have an exact cover.

Both are proved through an abstract count `sc_T` of the selected items containing a digit,
parametrised by the selection bits of the three groups of items (`sc_decomp`,
`sc_construct`), evaluated on each kind of digit (`sc_T_var`, `sc_T_cl`, `sc_T_p`, `sc_T_q`,
`sc_T_out`).
-/

namespace Pnp.Karp.SubsetSum

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## `cnt` over lists -/

theorem sc_cnt_append : ∀ (A B : List (ℕ → Bool)) (y : List Bool) (p : ℕ),
    cnt (A ++ B) y p = cnt A y p + cnt B (y.drop A.length) p
  | [], B, y, p => by simp [cnt]
  | S :: A, B, y, p => by
    simp only [List.cons_append, cnt, sc_cnt_append A B y.tail p, List.length_cons]
    have : y.tail.drop A.length = y.drop (A.length + 1) := by cases y <;> simp
    rw [this]; omega

theorem sc_cnt_app2 : ∀ (A B : List (ℕ → Bool)) (yA yB : List Bool) (p : ℕ),
    yA.length = A.length → cnt (A ++ B) (yA ++ yB) p = cnt A yA p + cnt B yB p
  | [], B, [], yB, p, _ => by simp [cnt]
  | S :: A, B, b :: yA, yB, p, h => by
    simp only [List.cons_append, cnt, List.headD_cons, List.tail_cons]
    rw [sc_cnt_app2 A B yA yB p (by simpa using h)]; simp [Nat.add_assoc]
  | [], _, _ :: _, _, _, h => by simp at h
  | _ :: _, _, [], _, _, h => by simp at h

theorem sc_len_fm {α : Type} (f : ℕ → List α) : ∀ n,
    ((List.range n).flatMap f).length = ∑ i ∈ Finset.range n, (f i).length
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, sc_len_fm f n,
      Finset.sum_range_succ]
    simp

theorem sc_cnt_fm2 (f : ℕ → List (ℕ → Bool)) (g : ℕ → List Bool)
    (hg : ∀ i, (g i).length = (f i).length) (p : ℕ) : ∀ n,
    cnt ((List.range n).flatMap f) ((List.range n).flatMap g) p =
      ∑ i ∈ Finset.range n, cnt (f i) (g i) p
  | 0 => by simp [cnt]
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, sc_cnt_app2,
      sc_cnt_fm2 f g hg p n, Finset.sum_range_succ]
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · rw [sc_len_fm, sc_len_fm]; simp [hg]

theorem sc_cnt_map2 (F : ℕ → ℕ → Bool) (b : ℕ → Bool) (p : ℕ) : ∀ n,
    cnt ((List.range n).map F) ((List.range n).map b) p =
      ∑ i ∈ Finset.range n, if b i && F i p then 1 else 0
  | 0 => by simp [cnt]
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, sc_cnt_app2,
      sc_cnt_map2 F b p n, Finset.sum_range_succ]
    · simp [cnt]
    · simp

theorem sc_cnt_fm (f : ℕ → List (ℕ → Bool)) (y : List Bool) (p : ℕ) : ∀ n,
    cnt ((List.range n).flatMap f) y p =
      ∑ i ∈ Finset.range n, cnt (f i) (y.drop (∑ i' ∈ Finset.range i, (f i').length)) p
  | 0 => by simp [cnt]
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, sc_cnt_append, sc_cnt_fm f y p n,
      Finset.sum_range_succ, sc_len_fm]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem sc_cnt_fm' (f : ℕ → List (ℕ → Bool)) (y : List Bool) (n : ℕ) :
    ∃ g : ℕ → List Bool, ∀ p,
      cnt ((List.range n).flatMap f) y p = ∑ i ∈ Finset.range n, cnt (f i) (g i) p :=
  ⟨_, fun p => sc_cnt_fm f y p n⟩

theorem sc_cnt_map (F : ℕ → ℕ → Bool) (y : List Bool) (p : ℕ) : ∀ n,
    cnt ((List.range n).map F) y p =
      ∑ i ∈ Finset.range n, if (y.drop i).headD false && F i p then 1 else 0
  | 0 => by simp [cnt]
  | n + 1 => by
    rw [List.range_succ, List.map_append, sc_cnt_append, sc_cnt_map F y p n,
      Finset.sum_range_succ]
    simp [cnt]

theorem sc_cnt_map' (F : ℕ → ℕ → Bool) (y : List Bool) (n : ℕ) :
    ∃ b : ℕ → Bool, ∀ p,
      cnt ((List.range n).map F) y p = ∑ i ∈ Finset.range n, if b i && F i p then 1 else 0 :=
  ⟨_, fun p => sc_cnt_map F y p n⟩

/-! ## The abstract count -/

/-- Selected variable items containing `p`. -/
def sc_fA (N m : ℕ) (a1 a2 : ℕ → Bool) (p j : ℕ) : ℕ :=
  (if a1 j && tP N m j p then 1 else 0) + (if a2 j && fP N m j p then 1 else 0)

/-- Selected witness items of clause `k` containing `p`. -/
def sc_fB (N : ℕ) (len : ℕ → ℕ) (s : ℕ → ℕ → SatSym) (b : ℕ → ℕ → Bool) (p k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (len k), if b k j && wP N k j (s k j) p then 1 else 0

/-- Selected fillers of clause `k` containing `p`. -/
def sc_fC (N : ℕ) (c1 c2 : ℕ → ℕ → Bool) (p k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range N,
    ((if c1 k j && oneP (pD N k j) p then 1 else 0) +
      (if c2 k j && oneP (qD N k j) p then 1 else 0))

/-- The number of selected items containing `p`. -/
def sc_T (N m : ℕ) (len : ℕ → ℕ) (s : ℕ → ℕ → SatSym) (a1 a2 : ℕ → Bool)
    (b c1 c2 : ℕ → ℕ → Bool) (p : ℕ) : ℕ :=
  (∑ j ∈ Finset.range N, sc_fA N m a1 a2 p j) + (∑ k ∈ Finset.range m, sc_fB N len s b p k) +
    ∑ k ∈ Finset.range m, sc_fC N c1 c2 p k

theorem sc_decomp (w : List SatSym) (y : List Bool) : ∃ a1 a2 b c1 c2, ∀ p,
    cnt (itemsP w) y p = sc_T (NV w) (mC w) (fun k => ((clauses w).getD k []).length) (sy w)
      a1 a2 b c1 c2 p := by
  obtain ⟨gA, hA⟩ := sc_cnt_fm' (fun j => [tP (NV w) (mC w) j, fP (NV w) (mC w) j]) y (NV w)
  obtain ⟨gB, hB⟩ := sc_cnt_fm' (fun k =>
      (List.range ((clauses w).getD k []).length).map fun j => wP (NV w) k j (sy w k j))
    (y.drop ((List.range (NV w)).flatMap
      (fun j => [tP (NV w) (mC w) j, fP (NV w) (mC w) j])).length) (mC w)
  obtain ⟨gC, hC⟩ := sc_cnt_fm' (fun k => (List.range (NV w)).flatMap fun j =>
      [oneP (pD (NV w) k j), oneP (qD (NV w) k j)])
    (y.drop ((List.range (NV w)).flatMap (fun j => [tP (NV w) (mC w) j, fP (NV w) (mC w) j]) ++
      (List.range (mC w)).flatMap (fun k =>
        (List.range ((clauses w).getD k []).length).map fun j => wP (NV w) k j (sy w k j))).length)
    (mC w)
  have hB' : ∀ k, ∃ bk : ℕ → Bool, ∀ p,
      cnt ((List.range ((clauses w).getD k []).length).map fun j => wP (NV w) k j (sy w k j))
        (gB k) p = ∑ i ∈ Finset.range ((clauses w).getD k []).length,
          if bk i && wP (NV w) k i (sy w k i) p then 1 else 0 :=
    fun k => sc_cnt_map' (fun j => wP (NV w) k j (sy w k j)) (gB k) _
  choose bB hbB using hB'
  have hC' : ∀ k, ∃ g : ℕ → List Bool, ∀ p,
      cnt ((List.range (NV w)).flatMap fun j => [oneP (pD (NV w) k j), oneP (qD (NV w) k j)])
        (gC k) p = ∑ i ∈ Finset.range (NV w),
          cnt [oneP (pD (NV w) k i), oneP (qD (NV w) k i)] (g i) p :=
    fun k => sc_cnt_fm' _ (gC k) _
  choose gCC hgCC using hC'
  refine ⟨fun j => (gA j).headD false, fun j => (gA j).tail.headD false, bB,
    fun k j => (gCC k j).headD false, fun k j => (gCC k j).tail.headD false, fun p => ?_⟩
  unfold itemsP
  rw [sc_cnt_append, sc_cnt_append, hA, hB, hC]
  unfold sc_T sc_fA sc_fB sc_fC
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun j _ => by simp [cnt]
  · exact Finset.sum_congr rfl fun k _ => hbB k p
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hgCC k p]
    exact Finset.sum_congr rfl fun j _ => by simp [cnt]

theorem sc_construct (w : List SatSym) (a1 a2 : ℕ → Bool) (b c1 c2 : ℕ → ℕ → Bool) :
    ∃ y, ∀ p, cnt (itemsP w) y p =
      sc_T (NV w) (mC w) (fun k => ((clauses w).getD k []).length) (sy w) a1 a2 b c1 c2 p := by
  refine ⟨(List.range (NV w)).flatMap (fun j => [a1 j, a2 j]) ++
    (List.range (mC w)).flatMap (fun k => (List.range ((clauses w).getD k []).length).map (b k)) ++
    (List.range (mC w)).flatMap (fun k => (List.range (NV w)).flatMap fun j => [c1 k j, c2 k j]),
    fun p => ?_⟩
  unfold itemsP
  rw [sc_cnt_app2, sc_cnt_app2, sc_cnt_fm2, sc_cnt_fm2, sc_cnt_fm2]
  · unfold sc_T sc_fA sc_fB sc_fC
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
    · exact Finset.sum_congr rfl fun j _ => by simp [cnt]
    · exact Finset.sum_congr rfl fun k _ => sc_cnt_map2 _ _ p _
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [sc_cnt_fm2]
      · exact Finset.sum_congr rfl fun j _ => by simp [cnt]
      · intro j; simp
  · intro k; rw [sc_len_fm, sc_len_fm]; simp
  · intro k; simp
  · intro k; simp
  · rw [sc_len_fm, sc_len_fm]; simp
  · simp only [List.length_append]; rw [sc_len_fm, sc_len_fm, sc_len_fm, sc_len_fm]; simp

/-! ## Digits -/

theorem sc_blk {N k k' r r' : ℕ} (hr : r < 2 * N + 1) (hr' : r' < 2 * N + 1)
    (h : (2 * N + 1) * k + r = (2 * N + 1) * k' + r') : k = k' ∧ r = r' := by
  rcases lt_trichotomy k k' with hk | hk | hk
  · have := Nat.mul_le_mul_left (2 * N + 1) (show k + 1 ≤ k' from hk)
    rw [Nat.mul_succ] at this; omega
  · subst hk; omega
  · have := Nat.mul_le_mul_left (2 * N + 1) (show k' + 1 ≤ k from hk)
    rw [Nat.mul_succ] at this; omega

theorem sc_blk_lt {N k m : ℕ} (hk : k < m) : (2 * N + 1) * k + (2 * N + 1) ≤ (2 * N + 1) * m := by
  have := Nat.mul_le_mul_left (2 * N + 1) (show k + 1 ≤ m from hk)
  rw [Nat.mul_succ] at this; exact this

variable {N m k k' j j' j0 p : ℕ}

theorem sc_v_cl (h : j0 < N) : j0 ≠ clD N k := by unfold clD; omega
theorem sc_v_p (h : j0 < N) : j0 ≠ pD N k j := by unfold pD clD; omega
theorem sc_v_q (h : j0 < N) : j0 ≠ qD N k j := by unfold qD clD; omega
theorem sc_cl_v (h : j < N) : clD N k ≠ j := fun e => sc_v_cl h e.symm
theorem sc_p_v (h : j < N) : pD N k j0 ≠ j := fun e => sc_v_p h e.symm
theorem sc_q_v (h : j < N) : qD N k j0 ≠ j := fun e => sc_v_q h e.symm

theorem sc_cl_cl : clD N k = clD N k' ↔ k = k' := by
  unfold clD; constructor
  · intro h; exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * N + 1) (by omega)
  · rintro rfl; rfl

theorem sc_cl_p (hj : j < N) : clD N k ≠ pD N k' j := by
  unfold pD clD; intro h
  have := @sc_blk N k k' 0 (1 + 2 * j) (by omega) (by omega) (by omega); omega

theorem sc_cl_q (hj : j < N) : clD N k ≠ qD N k' j := by
  unfold qD clD; intro h
  have := @sc_blk N k k' 0 (2 + 2 * j) (by omega) (by omega) (by omega); omega

theorem sc_p_cl (hj : j < N) : pD N k j ≠ clD N k' := fun e => sc_cl_p hj e.symm
theorem sc_q_cl (hj : j < N) : qD N k j ≠ clD N k' := fun e => sc_cl_q hj e.symm

theorem sc_p_p (hj : j < N) (hj' : j' < N) : pD N k j = pD N k' j' ↔ k = k' ∧ j = j' := by
  unfold pD clD; constructor
  · intro h
    have := @sc_blk N k k' (1 + 2 * j) (1 + 2 * j') (by omega) (by omega) (by omega); omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem sc_q_q (hj : j < N) (hj' : j' < N) : qD N k j = qD N k' j' ↔ k = k' ∧ j = j' := by
  unfold qD clD; constructor
  · intro h
    have := @sc_blk N k k' (2 + 2 * j) (2 + 2 * j') (by omega) (by omega) (by omega); omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem sc_p_q (hj : j < N) (hj' : j' < N) : pD N k j ≠ qD N k' j' := by
  unfold pD qD clD; intro h
  have := @sc_blk N k k' (1 + 2 * j) (2 + 2 * j') (by omega) (by omega) (by omega); omega

theorem sc_q_p (hj : j < N) (hj' : j' < N) : qD N k j ≠ pD N k' j' :=
  fun e => sc_p_q hj' hj e.symm

theorem sc_o_v (hp : DD N m ≤ p) (hj : j < N) : p ≠ j := by unfold DD at hp; omega

theorem sc_o_cl (hp : DD N m ≤ p) (hk : k < m) : p ≠ clD N k := by
  unfold DD at hp; unfold clD; have := @sc_blk_lt N k m hk; omega

theorem sc_o_p (hp : DD N m ≤ p) (hk : k < m) (hj : j < N) : p ≠ pD N k j := by
  unfold DD at hp; unfold pD clD; have := @sc_blk_lt N k m hk; omega

theorem sc_o_q (hp : DD N m ≤ p) (hk : k < m) (hj : j < N) : p ≠ qD N k j := by
  unfold DD at hp; unfold qD clD; have := @sc_blk_lt N k m hk; omega

theorem sc_cl_lt (hk : k < m) : clD N k < DD N m := by
  unfold clD DD; have := @sc_blk_lt N k m hk; omega

theorem sc_p_lt (hk : k < m) (hj : j < N) : pD N k j < DD N m := by
  unfold pD clD DD; have := @sc_blk_lt N k m hk; omega

theorem sc_q_lt (hk : k < m) (hj : j < N) : qD N k j < DD N m := by
  unfold qD clD DD; have := @sc_blk_lt N k m hk; omega

theorem sc_v_lt (hj : j < N) : j < DD N m := by unfold DD; omega

theorem sc_decode (hp : p < DD N m) : p < N ∨ (∃ k < m, p = clD N k) ∨
    (∃ k < m, ∃ j < N, p = pD N k j) ∨ (∃ k < m, ∃ j < N, p = qD N k j) := by
  by_cases h : p < N
  · exact Or.inl h
  right
  have hd := Nat.div_add_mod (p - N) (2 * N + 1)
  have hr := Nat.mod_lt (p - N) (show 2 * N + 1 > 0 by omega)
  have hk : (p - N) / (2 * N + 1) < m := by
    by_contra hc
    have := Nat.mul_le_mul_left (2 * N + 1) (show m ≤ (p - N) / (2 * N + 1) by omega)
    unfold DD at hp; omega
  generalize (p - N) / (2 * N + 1) = k at hd hk
  generalize (p - N) % (2 * N + 1) = r at hd hr
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · left; exact ⟨k, hk, by unfold clD; omega⟩
  · rcases Nat.even_or_odd r with ⟨t, ht⟩ | ⟨t, ht⟩
    · right; right; exact ⟨k, hk, t - 1, by omega, by unfold qD clD; omega⟩
    · right; left; exact ⟨k, hk, t, by omega, by unfold pD clD; omega⟩

/-! ## Items at digits -/

theorem sc_wP (s : SatSym) : wP N k j s p =
    ((decide (s = pos) && decide (p = clD N k ∨ p = pD N k j)) ||
      (decide (s = neg) && decide (p = clD N k ∨ p = qD N k j))) := by
  cases s <;> simp [wP]

theorem sc_sum_single {f : ℕ → ℕ} {n i0 : ℕ} (h : ∀ i < n, i ≠ i0 → f i = 0) :
    ∑ i ∈ Finset.range n, f i = if i0 < n then f i0 else 0 := by
  split_ifs with hi
  · exact Finset.sum_eq_single_of_mem i0 (Finset.mem_range.2 hi)
      (fun i hi' hne => h i (Finset.mem_range.1 hi') hne)
  · exact Finset.sum_eq_zero fun i hi' =>
      h i (Finset.mem_range.1 hi') (by rintro rfl; exact hi (Finset.mem_range.1 hi'))

variable {len : ℕ → ℕ} {s : ℕ → ℕ → SatSym} {a1 a2 : ℕ → Bool} {b c1 c2 : ℕ → ℕ → Bool}

theorem sc_T_var (_hlen : ∀ k, len k < N) (hj0 : j0 < N) :
    sc_T N m len s a1 a2 b c1 c2 j0 = (if a1 j0 then 1 else 0) + (if a2 j0 then 1 else 0) := by
  have hA : ∑ j ∈ Finset.range N, sc_fA N m a1 a2 j0 j =
      (if a1 j0 then 1 else 0) + (if a2 j0 then 1 else 0) := by
    rw [sc_sum_single (i0 := j0) (fun j hj hne => ?_)]
    · simp [sc_fA, hj0, tP, fP, sc_v_q hj0, sc_v_p hj0]
    · simp [sc_fA, tP, fP, sc_v_q hj0, sc_v_p hj0, Ne.symm hne]
  have hB : ∑ k ∈ Finset.range m, sc_fB N len s b j0 k = 0 :=
    Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => by
      simp [sc_wP, sc_v_cl hj0, sc_v_p hj0, sc_v_q hj0]
  have hC : ∑ k ∈ Finset.range m, sc_fC N c1 c2 j0 k = 0 :=
    Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => by
      simp [oneP, sc_v_p hj0, sc_v_q hj0]
  unfold sc_T; rw [hA, hB, hC]; simp

theorem sc_T_cl (hlen : ∀ k, len k < N) (hk0 : k0 < m) :
    sc_T N m len s a1 a2 b c1 c2 (clD N k0) = ∑ j ∈ Finset.range (len k0),
      if b k0 j && decide (s k0 j = pos ∨ s k0 j = neg) then 1 else 0 := by
  have hA : ∑ j ∈ Finset.range N, sc_fA N m a1 a2 (clD N k0) j = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have hj := Finset.mem_range.1 hj
      simp [sc_fA, tP, fP, sc_cl_v hj, sc_cl_p hj, sc_cl_q hj]
  have hB : ∑ k ∈ Finset.range m, sc_fB N len s b (clD N k0) k = ∑ j ∈ Finset.range (len k0),
      if b k0 j && decide (s k0 j = pos ∨ s k0 j = neg) then 1 else 0 := by
    rw [sc_sum_single (i0 := k0) (fun k hk hne => ?_)]
    · rw [if_pos hk0]; unfold sc_fB
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj : j < N := lt_trans (Finset.mem_range.1 hj) (hlen k0)
      cases h : s k0 j <;> simp [sc_wP, sc_cl_p hj, sc_cl_q hj]
    · unfold sc_fB
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj : j < N := lt_trans (Finset.mem_range.1 hj) (hlen k)
      simp [sc_wP, sc_cl_p hj, sc_cl_q hj, sc_cl_cl, Ne.symm hne]
  have hC : ∑ k ∈ Finset.range m, sc_fC N c1 c2 (clD N k0) k = 0 :=
    Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j hj => by
      have hj := Finset.mem_range.1 hj
      simp [oneP, sc_cl_p hj, sc_cl_q hj]
  unfold sc_T; rw [hA, hB, hC]; simp

theorem sc_T_p (hlen : ∀ k, len k < N) (hk0 : k0 < m) (hj0 : j0 < N) :
    sc_T N m len s a1 a2 b c1 c2 (pD N k0 j0) = (if a2 j0 then 1 else 0) +
      (if j0 < len k0 ∧ b k0 j0 = true ∧ s k0 j0 = pos then 1 else 0) +
      (if c1 k0 j0 then 1 else 0) := by
  have hA : ∑ j ∈ Finset.range N, sc_fA N m a1 a2 (pD N k0 j0) j = if a2 j0 then 1 else 0 := by
    rw [sc_sum_single (i0 := j0) (fun j hj hne => ?_)]
    · simp [sc_fA, hj0, hk0, tP, fP, sc_p_v hj0, sc_p_q hj0 hj0, sc_p_p hj0 hj0]
    · simp [sc_fA, tP, fP, sc_p_v hj, sc_p_q hj0 hj, sc_p_p hj0 hj, Ne.symm hne]
  have hB : ∑ k ∈ Finset.range m, sc_fB N len s b (pD N k0 j0) k =
      if j0 < len k0 ∧ b k0 j0 = true ∧ s k0 j0 = pos then 1 else 0 := by
    rw [sc_sum_single (i0 := k0) (fun k hk hne => ?_)]
    · rw [if_pos hk0]; unfold sc_fB
      rw [sc_sum_single (i0 := j0) (fun j hj hne => ?_)]
      · by_cases hl : j0 < len k0
        · rw [if_pos hl]
          cases h : s k0 j0 <;> simp [sc_wP, hl, sc_p_cl hj0, sc_p_q hj0 hj0]
        · rw [if_neg hl]; simp [hl]
      · have hj : j < N := lt_trans hj (hlen k0)
        simp [sc_wP, sc_p_cl hj0, sc_p_q hj0 hj, sc_p_p hj0 hj, Ne.symm hne]
    · unfold sc_fB
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj : j < N := lt_trans (Finset.mem_range.1 hj) (hlen k)
      simp [sc_wP, sc_p_cl hj0, sc_p_q hj0 hj, sc_p_p hj0 hj, Ne.symm hne]
  have hC : ∑ k ∈ Finset.range m, sc_fC N c1 c2 (pD N k0 j0) k = if c1 k0 j0 then 1 else 0 := by
    rw [sc_sum_single (i0 := k0) (fun k hk hne => ?_)]
    · rw [if_pos hk0]; unfold sc_fC
      rw [sc_sum_single (i0 := j0) (fun j hj hne => ?_)]
      · simp [oneP, hj0, sc_p_q hj0 hj0]
      · simp [oneP, sc_p_q hj0 hj, sc_p_p hj0 hj, Ne.symm hne]
    · unfold sc_fC
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj := Finset.mem_range.1 hj
      simp [oneP, sc_p_q hj0 hj, sc_p_p hj0 hj, Ne.symm hne]
  unfold sc_T; rw [hA, hB, hC]

theorem sc_T_q (hlen : ∀ k, len k < N) (hk0 : k0 < m) (hj0 : j0 < N) :
    sc_T N m len s a1 a2 b c1 c2 (qD N k0 j0) = (if a1 j0 then 1 else 0) +
      (if j0 < len k0 ∧ b k0 j0 = true ∧ s k0 j0 = neg then 1 else 0) +
      (if c2 k0 j0 then 1 else 0) := by
  have hA : ∑ j ∈ Finset.range N, sc_fA N m a1 a2 (qD N k0 j0) j = if a1 j0 then 1 else 0 := by
    rw [sc_sum_single (i0 := j0) (fun j hj hne => ?_)]
    · simp [sc_fA, hj0, hk0, tP, fP, sc_q_v hj0, sc_q_p hj0 hj0, sc_q_q hj0 hj0]
    · simp [sc_fA, tP, fP, sc_q_v hj, sc_q_p hj0 hj, sc_q_q hj0 hj, Ne.symm hne]
  have hB : ∑ k ∈ Finset.range m, sc_fB N len s b (qD N k0 j0) k =
      if j0 < len k0 ∧ b k0 j0 = true ∧ s k0 j0 = neg then 1 else 0 := by
    rw [sc_sum_single (i0 := k0) (fun k hk hne => ?_)]
    · rw [if_pos hk0]; unfold sc_fB
      rw [sc_sum_single (i0 := j0) (fun j hj hne => ?_)]
      · by_cases hl : j0 < len k0
        · rw [if_pos hl]
          cases h : s k0 j0 <;> simp [sc_wP, hl, sc_q_cl hj0, sc_q_p hj0 hj0]
        · rw [if_neg hl]; simp [hl]
      · have hj : j < N := lt_trans hj (hlen k0)
        simp [sc_wP, sc_q_cl hj0, sc_q_p hj0 hj, sc_q_q hj0 hj, Ne.symm hne]
    · unfold sc_fB
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj : j < N := lt_trans (Finset.mem_range.1 hj) (hlen k)
      simp [sc_wP, sc_q_cl hj0, sc_q_p hj0 hj, sc_q_q hj0 hj, Ne.symm hne]
  have hC : ∑ k ∈ Finset.range m, sc_fC N c1 c2 (qD N k0 j0) k = if c2 k0 j0 then 1 else 0 := by
    rw [sc_sum_single (i0 := k0) (fun k hk hne => ?_)]
    · rw [if_pos hk0]; unfold sc_fC
      rw [sc_sum_single (i0 := j0) (fun j hj hne => ?_)]
      · simp [oneP, hj0, sc_q_p hj0 hj0]
      · simp [oneP, sc_q_p hj0 hj, sc_q_q hj0 hj, Ne.symm hne]
    · unfold sc_fC
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj := Finset.mem_range.1 hj
      simp [oneP, sc_q_p hj0 hj, sc_q_q hj0 hj, Ne.symm hne]
  unfold sc_T; rw [hA, hB, hC]

theorem sc_T_out (hlen : ∀ k, len k < N) (hp : DD N m ≤ p) :
    sc_T N m len s a1 a2 b c1 c2 p = 0 := by
  have h1 : ∑ j ∈ Finset.range N, sc_fA N m a1 a2 p j = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have hj := Finset.mem_range.1 hj
      simp only [sc_fA, tP, fP, sc_o_v hp hj, false_or]
      have e1 : ¬ ∃ k < m, p = qD N k j := fun ⟨k, hk, e⟩ => sc_o_q hp hk hj e
      have e2 : ¬ ∃ k < m, p = pD N k j := fun ⟨k, hk, e⟩ => sc_o_p hp hk hj e
      simp [e1, e2]
  have h2 : ∑ k ∈ Finset.range m, sc_fB N len s b p k = 0 :=
    Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun j hj => by
      have hk := Finset.mem_range.1 hk
      have hj : j < N := lt_trans (Finset.mem_range.1 hj) (hlen k)
      simp [sc_wP, sc_o_cl hp hk, sc_o_p hp hk hj, sc_o_q hp hk hj]
  have h3 : ∑ k ∈ Finset.range m, sc_fC N c1 c2 p k = 0 :=
    Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun j hj => by
      have hk := Finset.mem_range.1 hk
      have hj := Finset.mem_range.1 hj
      simp [oneP, sc_o_p hp hk hj, sc_o_q hp hk hj]
  unfold sc_T; rw [h1, h2, h3]

/-! ## The final theorems -/

theorem sc_len_clause_lt (w : List SatSym) (k : ℕ) : ((clauses w).getD k []).length < NV w := by
  by_cases hk : k < (clauses w).length
  · rw [List.getD_eq_getElem _ _ hk]
    have h : List.Sublist ((clauses w)[k] ++ [sep]) (trunc w) := by
      unfold trunc; rw [List.flatMap_def]
      exact List.sublist_flatten_of_mem (List.mem_map.2 ⟨_, List.getElem_mem hk, rfl⟩)
    have := h.length_le; simp at this; unfold NV; omega
  · rw [List.getD_eq_default _ _ (by omega)]; simp [NV]

theorem cnt_lt (w : List SatSym) : ∀ y p, cnt (itemsP w) y p < 2 ^ BW w := by
  intro y p
  obtain ⟨a1, a2, b, c1, c2, h⟩ := sc_decomp w y
  rw [h]
  have hlen := sc_len_clause_lt w
  have h4 : 4 ≤ 2 ^ BW w := by
    have : 2 ≤ BW w := by unfold BW NV; omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ BW w := Nat.pow_le_pow_right (by norm_num) this
  have hN : NV w < 2 ^ BW w :=
    lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by norm_num) (by unfold BW; omega))
  by_cases hp : p < DD (NV w) (mC w)
  · rcases sc_decode hp with hv | ⟨k, hk, rfl⟩ | ⟨k, hk, j, hj, rfl⟩ | ⟨k, hk, j, hj, rfl⟩
    · rw [sc_T_var hlen hv]; split_ifs <;> omega
    · rw [sc_T_cl hlen hk]
      calc _ ≤ ∑ j ∈ Finset.range (((clauses w).getD k []).length), 1 :=
            Finset.sum_le_sum fun _ _ => by split_ifs <;> omega
        _ < 2 ^ BW w := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]; exact lt_trans (hlen k) hN
    · rw [sc_T_p hlen hk hj]; split_ifs <;> omega
    · rw [sc_T_q hlen hk hj]; split_ifs <;> omega
  · rw [sc_T_out hlen (by omega)]; omega

theorem sc_lit (a : ℕ → Bool) (j : ℕ) (s : SatSym) (h : litTrue a j s) : s = pos ∨ s = neg := by
  cases s <;> simp_all [litTrue]

theorem sat_iff_excov (w : List SatSym) : SATLang w ↔ ExCov w := by
  have hlen := sc_len_clause_lt w
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
    obtain ⟨y, hy⟩ := sc_construct w a (fun j => !a j) (fun k j => decide (j = wit k))
      (fun k j => a j && !decide (j = wit k ∧ sy w k j = pos))
      (fun k j => !a j && !decide (j = wit k ∧ sy w k j = neg))
    refine ⟨y, fun p hp => ?_⟩
    rw [hy]
    rcases sc_decode hp with hv | ⟨k, hk, rfl⟩ | ⟨k, hk, j, hj, rfl⟩ | ⟨k, hk, j, hj, rfl⟩
    · rw [sc_T_var hlen hv]; cases a p <;> simp
    · rw [sc_T_cl hlen hk]
      obtain ⟨hw1, hw2⟩ := hwit k hk
      have hw1 : wit k < ((clauses w)[k]?.getD []).length := by simpa using hw1
      rw [sc_sum_single (i0 := wit k) (fun j _ hne => by simp [hne])]
      simp [hw1, sc_lit a _ _ hw2]
    · rw [sc_T_p hlen hk hj]
      obtain ⟨hw1, hw2⟩ := hwit k hk
      have hw1 : wit k < ((clauses w)[k]?.getD []).length := by simpa using hw1
      by_cases h1 : j = wit k
      · subst h1
        by_cases h2 : sy w k (wit k) = pos
        · have h3 := hw2; rw [h2] at h3; simp only [litTrue] at h3
          simp [hw1, h2, h3]
        · cases h : a (wit k) <;> simp [h2]
      · cases h : a j <;> simp [h1]
    · rw [sc_T_q hlen hk hj]
      obtain ⟨hw1, hw2⟩ := hwit k hk
      have hw1 : wit k < ((clauses w)[k]?.getD []).length := by simpa using hw1
      by_cases h1 : j = wit k
      · subst h1
        by_cases h2 : sy w k (wit k) = neg
        · have h3 := hw2; rw [h2] at h3; simp only [litTrue] at h3
          simp [hw1, h2, h3]
        · cases h : a (wit k) <;> simp [h2]
      · cases h : a j <;> simp [h1]
  · rintro ⟨y, hy⟩
    obtain ⟨a1, a2, b, c1, c2, hd⟩ := sc_decomp w y
    refine ⟨a1, fun c hc => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hc
    have hk' : k < mC w := hk
    have hcl := hy _ (sc_cl_lt hk')
    rw [hd, sc_T_cl hlen hk'] at hcl
    obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_eq_of_ne hcl one_ne_zero)
    have hj : j < ((clauses w).getD k []).length := Finset.mem_range.1 hj
    have hb : b k j = true := by by_contra hc; simp [hc] at hne
    have hs : sy w k j = pos ∨ sy w k j = neg := by by_contra hc; simp [hc] at hne
    have hjN : j < NV w := lt_trans hj (hlen k)
    have hj' : j < ((clauses w)[k]?.getD []).length := by simpa using hj
    rw [← List.getD_eq_getElem _ [] hk]
    refine ⟨j, hj, ?_⟩
    show litTrue a1 j (sy w k j)
    have hv := hy j (sc_v_lt hjN)
    rw [hd, sc_T_var hlen hjN] at hv
    rcases hs with hs | hs
    · have hpd := hy _ (sc_p_lt hk' hjN)
      rw [hd, sc_T_p hlen hk' hjN] at hpd
      rw [hs]; show a1 j = true
      revert hpd hv
      cases a1 j <;> cases a2 j <;> cases c1 k j <;> simp [hj', hb, hs]
    · have hqd := hy _ (sc_q_lt hk' hjN)
      rw [hd, sc_T_q hlen hk' hjN] at hqd
      rw [hs]; show a1 j = false
      revert hqd hv
      cases a1 j <;> cases a2 j <;> cases c2 k j <;> simp [hj', hb, hs]

end Pnp.Karp.SubsetSum
