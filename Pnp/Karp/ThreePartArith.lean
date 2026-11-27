import Pnp.Karp.ThreePart

/-!
# 3-PARTITION: arithmetic of the items (no carries) and the rigidity of the groups
-/

namespace Pnp.Karp.ThreePart

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM

/-- The parameters of an item are in range. -/
def OkEl (q M : ℕ) : El → Prop
  | .cp c e _ => c < 3 ∧ e < q
  | .al c t _ => c < 3 ∧ t < M
  | .be c t e => c < 3 ∧ t < M ∧ e < q

/-- The intended groups: `{cp c e s, al c t s, be c t e}` and `{al 0 t s, al 1 t s, al 2 t s}`
(in any order). -/
def IsPat (g : List El) : Prop :=
  (∃ c e t s, g.Perm [.cp c e s, .al c t s, .be c t e]) ∨
    ∃ t s, g.Perm [.al 0 t s, .al 1 t s, .al 2 t s]

/-! ## Base-`4` arithmetic -/
/-- Base-`4` value of a `0/1` digit list (least significant first). -/
def tpa_v : List Bool → ℕ
  | [] => 0
  | b :: r => b.toNat + 4 * tpa_v r

/-- The all-ones value. -/
def tpa_R (n : ℕ) : ℕ := tpa_v (List.replicate n true)

theorem tpa_v_append (a b : List Bool) : tpa_v (a ++ b) = tpa_v a + 4 ^ a.length * tpa_v b := by
  induction a with
  | nil => simp [tpa_v]
  | cons x a ih => simp only [List.cons_append, tpa_v, ih, List.length_cons, pow_succ]; ring

theorem tpa_v_le (a : List Bool) : tpa_v a ≤ tpa_R a.length := by
  induction a with
  | nil => simp [tpa_v, tpa_R]
  | cons x a ih =>
    simp only [tpa_R, List.length_cons, List.replicate_succ, tpa_v] at ih ⊢
    have : x.toNat ≤ 1 := Bool.toNat_le x
    simp only [Bool.toNat_true]; omega

theorem tpa_R_lt (n : ℕ) : tpa_R n < 4 ^ n := by
  induction n with
  | zero => simp [tpa_R, tpa_v]
  | succ n ih =>
    simp only [tpa_R, List.replicate_succ, tpa_v, Bool.toNat_true] at ih ⊢
    rw [pow_succ]; omega

theorem tpa_bv_flat (l : List Bool) :
    bv (l.flatMap fun b => [if b then pos else zero, zero]) = tpa_v l := by
  induction l with
  | nil => simp [bv, tpa_v]
  | cons x l ih =>
    rw [List.flatMap_cons]
    cases x <;> simp [bv, tpa_v, ih] <;> ring

theorem tpa_bv_rep (n : ℕ) (r : List SatSym) :
    bv ((List.replicate n [pos, zero]).flatten ++ r) = tpa_R n + 4 ^ n * bv r := by
  induction n with
  | zero => simp [tpa_R, tpa_v]
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append, bv,
      tpa_R, tpa_v] at ih ⊢
    rw [ih, pow_succ]; simp; ring

theorem tpa_v3 (n : ℕ) (a b c : List Bool) (ha : a.length = n) (hb : b.length = n)
    (hc : c.length = n) : tpa_v a + tpa_v b + tpa_v c = tpa_R n ↔
      ∀ i < n, (a.getD i false).toNat + (b.getD i false).toNat + (c.getD i false).toNat = 1 := by
  induction n generalizing a b c with
  | zero =>
    rw [List.length_eq_zero_iff] at ha hb hc; subst ha hb hc; simp [tpa_v, tpa_R]
  | succ n ih =>
    match a, b, c, ha, hb, hc with
    | x :: a, y :: b, z :: c, ha, hb, hc =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at ha hb hc
      have := ih a b c ha hb hc
      simp only [tpa_v, tpa_R, List.replicate_succ, Bool.toNat_true] at this ⊢
      have hx := Bool.toNat_le x; have hy := Bool.toNat_le y; have hz := Bool.toNat_le z
      constructor
      · intro h
        have h1 : x.toNat + y.toNat + z.toNat = 1 := by omega
        have h2 := this.1 (by omega)
        intro i hi
        cases i with
        | zero => simpa using h1
        | succ i => simpa using h2 i (by omega)
      · intro h
        have h1 := h 0 (by omega)
        have h2 := this.2 (fun i hi => by simpa using h (i + 1) (by omega))
        simp at h1; omega

theorem tpa_v3_app (n m : ℕ) (a b c a' b' c' : List Bool) (ha : a.length = n) (hb : b.length = n)
    (hc : c.length = n) (ha' : a'.length = m) (hb' : b'.length = m) (hc' : c'.length = m) :
    tpa_v (a ++ a') + tpa_v (b ++ b') + tpa_v (c ++ c') = tpa_R (n + m) ↔
      (tpa_v a + tpa_v b + tpa_v c = tpa_R n ∧ tpa_v a' + tpa_v b' + tpa_v c' = tpa_R m) := by
  rw [tpa_v3 (n + m) _ _ _ (by simp [*]) (by simp [*]) (by simp [*]), tpa_v3 n _ _ _ ha hb hc,
    tpa_v3 m _ _ _ ha' hb' hc']
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by omega)
      rwa [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)] at this
    · have := h (n + i) (by omega)
      rwa [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), ha, hb, hc, Nat.add_sub_cancel_left] at this
  · rintro ⟨h1, h2⟩ i hi
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)]; exact h1 i hin
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), ha, hb, hc]; exact h2 (i - n) (by omega)

theorem tpa_v3_map (n : ℕ) (f g h : ℕ → Bool) :
    tpa_v ((List.range n).map f) + tpa_v ((List.range n).map g) + tpa_v ((List.range n).map h) =
      tpa_R n ↔ ∀ i < n, (f i).toNat + (g i).toNat + (h i).toNat = 1 := by
  rw [tpa_v3 n _ _ _ (by simp) (by simp) (by simp)]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  simp [List.getD_eq_getElem?_getD, hi]

/-- Pointwise index-block digits. -/
def tpa_I : El → ℕ → ℕ → Bool
  | .cp c0 e _, c, i => if c = c0 then decide (i = e) else false
  | .al c0 _ _, c, _ => decide (c = (c0 + 2) % 3)
  | .be c0 _ e, c, i => if c = c0 then decide (i ≠ e) else decide (c = (c0 + 1) % 3)

/-- Pointwise tag-block digits. -/
def tpa_L : El → ℕ → ℕ → Bool
  | .cp _ _ _, _, _ => false
  | .al c0 t _, c, i => if c = c0 then decide (i = t) else
      if c = (c0 + 1) % 3 then decide (i ≠ t) else false
  | .be c0 t _, c, i => if c = c0 then decide (i ≠ t) else
      if c = (c0 + 1) % 3 then decide (i = t) else true

theorem tpa_rep (n : ℕ) (b : Bool) : List.replicate n b = (List.range n).map (fun _ => b) := by
  simp [List.map_const']

theorem tpa_blkI (q : ℕ) (x : El) (c : ℕ) : blkI q x c = (List.range q).map (tpa_I x c) := by
  cases x <;> simp only [blkI] <;> (try split_ifs) <;> simp only [ohB, coB, tpa_rep] <;>
    apply List.map_congr_left <;> intro i _ <;> simp_all [tpa_I]

theorem tpa_blkL (M : ℕ) (x : El) (c : ℕ) : blkL M x c = (List.range M).map (tpa_L x c) := by
  cases x <;> simp only [blkL] <;> (try split_ifs) <;> simp only [ohB, coB, tpa_rep] <;>
    apply List.map_congr_left <;> intro i _ <;> simp_all [tpa_L]

/-- The digits without the leading one. -/
def tpa_D (q M : ℕ) (x : El) : List Bool :=
  (List.range q).map (tpa_I x 0) ++ (List.range q).map (tpa_I x 1) ++
    (List.range q).map (tpa_I x 2) ++ (List.range M).map (tpa_L x 0) ++
    (List.range M).map (tpa_L x 1) ++ (List.range M).map (tpa_L x 2) ++ [st1 x, st2 x]

theorem tpa_D_len (q M : ℕ) (x : El) : (tpa_D q M x).length = 3 * q + 3 * M + 2 := by
  simp [tpa_D]; ring

theorem tpa_bv_el (q M : ℕ) (x : El) :
    bv (elRow q M x) = tpa_v (tpa_D q M x) + 4 ^ (3 * q + 3 * M + 2) := by
  have : digs q M x = tpa_D q M x ++ [true] := by
    simp [digs, tpa_D, tpa_blkI, tpa_blkL]
  rw [elRow, tpa_bv_flat, this, tpa_v_append, tpa_D_len]; simp [tpa_v]

theorem tpa_bv_b (q M : ℕ) :
    bv (bRow q M) = tpa_R (3 * q + 3 * M + 2) + 3 * 4 ^ (3 * q + 3 * M + 2) := by
  rw [bRow, tpa_bv_rep]; simp [bv]; ring

/-- Every item is strictly between a quarter and a half of the bound. -/
theorem tp_el_bounds (q M : ℕ) (x : El) :
    bv (bRow q M) < 4 * bv (elRow q M x) ∧ 2 * bv (elRow q M x) < bv (bRow q M) := by
  rw [tpa_bv_el, tpa_bv_b]
  have h1 := tpa_v_le (tpa_D q M x); rw [tpa_D_len] at h1
  have h2 := tpa_R_lt (3 * q + 3 * M + 2)
  constructor <;> omega

/-- The exact-cover condition on the positions for three items. -/
def tpa_Ex (q M : ℕ) (x y z : El) : Prop :=
  (∀ c < 3, ∀ i < q, (tpa_I x c i).toNat + (tpa_I y c i).toNat + (tpa_I z c i).toNat = 1) ∧
  (∀ c < 3, ∀ i < M, (tpa_L x c i).toNat + (tpa_L y c i).toNat + (tpa_L z c i).toNat = 1) ∧
  (st1 x).toNat + (st1 y).toNat + (st1 z).toNat = 1 ∧
  (st2 x).toNat + (st2 y).toNat + (st2 z).toNat = 1

theorem tpa_ex_iff (q M : ℕ) (x y z : El) :
    tpa_v (tpa_D q M x) + tpa_v (tpa_D q M y) + tpa_v (tpa_D q M z) = tpa_R (3 * q + 3 * M + 2)
      ↔ tpa_Ex q M x y z := by
  rw [show 3 * q + 3 * M + 2 = q + q + q + M + M + M + 2 by ring]
  simp only [tpa_D]
  rw [tpa_v3_app (q + q + q + M + M + M) 2 _ _ _ _ _ _ (by simp; omega) (by simp; omega)
      (by simp; omega) rfl rfl rfl,
    tpa_v3_app (q + q + q + M + M) M _ _ _ _ _ _ (by simp; omega) (by simp; omega)
      (by simp; omega) (by simp)
      (by simp) (by simp),
    tpa_v3_app (q + q + q + M) M _ _ _ _ _ _ (by simp; omega) (by simp; omega)
      (by simp; omega) (by simp)
      (by simp) (by simp),
    tpa_v3_app (q + q + q) M _ _ _ _ _ _ (by simp; omega) (by simp; omega)
      (by simp; omega) (by simp)
      (by simp) (by simp),
    tpa_v3_app (q + q) q _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp),
    tpa_v3_app q q _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp),
    tpa_v3_map, tpa_v3_map, tpa_v3_map, tpa_v3_map, tpa_v3_map, tpa_v3_map,
    tpa_v3 2 _ _ _ rfl rfl rfl]
  unfold tpa_Ex
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, l0⟩, l1⟩, l2⟩, hs⟩
    refine ⟨fun c hc => ?_, fun c hc => ?_, by simpa using hs 0 (by omega),
      by simpa using hs 1 (by omega)⟩ <;> interval_cases c <;> assumption
  · rintro ⟨hI, hL, s1, s2⟩
    refine ⟨⟨⟨⟨⟨⟨hI 0 (by omega), hI 1 (by omega)⟩, hI 2 (by omega)⟩, hL 0 (by omega)⟩,
      hL 1 (by omega)⟩, hL 2 (by omega)⟩, fun i hi => ?_⟩
    interval_cases i <;> simpa


/-- The footprint of an item on the index block `I_c`. -/
def tpa_F (q : ℕ) (x : El) (c : ℕ) : ℕ := ∑ i ∈ Finset.range q, (tpa_I x c i).toNat

/-- The total index footprint by kind. -/
def tpa_fp (q : ℕ) : El → ℕ
  | .cp _ _ _ => 1
  | .al _ _ _ => q
  | .be _ _ _ => 2 * q - 1

theorem tpa_sum_eq (q e : ℕ) (he : e < q) :
    ∑ i ∈ Finset.range q, (decide (i = e)).toNat = 1 := by
  rw [Finset.sum_congr rfl (g := fun i => if e = i then 1 else 0)
    (fun i _ => by
      by_cases h : i = e
      · simp [h]
      · simp only [h, decide_false, Bool.toNat_false]; rw [if_neg (Ne.symm h)])]
  simp [Finset.sum_ite_eq, he]

theorem tpa_sum_ne (q e : ℕ) (he : e < q) :
    ∑ i ∈ Finset.range q, (!decide (i = e)).toNat = q - 1 := by
  rw [Finset.sum_congr rfl (g := fun i => if i ≠ e then 1 else 0)
    (fun i _ => by by_cases h : i = e <;> simp [h]), Finset.sum_boole, Finset.filter_ne',
    Finset.card_erase_of_mem (by simpa), Finset.card_range]
  simp

theorem tpa_fp_eq (q M : ℕ) (hq : 1 ≤ q) (x : El) (hx : OkEl q M x) :
    tpa_F q x 0 + tpa_F q x 1 + tpa_F q x 2 = tpa_fp q x := by
  rcases x with ⟨c, e, s⟩ | ⟨c, t, s⟩ | ⟨c, t, e⟩
  · obtain ⟨hc, he⟩ := hx
    interval_cases c <;> simp [tpa_F, tpa_I, tpa_fp, tpa_sum_eq q e he]
  · obtain ⟨hc, ht⟩ := hx
    interval_cases c <;> simp [tpa_F, tpa_I, tpa_fp]
  · obtain ⟨hc, ht, he⟩ := hx
    interval_cases c <;> simp [tpa_F, tpa_I, tpa_fp, tpa_sum_ne q e he] <;> omega

theorem tpa_fp_sum (q M : ℕ) (hq : 1 ≤ q) (x y z : El) (hx : OkEl q M x) (hy : OkEl q M y)
    (hz : OkEl q M z) (h : tpa_Ex q M x y z) : tpa_fp q x + tpa_fp q y + tpa_fp q z = 3 * q := by
  have hc : ∀ c < 3, tpa_F q x c + tpa_F q y c + tpa_F q z c = q := by
    intro c hc
    unfold tpa_F
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun i hi => h.1 c hc i (Finset.mem_range.1 hi)),
      Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rw [← tpa_fp_eq q M hq x hx, ← tpa_fp_eq q M hq y hy, ← tpa_fp_eq q M hq z hz]
  have := hc 0 (by omega); have := hc 1 (by omega); have := hc 2 (by omega)
  omega


theorem tpa_A (q M : ℕ) (hq : 2 ≤ q) {c1 e1 c2 t2 c3 t3 e3 : ℕ} {s1 s2 : Bool} (hc1 : c1 < 3)
    (he1 : e1 < q) (hc2 : c2 < 3) (ht2 : t2 < M) (hc3 : c3 < 3) (he3 : e3 < q)
    (h : tpa_Ex q M (.cp c1 e1 s1) (.al c2 t2 s2) (.be c3 t3 e3)) :
    c1 = c3 ∧ c2 = c3 ∧ e1 = e3 ∧ t2 = t3 ∧ s1 = s2 := by
  obtain ⟨hI, hL, h1, h2⟩ := h
  obtain ⟨i', hi'q, hi'e⟩ : ∃ i, i < q ∧ i ≠ e1 :=
    ⟨if e1 = 0 then 1 else 0, by split_ifs <;> omega, by split_ifs <;> omega⟩
  have a := hI ((c3 + 2) % 3) (by omega) i' hi'q
  have b := hI c3 hc3 e3 he3
  have l := hL c2 hc2 t2 ht2
  simp only [tpa_I, tpa_L, st1, st2] at a b l h1 h2
  interval_cases c1 <;> interval_cases c2 <;> interval_cases c3 <;>
    simp [hi'e] at a b l h1 h2 ⊢
  all_goals (refine ⟨b.symm, l, ?_⟩; cases s1 <;> cases s2 <;> simp at h1 h2 ⊢)


theorem tpa_p1 {α : Type} (a b c : α) : [a, b, c].Perm [a, b, c] := List.Perm.refl _
theorem tpa_p2 {α : Type} (a b c : α) : [b, a, c].Perm [a, b, c] := List.Perm.swap a b [c]
theorem tpa_p3 {α : Type} (a b c : α) : [a, c, b].Perm [a, b, c] := (List.Perm.swap b c []).cons a
theorem tpa_p4 {α : Type} (a b c : α) : [b, c, a].Perm [a, b, c] :=
  ((List.Perm.swap a c []).cons b).trans (List.Perm.swap a b [c])
theorem tpa_p5 {α : Type} (a b c : α) : [c, a, b].Perm [a, b, c] :=
  (List.Perm.swap a c [b]).trans ((List.Perm.swap b c []).cons a)
theorem tpa_p6 {α : Type} (a b c : α) : [c, b, a].Perm [a, b, c] :=
  (List.Perm.swap b c [a]).trans (tpa_p4 a b c)

theorem tpa_B (q M : ℕ) (hq : 2 ≤ q) {c1 t1 c2 t2 c3 t3 : ℕ} {s1 s2 s3 : Bool} (hc1 : c1 < 3)
    (ht1 : t1 < M) (hc2 : c2 < 3) (ht2 : t2 < M) (hc3 : c3 < 3) (ht3 : t3 < M)
    (h : tpa_Ex q M (.al c1 t1 s1) (.al c2 t2 s2) (.al c3 t3 s3)) :
    IsPat [.al c1 t1 s1, .al c2 t2 s2, .al c3 t3 s3] := by
  obtain ⟨hI, hL, h1, h2⟩ := h
  have a0 := hI 0 (by omega) 0 (by omega)
  have a1 := hI 1 (by omega) 0 (by omega)
  have a2 := hI 2 (by omega) 0 (by omega)
  have l1 := hL c1 hc1 t1 ht1
  have l2 := hL c2 hc2 t2 ht2
  have l3 := hL c3 hc3 t3 ht3
  simp only [tpa_I, tpa_L, st1, st2] at a0 a1 a2 l1 l2 l3 h1 h2
  interval_cases c1 <;> interval_cases c2 <;> interval_cases c3 <;>
    simp at a0 a1 a2 l1 l2 l3 h1 h2 ⊢
  all_goals subst_vars
  all_goals cases s1 <;> cases s2 <;> cases s3 <;> simp at h1 h2
  all_goals first
    | exact Or.inr ⟨_, _, tpa_p1 _ _ _⟩
    | exact Or.inr ⟨_, _, tpa_p2 _ _ _⟩
    | exact Or.inr ⟨_, _, tpa_p3 _ _ _⟩
    | exact Or.inr ⟨_, _, tpa_p4 _ _ _⟩
    | exact Or.inr ⟨_, _, tpa_p5 _ _ _⟩
    | exact Or.inr ⟨_, _, tpa_p6 _ _ _⟩


theorem tpa_exA (q M : ℕ) {c e t : ℕ} {s : Bool} (hc : c < 3) (he : e < q) (ht : t < M) :
    tpa_Ex q M (.cp c e s) (.al c t s) (.be c t e) := by
  refine ⟨fun c' hc' i hi => ?_, fun c' hc' i hi => ?_, ?_, ?_⟩
  · simp only [tpa_I]
    interval_cases c <;> interval_cases c' <;> by_cases h : i = e <;> simp [h]
  · simp only [tpa_L]
    interval_cases c <;> interval_cases c' <;> by_cases h : i = t <;> simp [h]
  · cases s <;> interval_cases c <;> simp [st1]
  · cases s <;> interval_cases c <;> simp [st2]

theorem tpa_exB (q M : ℕ) {t : ℕ} {s : Bool} (ht : t < M) :
    tpa_Ex q M (.al 0 t s) (.al 1 t s) (.al 2 t s) := by
  refine ⟨fun c' hc' i hi => ?_, fun c' hc' i hi => ?_, ?_, ?_⟩
  · simp only [tpa_I]; interval_cases c' <;> simp
  · simp only [tpa_L]; interval_cases c' <;> by_cases h : i = t <;> simp [h]
  · cases s <;> simp [st1]
  · cases s <;> simp [st2]

theorem tpa_Ex_s12 {q M : ℕ} {x y z : El} (h : tpa_Ex q M x y z) : tpa_Ex q M y x z := by
  obtain ⟨hI, hL, h1, h2⟩ := h
  refine ⟨fun c hc i hi => ?_, fun c hc i hi => ?_, by omega, by omega⟩
  · have := hI c hc i hi; omega
  · have := hL c hc i hi; omega

theorem tpa_Ex_s23 {q M : ℕ} {x y z : El} (h : tpa_Ex q M x y z) : tpa_Ex q M x z y := by
  obtain ⟨hI, hL, h1, h2⟩ := h
  refine ⟨fun c hc i hi => ?_, fun c hc i hi => ?_, by omega, by omega⟩
  · have := hI c hc i hi; omega
  · have := hL c hc i hi; omega

theorem tpa_isPat_perm {l l' : List El} (h : IsPat l) (hp : l'.Perm l) : IsPat l' := by
  rcases h with ⟨c, e, t, s, h⟩ | ⟨t, s, h⟩
  · exact Or.inl ⟨c, e, t, s, hp.trans h⟩
  · exact Or.inr ⟨t, s, hp.trans h⟩

theorem tpa_Aok (q M : ℕ) (hq : 2 ≤ q) {c1 e1 c2 t2 c3 t3 e3 : ℕ} {s1 s2 : Bool}
    (hx : OkEl q M (.cp c1 e1 s1)) (hy : OkEl q M (.al c2 t2 s2)) (hz : OkEl q M (.be c3 t3 e3))
    (h : tpa_Ex q M (.cp c1 e1 s1) (.al c2 t2 s2) (.be c3 t3 e3)) :
    IsPat [.cp c1 e1 s1, .al c2 t2 s2, .be c3 t3 e3] := by
  obtain ⟨r1, r2, r3, r4, r5⟩ := tpa_A q M hq hx.1 hx.2 hy.1 hy.2 hz.1 hz.2.2 h
  subst r1 r2 r3 r4 r5
  exact Or.inl ⟨_, _, _, _, List.Perm.refl _⟩

theorem tpa_class (q M : ℕ) (hq : 2 ≤ q) (x y z : El) (hx : OkEl q M x) (hy : OkEl q M y)
    (hz : OkEl q M z) (h : tpa_Ex q M x y z) : IsPat [x, y, z] := by
  have hs := tpa_fp_sum q M (by omega) x y z hx hy hz h
  rcases x with ⟨c1, e1, s1⟩ | ⟨c1, t1, s1⟩ | ⟨c1, t1, e1⟩ <;>
  rcases y with ⟨c2, e2, s2⟩ | ⟨c2, t2, s2⟩ | ⟨c2, t2, e2⟩ <;>
  rcases z with ⟨c3, e3, s3⟩ | ⟨c3, t3, s3⟩ | ⟨c3, t3, e3⟩ <;>
  simp only [tpa_fp] at hs
  all_goals first
    | omega
    | exact tpa_B q M hq hx.1 hx.2 hy.1 hy.2 hz.1 hz.2 h
    | exact tpa_isPat_perm (tpa_Aok q M hq hx hy hz h) (tpa_p1 _ _ _)
    | exact tpa_isPat_perm (tpa_Aok q M hq hy hx hz (tpa_Ex_s12 h)) (tpa_p2 _ _ _)
    | exact tpa_isPat_perm (tpa_Aok q M hq hx hz hy (tpa_Ex_s23 h)) (tpa_p3 _ _ _)
    | exact tpa_isPat_perm (tpa_Aok q M hq hz hx hy (tpa_Ex_s12 (tpa_Ex_s23 h))) (tpa_p4 _ _ _)
    | exact tpa_isPat_perm (tpa_Aok q M hq hy hz hx (tpa_Ex_s23 (tpa_Ex_s12 h))) (tpa_p5 _ _ _)
    | exact tpa_isPat_perm (tpa_Aok q M hq hz hy hx (tpa_Ex_s23 (tpa_Ex_s12 (tpa_Ex_s23 h))))
        (tpa_p6 _ _ _)


/-- **Rigidity**: a list of items (in range, `q ≥ 2`) sums to the bound iff it is an intended
group. -/
theorem tp_sum_iff (q M : ℕ) (hq : 2 ≤ q) (g : List El) (hg : ∀ x ∈ g, OkEl q M x) :
    (g.map fun x => bv (elRow q M x)).sum = bv (bRow q M) ↔ IsPat g := by
  have hval : ∀ l : List El, (l.map fun x => bv (elRow q M x)).sum =
      (l.map fun x => tpa_v (tpa_D q M x)).sum + l.length * 4 ^ (3 * q + 3 * M + 2) := by
    intro l; induction l with
    | nil => simp
    | cons x l ih =>
      rw [List.map_cons, List.sum_cons, ih, tpa_bv_el, List.map_cons, List.sum_cons,
        List.length_cons]; ring
  have hle : ∀ l : List El, (l.map fun x => tpa_v (tpa_D q M x)).sum ≤
      l.length * tpa_R (3 * q + 3 * M + 2) := by
    intro l; induction l with
    | nil => simp
    | cons x l ih =>
      have := tpa_v_le (tpa_D q M x); rw [tpa_D_len] at this
      rw [List.map_cons, List.sum_cons, List.length_cons, add_mul, one_mul]; omega
  have hR := tpa_R_lt (3 * q + 3 * M + 2)
  rw [hval, tpa_bv_b]
  by_cases hlen : g.length = 3
  · obtain ⟨x, y, z, rfl⟩ : ∃ x y z, g = [x, y, z] := by
      match g, hlen with
      | [x, y, z], _ => exact ⟨x, y, z, rfl⟩
    have hx := hg x (by simp); have hy := hg y (by simp); have hz := hg z (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    have key : ∀ a b c R X : ℕ, a + (b + (c + 0)) + (0 + 1 + 1 + 1) * X = R + 3 * X ↔
        a + b + c = R := by intros; omega
    rw [key]
    constructor
    · intro h
      exact tpa_class q M hq x y z hx hy hz ((tpa_ex_iff q M x y z).1 h)
    · rintro (⟨c, e, t, s, hp⟩ | ⟨t, s, hp⟩)
      · have h1 := hg _ (hp.mem_iff.2 (by simp : El.cp c e s ∈ _))
        have h3 := hg _ (hp.mem_iff.2 (by simp : El.be c t e ∈ _))
        have := (hp.map fun x => tpa_v (tpa_D q M x)).sum_eq
        have h := (tpa_ex_iff q M _ _ _).2 (tpa_exA q M (s := s) h1.1 h1.2 h3.2.1)
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
        omega
      · have h1 := hg _ (hp.mem_iff.2 (by simp : El.al 0 t s ∈ _))
        have := (hp.map fun x => tpa_v (tpa_D q M x)).sum_eq
        have h := (tpa_ex_iff q M _ _ _).2 (tpa_exB q M (s := s) h1.2)
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
        omega
  · have hnot : ¬ IsPat g := by
      rintro (⟨c, e, t, s, hp⟩ | ⟨t, s, hp⟩) <;> exact hlen (by simpa using hp.length_eq)
    simp only [hnot, iff_false]
    intro h
    have hl := hle g
    generalize g.length = n at h hl hlen
    generalize (g.map fun x => tpa_v (tpa_D q M x)).sum = S at h hl
    generalize tpa_R (3 * q + 3 * M + 2) = R at h hl hR
    generalize 4 ^ (3 * q + 3 * M + 2) = X at h hl hR
    rcases (show n ≤ 2 ∨ 4 ≤ n by omega) with hn | hn
    · interval_cases n <;> omega
    · have := Nat.mul_le_mul_right X hn; omega

/-- `binSum` as a sum over the indices of the group. -/
theorem tp_binSum_eq (rs : List (List SatSym)) (f : ℕ → ℕ) (b : ℕ) :
    binSum rs f b = (((List.range rs.length).filter fun i => f i = b).map
      fun i => bv (rs.getD i [])).sum := by
  induction rs generalizing f with
  | nil => simp [binSum]
  | cons r rs ih =>
    rw [binSum, ih, List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    by_cases h0 : f 0 = b <;> simp [h0, Function.comp_def, List.map_map]

end Pnp.Karp.ThreePart
