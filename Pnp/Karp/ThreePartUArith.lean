import Pnp.Karp.ThreePartU
import Pnp.Karp.ThreePartArith

/-!
# Unary 3-PARTITION: arithmetic of the items and the rigidity of the groups

* `tpu_el_bounds`: every item (in range) is strictly between a quarter and a half of the bound;
* `tpu_sum_iff`: a list of items (in range, `q ≥ 2`) sums to the bound iff it is an intended
  group (`IsPat`).  Three digits of a block sum to `3 L` only for the shapes `{a, z, z}` and
  `{o e, c e, z}` (`tpua_blk`), so the bits of the blocks partition the positions (`tpa_Ex`) and
  M63's classification `tpa_class` applies.
-/

namespace Pnp.Karp.ThreePartU

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

/-! ## Base-`R` values -/

theorem tpua_nv_append (R : ℕ) (a b : List ℕ) :
    nv R (a ++ b) = nv R a + R ^ a.length * nv R b := by
  induction a with
  | nil => simp [nv]
  | cons x a ih => simp only [List.cons_append, nv, ih, List.length_cons, pow_succ]; ring

theorem tpua_nv_two (R : ℕ) : ∀ ds : List ℕ, (∀ d ∈ ds, 2 * d < R) →
    2 * nv R ds < R ^ ds.length
  | [], _ => by simp [nv]
  | d :: ds, h => by
    have h1 := h d (by simp)
    have h2 := tpua_nv_two R ds fun x hx => h x (by simp [hx])
    simp only [nv, List.length_cons, pow_succ]
    have : R * (2 * nv R ds) + R ≤ R * R ^ ds.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
    nlinarith

theorem tpua_nv_inj (R : ℕ) : ∀ s t : List ℕ, s.length = t.length → (∀ d ∈ s, d < R) →
    (∀ d ∈ t, d < R) → nv R s = nv R t → s = t
  | [], [], _, _, _, _ => rfl
  | a :: s, b :: t, hl, hs, ht, h => by
    simp only [nv] at h
    have ha := hs a (by simp)
    have hb := ht b (by simp)
    have hR : 0 < R := by omega
    have e1 : a = b := by
      have := congrArg (· % R) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
      exact this
    subst e1
    have e2 : nv R s = nv R t := by
      have := Nat.eq_of_mul_eq_mul_left hR (Nat.add_left_cancel h)
      exact this
    rw [tpua_nv_inj R s t (by simpa using hl) (fun d hd => hs d (by simp [hd]))
      (fun d hd => ht d (by simp [hd])) e2]

/-- Pointwise sum of three digit lists. -/
def tpua_z3 : List ℕ → List ℕ → List ℕ → List ℕ
  | a :: as, b :: bs, c :: cs => (a + b + c) :: tpua_z3 as bs cs
  | _, _, _ => []

theorem tpua_nv_add3 (R : ℕ) : ∀ a b c : List ℕ, a.length = b.length → b.length = c.length →
    nv R a + nv R b + nv R c = nv R (tpua_z3 a b c)
  | [], [], [], _, _ => by simp [nv, tpua_z3]
  | x :: a, y :: b, z :: c, h1, h2 => by
    simp only [nv, tpua_z3]
    rw [← tpua_nv_add3 R a b c (by simpa using h1) (by simpa using h2)]
    ring

theorem tpua_z3_lt (R D : ℕ) : ∀ a b c : List ℕ, (∀ d ∈ a, d ≤ D) → (∀ d ∈ b, d ≤ D) →
    (∀ d ∈ c, d ≤ D) → 3 * D < R → ∀ d ∈ tpua_z3 a b c, d < R
  | x :: a, y :: b, z :: c, ha, hb, hc, hR, d, hd => by
    simp only [tpua_z3, List.mem_cons] at hd
    rcases hd with rfl | hd
    · have := ha x (by simp); have := hb y (by simp); have := hc z (by simp); omega
    · exact tpua_z3_lt R D a b c (fun d h => ha d (by simp [h])) (fun d h => hb d (by simp [h]))
        (fun d h => hc d (by simp [h])) hR d hd
  | [], _, _, _, _, _, _, d, hd => by simp [tpua_z3] at hd
  | _ :: _, [], _, _, _, _, _, d, hd => by simp [tpua_z3] at hd
  | _ :: _, _ :: _, [], _, _, _, _, d, hd => by simp [tpua_z3] at hd

/-! ## Blocks -/

/-- The bit at position `i` of a block of shape `s`. -/
def sbit : Sh → ℕ → Bool
  | .z, _ => false
  | .o e, i => decide (i = e)
  | .c e, i => decide (i ≠ e)
  | .a, _ => true

/-- A shape is in range `n`. -/
def ShOk (n : ℕ) : Sh → Prop
  | .z => True
  | .o e => e < n
  | .c e => e < n
  | .a => True

theorem tpua_I (x : El) (c i : ℕ) : tpa_I x c i = sbit (shI x c) i := by
  cases x <;> simp only [tpa_I, shI] <;> (try split_ifs) <;> simp_all [sbit]

theorem tpua_L (x : El) (c i : ℕ) : tpa_L x c i = sbit (shL x c) i := by
  cases x <;> simp only [tpa_L, shL] <;> (try split_ifs) <;> simp_all [sbit]

theorem tpua_okI (q M : ℕ) (x : El) (hx : OkEl q M x) (c : ℕ) : ShOk q (shI x c) := by
  cases x <;> simp only [shI] <;> (try split_ifs) <;> simp_all [ShOk, OkEl]

theorem tpua_okL (q M : ℕ) (x : El) (hx : OkEl q M x) (c : ℕ) : ShOk M (shL x c) := by
  cases x <;> simp only [shL] <;> (try split_ifs) <;> simp_all [ShOk, OkEl]

theorem tpua_dv_le (L n : ℕ) (hn : 2 * n < L) (s : Sh) (hs : ShOk n s) : dv L n s ≤ 3 * L := by
  cases s <;> simp only [dv, ShOk] at hs ⊢ <;> omega

/-- **The block lemma**: three digits of shapes in range sum to `3 L` iff the blocks partition
the positions (one direction). -/
theorem tpua_blk (L n : ℕ) (hn : 2 * n < L) (s1 s2 s3 : Sh) (h1 : ShOk n s1) (h2 : ShOk n s2)
    (h3 : ShOk n s3) (h : dv L n s1 + dv L n s2 + dv L n s3 = 3 * L) :
    ∀ i < n, (sbit s1 i).toNat + (sbit s2 i).toNat + (sbit s3 i).toNat = 1 := by
  intro i hi
  rcases s1 with _ | e1 | e1 | _ <;> rcases s2 with _ | e2 | e2 | _ <;>
    rcases s3 with _ | e3 | e3 | _ <;> simp only [dv, ShOk] at h h1 h2 h3 <;>
    (try omega) <;>
    first
    | (simp [sbit]; done)
    | (obtain rfl : e1 = e2 := by omega
       by_cases hi' : i = e1 <;> simp [sbit, hi'])
    | (obtain rfl : e1 = e3 := by omega
       by_cases hi' : i = e1 <;> simp [sbit, hi'])
    | (obtain rfl : e2 = e3 := by omega
       by_cases hi' : i = e2 <;> simp [sbit, hi'])

/-! ## Items -/

theorem tpua_udg_len (q M : ℕ) (x : El) : (udg q M x).length = 8 := rfl

theorem tpua_udg_le (q M : ℕ) (hqM : q ≤ M) (x : El) (hx : OkEl q M x) :
    ∀ d ∈ udg q M x, d ≤ 3 * uL M := by
  have hI := fun c => tpua_dv_le (uL M) q (by unfold uL; omega) _ (tpua_okI q M x hx c)
  have hL := fun c => tpua_dv_le (uL M) M (by unfold uL; omega) _ (tpua_okL q M x hx c)
  have hb : ∀ b : Bool, b.toNat ≤ 3 * uL M := fun b => by cases b <;> simp [uL] ; omega
  intro d hd
  simp only [udg, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hI 0
  · exact hI 1
  · exact hI 2
  · exact hL 0
  · exact hL 1
  · exact hL 2
  · exact hb _
  · exact hb _

/-- The low part of an item. -/
theorem tpua_uval (q M : ℕ) (x : El) :
    uval q M x = nv (uR M) (udg q M x) + uR M ^ 8 := by
  rw [uval, tpua_nv_append, tpua_udg_len]; simp [nv]

theorem tpua_low_lt (q M : ℕ) (hqM : q ≤ M) (x : El) (hx : OkEl q M x) :
    2 * nv (uR M) (udg q M x) < uR M ^ 8 := by
  have := tpua_nv_two (uR M) (udg q M x) fun d hd => by
    have := tpua_udg_le q M hqM x hx d hd; unfold uR; omega
  simpa [tpua_udg_len] using this

/-- The digits of the bound. -/
def tpua_bd (M : ℕ) : List ℕ :=
  [3 * uL M, 3 * uL M, 3 * uL M, 3 * uL M, 3 * uL M, 3 * uL M, 1, 1]

theorem tpua_uB (M : ℕ) : uB M = nv (uR M) (tpua_bd M) + 3 * uR M ^ 8 := by
  have : uB M = nv (uR M) (tpua_bd M ++ [3]) := rfl
  rw [this, tpua_nv_append]; simp [nv, tpua_bd]; ring

theorem tpua_bd_lt (M : ℕ) : nv (uR M) (tpua_bd M) < uR M ^ 8 := by
  have := tpua_nv_two (uR M) (tpua_bd M) fun d hd => by
    simp only [tpua_bd, List.mem_cons, List.not_mem_nil, or_false] at hd
    have h1 : uR M = 9 * uL M + 1 := rfl
    have h2 : 1 ≤ uL M := by unfold uL; omega
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hl : (tpua_bd M).length = 8 := rfl
  rw [hl] at this
  omega

/-- Every item (in range) is strictly between a quarter and a half of the bound. -/
theorem tpu_el_bounds (q M : ℕ) (hqM : q ≤ M) (x : El) (hx : OkEl q M x) :
    uB M < 4 * uval q M x ∧ 2 * uval q M x < uB M := by
  rw [tpua_uval, tpua_uB]
  have h1 := tpua_low_lt q M hqM x hx
  have h2 := tpua_bd_lt M
  constructor <;> omega

/-! ## Rigidity -/

theorem tpua_ex (q M : ℕ) (hqM : q ≤ M) (x y z : El) (hx : OkEl q M x) (hy : OkEl q M y)
    (hz : OkEl q M z)
    (h : nv (uR M) (udg q M x) + nv (uR M) (udg q M y) + nv (uR M) (udg q M z) =
      nv (uR M) (tpua_bd M)) : tpa_Ex q M x y z := by
  rw [tpua_nv_add3 (uR M) (udg q M x) (udg q M y) (udg q M z) rfl rfl] at h
  have hR3 : 3 * (3 * uL M) < uR M := by unfold uR; omega
  have hu1 : 1 ≤ uL M := by unfold uL; omega
  have e := tpua_nv_inj (uR M) (tpua_z3 (udg q M x) (udg q M y) (udg q M z)) (tpua_bd M) rfl
    (tpua_z3_lt _ _ _ _ _ (tpua_udg_le q M hqM _ hx) (tpua_udg_le q M hqM _ hy)
      (tpua_udg_le q M hqM _ hz) hR3)
    (fun d hd => by
      simp only [tpua_bd, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega) h
  simp only [udg, tpua_z3, tpua_bd, List.cons.injEq, and_true] at e
  obtain ⟨i0, i1, i2, l0, l1, l2, s1, s2⟩ := e
  have hL : 2 * q < uL M := by unfold uL; omega
  have hL' : 2 * M < uL M := by unfold uL; omega
  have bI := fun c => tpua_blk (uL M) q hL _ _ _ (tpua_okI q M x hx c) (tpua_okI q M y hy c)
    (tpua_okI q M z hz c)
  have bL := fun c => tpua_blk (uL M) M hL' _ _ _ (tpua_okL q M x hx c) (tpua_okL q M y hy c)
    (tpua_okL q M z hz c)
  refine ⟨fun c hc i hi => ?_, fun c hc i hi => ?_, s1, s2⟩
  · simp only [tpua_I]
    interval_cases c
    · exact bI 0 i0 i hi
    · exact bI 1 i1 i hi
    · exact bI 2 i2 i hi
  · simp only [tpua_L]
    interval_cases c
    · exact bL 0 l0 i hi
    · exact bL 1 l1 i hi
    · exact bL 2 l2 i hi

theorem tpua_patA (q M : ℕ) (hqM : q ≤ M) {c e t : ℕ} {s : Bool} (hc : c < 3) (he : e < q)
    (ht : t < M) :
    nv (uR M) (udg q M (.cp c e s)) + nv (uR M) (udg q M (.al c t s)) +
      nv (uR M) (udg q M (.be c t e)) = nv (uR M) (tpua_bd M) := by
  rw [tpua_nv_add3 (uR M) (udg q M (.cp c e s)) (udg q M (.al c t s)) (udg q M (.be c t e))
    rfl rfl]
  congr 1
  have hL : q ≤ uL M := by unfold uL; omega
  have hL' : M ≤ uL M := by unfold uL; omega
  cases s <;> interval_cases c <;>
    simp only [udg, tpua_z3, tpua_bd, shI, shL, dv, ThreePart.st1, ThreePart.st2, List.cons.injEq] <;> simp <;> omega

theorem tpua_patB (q M : ℕ) {t : ℕ} {s : Bool} (ht : t < M) :
    nv (uR M) (udg q M (.al 0 t s)) + nv (uR M) (udg q M (.al 1 t s)) +
      nv (uR M) (udg q M (.al 2 t s)) = nv (uR M) (tpua_bd M) := by
  rw [tpua_nv_add3 (uR M) (udg q M (.al 0 t s)) (udg q M (.al 1 t s)) (udg q M (.al 2 t s))
    rfl rfl]
  congr 1
  have hL' : M ≤ uL M := by unfold uL; omega
  cases s <;> simp only [udg, tpua_z3, tpua_bd, shI, shL, dv, ThreePart.st1, ThreePart.st2, List.cons.injEq] <;>
    simp <;> omega

/-- **Rigidity**: a list of items (in range, `q ≥ 2`, `q ≤ M`) sums to the bound iff it is an
intended group. -/
theorem tpu_sum_iff (q M : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M) (g : List El)
    (hg : ∀ x ∈ g, OkEl q M x) :
    (g.map fun x => uval q M x).sum = uB M ↔ IsPat g := by
  have hval : ∀ l : List El, (l.map fun x => uval q M x).sum =
      (l.map fun x => nv (uR M) (udg q M x)).sum + l.length * uR M ^ 8 := by
    intro l; induction l with
    | nil => simp
    | cons x l ih =>
      rw [List.map_cons, List.sum_cons, ih, tpua_uval, List.map_cons, List.sum_cons,
        List.length_cons]; ring
  have hle : ∀ l : List El, (∀ x ∈ l, OkEl q M x) →
      2 * (l.map fun x => nv (uR M) (udg q M x)).sum + l.length ≤ l.length * uR M ^ 8 := by
    intro l hl; induction l with
    | nil => simp
    | cons x l ih =>
      have := tpua_low_lt q M hqM x (hl x (by simp))
      have ih' := ih fun y hy => hl y (by simp [hy])
      rw [List.map_cons, List.sum_cons, List.length_cons, add_mul, one_mul]; omega
  have hR := tpua_bd_lt M
  have hX : 0 < uR M ^ 8 := Nat.pow_pos (by unfold uR; omega)
  rw [hval, tpua_uB]
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
      exact tpa_class q M hq x y z hx hy hz (tpua_ex q M hqM x y z hx hy hz h)
    · rintro (⟨c, e, t, s, hp⟩ | ⟨t, s, hp⟩)
      · have h1 := hg _ (hp.mem_iff.2 (by simp : El.cp c e s ∈ _))
        have h3 := hg _ (hp.mem_iff.2 (by simp : El.be c t e ∈ _))
        have := (hp.map fun x => nv (uR M) (udg q M x)).sum_eq
        have h := tpua_patA q M hqM (s := s) h1.1 h1.2 h3.2.1
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
        omega
      · have h1 := hg _ (hp.mem_iff.2 (by simp : El.al 0 t s ∈ _))
        have := (hp.map fun x => nv (uR M) (udg q M x)).sum_eq
        have h := tpua_patB q M (s := s) h1.2
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
        omega
  · have hnot : ¬ IsPat g := by
      rintro (⟨c, e, t, s, hp⟩ | ⟨t, s, hp⟩) <;> exact hlen (by simpa using hp.length_eq)
    simp only [hnot, iff_false]
    intro h
    have hl := hle g hg
    generalize g.length = n at h hl hlen
    generalize (g.map fun x => nv (uR M) (udg q M x)).sum = S at h hl
    generalize nv (uR M) (tpua_bd M) = Rb at h hl hR
    generalize uR M ^ 8 = X at h hl hR hX
    rcases (show n ≤ 2 ∨ 4 ≤ n by omega) with hn | hn
    · have h2 : n * X ≤ 2 * X := Nat.mul_le_mul_right X hn
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp at h; omega
      · omega
    · have := Nat.mul_le_mul_right X hn; omega

/-- `unSum` as a sum over the indices of the group. -/
theorem tpu_unSum_eq (rs : List (List SatSym)) (f : ℕ → ℕ) (b : ℕ) :
    unSum rs f b = (((List.range rs.length).filter fun i => f i = b).map
      fun i => (rs.getD i []).length).sum := by
  induction rs generalizing f with
  | nil => simp [unSum]
  | cons r rs ih =>
    rw [unSum, ih, List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    by_cases h0 : f 0 = b <;> simp [h0, Function.comp_def, List.map_map]

end Pnp.Karp.ThreePartU
