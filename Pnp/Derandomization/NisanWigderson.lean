import Pnp.NaturalProofs.BlumMicali
import Pnp.PPoly.Encode

/-!
# The Nisan–Wigderson generator (M18)

Hardness versus randomness. Let `f : {0,1}^m → {0,1}` be *hard on average*: no circuit with
`s` gates agrees with `f` on more than a `1/2 + ε` fraction of inputs. Let `S₁, …, S_L` be
an `(m, a)`-*design* in `{1, …, d}`: `|Sᵢ| = m` and `|Sᵢ ∩ Sⱼ| ≤ a` for `i ≠ j`. The
Nisan–Wigderson generator stretches a seed `z ∈ {0,1}^d` to

`NW(z) = (f(z|S₁), …, f(z|S_L)) ∈ {0,1}^L`.

* `nw_reduction`: a test `D` (`sD` gates) with advantage `α` against `NW` yields a predictor
  for `f` with `L·juntaSize a + sD + 1` gates and success `≥ 1/2 + α/L` (hybrid argument,
  Yao's distinguisher ⇒ predictor, and the design property: once the bits outside `Sⱼ` are
  fixed, every other output depends on at most `a` seed bits, a junta of `4·2^a` gates).
* `nw_secure`: hence if `f` is `(L·juntaSize a + sD + 1, ε)`-hard on average, no test with
  `sD` gates has advantage more than `L·ε`.
* `polyDesign`: designs exist — over a finite field `K` with `q` elements, the graphs of the
  polynomials of degree `< k` form a design with `q^k` sets of size `q` in `K × K` (a seed of
  `q²` bits) with pairwise intersections `≤ k − 1`.
* `nw_poly_secure`: the combination, with explicit parameters.
-/

namespace Pnp.Derand

open Pnp.Circuits Pnp.NaturalProofs Pnp.PPoly Classical

noncomputable section

/-! ## Designs, the generator and average-case hardness -/

/-- An `(m, a)`-design with `L` sets in `Fin d`: each set is listed injectively by
`S i : Fin m → Fin d`; for `i ≠ j`, at most `a` positions of `S j` lie in `S i`. -/
structure Design (d m L a : ℕ) where
  S : Fin L → Fin m → Fin d
  inj : ∀ i, Function.Injective (S i)
  inter : ∀ i j, i ≠ j → (Finset.univ.filter (fun t => ∃ k, S i k = S j t)).card ≤ a

/-- The Nisan–Wigderson generator: output `i` is `f` applied to the seed restricted to `S i`. -/
def nw {d m L : ℕ} (f : (Fin m → Bool) → Bool) (S : Fin L → Fin m → Fin d)
    (z : Fin d → Bool) : Fin L → Bool :=
  fun i => f (fun k => z (S i k))

/-- `f` is `(s, ε)`-hard on average: circuits with `s` gates agree with `f` on at most a
`1/2 + ε` fraction of the inputs. -/
def AvgHard {m : ℕ} (f : (Fin m → Bool) → Bool) (s : ℕ) (ε : ℝ) : Prop :=
  ∀ B : (Fin m → Bool) → Bool, HasCircuitOfSize B s → prob (fun x => B x = f x) ≤ 1 / 2 + ε

/-! ## Overwriting the bits of one set -/

section Overwrite

variable {d m : ℕ} (S : Fin m → Fin d)

/-- Write `x` into the positions `S` of `y`. -/
def ow (y : Fin d → Bool) (x : Fin m → Bool) : Fin d → Bool :=
  fun p => if h : ∃ t, S t = p then x h.choose else y p

variable {S}

theorem ow_apply_S (hS : Function.Injective S) (y : Fin d → Bool) (x : Fin m → Bool)
    (t : Fin m) : ow S y x (S t) = x t := by
  have h : ∃ t', S t' = S t := ⟨t, rfl⟩
  rw [ow, dif_pos h, hS h.choose_spec]

theorem ow_comp (hS : Function.Injective S) (y : Fin d → Bool) (x : Fin m → Bool) :
    (fun t => ow S y x (S t)) = x :=
  funext (ow_apply_S hS y x)

theorem ow_ow (y : Fin d → Bool) (x : Fin m → Bool) :
    ow S (ow S y x) (fun t => y (S t)) = y := by
  funext p
  by_cases h : ∃ t, S t = p
  · rw [ow, dif_pos h, h.choose_spec]
  · rw [ow, dif_neg h, ow, dif_neg h]

/-- `(y, x) ↦ (ow y x, y|S)` is a bijection. -/
def owEquiv (hS : Function.Injective S) :
    (Fin d → Bool) × (Fin m → Bool) ≃ (Fin d → Bool) × (Fin m → Bool) where
  toFun q := (ow S q.1 q.2, fun t => q.1 (S t))
  invFun q := (ow S q.1 q.2, fun t => q.1 (S t))
  left_inv q := by
    rcases q with ⟨y, x⟩
    simp only [ow_ow, ow_comp hS]
  right_inv q := by
    rcases q with ⟨y, x⟩
    simp only [ow_ow, ow_comp hS]

/-- A uniform seed is a uniform `y` with a uniform `x` written into `S`. -/
theorem ex_ow (hS : Function.Injective S) (g : (Fin d → Bool) → ℝ) :
    ex g = ex (fun y => ex (fun x => g (ow S y x))) := by
  rw [← ex_prod (fun q : (Fin d → Bool) × (Fin m → Bool) => g (ow S q.1 q.2))]
  have := ex_equiv (owEquiv hS) (fun q => g q.1)
  rw [ex_fst] at this
  rw [← this]
  rfl

end Overwrite

/-! ## The hybrid argument -/

section Hybrid

variable {d m L : ℕ} (f : (Fin m → Bool) → Bool) (S : Fin L → Fin m → Fin d)
  (D : (Fin L → Bool) → Bool)

/-- Hybrid `j`: the first `j` outputs are real, the rest are the uniform `u`. -/
def nhyb (j : ℕ) (z : Fin d → Bool) (u : Fin L → Bool) : Fin L → Bool :=
  fun i => if i.val < j then nw f S z i else u i

/-- Acceptance probability of `D` on hybrid `j`. -/
def nH (j : ℕ) : ℝ := ex (fun z : Fin d → Bool => ex (fun u : Fin L → Bool => bv (D (nhyb f S j z u))))

theorem nH_zero : nH f S D 0 = ex (fun u : Fin L → Bool => bv (D u)) := by
  have h : ∀ z u, nhyb f S 0 z u = u := fun z u => funext fun i => by simp [nhyb]
  simp only [nH, h]
  exact ex_const (α := Fin d → Bool) _

theorem nH_L : nH f S D L = ex (fun z : Fin d → Bool => bv (D (nw f S z))) := by
  have h : ∀ z u, nhyb f S L z u = nw f S z := fun z u => funext fun i => by simp [nhyb]
  simp only [nH, h]
  congr 1; funext z
  exact ex_const (α := Fin L → Bool) _

/-- Hybrid step: some `j` carries a `1/L` share of the advantage. -/
theorem nw_exists_step (hL : 0 < L) : ∃ j < L,
    |ex (fun u : Fin L → Bool => bv (D u)) - ex (fun z : Fin d → Bool => bv (D (nw f S z)))| / L ≤
      |nH f S D (j + 1) - nH f S D j| := by
  rw [← nH_zero f S D, ← nH_L f S D]
  have htel : nH f S D L - nH f S D 0 =
      ∑ j ∈ Finset.range L, (nH f S D (j + 1) - nH f S D j) :=
    (Finset.sum_range_sub (nH f S D) L).symm
  have hle : ∑ _j ∈ Finset.range L, |nH f S D 0 - nH f S D L| / L ≤
      ∑ j ∈ Finset.range L, |nH f S D (j + 1) - nH f S D j| := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ _ (by exact_mod_cast hL.ne' : (L : ℝ) ≠ 0), abs_sub_comm, htel]
    exact Finset.abs_sum_le_sum_abs _ _
  obtain ⟨j, hj, hjle⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr hL.ne') hle
  exact ⟨j, Finset.mem_range.mp hj, hjle⟩

/-- The string seen by the predictor: outputs `< j` real (with `x` written into `S j` of `y`),
output `j` equal to `β`, the rest from `u`. -/
def nwStr (j : Fin L) (y : Fin d → Bool) (u : Fin L → Bool) (x : Fin m → Bool) (β : Bool) :
    Fin L → Bool :=
  fun i => if i.val < j.val then f (fun k => ow (S j) y x (S i k)) else if i = j then β else u i

theorem nhyb_succ_eq (hS : ∀ i, Function.Injective (S i)) (j : Fin L) (y : Fin d → Bool)
    (u : Fin L → Bool) (x : Fin m → Bool) :
    nhyb f S (j.val + 1) (ow (S j) y x) u = nwStr f S j y u x (f x) := by
  funext i
  simp only [nhyb, nwStr, nw]
  by_cases h1 : i.val < j.val
  · rw [if_pos (by omega), if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : i = j
    · subst h2
      rw [if_pos (by omega), if_pos rfl, ow_comp (hS i)]
    · rw [if_neg (fun h => h2 (Fin.ext (by omega))), if_neg h2]

theorem nhyb_eq (j : Fin L) (y : Fin d → Bool) (u : Fin L → Bool) (x : Fin m → Bool) (β : Bool) :
    nhyb f S j.val (ow (S j) y x) (Function.update u j β) = nwStr f S j y u x β := by
  funext i
  simp only [nhyb, nwStr, nw]
  by_cases h1 : i.val < j.val
  · simp only [h1, if_true]
  · simp only [h1, if_false]
    by_cases h2 : i = j
    · subst h2; simp
    · simp [h2]

/-- Real and random versions of the step at `j`, for fixed `y` and `u`. -/
def nReal (j : Fin L) (y : Fin d → Bool) (u : Fin L → Bool) : ℝ :=
  ex (fun x : Fin m → Bool => bv (D (nwStr f S j y u x (f x))))

def nRand (j : Fin L) (y : Fin d → Bool) (u : Fin L → Bool) : ℝ :=
  ex (fun x : Fin m → Bool => ex (fun β : Bool => bv (D (nwStr f S j y u x β))))

theorem nH_succ_eq (hS : ∀ i, Function.Injective (S i)) (j : Fin L) :
    nH f S D (j.val + 1) = ex (fun y : Fin d → Bool => ex (fun u : Fin L → Bool =>
      nReal f S D j y u)) := by
  rw [nH, ex_ow (hS j)]
  congr 1; funext y
  rw [ex_comm]
  congr 1; funext u
  simp only [nReal, nhyb_succ_eq f S hS]

theorem nH_eq (hS : ∀ i, Function.Injective (S i)) (j : Fin L) :
    nH f S D j.val = ex (fun y : Fin d → Bool => ex (fun u : Fin L → Bool =>
      nRand f S D j y u)) := by
  rw [nH, ex_ow (hS j)]
  congr 1; funext y
  have h1 : ∀ x : Fin m → Bool, ex (fun u : Fin L → Bool => bv (D (nhyb f S j.val (ow (S j) y x) u)))
      = ex (fun u : Fin L → Bool => ex (fun β : Bool => bv (D (nwStr f S j y u x β)))) := by
    intro x
    rw [ex_update j]
    simp only [nhyb_eq]
  simp only [h1]
  rw [ex_comm]
  rfl

/-- Some `j`, `y`, `u` carry a `1/L` share of the advantage. -/
theorem nw_exists_point (hS : ∀ i, Function.Injective (S i)) (hL : 0 < L) :
    ∃ (j : Fin L) (y : Fin d → Bool) (u : Fin L → Bool),
      |ex (fun w : Fin L → Bool => bv (D w)) - ex (fun z : Fin d → Bool => bv (D (nw f S z)))| / L
        ≤ |nReal f S D j y u - nRand f S D j y u| := by
  obtain ⟨j, hj, hle⟩ := nw_exists_step f S D hL
  have e1 := nH_succ_eq f S D hS ⟨j, hj⟩
  have e2 := nH_eq f S D hS ⟨j, hj⟩
  simp only at e1 e2
  rw [e1, e2, ← ex_sub] at hle
  obtain ⟨y, hy⟩ := exists_le_of_le_ex (hle.trans (abs_ex_le _))
  rw [← ex_sub] at hy
  obtain ⟨u, hu⟩ := exists_le_of_le_ex (hy.trans (abs_ex_le _))
  exact ⟨⟨j, hj⟩, y, u, hu⟩

/-- Yao's step: guessing `c` and flipping according to the test gives a predictor whose
average success is `1/2 ± (nReal − nRand)`. -/
theorem nw_yao (j : Fin L) (y : Fin d → Bool) (u : Fin L → Bool) (e : Bool) :
    ex (fun c : Bool => ex (fun x : Fin m → Bool =>
      ind (fun c => xor (D (nwStr f S j y u x c)) (xor c e) = f x) c)) =
      1 / 2 + (if e then 1 else -1) * (nReal f S D j y u - nRand f S D j y u) := by
  rw [ex_comm, nReal, nRand, ← ex_sub, ← ex_const_mul,
    ← ex_const (α := Fin m → Bool) (1 / 2), ← ex_add]
  congr 1; funext x
  exact yao_pt (fun c => D (nwStr f S j y u x c)) (f x) e

end Hybrid

/-! ## The predictor is a small circuit -/

theorem juntaSize_mono {k k' : ℕ} (h : k ≤ k') : juntaSize k ≤ juntaSize k' := by
  unfold juntaSize
  exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num) h)

/-- With `y`, `u`, `β` fixed, the predictor's string is a local map of `x`: output `i < j`
reads only the `≤ a` bits of `x` at positions of `S j` inside `S i`. -/
theorem hasMCircuitOfSize_nwStr {d m L a : ℕ} (hm : 0 < m) (f : (Fin m → Bool) → Bool)
    (Des : Design d m L a) (j : Fin L) (y : Fin d → Bool) (u : Fin L → Bool) (β : Bool) :
    HasMCircuitOfSize (fun x => nwStr f Des.S j y u x β) (L * juntaSize a) := by
  refine hasMCircuitOfSize_of_forall _ fun i => ?_
  let A : Finset (Fin m) :=
    if i.val < j.val then Finset.univ.filter (fun t => ∃ k, Des.S i k = Des.S j t) else ∅
  have hA : A.card ≤ a := by
    by_cases h : i.val < j.val
    · simp only [A, if_pos h]
      exact Des.inter i j (fun hij => by rw [hij] at h; exact lt_irrefl _ h)
    · simp only [A, if_neg h, Finset.card_empty]; exact Nat.zero_le _
  refine (hasCircuitOfSize_dep hm (fun x => nwStr f Des.S j y u x β i) (fun t : A => t.val)
    ?_).mono (juntaSize_mono (by rw [Fintype.card_coe]; exact hA))
  intro x x' hxx
  simp only [nwStr]
  by_cases h : i.val < j.val
  · simp only [h, if_true]
    congr 1; funext k
    simp only [ow]
    by_cases hk : ∃ t, Des.S j t = Des.S i k
    · rw [dif_pos hk, dif_pos hk]
      have hmem : hk.choose ∈ A := by
        simp only [A, if_pos h, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨k, hk.choose_spec.symm⟩
      exact hxx ⟨_, hmem⟩
    · rw [dif_neg hk, dif_neg hk]
  · simp only [h, if_false]

/-! ## The Nisan–Wigderson theorem -/

/-- **Nisan–Wigderson reduction** (explicit parameters). A test `D` with `sD` gates and
advantage `α` against `nw f S` yields a predictor for `f` with `L · juntaSize a + sD + 1`
gates and success `≥ 1/2 + α/L`. -/
theorem nw_reduction {d m L a sD : ℕ} (hm : 0 < m) (hL : 0 < L) (f : (Fin m → Bool) → Bool)
    (Des : Design d m L a) {D : (Fin L → Bool) → Bool} (hD : HasCircuitOfSize D sD) :
    ∃ B : (Fin m → Bool) → Bool, HasCircuitOfSize B (L * juntaSize a + sD + 1) ∧
      1 / 2 + |ex (fun w : Fin L → Bool => bv (D w)) -
        ex (fun z : Fin d → Bool => bv (D (nw f Des.S z)))| / L ≤
      prob (fun x => B x = f x) := by
  obtain ⟨j, y, u, hu⟩ := nw_exists_point f Des.S D Des.inj hL
  let e : Bool := decide (nRand f Des.S D j y u ≤ nReal f Des.S D j y u)
  have hy := nw_yao f Des.S D j y u e
  have hge : |nReal f Des.S D j y u - nRand f Des.S D j y u| ≤ (if e then 1 else -1) *
      (nReal f Des.S D j y u - nRand f Des.S D j y u) := by
    by_cases h : nRand f Des.S D j y u ≤ nReal f Des.S D j y u
    · simp only [e, h, decide_true, if_true, one_mul]
      exact le_of_eq (abs_of_nonneg (by linarith))
    · simp only [e, h, decide_false, Bool.false_eq_true, if_false]
      rw [abs_of_neg (by linarith)]; linarith
  have hall : 1 / 2 + |ex (fun w : Fin L → Bool => bv (D w)) -
      ex (fun z : Fin d → Bool => bv (D (nw f Des.S z)))| / L ≤
      ex (fun c : Bool => ex (fun x : Fin m → Bool =>
        ind (fun c => xor (D (nwStr f Des.S j y u x c)) (xor c e) = f x) c)) := by
    rw [hy]; linarith
  obtain ⟨c, hc⟩ := exists_le_of_le_ex hall
  refine ⟨fun x => xor (D (nwStr f Des.S j y u x c)) (xor c e), ?_, ?_⟩
  · have h1 := ((hasMCircuitOfSize_nwStr hm f Des j y u c).comp_single hD).toM 1
    exact h1.comp_single (hasCircuitOfSize_xor_const (xor c e))
  · rw [prob_eq_ex]
    exact hc.trans (le_of_eq rfl)

/-- **Nisan–Wigderson theorem.** If `f` is `(L · juntaSize a + sD + 1, ε)`-hard on average,
then no test with `sD` gates distinguishes `nw f S` (seed `d` bits, output `L` bits) from
uniform with advantage more than `L · ε`. -/
theorem nw_secure {d m L a sD : ℕ} (hm : 0 < m) (f : (Fin m → Bool) → Bool)
    (Des : Design d m L a) {ε : ℝ} (hf : AvgHard f (L * juntaSize a + sD + 1) ε)
    {D : (Fin L → Bool) → Bool} (hD : HasCircuitOfSize D sD) :
    |ex (fun w : Fin L → Bool => bv (D w)) -
      ex (fun z : Fin d → Bool => bv (D (nw f Des.S z)))| ≤ L * ε := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    have : ∀ w : Fin 0 → Bool, w = fun i => i.elim0 := fun w => funext fun i => i.elim0
    have h1 : ex (fun w : Fin 0 → Bool => bv (D w)) = bv (D fun i => i.elim0) := by
      simp only [this]; exact ex_const _
    have h2 : ex (fun z : Fin d → Bool => bv (D (nw f Des.S z))) = bv (D fun i => i.elim0) := by
      simp only [this]; exact ex_const _
    rw [h1, h2]; simp
  · obtain ⟨B, hB, hle⟩ := nw_reduction hm hL f Des hD
    have := hle.trans (hf B hB)
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have h3 : |ex (fun w : Fin L → Bool => bv (D w)) -
        ex (fun z : Fin d → Bool => bv (D (nw f Des.S z)))| / L ≤ ε := by linarith
    rwa [div_le_iff₀' hLr] at h3

/-! ## Designs from polynomials over a finite field -/

section PolyDesign

open Polynomial

variable (K : Type) [Field K] [Fintype K] (k : ℕ)

/-- Points of the plane `K × K`, numbered. -/
def plane : K × K ≃ Fin (Fintype.card K * Fintype.card K) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_prod])

/-- Coefficient vectors of polynomials of degree `< k`, numbered. -/
def coeffs : (Fin k → K) ≃ Fin (Fintype.card K ^ k) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_fun, Fintype.card_fin])

/-- The polynomial with coefficient vector `c` (degree `< k`). -/
def cpoly (c : Fin k → K) : K[X] := ((degreeLTEquiv K k).symm c : K[X])

/-- Set number `i`: the graph `{(x, Pᵢ(x))}` of the `i`-th polynomial of degree `< k`. -/
def polyS (i : Fin (Fintype.card K ^ k)) (t : Fin (Fintype.card K)) :
    Fin (Fintype.card K * Fintype.card K) :=
  plane K ((Fintype.equivFin K).symm t,
    (cpoly K k ((coeffs K k).symm i)).eval ((Fintype.equivFin K).symm t))

theorem polyS_inj (i : Fin (Fintype.card K ^ k)) : Function.Injective (polyS K k i) := by
  intro t t' h
  have h' := congrArg Prod.fst ((plane K).injective h)
  exact (Fintype.equivFin K).symm.injective h'

theorem cpoly_sub_ne {i j : Fin (Fintype.card K ^ k)} (hij : i ≠ j) :
    cpoly K k ((coeffs K k).symm i) - cpoly K k ((coeffs K k).symm j) ≠ 0 := by
  intro h
  apply hij
  have h1 : cpoly K k ((coeffs K k).symm i) = cpoly K k ((coeffs K k).symm j) := sub_eq_zero.mp h
  have h2 := (degreeLTEquiv K k).symm.injective (Subtype.ext h1)
  exact (coeffs K k).symm.injective h2

theorem natDegree_cpoly_sub_lt {i j : Fin (Fintype.card K ^ k)} (hij : i ≠ j) :
    (cpoly K k ((coeffs K k).symm i) - cpoly K k ((coeffs K k).symm j)).natDegree < k := by
  have hmem : cpoly K k ((coeffs K k).symm i) - cpoly K k ((coeffs K k).symm j) ∈
      degreeLT K k :=
    Submodule.sub_mem _ ((degreeLTEquiv K k).symm _).2 ((degreeLTEquiv K k).symm _).2
  rw [mem_degreeLT] at hmem
  exact (natDegree_lt_iff_degree_lt (cpoly_sub_ne K k hij)).mpr hmem

theorem polyS_inter (i j : Fin (Fintype.card K ^ k)) (hij : i ≠ j) :
    (Finset.univ.filter (fun t => ∃ s, polyS K k i s = polyS K k j t)).card ≤ k - 1 := by
  set P := cpoly K k ((coeffs K k).symm i) - cpoly K k ((coeffs K k).symm j)
  have hP : P ≠ 0 := cpoly_sub_ne K k hij
  have hmaps : ∀ t ∈ Finset.univ.filter (fun t => ∃ s, polyS K k i s = polyS K k j t),
      (Fintype.equivFin K).symm t ∈ P.roots.toFinset := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨s, hs⟩ := ht
    have h := (plane K).injective hs
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, ← h1, h2, h1, sub_self]
  have hc := Finset.card_le_card_of_injOn _ hmaps
    (fun a _ b _ hab => (Fintype.equivFin K).symm.injective hab)
  have hdeg : P.natDegree < k := natDegree_cpoly_sub_lt K k hij
  calc _ ≤ P.roots.toFinset.card := hc
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ ≤ k - 1 := by omega

/-- **Polynomial designs.** Over a field with `q` elements, the graphs of the `q^k`
polynomials of degree `< k` are `q`-subsets of the `q²` points of the plane, any two meeting
in at most `k − 1` points. -/
def polyDesign : Design (Fintype.card K * Fintype.card K) (Fintype.card K)
    (Fintype.card K ^ k) (k - 1) where
  S := polyS K k
  inj := polyS_inj K k
  inter := polyS_inter K k

/-- **Nisan–Wigderson with polynomial designs.** Let `K` have `q` elements and let
`f : {0,1}^q → {0,1}` be `(q^k · 4 · 2^(k-1) + sD + 1, ε)`-hard on average. Then the generator
stretching `q²` seed bits to `q^k` output bits fools every test with `sD` gates up to
advantage `q^k · ε`. -/
theorem nw_poly_secure {sD : ℕ} (f : (Fin (Fintype.card K) → Bool) → Bool) {ε : ℝ}
    (hf : AvgHard f (Fintype.card K ^ k * juntaSize (k - 1) + sD + 1) ε)
    {D : (Fin (Fintype.card K ^ k) → Bool) → Bool} (hD : HasCircuitOfSize D sD) :
    |ex (fun w : Fin (Fintype.card K ^ k) → Bool => bv (D w)) -
      ex (fun z : Fin (Fintype.card K * Fintype.card K) → Bool =>
        bv (D (nw f (polyDesign K k).S z)))| ≤ (Fintype.card K ^ k : ℕ) * ε :=
  nw_secure Fintype.card_pos f (polyDesign K k) hf hD

end PolyDesign

end

end Pnp.Derand
