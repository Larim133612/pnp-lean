import Pnp.Oracle.StructLib

/-!
# Evaluating a fixed polynomial in unary (M32c)

`hornerCmd xs acc nxt ta tm L`: for the list `L` of coefficients (lowest degree first) and `X`
marks on stack `xs`, push `∑ᵢ L[i] · Xⁱ` marks onto the empty stack `acc` (Horner's rule:
`acc ← c + X · acc` for the coefficients from the highest one down, with the unary
multiplication `mul` of `Pnp/Oracle/StructLib.lean`).

* `exec_hornerCmd`: exact semantics, cost `hT`.
* `polyCmd q`: the coefficients of a polynomial `q : ℕ[X]`; `exec_polyCmd`: `acc` receives
  `q.eval X` marks, within `polyT q X` steps, and `polyT_le`: `polyT q X ≤ C (X + 2)^E` for
  constants depending only on `q`.
-/

namespace Pnp.Relativize.Struct

open Function

section Horner

variable (xs acc nxt ta tm : ℕ)

/-- One Horner step `acc ← c + X · acc`. -/
def hStep (c : ℕ) : Cmd :=
  .seq (mul acc xs nxt ta tm) (.seq (drain acc) (.seq (pushList nxt (List.replicate c true))
    (move nxt acc)))

/-- Horner's rule for the coefficients `L` (lowest degree first). -/
def hornerCmd (L : List ℕ) : Cmd := cmdSeq (L.reverse.map (hStep xs acc nxt ta tm))

end Horner

/-- Horner value of a list of coefficients processed in this order. -/
def hFold (X : ℕ) (A : ℕ) (L : List ℕ) : ℕ := L.foldl (fun a c => c + X * a) A

/-- Exact cost of one Horner step. -/
def stepCost (X A c : ℕ) : ℕ := A * (5 * X + 8) + 4 + (2 * A + 2) + (c + 1) + (2 * (c + A * X) + 2)

/-- Exact cost of the Horner loop. -/
def hT (X : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 1
  | A, c :: L => stepCost X A c + hT X (c + X * A) L

section Correct

variable {xs acc nxt ta tm : ℕ} (h1 : acc ≠ xs) (h2 : acc ≠ nxt) (h3 : acc ≠ ta) (h4 : acc ≠ tm)
  (h5 : xs ≠ nxt) (h6 : xs ≠ ta) (h7 : xs ≠ tm) (h8 : nxt ≠ ta) (h9 : nxt ≠ tm) (h10 : ta ≠ tm)

include h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 in
theorem exec_hStep (X A c : ℕ) (σ : ℕ → Str) (hx : σ xs = List.replicate X true)
    (ha : σ acc = List.replicate A true) (hn : σ nxt = []) (hta : σ ta = []) (htm : σ tm = []) :
    Exec (hStep xs acc nxt ta tm c) σ (.norm (update σ acc (List.replicate (c + X * A) true)))
      (stepCost X A c) := by
  have e1 := exec_mul h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 A X σ ha hx hta htm
  set σ1 := update σ nxt (List.replicate (A * X) true ++ σ nxt)
  have e2 := exec_drain acc (σ1 acc) σ1 rfl
  set σ2 := update σ1 acc []
  have e3 := exec_pushList nxt (List.replicate c true) σ2
  set σ3 := update σ2 nxt (List.replicate c true ++ σ2 nxt)
  have e4 := exec_move h2.symm (σ3 nxt) σ3 rfl
  refine (Exec.seq_norm e1 (Exec.seq_norm e2 (Exec.seq_norm e3 e4))).cast ?_ ?_
  · congr 1; funext j
    simp only [σ3, σ2, σ1, update_apply]
    split_ifs <;> simp_all [List.reverse_replicate, ← List.replicate_add, Nat.mul_comm, Nat.add_comm]
  · simp [σ3, σ2, σ1, stepCost, h2, hn, ha, h2.symm, List.length_replicate] <;> ring

include h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 in
theorem exec_hLoop (X : ℕ) : ∀ (L : List ℕ) (A : ℕ) (σ : ℕ → Str),
    σ xs = List.replicate X true → σ acc = List.replicate A true → σ nxt = [] → σ ta = [] →
    σ tm = [] →
    Exec (cmdSeq (L.map (hStep xs acc nxt ta tm))) σ
      (.norm (update σ acc (List.replicate (hFold X A L) true))) (hT X A L)
  | [], A, σ, _, ha, _, _, _ => by
    refine (Exec.skip σ).cast ?_ rfl
    simp [hFold, ← ha]
  | c :: L, A, σ, hx, ha, hn, hta, htm => by
    have e1 := exec_hStep h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 X A c σ hx ha hn hta htm
    set σ1 := update σ acc (List.replicate (c + X * A) true)
    have e2 := exec_hLoop X L (c + X * A) σ1 (by simp [σ1, h1.symm, hx]) (by simp [σ1])
      (by simp [σ1, h2.symm, hn]) (by simp [σ1, h3.symm, hta]) (by simp [σ1, h4.symm, htm])
    refine (Exec.seq_norm e1 e2).cast ?_ rfl
    simp [σ1, hFold]

end Correct

/-- `hFold` from `0` on the reversed coefficient list is the polynomial value. -/
theorem hFold_reverse (X : ℕ) : ∀ L : List ℕ,
    hFold X 0 L.reverse = ∑ i ∈ Finset.range L.length, L.getD i 0 * X ^ i
  | [] => by simp [hFold]
  | c :: L => by
    have ih := hFold_reverse X L
    simp only [hFold, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [Finset.mul_sum]
    ring_nf

/-- The coefficient list of a polynomial, lowest degree first. -/
noncomputable def coeffs (q : Polynomial ℕ) : List ℕ := (List.range (q.natDegree + 1)).map q.coeff

theorem hFold_coeffs (q : Polynomial ℕ) (X : ℕ) : hFold X 0 (coeffs q).reverse = q.eval X := by
  rw [hFold_reverse, Polynomial.eval_eq_sum_range]
  simp only [coeffs, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- Evaluate the polynomial `q` in unary. -/
noncomputable def polyCmd (xs acc nxt ta tm : ℕ) (q : Polynomial ℕ) : Cmd :=
  hornerCmd xs acc nxt ta tm (coeffs q)

/-- Cost of `polyCmd`. -/
noncomputable def polyT (q : Polynomial ℕ) (X : ℕ) : ℕ := hT X 0 (coeffs q).reverse

section Poly

variable {xs acc nxt ta tm : ℕ} (h1 : acc ≠ xs) (h2 : acc ≠ nxt) (h3 : acc ≠ ta) (h4 : acc ≠ tm)
  (h5 : xs ≠ nxt) (h6 : xs ≠ ta) (h7 : xs ≠ tm) (h8 : nxt ≠ ta) (h9 : nxt ≠ tm) (h10 : ta ≠ tm)

include h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 in
/-- **Unary polynomial evaluation.** -/
theorem exec_polyCmd (q : Polynomial ℕ) (X : ℕ) (σ : ℕ → Str)
    (hx : σ xs = List.replicate X true) (ha : σ acc = []) (hn : σ nxt = []) (hta : σ ta = [])
    (htm : σ tm = []) :
    Exec (polyCmd xs acc nxt ta tm q) σ
      (.norm (update σ acc (List.replicate (q.eval X) true))) (polyT q X) := by
  have := exec_hLoop h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 X (coeffs q).reverse 0 σ hx (by simp [ha]) hn
    hta htm
  rw [hFold_coeffs] at this
  exact this

end Poly

/-! ## A polynomial bound on the cost -/

theorem stepCost_le (X A c : ℕ) : stepCost X A c ≤ (A + 1) * (7 * X + 12) + 3 * c + 10 := by
  unfold stepCost; nlinarith

theorem hT_le (X : ℕ) : ∀ (L : List ℕ) (A : ℕ),
    hT X A L ≤ (L.length + 1) * (((A + L.sum) * (X + 1) ^ L.length + 1) * (7 * X + 12) +
      3 * L.sum + 10)
  | [], A => by simp [hT]
  | c :: L, A => by
    have ih := hT_le X L (c + X * A)
    have hs := stepCost_le X A c
    simp only [hT, List.length_cons, List.sum_cons]
    set P := (X + 1) ^ L.length
    have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
    have hk : (c + X * A + L.sum) * P ≤ (A + (c + L.sum)) * (P * (X + 1)) := by
      have : c + X * A + L.sum ≤ (A + (c + L.sum)) * (X + 1) := by
        have e : (A + (c + L.sum)) * (X + 1) = X * A + A + c * X + c + L.sum * X + L.sum := by ring
        omega
      calc (c + X * A + L.sum) * P ≤ (A + (c + L.sum)) * (X + 1) * P := Nat.mul_le_mul_right _ this
        _ = _ := by ring
    have hA : A ≤ (A + (c + L.sum)) * (P * (X + 1)) := by
      have : A ≤ A + (c + L.sum) := by omega
      exact this.trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos hP (by omega)))
    rw [pow_succ]
    set Q := (A + (c + L.sum)) * (P * (X + 1))
    have e1 : ((c + X * A + L.sum) * P + 1) * (7 * X + 12) ≤ (Q + 1) * (7 * X + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    have e2 : (A + 1) * (7 * X + 12) ≤ (Q + 1) * (7 * X + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    set R := (Q + 1) * (7 * X + 12) + 3 * (c + L.sum) + 10
    have e3 : (L.length + 1) * (((c + X * A + L.sum) * P + 1) * (7 * X + 12) + 3 * L.sum + 10) ≤
        (L.length + 1) * R :=
      Nat.mul_le_mul_left _ (by omega)
    have e5 : (L.length + 1 + 1) * R = (L.length + 1) * R + R := by ring
    rw [e5]
    omega

/-- **The cost of `polyCmd q` is polynomial in `X`.** -/
theorem polyT_le (q : Polynomial ℕ) : ∃ C E : ℕ, ∀ X, polyT q X ≤ C * (X + 2) ^ E := by
  set L := (coeffs q).reverse
  refine ⟨(L.length + 1) * ((L.sum + 1) * 7 + 3 * L.sum + 10), L.length + 1, fun X => ?_⟩
  have h := hT_le X L 0
  unfold polyT
  refine h.trans ?_
  set P := (X + 2) ^ L.length
  have hP1 : (X + 1) ^ L.length ≤ P := Nat.pow_le_pow_left (by omega) _
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ]
  have e1 : ((0 + L.sum) * (X + 1) ^ L.length + 1) * (7 * X + 12) ≤
      ((L.sum + 1) * P) * (7 * (X + 2)) := by
    have : (0 + L.sum) * (X + 1) ^ L.length + 1 ≤ (L.sum + 1) * P := by
      have := Nat.mul_le_mul_left L.sum hP1; nlinarith
    exact Nat.mul_le_mul this (by omega)
  have e2 : 3 * L.sum + 10 ≤ (3 * L.sum + 10) * (P * (X + 2)) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos hP (by omega))
  have e3 : ((0 + L.sum) * (X + 1) ^ L.length + 1) * (7 * X + 12) + 3 * L.sum + 10 ≤
      ((L.sum + 1) * 7 + 3 * L.sum + 10) * (P * (X + 2)) := by
    have : (L.sum + 1) * P * (7 * (X + 2)) = ((L.sum + 1) * 7) * (P * (X + 2)) := by ring
    have e6 : ((L.sum + 1) * 7 + 3 * L.sum + 10) * (P * (X + 2)) =
        ((L.sum + 1) * 7) * (P * (X + 2)) + (3 * L.sum + 10) * (P * (X + 2)) := by ring
    omega
  calc (L.length + 1) * (((0 + L.sum) * (X + 1) ^ L.length + 1) * (7 * X + 12) + 3 * L.sum + 10)
      ≤ (L.length + 1) * (((L.sum + 1) * 7 + 3 * L.sum + 10) * (P * (X + 2))) :=
        Nat.mul_le_mul_left _ e3
    _ = _ := by simp only [P]; ring

end Pnp.Relativize.Struct
