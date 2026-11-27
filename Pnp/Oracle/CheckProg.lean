import Pnp.Oracle.NPEquiv

/-!
# Official checking relations as subroutines of our machines

`checkProg`: for an official polynomial-time checking relation `R` on bit strings and any
exponent `k`, there is one of our programs `q` (the verifier of `Pnp.Oracle.NPEquiv`) and a
symbol code `cc` such that on input `x` and certificate `(ys.flatMap cc).reverse` with
`|ys| ≤ |x|^k`, `q` halts within `(|x|+2)^K` steps with answer `R x ys`.
-/

namespace Pnp.Relativize.NPEquiv

open Turing Function Polynomial Pnp.Relativize.Comb Pnp.Relativize.FromTM2 Pnp.Relativize.FromNP
open scoped Classical

theorem checkProg {R : Str → Str → Prop}
    (hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string Bool)
      (Millennium.fin_encoding_string Bool) R) (k : ℕ) :
    ∃ (q : Prog) (cc : Bool → Str) (K : ℕ), ∀ x ys : Str, ys.length ≤ x.length ^ k →
      runFor ∅ q (tb K x.length) (.run (init [x, (ys.flatMap cc).reverse])) =
        .done (decide (R x ys)) := by
  classical
  let Γ₁ := Bool
  obtain ⟨f, comp, hf⟩ := hR
  let tm := comp.tm
  let e₀ : tm.Γ tm.k₀ ≃ (Bool ⊕ Option Γ₁) := comp.inputAlphabet
  let e₁ : tm.Γ tm.k₁ ≃ Bool := comp.outputAlphabet
  have hout : ∀ (x : Str) (ys : List Γ₁), TM2OutputsInTime tm ((inputOf x ys).map e₀.symm)
      (some [e₁.symm (f (x, ys))]) (comp.time.eval (inputOf x ys).length) :=
    fun x ys => comp.outputsFun (x, ys)
  obtain ⟨c, d, hcd⟩ := OfficialP.eval_le comp.time
  -- constants
  set n := n0 tm k with hn
  set DB := Dm tm * B tm (lay tm k) with hDB
  set N₁ := N tm (lay tm k) tm.k₁ with hN₁
  let E := 3 * k + 1 + (k + 1) * d
  let M := 2 * n + (k + 3) + 1 + 2 * (2 * n + 2) + 3 * n + 2 + (n + 3) + 1 +
    c * 3 ^ d * DB + 1 + N₁ + 1 + 1 + 1
  let K := M + 0 + E
  refine ⟨V tm e₀ e₁ k, cc tm e₀ k, K, fun x => ?_⟩
  set X := x.length + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hP : ∀ a, a ≤ E → X ^ a ≤ X ^ E := fun a ha => Nat.pow_le_pow_right (by omega) ha
  have hP1 : 1 ≤ X ^ E := Nat.one_le_pow _ _ (by omega)
  have hxk : x.length ^ k ≤ X ^ E :=
    (Nat.pow_le_pow_left (by omega) k).trans (hP k (by omega))
  have hxX : x.length ≤ X ^ E := by
    have := hP 1 (by omega); rw [pow_one] at this; omega
  have hKb : M * X ^ E ≤ tb K x.length := by
    have := OfficialP.absorb M 0 E x.length
    simpa [tb, K] using this
  -- bound of a run on an honest certificate
  have hbnd : ∀ ys : List Γ₁, ys.length ≤ x.length ^ k →
      bnd tm e₀ k comp.time x ys ≤ M * X ^ E := by
    intro ys hy
    have hy' : ys.length ≤ X ^ E := hy.trans hxk
    have h1 := flatMap_cc_length_le tm e₀ k ys
    have h2 : Tpad x.length k ≤ X ^ E :=
      (Tpad_mono (by omega) k).trans ((Tpad_le hX2 k).trans (hP _ (by omega)))
    have h3 : comp.time.eval (x.length + 1 + ys.length) ≤ c * 3 ^ d * X ^ E := by
      refine (hcd _).trans ?_
      have hk1 : X ≤ X ^ (k + 1) := by
        calc X = X ^ 1 := (pow_one X).symm
          _ ≤ X ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hk2 : 1 ≤ X ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
      have hk3 : ys.length ≤ X ^ (k + 1) :=
        hy.trans ((Nat.pow_le_pow_left (by omega) k).trans
          (Nat.pow_le_pow_right (by omega) (by omega)))
      have hb : x.length + 1 + ys.length + 2 ≤ 3 * X ^ (k + 1) := by omega
      calc c * (x.length + 1 + ys.length + 2) ^ d ≤ c * (3 * X ^ (k + 1)) ^ d :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb d)
        _ = c * 3 ^ d * X ^ ((k + 1) * d) := by rw [mul_pow, ← pow_mul]; ring
        _ ≤ c * 3 ^ d * X ^ E := Nat.mul_le_mul_left _ (hP _ (by omega))
    have h4 := Nat.mul_le_mul_right DB h3
    have h5 : ys.length * n ≤ X ^ E * n := Nat.mul_le_mul_right _ hy'
    have h6 : ys.length * (2 * n + 2) ≤ X ^ E * (2 * n + 2) := Nat.mul_le_mul_right _ hy'
    have h7 : x.length * (k + 3) ≤ X ^ E * (k + 3) := Nat.mul_le_mul_right _ hxX
    have h8 : x.length * (n + 3) ≤ X ^ E * (n + 3) := Nat.mul_le_mul_right _ hxX
    have hnP : n ≤ n * X ^ E := Nat.le_mul_of_pos_right _ hP1
    have hNP : N₁ ≤ N₁ * X ^ E := Nat.le_mul_of_pos_right _ hP1
    have hFL : (ys.flatMap (cc tm e₀ k)).length ≤ X ^ E * n := h1.trans h5
    simp only [bnd]
    simp only [M]
    rw [← hn, ← hDB, ← hN₁]
    generalize X ^ E = P at *
    nlinarith [h1, h2, h4, h5, h6, h7, h8, hnP, hNP, hFL, hP1]
  intro ys hyl
  rcases outcome tm e₀ e₁ k hout x (ys.flatMap (cc tm e₀ k)).reverse with
    ⟨t, -, hno⟩ | ⟨ys', t, hyl', hys', htb, ht⟩
  · exact absurd ⟨ys, hyl, by rw [List.reverse_reverse]⟩ hno
  · rw [List.reverse_reverse] at hys'
    have := flatMap_cc_injective tm e₀ k hys'
    subst this
    have hfx : f (x, ys) = decide (R x ys) := by
      have := hf (x, ys)
      cases h : f (x, ys) <;> simp_all
    rw [hfx] at ht
    exact runFor_mono ht ((htb.trans (hbnd ys hyl)).trans hKb)

end Pnp.Relativize.NPEquiv
