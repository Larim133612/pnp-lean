import Pnp.Oracle.OfficialP
import Pnp.Oracle.NPEquiv

/-!
# Official `P` for any finite alphabet, as one of our programs on a bit code (M32a)

`Pnp.Relativize.OfficialP.mem_P_empty_of_inPolynomialTime` compiles an official polynomial-time
machine over the alphabet `Bool` into one of our stack programs.  Here the input alphabet is an
arbitrary finite type: with the layout `⟨[], 0⟩` the compiled program reads the input stack in the
truncated-unary code `FromTM2.code` of the input symbols, so the program decides the **bit code**
`(e.encode t).flatMap c` of the official input.

* `decide_of_inPolynomialTime`: for every official `InPolynomialTime e L` (any `FinEncoding e`)
  there are a program `q`, a code `c : e.Γ → Str` of nonempty words and an exponent `K` with
  `runFor ∅ q (tb K |x|) (init [x]) = done (decide (L t))` for `x = (e.encode t).flatMap c`.

This lets official polynomial-time predicates over pair encodings with arbitrary alphabets be used
as subroutines (`Struct.Cmd.call`) of our own programs.
-/

namespace Pnp.Relativize.OfficialCode

open Turing Function Polynomial Pnp.Relativize.Comb Pnp.Relativize.FromTM2

open Classical in
/-- **Official `P` (any finite alphabet) ⊆ our programs on bit codes.** -/
theorem decide_of_inPolynomialTime {T : Type} (e : Computability.FinEncoding T)
    {L : Millennium.Language T} (h : Millennium.InPolynomialTime e L) :
    ∃ (q : Prog) (c : e.Γ → Str) (K : ℕ), (∀ g, c g ≠ []) ∧ ∀ t : T,
      runFor ∅ q (tb K ((e.encode t).flatMap c).length)
        (.run (init [(e.encode t).flatMap c])) = .done (decide (L t)) := by
  classical
  obtain ⟨f, comp, hf⟩ := h
  let tm := comp.tm
  let e₀ : tm.Γ tm.k₀ ≃ e.Γ := comp.inputAlphabet
  let e₁ : tm.Γ tm.k₁ ≃ Bool := comp.outputAlphabet
  let ly : Layout tm := ⟨[], 0⟩
  let c : e.Γ → Str := fun g => FromTM2.code tm ly tm.k₀ (e₀.symm g)
  have hc : ∀ g, c g ≠ [] := by
    intro g
    refine FromNP.tu_ne_nil ?_ (two_le_N tm ly tm.k₀)
    have hmem : e₀.symm g ∈ FromTM2.L tm ly tm.k₀ := by
      simp [FromTM2.L, ly]
    exact lt_of_lt_of_le (List.idxOf_lt_length_of_mem hmem) (le_max_right _ _)
  obtain ⟨cc, d, hcd⟩ := OfficialP.eval_le comp.time
  let a := cc * (Dm tm * B tm ly)
  let b := N tm ly tm.k₁ + 3
  refine ⟨prog tm ly e₁, c, a + b + d, hc, fun t => ?_⟩
  set w := e.encode t with hw
  set x := w.flatMap c with hx
  have hlen : w.length ≤ x.length := by
    rw [hx]
    clear hx hw
    induction w with
    | nil => simp
    | cons g w ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have := List.length_pos_of_ne_nil (hc g)
      omega
  let g : tm.Γ tm.k₁ := e₁.symm (f t)
  have ho : TM2OutputsInTime tm (w.map e₀.symm) (some [g]) (comp.time.eval w.length) :=
    comp.outputsFun t
  have hE : Enc tm ly (initList tm (w.map e₀.symm) : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ).stk
      (init [x]).stk := by
    intro k
    rw [Pnp.PPoly.initList_stk]
    by_cases hk : k = tm.k₀
    · subst hk
      simp only [dite_true, sk_k₀ tm ly, init]
      show x = FromTM2.enc tm ly tm.k₀ (w.map e₀.symm)
      rw [hx, FromTM2.enc, List.flatMap_map]
    · simp only [hk, dite_false, init]
      have := sk_ne_zero tm ly hk
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hj]; rfl
  obtain ⟨t₁, σ', ht₁, hR⟩ := run_compiled tm ly e₁ ho _ hE
  have hfin : runFor ∅ (prog tm ly e₁) (t₁ + 1) (.run (init [x])) = .done (f t) := by
    have e0 : init [x] = ⟨0, (init [x]).stk⟩ := rfl
    rw [e0]
    refine FromNP.runFor_halt hR ?_
    rw [prog_idx tm ly e₁ (fin_mem tm ly _)]
    simp [act, g]
  have hft : f t = decide (L t) := by
    have := hf t
    cases h : f t <;> simp_all
  rw [← hft]
  refine runFor_mono hfin ?_
  have hTle : comp.time.eval w.length ≤ cc * (x.length + 2) ^ d :=
    (OfficialP.eval_le comp.time |> fun _ => hcd _).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have := Nat.mul_le_mul_right (Dm tm * B tm ly) hTle
  have hab := OfficialP.absorb a b d x.length
  simp only [tb]
  have e : cc * (x.length + 2) ^ d * (Dm tm * B tm ly) = a * (x.length + 2) ^ d := by
    simp only [a]; ring
  omega

end Pnp.Relativize.OfficialCode
