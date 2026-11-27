import Pnp.KarpLipton.KarpLipton
import Pnp.CookLevin.SAT

/-!
# The Karp–Lipton hypothesis is exactly `NP ⊆ P/poly` (M31)

`Pnp.KarpLipton.SmallExistentials T` says that circuit satisfiability has polynomial-size
circuits (non-uniformly).  M30 showed that it implies `NP ⊆ P/poly`
(`inPPoly_of_smallExistentials`).  Here we prove the converse, so that the hypothesis of the
Karp–Lipton theorem becomes the official-style statement `NP ⊆ P/poly`:

* `inst C x`: for a circuit `C` on `n + Z` inputs, the dense CNF word (Tseitin's formula of `C`
  with the first `n` inputs fixed to `x` by unit clauses).  It is satisfiable iff
  `∃ z, C(x, z) = true` (`Pnp.CookLevin.sat_fixed_iff`), and every symbol of it depends on at most
  one bit of `x` (`inst_getElem?_congr`), so `x ↦ oneHot (inst C x)` is computed by a circuit of
  linear size.
* `smallExistentials_of_inPPoly_sat`: if the language `SATLang` (official `NP`,
  `Pnp.CookLevin.sat_in_np`) has polynomial-size circuits, then `SmallExistentials T` holds for
  some polynomial `T` (compose the SAT circuit with the instance-building circuit).
* `smallExistentials_iff`: `(∃ T, SmallExistentials T) ↔ InPPoly SATLang ↔ NPSubsetPPoly`, where
  `NPSubsetPPoly` says that every language in the official class `NP` (strings over a finite
  alphabet) has polynomial-size circuits.
* `karp_lipton_of_np_subset_ppoly`: the Karp–Lipton theorem (circuit form, M30) with the
  hypothesis `NP ⊆ P/poly`.

No polynomial-time Turing machine is needed here: the converse only uses that `SAT` itself is
in `NP` and that the Tseitin construction with fixed inputs is local.  Nothing here proves or
refutes `P ≠ NP`.
-/

namespace Pnp.KarpLipton

open Pnp.Circuits Pnp.PPoly Pnp.CookLevin Classical

noncomputable section

/-! ## Positions in a dense CNF word -/

theorem encodeCNF_getElem? (N : ℕ) : ∀ (cs : List (ℕ → Option Bool)) (i : ℕ),
    (encodeCNF N cs)[i]? = (cs[i / (N + 1)]?).bind (fun L => (denseClause N L)[i % (N + 1)]?)
  | [], i => by simp [encodeCNF]
  | L :: cs, i => by
    have e : encodeCNF N (L :: cs) = denseClause N L ++ encodeCNF N cs := by
      simp [encodeCNF]
    rw [e, List.getElem?_append, length_denseClause]
    split_ifs with h
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      simp
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + (N + 1) := ⟨i - (N + 1), by omega⟩
      rw [Nat.add_sub_cancel, encodeCNF_getElem? N cs j, Nat.add_div_right _ (by omega),
        Nat.add_mod_right]
      simp

/-! ## The instance with fixed inputs -/

variable {n Z t : ℕ}

/-- Tseitin's formula of `C` with the first `n` inputs fixed to `x`. -/
def inst (C : Circuit (n + Z) t) (x : Fin n → Bool) : List SatSym :=
  encodeCNF (n + Z + t) (tseitinCNF C ++ inputUnits x)

/-- The length of the instance does not depend on `x`. -/
def instLen (C : Circuit (n + Z) t) : ℕ := ((tseitinCNF C).length + n) * (n + Z + t + 1)

theorem length_inst (C : Circuit (n + Z) t) (x : Fin n → Bool) :
    (inst C x).length = instLen C := by
  rw [inst, length_encodeCNF, List.length_append, length_inputUnits, instLen]

theorem inst_sat_iff (C : Circuit (n + Z) t) (x : Fin n → Bool) :
    SATLang (inst C x) ↔ ∃ z : Fin Z → Bool, C.eval (Fin.append x z) = true :=
  sat_fixed_iff C x

/-- The input bit on which position `i` of the instance may depend. -/
def instDep (C : Circuit (n + Z) t) (hn : 0 < n) (i : ℕ) : Fin n :=
  if h : i / (n + Z + t + 1) - (tseitinCNF C).length < n then
    ⟨i / (n + Z + t + 1) - (tseitinCNF C).length, h⟩
  else ⟨0, hn⟩

/-- **Locality.** Position `i` of the instance only depends on the input bit `instDep C hn i`. -/
theorem inst_getElem?_congr (C : Circuit (n + Z) t) (hn : 0 < n) (x y : Fin n → Bool) (i : ℕ)
    (h : x (instDep C hn i) = y (instDep C hn i)) : (inst C x)[i]? = (inst C y)[i]? := by
  unfold inst
  rw [encodeCNF_getElem?, encodeCNF_getElem?]
  congr 1
  set c := i / (n + Z + t + 1)
  rw [List.getElem?_append, List.getElem?_append]
  split_ifs with hc
  · rfl
  · simp only [inputUnits, List.getElem?_ofFn]
    by_cases hj : c - (tseitinCNF C).length < n
    · rw [dif_pos hj, dif_pos hj]
      have : instDep C hn i = ⟨c - (tseitinCNF C).length, hj⟩ := by
        simp only [instDep, dif_pos hj, c]
      rw [this] at h
      simp only [h]
    · rw [dif_neg hj, dif_neg hj]

/-- The one-hot code of the instance is computed by a circuit of linear size. -/
theorem hasMCircuitOfSize_inst (C : Circuit (n + Z) t) (hn : 0 < n) :
    HasMCircuitOfSize (fun x : Fin n → Bool => oneHot (instLen C) (inst C x))
      (instLen C * Fintype.card SatSym * juntaSize 1) := by
  have := hasMCircuitOfSize_dep (Dep := Unit) hn
    (fun x : Fin n → Bool => oneHot (instLen C) (inst C x))
    (fun j _ => instDep C hn (finProdFinEquiv.symm j).1.val)
    (fun j x y hxy => by
      have e := inst_getElem?_congr C hn x y (finProdFinEquiv.symm j).1.val (hxy ())
      simp only [oneHot, e])
  simpa using this

/-! ## From SAT circuits to `SmallExistentials` -/

/-- The polynomial bounding the instance length in terms of `n + Z + s`. -/
def lenP : Polynomial ℕ := (5 * Polynomial.X + 1) * (Polynomial.X + 1)

theorem instLen_le (C : Circuit (n + Z) t) {s : ℕ} (hts : t ≤ s) :
    instLen C ≤ lenP.eval (n + Z + s) := by
  have h1 := length_tseitinCNF_le C
  simp only [lenP, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold instLen
  exact Nat.mul_le_mul (by nlinarith) (by omega)

/-- **`SAT ∈ P/poly` implies the Karp–Lipton hypothesis.** -/
theorem smallExistentials_of_inPPoly_sat (h : InPPoly SATLang) : ∃ T, SmallExistentials T := by
  obtain ⟨p, hp⟩ := h
  refine ⟨Polynomial.C (Fintype.card SatSym * juntaSize 1) * lenP + p.comp lenP, ?_⟩
  intro n Z s V hn hV
  obtain ⟨t, hts, C, rfl⟩ := hV
  have hL : 0 < instLen C := by
    unfold instLen
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨f, hf, hfL⟩ := hp (instLen C) hL
  have hcomp := (hasMCircuitOfSize_inst C hn).comp_single hf
  have heq : (fun x : Fin n → Bool =>
      decide (∃ z : Fin Z → Bool, C.eval (Fin.append x z) = true)) =
      f ∘ (fun x : Fin n → Bool => oneHot (instLen C) (inst C x)) := by
    funext x
    simp only [Function.comp]
    rw [Bool.eq_iff_iff, hfL _ (length_inst C x), inst_sat_iff, decide_eq_true_iff]
  rw [heq]
  refine hcomp.mono ?_
  have hle := instLen_le C hts
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  have h2 := eval_le_of_le p hle
  have h3 := Nat.mul_le_mul_left (Fintype.card SatSym * juntaSize 1) hle
  rw [show instLen C * Fintype.card SatSym * juntaSize 1 =
    Fintype.card SatSym * juntaSize 1 * instLen C by ring]
  omega

/-! ## `NP ⊆ P/poly` -/

/-- Every language of the official class `NP` (strings over a finite nonempty alphabet) has
polynomial-size circuits. -/
def NPSubsetPPoly : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] [Nonempty α] (L : Millennium.Language (List α)),
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string α) L → InPPoly L

instance : Nonempty SatSym := ⟨SatSym.pos⟩

/-- **The Karp–Lipton hypothesis is `NP ⊆ P/poly`**, and both are equivalent to
`SAT ∈ P/poly`. -/
theorem smallExistentials_iff :
    ((∃ T, SmallExistentials T) ↔ InPPoly SATLang) ∧ (InPPoly SATLang ↔ NPSubsetPPoly) := by
  have h1 : (∃ T, SmallExistentials T) → NPSubsetPPoly := fun ⟨T, hT⟩ α _ _ _ L hL =>
    inPPoly_of_smallExistentials hT hL
  have h2 : NPSubsetPPoly → InPPoly SATLang := fun h => h SatSym SATLang sat_in_np
  exact ⟨⟨fun h => h2 (h1 h), smallExistentials_of_inPPoly_sat⟩,
    ⟨fun h => h1 (smallExistentials_of_inPPoly_sat h), h2⟩⟩

/-- **Karp–Lipton (circuit form) under `NP ⊆ P/poly`.** -/
theorem karp_lipton_of_np_subset_ppoly (hNP : NPSubsetPPoly)
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Primcodable α]
    {L : Millennium.Language (List α)}
    (hL : Millennium.polynomial_hierarchy_pi_level 2 (Millennium.fin_encoding_string α) L) :
    ∃ (β γ : Type) (_ : Fintype β) (_ : Fintype γ) (_ : Primcodable β) (_ : Primcodable γ)
      (L'' : Millennium.Language ((List α × List β) × List γ)) (p q r : Polynomial ℕ),
      Millennium.InPolynomialTime
        (Millennium.pair_encoding (Millennium.pair_encoding (Millennium.fin_encoding_string α)
          (Millennium.fin_encoding_string β)) (Millennium.fin_encoding_string γ))
        (Millennium.complement L'') ∧
      ∀ n, ∀ w : List α, w.length = n →
        (L w ↔ ∃ S : (m : ℕ) → (Fin ((n + 1 + m) * Fintype.card (α ⊕ Option β)) → Bool) →
            (Fin (nCert γ q (n + 1 + m) * Fintype.card γ) → Bool),
          (∀ m ≤ p.eval n, HasMCircuitOfSize (S m) (r.eval n)) ∧
          ∀ b : List β, b.length ≤ p.eval n →
            ∃ m' ≤ nCert γ q (n + 1 + b.length),
              L'' ((w, b), cert γ (nCert γ q (n + 1 + b.length)) m'
                (S b.length (oneHot (n + 1 + b.length) (pe2 w b))))) := by
  obtain ⟨T, hT⟩ := smallExistentials_iff.1.2 (smallExistentials_iff.2.2 hNP)
  exact karp_lipton hT hL

end

end Pnp.KarpLipton
