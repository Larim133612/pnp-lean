import Pnp.Derandomization.Lautemann
import Pnp.Upstream.PolynomialHierarchy

/-!
# Lautemann's characterization on lists, and an introduction rule for the official `Σ₂ᴾ`

This file prepares the official `BPP ⊆ Σ₂ᴾ` (M26) on the mathematical side.

* `sigma2_intro`: to put a language into the official second level
  `Millennium.polynomial_hierarchy_sigma_level 2` it suffices to give a polynomial-time
  predicate `D` (official class `P`, nested Cook pair encoding `(a#b)#c`) with
  `a ∈ L ↔ ∃ b (|b| ≤ p(|a|)) ∀ c (|c| ≤ q(|a#b|)) D((a,b),c)`.
* `lautemann_list`: for one fixed input, if a predicate `R` on `ℓ`-bit strings agrees with the
  truth value `b` except with probability `≤ 1/3`, then
  `b ↔ ∃ u (|u| ≤ L²) ∀ y, lautSpec R ℓ u y`, where `L = sglReps ℓ · ℓ` and `lautSpec` is the
  explicit inner predicate on lists: `u` consists of `L` shifts of length `L`; for `|y| = L` some
  shift `tᵢ` has a majority of accepting blocks among the `sglReps ℓ` blocks of `tᵢ ⊕ y`
  (amplification + Sipser–Gács–Lautemann covering).  For `ℓ = 0` it is just `R []`.
-/

namespace Pnp.Derand

open Pnp.Circuits Pnp.NaturalProofs Classical

noncomputable section

/-! ## The official `Σ₂ᴾ` -/

open Millennium in
/-- Introduction rule for the official second level of the polynomial hierarchy. -/
theorem sigma2_intro {α : Type} [Primcodable α] (ea : Computability.FinEncoding α)
    (L : Millennium.Language α) (β γ : Type) [Fintype β] [Primcodable β] [Fintype γ] [Primcodable γ]
    (D : Millennium.Language ((α × List β) × List γ))
    (hD : InPolynomialTime
      (pair_encoding (pair_encoding ea (fin_encoding_string β)) (fin_encoding_string γ)) D)
    (p q : Polynomial ℕ)
    (hL : ∀ a, L a ↔ ∃ b : List β, b.length ≤ p.eval (ea.encode a).length ∧
      ∀ c : List γ, c.length ≤ q.eval ((pair_encoding ea (fin_encoding_string β)).encode (a, b)).length →
        D ((a, b), c)) :
    polynomial_hierarchy_sigma_level 2 ea L := by
  refine ⟨β, inferInstance, inferInstance,
    fun ab => ∀ c : List γ,
      c.length ≤ q.eval ((pair_encoding ea (fin_encoding_string β)).encode ab).length → D (ab, c),
    ?_, p, fun a => hL a⟩
  refine ⟨γ, inferInstance, inferInstance, fun x => ¬ D x, ?_, q, fun ab => ?_⟩
  · obtain ⟨f, hf, hfL⟩ := hD
    exact ⟨f, hf, fun x => by
      show ¬ ¬ D x ↔ _
      rw [not_not]; exact hfL x⟩
  · show (¬ ∀ c : List γ, _ → _) ↔ _
    push Not
    rfl

/-! ## Lautemann on lists -/

/-- Number of shifts and their length, `L = sglReps ℓ · ℓ`. -/
def sgL (ℓ : ℕ) : ℕ := sglReps ℓ * ℓ

/-- Bit `b` of block `j` of the shifted string `tᵢ ⊕ y`, where `tᵢ` is the `i`-th length-`L`
piece of `u`. -/
def lbit (ℓ : ℕ) (u y : List Bool) (i j b : ℕ) : Bool :=
  xor (u.getD (i * sgL ℓ + (j * ℓ + b)) false) (y.getD (j * ℓ + b) false)

/-- Block `j` (an `ℓ`-bit random string) of `tᵢ ⊕ y`. -/
def lblock (ℓ : ℕ) (u y : List Bool) (i j : ℕ) : List Bool :=
  List.ofFn fun b : Fin ℓ => lbit ℓ u y i j b

/-- Majority over the `sglReps ℓ` blocks of `tᵢ ⊕ y`. -/
def lmaj (R : List Bool → Prop) (ℓ : ℕ) (u y : List Bool) (i : ℕ) : Prop :=
  sglReps ℓ < 2 * (Finset.univ.filter fun j : Fin (sglReps ℓ) => R (lblock ℓ u y i j)).card

/-- **The inner predicate** of the `Σ₂` form of `BPP`. -/
def lautSpec (R : List Bool → Prop) (ℓ : ℕ) (u y : List Bool) : Prop :=
  if ℓ = 0 then R [] else
    u.length = sgL ℓ * sgL ℓ ∧ (y.length = sgL ℓ → ∃ i < sgL ℓ, lmaj R ℓ u y i)

section Key

variable (R : List Bool → Prop) (ℓ : ℕ)

/-- The single-copy "circuit" (as a function on `Fin (0 + ℓ)`). -/
def cR (z : Fin (0 + ℓ) → Bool) : Bool := decide (R (List.ofFn fun b : Fin ℓ => z (Fin.natAdd 0 b)))

theorem cR_append (r : Fin ℓ → Bool) :
    cR R ℓ (Fin.append (Fin.elim0 : Fin 0 → Bool) r) = decide (R (List.ofFn r)) := by
  simp only [cR, Fin.append_right]

/-- The amplified predicate on `L = sglReps ℓ · ℓ` random bits. -/
def ampP (r : Seed (sgL ℓ)) : Prop :=
  vote (cR R ℓ) (Fin.elim0 : Fin 0 → Bool) (unflat (k := sglReps ℓ) (ℓ := ℓ) r) = true

theorem lt_sgL {j b : ℕ} (hj : j < sglReps ℓ) (hb : b < ℓ) : j * ℓ + b < sgL ℓ := by
  unfold sgL
  calc j * ℓ + b < j * ℓ + ℓ := by omega
    _ = (j + 1) * ℓ := by ring
    _ ≤ sglReps ℓ * ℓ := Nat.mul_le_mul_right _ hj

/-- The list predicate agrees with the amplified predicate on `tᵢ ⊕ y`. -/
theorem lmaj_iff (t : Seed (sgL ℓ)) (y0 : Seed (sgL ℓ)) (u y : List Bool) (i : ℕ)
    (hu : ∀ c : Fin (sgL ℓ), u.getD (i * sgL ℓ + c) false = t c)
    (hy : ∀ c : Fin (sgL ℓ), y.getD c false = y0 c) :
    lmaj R ℓ u y i ↔ ampP R ℓ (vxor t y0) := by
  unfold lmaj ampP vote maj
  rw [decide_eq_true_iff]
  have : ∀ j : Fin (sglReps ℓ), (R (lblock ℓ u y i j) ↔
      cR R ℓ (Fin.append (Fin.elim0 : Fin 0 → Bool) (unflat (vxor t y0) j)) = true) := by
    intro j
    rw [cR_append, decide_eq_true_iff]
    have hl : lblock ℓ u y i j = List.ofFn (unflat (vxor t y0) j) := by
      unfold lblock
      congr 1
      funext b
      have hc := lt_sgL ℓ j.2 b.2
      have e : (finProdFinEquiv (j, b) : Fin (sglReps ℓ * ℓ)) = ⟨j * ℓ + b, hc⟩ := by
        ext; simp [finProdFinEquiv_apply_val]; ring
      simp only [lbit, unflat, vxor]
      rw [show (finProdFinEquiv (j, b) : Fin (sglReps ℓ * ℓ)) = (⟨j * ℓ + b, hc⟩ : Fin (sgL ℓ))
        from e]
      rw [← hu ⟨j * ℓ + b, hc⟩, ← hy ⟨j * ℓ + b, hc⟩]
    rw [hl]
  rw [Finset.filter_congr (fun j _ => this j)]
  exact Iff.rfl

end Key

/-- **Lautemann on lists.** If `R` (on `ℓ`-bit strings) agrees with `b` with error `≤ 1/3`,
then `b ↔ ∃ u, |u| ≤ L² ∧ ∀ y, |y| ≤ Q → lautSpec R ℓ u y` for every `Q ≥ L`. -/
theorem lautemann_list (R : List Bool → Prop) (b : Prop) (ℓ Q : ℕ) (hQ : sgL ℓ ≤ Q)
    (herr : prob (fun r : Fin ℓ → Bool => ¬ (R (List.ofFn r) ↔ b)) ≤ 1 / 3) :
    b ↔ ∃ u : List Bool, u.length ≤ sgL ℓ * sgL ℓ ∧
      ∀ y : List Bool, y.length ≤ Q → lautSpec R ℓ u y := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
  · subst hℓ
    have hR : R [] ↔ b := by
      obtain ⟨r, hr⟩ := exists_not_of_prob_lt_one (lt_of_le_of_lt herr (by norm_num))
      simpa using hr
    simp only [lautSpec, if_true]
    constructor
    · intro hb; exact ⟨[], by simp, fun _ _ => hR.2 hb⟩
    · rintro ⟨_, _, h⟩; exact hR.1 (h [] (by simp))
  have hne : ℓ ≠ 0 := by omega
  simp only [lautSpec, if_neg hne]
  set L := sgL ℓ with hL
  -- amplification
  set ε : ℝ := ((8 : ℝ) / 9) ^ (12 * (24 * ℓ + 1)) with hε
  have hamp : prob (fun r : Seed L => ¬ (ampP R ℓ r ↔ b)) ≤ ε := by
    have herr' : prob (fun r : Fin ℓ → Bool =>
        cR R ℓ (Fin.append (Fin.elim0 : Fin 0 → Bool) r) ≠ (fun _ : Fin 0 → Bool => decide b) Fin.elim0) ≤ 1 / 3 := by
      refine le_trans (le_of_eq ?_) herr
      congr 1; funext r
      rw [cR_append]
      simp only [ne_eq, decide_eq_decide]
    have := prob_vote_wrong_le (cR R ℓ) (fun _ => decide b) Fin.elim0 herr' (12 * (24 * ℓ + 1))
    have e := prob_equiv (unflatEquiv (sglReps ℓ) ℓ)
      (fun R' => vote (cR R ℓ) (Fin.elim0 : Fin 0 → Bool) R' ≠ decide b)
    refine le_trans (le_of_eq ?_) (e.trans_le this)
    congr 1; funext r
    simp only [ampP, ne_eq, unflatEquiv, Equiv.coe_fn_mk]
    cases h : vote (cR R ℓ) Fin.elim0 (unflat r) <;> by_cases hb : b <;> simp [hb]
  obtain ⟨h1, h2⟩ := sgl_params ℓ hℓ
  constructor
  · intro hb
    have hS : prob (fun r : Seed L => ¬ ampP R ℓ r) ≤ ε :=
      le_trans (le_of_eq (by congr 1; funext r; simp [hb])) hamp
    obtain ⟨t, ht⟩ := exists_cover (k := L) (ampP R ℓ) hS h2
    let u : List Bool := List.ofFn fun p : Fin (L * L) =>
      t ⟨p / L, Nat.div_lt_of_lt_mul p.2⟩ ⟨p % L, Nat.mod_lt _ (by
        have h := p.2; exact Nat.pos_of_ne_zero (fun h0 => by simp [h0] at h))⟩
    refine ⟨u, by simp [u], fun y _ => ⟨by simp [u], fun hy => ?_⟩⟩
    obtain ⟨i, hi⟩ := ht (fun c => y.getD c false)
    refine ⟨i, i.2, (lmaj_iff R ℓ (t i) _ u y i (fun c => ?_) (fun c => rfl)).2 ?_⟩
    · have hlt : (i : ℕ) * L + c < L * L := by
        calc (i : ℕ) * L + c < i * L + L := by omega
          _ = (i + 1) * L := by ring
          _ ≤ L * L := Nat.mul_le_mul_right _ i.2
      have hpos : 0 < L := lt_of_le_of_lt (Nat.zero_le _) c.2
      simp only [u, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      rw [dif_pos (show (i : ℕ) * sgL ℓ + c < L * L from hlt), Option.getD_some]
      have hc : (c : ℕ) < L := c.2
      have key : ∀ M a d : ℕ, d < M → (a * M + d) / M = a ∧ (a * M + d) % M = d := by
        intro M a d hd
        have hM : 0 < M := by omega
        refine ⟨?_, ?_⟩
        · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hd, zero_add]
        · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
      have e1 : ((i : ℕ) * sgL ℓ + c) / L = i := (key (sgL ℓ) i c c.2).1
      have e2 : ((i : ℕ) * sgL ℓ + c) % L = c := (key (sgL ℓ) i c c.2).2
      congr 1 <;> apply Fin.ext <;> simp only [e1, e2]
    · simpa [vxor_comm] using hi
  · rintro ⟨u, -, hu⟩
    by_contra hb
    have hS : prob (fun r : Seed L => ampP R ℓ r) ≤ ε :=
      le_trans (le_of_eq (by congr 1; funext r; simp [hb])) hamp
    let t : Fin L → Seed L := fun i c => u.getD (i * L + c) false
    obtain ⟨y0, hy0⟩ := no_cover (ampP R ℓ) hS h1 t
    obtain ⟨-, hu2⟩ := hu (List.ofFn y0) (by simpa using hQ)
    obtain ⟨i, hi, hmaj⟩ := hu2 (by simp [hL])
    have := (lmaj_iff R ℓ (t ⟨i, hi⟩) y0 u (List.ofFn y0) i (fun c => rfl)
      (fun c => by simp [List.getD_eq_getElem?_getD])).1 hmaj
    exact hy0 ⟨i, hi⟩ (by simpa [vxor_comm] using this)

end

end Pnp.Derand
