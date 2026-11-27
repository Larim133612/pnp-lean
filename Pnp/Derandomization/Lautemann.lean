import Pnp.Derandomization.Adleman

/-!
# The Sipser–Gács–Lautemann theorem, circuit form (M22)

Lautemann's proof of `BPP ⊆ Σ₂ ∩ Π₂`. Let `C(x, r)` be a randomized circuit for `f` with
`ℓ` random bits and error probability `≤ ε`, and write `S_x = {r : C(x, r) = 1}`.

* If `f x = 1`, `S_x` is huge, and `k` random shifts `t₁, …, t_k` cover the whole cube:
  `⋃ᵢ (S_x ⊕ tᵢ) = {0,1}^ℓ` (`exists_cover`, needs `2^ℓ ε^k < 1`).
* If `f x = 0`, `S_x` is tiny, and no `k` shifts can cover the cube (`no_cover`, needs
  `k ε < 1`).

Hence `f x = 1 ↔ ∃ t ∀ y ∃ i, C(x, y ⊕ tᵢ) = 1` (`lautemann_iff`): a `∃∀` (Σ₂) formula whose
inner predicate is a small circuit (`sipser_gacs_lautemann`), and likewise for `¬ f`
(`sipser_gacs_lautemann_compl`, the Π₂ side). `sipser_gacs_lautemann_third` starts from the
usual error `1/3`, amplifying by majority vote first.
-/

namespace Pnp.Derand

open Pnp.Circuits Pnp.NaturalProofs Classical

noncomputable section

/-! ## Probability lemmas -/

theorem exists_not_of_prob_lt_one {α : Type} [Fintype α] [Nonempty α] {P : α → Prop}
    (h : prob P < 1) : ∃ a, ¬ P a := by
  by_contra hne
  push Not at hne
  have : prob P = 1 := by
    have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    simp only [prob, Finset.filter_true_of_mem fun a _ => hne a, Finset.card_univ]
    field_simp
  linarith

theorem ind_forall_eq_prod {α : Type} {k : ℕ} (P : α → Prop) (R : Fin k → α) :
    ind (fun R : Fin k → α => ∀ i, P (R i)) R = ∏ i, ind P (R i) := by
  unfold ind
  by_cases h : ∀ i, P (R i)
  · rw [if_pos h]; exact (Finset.prod_eq_one fun i _ => if_pos (h i)).symm
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

/-- Independent copies: `Pr[∀ i, P(Rᵢ)] = Pr[P]^k`. -/
theorem prob_forall_pi {α : Type} [Fintype α] (k : ℕ) (P : α → Prop) :
    prob (fun R : Fin k → α => ∀ i, P (R i)) = prob P ^ k := by
  rw [prob_eq_ex, prob_eq_ex, ← ex_pi_prod]
  congr 1; funext R; exact ind_forall_eq_prod P R

theorem vxor_comm {ℓ : ℕ} (a b : Seed ℓ) : vxor a b = vxor b a := by
  funext i; simp [vxor, Bool.xor_comm]

/-- Translation invariance of the uniform probability on `{0,1}^ℓ`. -/
theorem prob_vxor {ℓ : ℕ} (c : Seed ℓ) (P : Seed ℓ → Prop) :
    prob (fun u => P (vxor u c)) = prob P := by
  rw [prob_eq_ex, prob_eq_ex]
  exact ex_vxor c (ind P)

/-! ## Lautemann's covering lemmas -/

/-- **Covering.** If `S` misses at most an `ε` fraction of `{0,1}^ℓ` and `2^ℓ ε^k < 1`, some
`k` shifts of `S` cover the cube. -/
theorem exists_cover {ℓ k : ℕ} (S : Seed ℓ → Prop) {ε : ℝ}
    (hS : prob (fun r => ¬ S r) ≤ ε) (hk : 2 ^ ℓ * ε ^ k < 1) :
    ∃ t : Fin k → Seed ℓ, ∀ y, ∃ i, S (vxor (t i) y) := by
  have hbad : prob (fun t : Fin k → Seed ℓ => ∃ y, ∀ i, ¬ S (vxor (t i) y)) < 1 := by
    rw [prob_eq_ex]
    refine lt_of_le_of_lt (ex_ind_exists_le
      (fun (y : Seed ℓ) (t : Fin k → Seed ℓ) => ∀ i, ¬ S (vxor (t i) y))) ?_
    have hy : ∀ y : Seed ℓ,
        ex (ind (fun t : Fin k → Seed ℓ => ∀ i, ¬ S (vxor (t i) y))) ≤ ε ^ k := by
      intro y
      rw [← prob_eq_ex, prob_forall_pi k (fun r => ¬ S (vxor r y)),
        prob_vxor y (fun r => ¬ S r)]
      exact pow_le_pow_left₀ (prob_nonneg _) hS k
    calc _ ≤ ∑ _y : Seed ℓ, ε ^ k := Finset.sum_le_sum fun y _ => hy y
      _ = 2 ^ ℓ * ε ^ k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
      _ < 1 := hk
  obtain ⟨t, ht⟩ := exists_not_of_prob_lt_one hbad
  push Not at ht
  exact ⟨t, ht⟩

/-- **No covering.** If `S` is at most an `ε` fraction of `{0,1}^ℓ` and `k ε < 1`, no `k`
shifts of `S` cover the cube. -/
theorem no_cover {ℓ k : ℕ} (S : Seed ℓ → Prop) {ε : ℝ}
    (hS : prob S ≤ ε) (hk : k * ε < 1) (t : Fin k → Seed ℓ) :
    ∃ y, ∀ i, ¬ S (vxor (t i) y) := by
  have hbad : prob (fun y : Seed ℓ => ∃ i, S (vxor (t i) y)) < 1 := by
    rw [prob_eq_ex]
    refine lt_of_le_of_lt (ex_ind_exists_le
      (fun (i : Fin k) (y : Seed ℓ) => S (vxor (t i) y))) ?_
    have hi : ∀ i : Fin k, ex (ind (fun y : Seed ℓ => S (vxor (t i) y))) ≤ ε := by
      intro i
      rw [← prob_eq_ex]
      have := prob_vxor (t i) S
      simp only [vxor_comm _ (t i)] at this
      rw [this]; exact hS
    calc _ ≤ ∑ _i : Fin k, ε := Finset.sum_le_sum fun i _ => hi i
      _ = k * ε := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ < 1 := hk
  obtain ⟨y, hy⟩ := exists_not_of_prob_lt_one hbad
  push Not at hy
  exact ⟨y, hy⟩

/-- **Lautemann.** For a randomized circuit with error `≤ ε`, `k ε < 1` and `2^ℓ ε^k < 1`:
`f x = 1 ↔ ∃ t ∀ y ∃ i, C(x, tᵢ ⊕ y) = 1`. -/
theorem lautemann_iff {n ℓ k : ℕ} (C : (Fin (n + ℓ) → Bool) → Bool) (f : (Fin n → Bool) → Bool)
    {ε : ℝ} (herr : ∀ x, prob (fun r : Seed ℓ => C (Fin.append x r) ≠ f x) ≤ ε)
    (h1 : k * ε < 1) (h2 : 2 ^ ℓ * ε ^ k < 1) (x : Fin n → Bool) :
    f x = true ↔ ∃ t : Fin k → Seed ℓ, ∀ y, ∃ i, C (Fin.append x (vxor (t i) y)) = true := by
  constructor
  · intro hx
    refine exists_cover (fun r => C (Fin.append x r) = true) ?_ h2
    exact (prob_mono fun r hr => by rw [hx]; exact hr).trans (herr x)
  · intro ⟨t, ht⟩
    by_contra hx
    rw [Bool.not_eq_true] at hx
    obtain ⟨y, hy⟩ := no_cover (fun r => C (Fin.append x r) = true)
      ((prob_mono fun r (hr : C (Fin.append x r) = true) => by rw [hx, hr]; simp).trans
        (herr x)) h1 t
    obtain ⟨i, hi⟩ := ht y
    exact hy i hi

/-! ## The Σ₂ predicate as a circuit -/

theorem hasCircuitOfSize_gate2 (op : Bool → Bool → Bool) :
    HasCircuitOfSize (fun v : Fin 2 → Bool => op (v 0) (v 1)) 1 := by
  refine ⟨1, le_rfl, (fun _ => (op, ⟨0, by omega⟩, ⟨1, by omega⟩), Fin.last 2), ?_⟩
  funext v
  simp only [Circuit.eval, wires_eq_wv, Fin.val_last]
  exact (wv_gate v 1 _ 0).trans (by
    rw [wv_input v 1 _ (show 0 < 2 by omega), wv_input v 1 _ (show 1 < 2 by omega)]; rfl)

/-- OR of `k + 1` bits with `k` gates. -/
theorem hasCircuitOfSize_any :
    ∀ k : ℕ, HasCircuitOfSize (fun w : Fin (k + 1) → Bool => decide (∃ i, w i = true)) k
  | 0 => by
    convert hasCircuitOfSize_var (n := 1) 0 using 2 with w
    cases h : w 0 <;> simp [Fin.exists_fin_one, h]
  | k + 1 => by
    have ht := (hasMCircuitOfSize_rewire (n := k + 2) (m := k + 1) Fin.succ).comp_single
      (hasCircuitOfSize_any k)
    have h2 := ((hasCircuitOfSize_var (n := k + 2) 0).cons (ht.toM 1)).comp_single
      (hasCircuitOfSize_gate2 (· || ·))
    have h3 := h2.mono (s' := k + 1) (by omega)
    convert h3 using 2 with w
    simp only [Function.comp, Fin.cons_zero]
    show _ = (w 0 || decide (∃ i : Fin (k + 1), w i.succ = true))
    simp only [Fin.exists_fin_succ, Bool.decide_or]
    cases w 0 <;> simp

/-- The `i`-th shift `tᵢ`, read off a flat string `u` of length `k ℓ`. -/
def unflat {k ℓ : ℕ} (u : Fin (k * ℓ) → Bool) (i : Fin k) : Seed ℓ :=
  fun j => u (finProdFinEquiv (i, j))

section Pred

variable {n ℓ k : ℕ}

/-- Parts of an input `z = x ++ u ++ y`. -/
def xPart (z : Fin (n + (k * ℓ + ℓ)) → Bool) : Fin n → Bool := fun a => z (Fin.castAdd _ a)
def uPart (z : Fin (n + (k * ℓ + ℓ)) → Bool) : Fin (k * ℓ) → Bool :=
  fun a => z (Fin.natAdd n (Fin.castAdd ℓ a))
def yPart (z : Fin (n + (k * ℓ + ℓ)) → Bool) : Seed ℓ :=
  fun a => z (Fin.natAdd n (Fin.natAdd (k * ℓ) a))

theorem xPart_append (x : Fin n → Bool) (u : Fin (k * ℓ) → Bool) (y : Seed ℓ) :
    xPart (Fin.append x (Fin.append u y)) = x := by
  funext a; unfold xPart; rw [Fin.append_left]
theorem uPart_append (x : Fin n → Bool) (u : Fin (k * ℓ) → Bool) (y : Seed ℓ) :
    uPart (Fin.append x (Fin.append u y)) = u := by
  funext a; unfold uPart; rw [Fin.append_right, Fin.append_left]
theorem yPart_append (x : Fin n → Bool) (u : Fin (k * ℓ) → Bool) (y : Seed ℓ) :
    yPart (Fin.append x (Fin.append u y)) = y := by
  funext a; unfold yPart; rw [Fin.append_right, Fin.append_right]

/-- The input of the `i`-th copy of `C`: `x ++ (tᵢ ⊕ y)`. -/
def blk (z : Fin (n + (k * ℓ + ℓ)) → Bool) (i : Fin k) : Fin (n + ℓ) → Bool :=
  Fin.append (xPart z) (vxor (unflat (uPart z) i) (yPart z))

/-- **Lautemann's inner predicate** `D(x, u, y) = ⋁ᵢ C(x, tᵢ ⊕ y)`. -/
def lautPred (C : (Fin (n + ℓ) → Bool) → Bool) (k : ℕ) (z : Fin (n + (k * ℓ + ℓ)) → Bool) :
    Bool :=
  decide (∃ i : Fin k, C (blk z i) = true)

theorem lautPred_append (C : (Fin (n + ℓ) → Bool) → Bool) (x : Fin n → Bool)
    (u : Fin (k * ℓ) → Bool) (y : Seed ℓ) :
    lautPred C k (Fin.append x (Fin.append u y)) =
      decide (∃ i, C (Fin.append x (vxor (unflat u i) y)) = true) := by
  simp only [lautPred, blk, xPart_append, uPart_append, yPart_append]

/-- `D` has a circuit with `k ((n + ℓ) · 16 + s + 1)` gates: an XOR layer, `k` copies of
`C` and an OR. -/
theorem hasCircuitOfSize_lautPred (hn : 0 < n) (hk : 0 < k) {C : (Fin (n + ℓ) → Bool) → Bool}
    {s : ℕ} (hC : HasCircuitOfSize C s) :
    HasCircuitOfSize (lautPred C k) (k * ((n + ℓ) * juntaSize 2 + s + 1)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  let e := (finProdFinEquiv : Fin (k' + 1) × Fin (n + ℓ) ≃ _)
  let F1 : (Fin (n + ((k' + 1) * ℓ + ℓ)) → Bool) → (Fin ((k' + 1) * (n + ℓ)) → Bool) :=
    fun z p => blk z (e.symm p).1 (e.symm p).2
  let F2 : (Fin ((k' + 1) * (n + ℓ)) → Bool) → (Fin (k' + 1) → Bool) :=
    fun w i => C (fun j => w (e (i, j)))
  have h1 : HasMCircuitOfSize F1 ((k' + 1) * (n + ℓ) * juntaSize 2) := by
    refine hasMCircuitOfSize_local' (by omega) F1 fun p => ?_
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective p
    refine Fin.addCases (fun a => ?_) (fun b => ?_) j
    · refine ⟨fun _ => Fin.castAdd _ a, fun w => w 0, fun z => ?_⟩
      simp [F1, blk, xPart]
    · refine ⟨![Fin.natAdd n (Fin.castAdd ℓ (finProdFinEquiv (i, b))),
        Fin.natAdd n (Fin.natAdd ((k' + 1) * ℓ) b)], fun w => xor (w 0) (w 1), fun z => ?_⟩
      simp [F1, blk, uPart, yPart, unflat, vxor]
  have h2 : HasMCircuitOfSize F2 ((k' + 1) * (0 + s)) :=
    hasMCircuitOfSize_of_forall F2 fun i =>
      (hasMCircuitOfSize_rewire (fun j => e (i, j))).comp_single hC
  have h3 := (h1.comp h2).comp_single (hasCircuitOfSize_any k')
  have hD : lautPred C (k' + 1) = (fun w : Fin (k' + 1) → Bool => decide (∃ i, w i = true)) ∘
      (F2 ∘ F1) := by
    funext z
    simp only [lautPred, Function.comp, F1, F2, Equiv.symm_apply_apply]
  rw [hD]
  exact h3.mono (by nlinarith)

end Pred

/-! ## The theorem -/

/-- Flattening `k` shifts into one string of length `k ℓ`. -/
def flat {k ℓ : ℕ} (t : Fin k → Seed ℓ) : Fin (k * ℓ) → Bool :=
  fun p => t (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2

theorem unflat_flat {k ℓ : ℕ} (t : Fin k → Seed ℓ) : unflat (flat t) = t := by
  funext i j; simp [unflat, flat]

/-- **Sipser–Gács–Lautemann (circuit form, Σ₂ side).** Let `C` (`s` gates) compute `f` with
`ℓ` random bits and error `≤ ε` on every input, where `k ε < 1` and `2^ℓ ε^k < 1`. Then there
is a circuit `D` with `k ((n + ℓ) · 16 + s + 1)` gates such that
`f x = 1 ↔ ∃ u ∈ {0,1}^{kℓ}, ∀ y ∈ {0,1}^ℓ, D(x, u, y) = 1`. -/
theorem sipser_gacs_lautemann {n ℓ k s : ℕ} (hn : 0 < n) (hk : 0 < k)
    {C : (Fin (n + ℓ) → Bool) → Bool} (hC : HasCircuitOfSize C s) (f : (Fin n → Bool) → Bool)
    {ε : ℝ} (herr : ∀ x, prob (fun r : Seed ℓ => C (Fin.append x r) ≠ f x) ≤ ε)
    (h1 : k * ε < 1) (h2 : 2 ^ ℓ * ε ^ k < 1) :
    ∃ D : (Fin (n + (k * ℓ + ℓ)) → Bool) → Bool,
      HasCircuitOfSize D (k * ((n + ℓ) * juntaSize 2 + s + 1)) ∧
      ∀ x, f x = true ↔
        ∃ u : Fin (k * ℓ) → Bool, ∀ y : Seed ℓ, D (Fin.append x (Fin.append u y)) = true := by
  refine ⟨lautPred C k, hasCircuitOfSize_lautPred hn hk hC, fun x => ?_⟩
  rw [lautemann_iff C f herr h1 h2 x]
  simp only [lautPred_append, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨flat t, by rw [unflat_flat]; exact ht⟩
  · rintro ⟨u, hu⟩; exact ⟨unflat u, hu⟩

/-- **Sipser–Gács–Lautemann (Π₂ side).** The same hypotheses give a `∃∀` circuit formula for
`f x = 0`, i.e. a `∀∃` formula for `f x = 1`. -/
theorem sipser_gacs_lautemann_compl {n ℓ k s : ℕ} (hn : 0 < n) (hk : 0 < k)
    {C : (Fin (n + ℓ) → Bool) → Bool} (hC : HasCircuitOfSize C s) (f : (Fin n → Bool) → Bool)
    {ε : ℝ} (herr : ∀ x, prob (fun r : Seed ℓ => C (Fin.append x r) ≠ f x) ≤ ε)
    (h1 : k * ε < 1) (h2 : 2 ^ ℓ * ε ^ k < 1) :
    ∃ D : (Fin (n + (k * ℓ + ℓ)) → Bool) → Bool,
      HasCircuitOfSize D (k * ((n + ℓ) * juntaSize 2 + (s + 1) + 1)) ∧
      ∀ x, f x = false ↔
        ∃ u : Fin (k * ℓ) → Bool, ∀ y : Seed ℓ, D (Fin.append x (Fin.append u y)) = true := by
  have hC' : HasCircuitOfSize (fun z => !C z) (s + 1) := by
    have := (hC.toM 1).comp_single (hasCircuitOfSize_xor_const true)
    convert this using 2 with z
    simp
  obtain ⟨D, hD, hDf⟩ := sipser_gacs_lautemann hn hk hC' (fun x => !f x)
    (fun x => (prob_mono fun r (hr : (!C (Fin.append x r)) ≠ !f x) => by
      intro h; exact hr (by rw [h])).trans (herr x)) h1 h2
  refine ⟨D, hD, fun x => ?_⟩
  rw [← hDf x]; simp

/-! ## Starting from error `1/3` -/

theorem flat_unflat {k ℓ : ℕ} (u : Fin (k * ℓ) → Bool) : flat (unflat u) = u := by
  funext p; simp only [unflat, flat, Prod.mk.eta, Equiv.apply_symm_apply]

/-- Strings of length `a ℓ` are `a`-tuples of strings of length `ℓ`. -/
def unflatEquiv (a ℓ : ℕ) : (Fin (a * ℓ) → Bool) ≃ (Fin a → Seed ℓ) where
  toFun := unflat
  invFun := flat
  left_inv := flat_unflat
  right_inv := unflat_flat

section Amplify

variable {n ℓ : ℕ}

/-- The amplified circuit: majority of `a` copies of `C`, with independent random strings
read off the `a ℓ` random input bits. -/
def ampl (C : (Fin (n + ℓ) → Bool) → Bool) (a : ℕ) (z : Fin (n + a * ℓ) → Bool) : Bool :=
  maj (fun i => C (Fin.append (fun b => z (Fin.castAdd _ b)) (unflat (fun c => z (Fin.natAdd n c)) i)))

theorem ampl_append (C : (Fin (n + ℓ) → Bool) → Bool) (a : ℕ) (x : Fin n → Bool)
    (r : Fin (a * ℓ) → Bool) : ampl C a (Fin.append x r) = vote C x (unflat r) := by
  simp only [ampl, vote, Fin.append_left, Fin.append_right]

theorem hasCircuitOfSize_ampl (hn : 0 < n) {a : ℕ} (ha : 0 < a)
    {C : (Fin (n + ℓ) → Bool) → Bool} {s : ℕ} (hC : HasCircuitOfSize C s) :
    HasCircuitOfSize (ampl C a) (a * (n + ℓ) * juntaSize 1 + a * s + majSize a) := by
  let e := (finProdFinEquiv : Fin a × Fin (n + ℓ) ≃ _)
  let F1 : (Fin (n + a * ℓ) → Bool) → (Fin (a * (n + ℓ)) → Bool) := fun z p =>
    Fin.append (fun b => z (Fin.castAdd _ b)) (unflat (fun c => z (Fin.natAdd n c)) (e.symm p).1)
      (e.symm p).2
  let F2 : (Fin (a * (n + ℓ)) → Bool) → (Fin a → Bool) := fun w i => C (fun j => w (e (i, j)))
  have h1 : HasMCircuitOfSize F1 (a * (n + ℓ) * juntaSize 1) := by
    refine hasMCircuitOfSize_local' (by omega) F1 fun p => ?_
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective p
    refine Fin.addCases (fun b => ?_) (fun c => ?_) j
    · exact ⟨fun _ => Fin.castAdd _ b, fun w => w 0, fun z => by simp [F1]⟩
    · exact ⟨fun _ => Fin.natAdd n (finProdFinEquiv (i, c)), fun w => w 0,
        fun z => by simp [F1, unflat]⟩
  have h2 : HasMCircuitOfSize F2 (a * (0 + s)) :=
    hasMCircuitOfSize_of_forall F2 fun i =>
      (hasMCircuitOfSize_rewire (fun j => e (i, j))).comp_single hC
  have h3 := (h1.comp h2).comp_single (hasCircuitOfSize_maj ha)
  have hD : ampl C a = maj ∘ (F2 ∘ F1) := by
    funext z
    simp only [ampl, Function.comp, F1, F2, Equiv.symm_apply_apply]
  rw [hD]
  exact h3.mono (by rw [Nat.zero_add])

end Amplify

/-- Number of copies used for amplification: `2 j` with `j = 12 (24 ℓ + 1)`. -/
def sglReps (ℓ : ℕ) : ℕ := 2 * (12 * (24 * ℓ + 1))

/-- Size of the amplified circuit. -/
def amplSize (n ℓ s : ℕ) : ℕ :=
  sglReps ℓ * (n + ℓ) * juntaSize 1 + sglReps ℓ * s + majSize (sglReps ℓ)

theorem sgl_params (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ((sglReps ℓ * ℓ : ℕ) : ℝ) * ((8 : ℝ) / 9) ^ (12 * (24 * ℓ + 1)) < 1 ∧
    (2 : ℝ) ^ (sglReps ℓ * ℓ) * (((8 : ℝ) / 9) ^ (12 * (24 * ℓ + 1))) ^ (sglReps ℓ * ℓ) < 1 := by
  set a := 24 * ℓ + 1
  have hq : ((8 : ℝ) / 9) ^ (12 * a) ≤ (1 / 4) ^ a := by
    rw [show 12 * a = 6 * (2 * a) by ring, pow_mul]
    calc _ ≤ ((1 : ℝ) / 2) ^ (2 * a) := pow_le_pow_left₀ (by norm_num) eight_ninths_pow_six _
      _ = _ := by rw [pow_mul]; norm_num
  have hq0 : (0 : ℝ) ≤ ((8 : ℝ) / 9) ^ (12 * a) := by positivity
  have h4 : (0 : ℝ) < 4 ^ a := by positivity
  constructor
  · have hN : sglReps ℓ * ℓ < 4 ^ a := by
      have h1 : a < 2 ^ a := Nat.lt_two_pow_self
      have h2 : 24 * ℓ < 2 ^ a := by omega
      have : 24 * ℓ * a < 2 ^ a * 2 ^ a := Nat.mul_lt_mul'' h2 h1
      rw [show (4 : ℕ) ^ a = 2 ^ a * 2 ^ a by rw [← mul_pow]; norm_num]
      simp only [sglReps]; nlinarith
    have hN' : ((sglReps ℓ * ℓ : ℕ) : ℝ) < 4 ^ a := by exact_mod_cast hN
    calc _ ≤ ((sglReps ℓ * ℓ : ℕ) : ℝ) * (1 / 4) ^ a :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = ((sglReps ℓ * ℓ : ℕ) : ℝ) / 4 ^ a := by rw [one_div_pow, mul_one_div]
      _ < 1 := by rw [div_lt_one h4]; exact hN'
  · rw [← mul_pow]
    have ha1 : (1 : ℝ) / 4 ^ a ≤ 1 / 4 := by
      rw [one_div_le_one_div h4 (by norm_num)]
      exact le_self_pow₀ (by norm_num) (by omega)
    have : 2 * ((8 : ℝ) / 9) ^ (12 * a) < 1 := by
      calc _ ≤ 2 * ((1 : ℝ) / 4) ^ a := by linarith
        _ = 2 * (1 / 4 ^ a) := by rw [one_div_pow]
        _ < 1 := by linarith
    refine pow_lt_one₀ (by positivity) this ?_
    have : 0 < sglReps ℓ := by simp [sglReps]
    positivity

/-- **Sipser–Gács–Lautemann from error `1/3`** (circuit form of `BPP ⊆ Σ₂`). If `C` (`s`
gates, `ℓ > 0` random bits) computes `f` with error `≤ 1/3` on every input, then with
`L = sglReps ℓ · ℓ` there is a circuit `D` of size `L ((n + L) · 16 + amplSize n ℓ s + 1)`
such that `f x = 1 ↔ ∃ u ∈ {0,1}^{L²} ∀ y ∈ {0,1}^L, D(x, u, y) = 1`. -/
theorem sipser_gacs_lautemann_third {n ℓ s : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ)
    {C : (Fin (n + ℓ) → Bool) → Bool} (hC : HasCircuitOfSize C s) (f : (Fin n → Bool) → Bool)
    (herr : ∀ x, prob (fun r : Seed ℓ => C (Fin.append x r) ≠ f x) ≤ 1 / 3) :
    ∃ D : (Fin (n + ((sglReps ℓ * ℓ) * (sglReps ℓ * ℓ) + sglReps ℓ * ℓ)) → Bool) → Bool,
      HasCircuitOfSize D
        (sglReps ℓ * ℓ * ((n + sglReps ℓ * ℓ) * juntaSize 2 + amplSize n ℓ s + 1)) ∧
      ∀ x, f x = true ↔ ∃ u : Fin ((sglReps ℓ * ℓ) * (sglReps ℓ * ℓ)) → Bool,
        ∀ y : Seed (sglReps ℓ * ℓ), D (Fin.append x (Fin.append u y)) = true := by
  have hr : 0 < sglReps ℓ := by simp [sglReps]
  have hA := hasCircuitOfSize_ampl hn hr hC
  have hAerr : ∀ x, prob (fun r : Seed (sglReps ℓ * ℓ) => ampl C (sglReps ℓ) (Fin.append x r) ≠ f x)
      ≤ ((8 : ℝ) / 9) ^ (12 * (24 * ℓ + 1)) := by
    intro x
    simp only [ampl_append]
    have := prob_equiv (unflatEquiv (sglReps ℓ) ℓ) (fun R => vote C x R ≠ f x)
    rw [show (fun r => vote C x (unflat r) ≠ f x) =
      (fun r => vote C x (unflatEquiv (sglReps ℓ) ℓ r) ≠ f x) from rfl, this]
    exact prob_vote_wrong_le C f x (herr x) _
  obtain ⟨h1, h2⟩ := sgl_params ℓ hℓ
  exact sipser_gacs_lautemann hn (Nat.mul_pos hr hℓ) hA f hAerr h1 h2

end

end Pnp.Derand
