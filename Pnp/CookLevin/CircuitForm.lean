import Pnp.CookLevin.Tseitin
import Pnp.PPoly.Simulate
import Pnp.Derandomization.Lautemann
import Pnp.TM2.Projection

/-!
# Cook–Levin, non-uniform form (M29)

For every language `L` in the official class `NP` (`Millennium.InNondeterministicPolynomialTime`,
input alphabet `α`) and every input length `n ≥ 1` we build

* `np_circuit_form`: a circuit `f_n` of polynomial size on the one-hot input bits of `w` and
  polynomially many extra “certificate” bits `z` such that `L w ↔ ∃ z, f_n(w, z) = true`
  (the verifier is simulated by circuits with `Pnp.PPoly.simulateOn`, once for every certificate
  length `m ≤ n^k`, and the results are OR-ed);
* `cook_levin_nonuniform`: a single clause list `φ_n` on `V_n` variables (Tseitin’s formula of
  `f_n`) with `L w ↔ SATLang (encodeCNF V_n (φ_n ++ inputUnits (oneHot n w)))` for every `w` of
  length `n`, all sizes bounded by one polynomial.  The input `w` enters only through the unit
  clauses `inputUnits (oneHot n w)` fixing the input variables.

This is the classical “NP has polynomial-size CNF families with fixed inputs” form of the
Cook–Levin theorem.  What is still missing for the official statement “SAT is NP-hard” is
uniformity: that `n ↦ φ_n` (equivalently the map `w ↦` formula) is computable by a polynomial-time
Turing machine.  Nothing here proves or refutes `P ≠ NP`.
-/

namespace Pnp.CookLevin

open Pnp.Circuits Pnp.PPoly Classical

noncomputable section

/-! ## Tseitin formulas with fixed inputs -/

/-- The unit clause `x_j = v`. -/
def unitLit (j : ℕ) (v : Bool) : ℕ → Option Bool := fun i => if i = j then some v else none

theorem unitLit_holds {N : ℕ} {a : ℕ → Bool} {j : ℕ} {v : Bool} (hj : j < N) :
    ClauseHolds N a (unitLit j v) ↔ a j = v := by
  constructor
  · rintro ⟨i, -, hi⟩
    unfold unitLit at hi
    split_ifs at hi with h
    · subst h; simp_all
  · intro h
    exact ⟨j, hj, by simp [unitLit, h]⟩

/-- Unit clauses fixing the first `n'` variables to `b`. -/
def inputUnits {n' : ℕ} (b : Fin n' → Bool) : List (ℕ → Option Bool) :=
  List.ofFn fun j => unitLit j.val (b j)

theorem length_inputUnits {n' : ℕ} (b : Fin n' → Bool) : (inputUnits b).length = n' := by
  simp [inputUnits]

/-- The canonical satisfying assignment of the Tseitin variables: the wire values. -/
def wireAssign {n s : ℕ} (x : Fin n → Bool) (g : Gates n s) : ℕ → Bool :=
  fun j => if h : j < n + s then wires x s g ⟨j, h⟩ else false

theorem wireAssign_fin {n s : ℕ} (x : Fin n → Bool) (g : Gates n s) (k : Fin (n + s)) :
    wireAssign x g k = wires x s g k := by
  simp [wireAssign, k.isLt]

theorem consistent_wireAssign {n s : ℕ} (x : Fin n → Bool) (g : Gates n s) :
    Consistent g (wireAssign x g) := by
  intro i
  have hw := wires_gate x s g i
  have e1 : wireAssign x g (n + i.val) = wires x s g ⟨n + i.val, by omega⟩ := by
    simp [wireAssign, show n + i.val < n + s by omega]
  rw [e1, hw, ← wireAssign_fin, ← wireAssign_fin]
  rfl

/-- **Tseitin with fixed inputs.** Fixing the first `n'` inputs of `C` to `b` by unit clauses,
the formula is satisfiable iff some completion `z` of the inputs makes `C` output `true`. -/
theorem sat_fixed_iff {n' Z s : ℕ} (C : Circuit (n' + Z) s) (b : Fin n' → Bool) :
    SATLang (encodeCNF (n' + Z + s) (tseitinCNF C ++ inputUnits b)) ↔
      ∃ z : Fin Z → Bool, C.eval (Fin.append b z) = true := by
  have hu : ∀ a : ℕ → Bool, (∀ L ∈ inputUnits b, ClauseHolds (n' + Z + s) a L) ↔
      ∀ j : Fin n', a j = b j := by
    intro a
    constructor
    · intro h j
      exact (unitLit_holds (by omega)).1 (h _ (List.mem_ofFn.2 ⟨j, rfl⟩))
    · intro h L hL
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hL
      exact (unitLit_holds (by omega)).2 (h j)
  unfold SATLang
  simp only [evalF_encodeCNF, List.forall_mem_append]
  constructor
  · rintro ⟨a, hc, hb⟩
    rw [tseitinCNF_holds] at hc
    rw [hu] at hb
    refine ⟨fun i => a (n' + i.val), ?_⟩
    have hx : Fin.append b (fun i : Fin Z => a (n' + i.val)) = fun j : Fin (n' + Z) => a j := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left, ← hb i]; rfl
      · rw [Fin.append_right]; rfl
    rw [hx, Circuit.eval, ← hc.2]
    exact (consistent_eq_wires hc.1 C.2 C.2.isLt).symm
  · rintro ⟨z, hz⟩
    refine ⟨wireAssign (Fin.append b z) C.1, ?_, ?_⟩
    · rw [tseitinCNF_holds]
      refine ⟨consistent_wireAssign _ _, ?_⟩
      rw [wireAssign_fin]; exact hz
    · rw [hu]
      intro j
      have := wireAssign_fin (Fin.append b z) C.1 ⟨j.val, by omega⟩
      simp only at this
      rw [this, wires_input _ s C.1 j.val (by omega)]
      exact Fin.append_left b z j

/-! ## Pair strings and certificate decoding -/

section Encoding

variable {α Γ : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype Γ]

/-- The Cook pair string `w#y` over `α ⊕ Option Γ`. -/
def pe2 (w : List α) (y : List Γ) : List (α ⊕ Option Γ) :=
  w.map Sum.inl ++ Sum.inr none :: y.map (fun b => Sum.inr (some b))

omit [DecidableEq α] [Nonempty α] in
theorem pe2_eq_encode (w : List α) (y : List Γ) :
    pe2 w y = (Millennium.pair_encoding (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string Γ)).encode (w, y) := rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] [Fintype Γ] in
theorem length_pe2 (w : List α) (y : List Γ) : (pe2 w y).length = w.length + 1 + y.length := by
  simp [pe2]; omega

omit [Fintype α] [DecidableEq α] [Nonempty α] [Fintype Γ] in
theorem getElem?_pe2 (w : List α) (y : List Γ) (i : ℕ) :
    (pe2 w y)[i]? = if i < w.length then (w[i]?).map Sum.inl
      else if i = w.length then some (Sum.inr none)
      else (y[i - w.length - 1]?).map (fun b => Sum.inr (some b)) := by
  unfold pe2
  rw [List.getElem?_append]
  simp only [List.length_map]
  split_ifs with h₁ h₂
  · simp [List.getElem?_map]
  · subst h₂; simp
  · obtain ⟨t, rfl⟩ : ∃ t, i = w.length + 1 + t := ⟨i - w.length - 1, by omega⟩
    rw [show w.length + 1 + t - w.length = t + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_map]
    simp

omit [Fintype α] [DecidableEq α] [Nonempty α] [Fintype Γ] in
theorem length_decWord' {β : Type} [Fintype β] [Nonempty β] (n : ℕ)
    (x : Fin (n * Fintype.card β) → Bool) : (decWord n x).length = n := by simp [decWord]

variable (Γ) in
/-- The length-`m` certificate read off `N` one-hot letter blocks (`[]` if `Γ` is empty). -/
def cert (N m : ℕ) (z : Fin (N * Fintype.card Γ) → Bool) : List Γ :=
  if h : Nonempty Γ then (haveI := h; (decWord N z).take m) else []

omit [Fintype α] [DecidableEq α] [Nonempty α] in
theorem length_cert {N m : ℕ} (hm : m ≤ N) (hΓ : ¬ Nonempty Γ → N = 0)
    (z : Fin (N * Fintype.card Γ) → Bool) : (cert Γ N m z).length = m := by
  unfold cert
  split_ifs with h
  · simp [length_decWord']; omega
  · have := hΓ h; simp; omega

omit [Fintype α] [DecidableEq α] [Nonempty α] in
theorem exists_cert {N : ℕ} (y : List Γ) (hy : y.length ≤ N) :
    ∃ z : Fin (N * Fintype.card Γ) → Bool, cert Γ N y.length z = y := by
  by_cases h : Nonempty Γ
  · obtain ⟨d⟩ := h
    haveI : Nonempty Γ := ⟨d⟩
    refine ⟨oneHot N (y ++ List.replicate (N - y.length) d), ?_⟩
    unfold cert
    rw [dif_pos ⟨d⟩]
    rw [decWord_oneHot _ (by simp; omega)]
    simp
  · cases y with
    | nil => exact ⟨fun _ => false, by unfold cert; split_ifs; simp⟩
    | cons c _ => exact absurd ⟨c⟩ h

omit [Fintype α] [DecidableEq α] [Nonempty α] in
theorem cert_getElem?_congr {N m : ℕ} {z z' : Fin (N * Fintype.card Γ) → Bool} (t : ℕ)
    (h : ∀ ht : t < N, ∀ c : Fin (Fintype.card Γ),
      z (finProdFinEquiv (⟨t, ht⟩, c)) = z' (finProdFinEquiv (⟨t, ht⟩, c))) :
    (cert Γ N m z)[t]? = (cert Γ N m z')[t]? := by
  unfold cert
  split_ifs with hΓ
  · rw [List.getElem?_take, List.getElem?_take]
    split_ifs
    · exact decWord_getElem?_congr t fun ht a => h ht _
    · rfl
  · rfl

variable (α Γ) in
/-- The re-encoding map: from the one-hot bits of `w` and the certificate bits to the one-hot
encoding of the pair string `w#y` with `y = cert N m z`. -/
def encN (n N m : ℕ) (u : Fin (n * Fintype.card α + N * Fintype.card Γ) → Bool) :
    Fin ((n + 1 + m) * Fintype.card (α ⊕ Option Γ)) → Bool :=
  oneHot (n + 1 + m) (pe2 (decWord n fun i => u (Fin.castAdd _ i))
    (cert Γ N m fun j => u (Fin.natAdd (n * Fintype.card α) j)))

theorem encN_append (n N m : ℕ) (x : Fin (n * Fintype.card α) → Bool)
    (z : Fin (N * Fintype.card Γ) → Bool) :
    encN α Γ n N m (Fin.append x z) = oneHot (n + 1 + m) (pe2 (decWord n x) (cert Γ N m z)) := by
  simp only [encN, Fin.append_left, Fin.append_right]

/-- Every output bit of `encN` reads at most `|α| + |Γ|` input bits. -/
theorem hasMCircuitOfSize_encN {n N m : ℕ} (hN : 0 < n * Fintype.card α + N * Fintype.card Γ) :
    HasMCircuitOfSize (encN α Γ n N m) ((n + 1 + m) * Fintype.card (α ⊕ Option Γ) *
      juntaSize (Fintype.card (Fin (Fintype.card α) ⊕ Fin (Fintype.card Γ)))) := by
  let d0 : Fin (n * Fintype.card α + N * Fintype.card Γ) := ⟨0, hN⟩
  let ι : Fin ((n + 1 + m) * Fintype.card (α ⊕ Option Γ)) →
      Fin (Fintype.card α) ⊕ Fin (Fintype.card Γ) →
      Fin (n * Fintype.card α + N * Fintype.card Γ) := fun j d =>
    let i := (finProdFinEquiv.symm j).1.val
    match d with
    | Sum.inl c => if h : i < n then Fin.castAdd _ (finProdFinEquiv (⟨i, h⟩, c)) else d0
    | Sum.inr c => if h : i - n - 1 < N then
        Fin.natAdd (n * Fintype.card α) (finProdFinEquiv (⟨i - n - 1, h⟩, c)) else d0
  refine hasMCircuitOfSize_dep hN _ ι fun j x y hxy => ?_
  simp only [encN, oneHot]
  congr 2
  set i := (finProdFinEquiv.symm j).1.val with hi
  rw [getElem?_pe2, getElem?_pe2, length_decWord', length_decWord']
  split_ifs with h₁ h₂
  · congr 1
    refine decWord_getElem?_congr i fun hi' a => ?_
    have := hxy (Sum.inl (Fintype.equivFin α a))
    simp only [ι, ← hi, dif_pos hi'] at this
    exact this
  · rfl
  · congr 1
    refine cert_getElem?_congr _ fun ht c => ?_
    have := hxy (Sum.inr c)
    simp only [ι, ← hi, dif_pos ht] at this
    exact this

end Encoding

/-! ## NP languages have polynomial-size circuits with certificate inputs -/

theorem eval_le_of_le (P : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : P.eval a ≤ P.eval b :=
  Pnp.TM2Proj.polynomial_eval_mono P h

/-- **Circuit form of NP** (core, for a given checking relation). -/
theorem np_circuits_of_relation {α Γ : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype Γ] {L : Millennium.Language (List α)} (R : List α → List Γ → Prop) (k : ℕ)
    (hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string Γ) R)
    (hL : ∀ w, L w ↔ ∃ y : List Γ, y.length ≤ w.length ^ k ∧ R w y) :
    ∃ p : Polynomial ℕ, ∀ n, 0 < n → ∃ Z ≤ p.eval n,
      ∃ f : (Fin (n * Fintype.card α + Z) → Bool) → Bool, HasCircuitOfSize f (p.eval n) ∧
        ∀ w : List α, w.length = n →
          (L w ↔ ∃ z : Fin Z → Bool, f (Fin.append (oneHot n w) z) = true) := by
  obtain ⟨V, comp, hV⟩ := hR
  let PE := Millennium.pair_encoding (Millennium.fin_encoding_string α)
    (Millennium.fin_encoding_string Γ)
  let dec : List (α ⊕ Option Γ) → List α × List Γ := fun u => (PE.decode u).getD ([], [])
  have hdec : ∀ w y, dec (pe2 w y) = (w, y) := fun w y => by
    simp only [dec, pe2_eq_encode]
    rw [PE.decode_encode]; rfl
  let S : List (α ⊕ Option Γ) → Prop := fun u => ∃ w y, pe2 w y = u
  obtain ⟨p₁, hp₁⟩ := simulateOn (α := α ⊕ Option Γ) comp.tm comp.inputAlphabet comp.time
    (fun u => comp.outputAlphabet.symm (V (dec u))) (comp.outputAlphabet.symm true) S
    (by
      intro u hS
      have e := hS.choose_spec.choose_spec
      rw [← e, hdec]
      exact comp.outputsFun (hS.choose, hS.choose_spec.choose))
  let a := Fintype.card α
  let b := Fintype.card Γ
  let c := Fintype.card (α ⊕ Option Γ)
  let J := juntaSize (Fintype.card (Fin a ⊕ Fin b))
  let mp : Polynomial ℕ := Polynomial.X + 1 + Polynomial.X ^ k
  let Bp : Polynomial ℕ := mp * Polynomial.C (c * J) + p₁.comp mp
  let P : Polynomial ℕ := (Polynomial.X ^ k + 1) * Bp + Polynomial.X ^ k +
    Polynomial.X ^ k * Polynomial.C b
  refine ⟨P, fun n hn => ?_⟩
  have ha : 0 < a := Fintype.card_pos
  let N := if Nonempty Γ then n ^ k else 0
  have hNk : N ≤ n ^ k := by simp only [N]; split_ifs <;> omega
  have hNΓ : ¬ Nonempty Γ → N = 0 := fun h => by simp only [N, if_neg h]
  have hN0 : 0 < n * a + N * b := Nat.add_pos_left (Nat.mul_pos hn ha) _
  -- the circuit for certificate length `m`
  let Cm : ℕ → (Fin (n * a + N * b) → Bool) → Bool := fun m =>
    (hp₁ (n + 1 + m) (by omega)).choose ∘ encN α Γ n N m
  let B := (n + 1 + n ^ k) * c * J + p₁.eval (n + 1 + n ^ k)
  have hCm : ∀ m ≤ N, HasCircuitOfSize (Cm m) B := by
    intro m hm
    have h1 := (hasMCircuitOfSize_encN (α := α) (Γ := Γ) (n := n) (N := N) (m := m) hN0).comp_single
      (hp₁ (n + 1 + m) (by omega)).choose_spec.1
    refine h1.mono ?_
    have hm' : n + 1 + m ≤ n + 1 + n ^ k := by omega
    have := eval_le_of_le p₁ hm'
    have : (n + 1 + m) * c * J ≤ (n + 1 + n ^ k) * c * J := by gcongr
    have e : (n + 1 + m) * Fintype.card (α ⊕ Option Γ) *
        juntaSize (Fintype.card (Fin (Fintype.card α) ⊕ Fin (Fintype.card Γ))) =
        (n + 1 + m) * c * J := rfl
    omega
  have hCm_spec : ∀ m ≤ N, ∀ (w : List α) (z : Fin (N * b) → Bool), w.length = n →
      (Cm m (Fin.append (oneHot n w) z) = true ↔ R w (cert Γ N m z)) := by
    intro m hm w z hw
    simp only [Cm, Function.comp_apply, encN_append, decWord_oneHot w hw]
    rw [(hp₁ (n + 1 + m) (by omega)).choose_spec.2 _ ⟨_, _, rfl⟩
      (by rw [length_pe2, length_cert hm hNΓ, hw]), hdec, Equiv.apply_eq_iff_eq]
    exact (hV (w, cert Γ N m z)).symm
  -- OR over all lengths `m ≤ N`
  let f : (Fin (n * a + N * b) → Bool) → Bool := fun u => decide (∃ i : Fin (N + 1), Cm i u = true)
  have hf : HasCircuitOfSize f ((N + 1) * B + N) := by
    have h1 := hasMCircuitOfSize_of_forall (fun u (i : Fin (N + 1)) => Cm i u)
      (fun i => hCm i (by omega))
    exact h1.comp_single (Pnp.Derand.hasCircuitOfSize_any N)
  refine ⟨N * b, ?_, f, hf.mono ?_, fun w hw => ?_⟩
  · simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    have : N * b ≤ n ^ k * b := Nat.mul_le_mul_right _ hNk
    omega
  · have hB : B = Bp.eval n := by
      simp only [B, Bp, mp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_pow]
      ring
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, ← hB]
    have : (N + 1) * B ≤ (n ^ k + 1) * B := Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [hL w]
    simp only [f, decide_eq_true_eq]
    constructor
    · rintro ⟨y, hy, hR⟩
      have hyN : y.length ≤ N := by
        by_cases h : Nonempty Γ
        · simp only [N, if_pos h]; rw [hw] at hy; exact hy
        · cases y with
          | nil => simp
          | cons c _ => exact absurd ⟨c⟩ h
      obtain ⟨z, hz⟩ := exists_cert y hyN
      refine ⟨z, ⟨y.length, by omega⟩, ?_⟩
      rw [hCm_spec _ hyN w z hw, hz]
      exact hR
    · rintro ⟨z, i, hi⟩
      have him : i.val ≤ N := by omega
      rw [hCm_spec _ him w z hw] at hi
      refine ⟨_, ?_, hi⟩
      rw [length_cert him hNΓ, hw]
      exact him.trans hNk

/-- **Circuit form of NP.** Every language in the official class `NP` has, for each input length
`n ≥ 1`, a polynomial-size circuit `f` on the one-hot bits of the input and polynomially many
certificate bits with `L w ↔ ∃ z, f (w, z) = true`. -/
theorem np_circuit_form {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {L : Millennium.Language (List α)}
    (hL : Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string α) L) :
    ∃ p : Polynomial ℕ, ∀ n, 0 < n → ∃ Z ≤ p.eval n,
      ∃ f : (Fin (n * Fintype.card α + Z) → Bool) → Bool, HasCircuitOfSize f (p.eval n) ∧
        ∀ w : List α, w.length = n →
          (L w ↔ ∃ z : Fin Z → Bool, f (Fin.append (oneHot n w) z) = true) := by
  obtain ⟨Γ, _, R, k, hR, hLR⟩ := hL
  exact np_circuits_of_relation R k hR (fun w => hLR w)

/-- **Cook–Levin, non-uniform form.** For every language in the official class `NP` there is a
polynomial `p` such that for every input length `n ≥ 1` some list `φ` of clauses on `V` variables
(both `≤ p(n)`) satisfies: for all `w` of length `n`, `w ∈ L` iff the dense CNF formula
`φ ∧ (input variables = oneHot w)` is satisfiable, and that formula has length `≤ p(n)`. -/
theorem cook_levin_nonuniform {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {L : Millennium.Language (List α)}
    (hL : Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string α) L) :
    ∃ p : Polynomial ℕ, ∀ n, 0 < n → ∃ (V : ℕ) (φ : List (ℕ → Option Bool)),
      V ≤ p.eval n ∧ φ.length ≤ p.eval n ∧
        ∀ w : List α, w.length = n →
          (encodeCNF V (φ ++ inputUnits (oneHot n w))).length ≤ p.eval n ∧
          (L w ↔ SATLang (encodeCNF V (φ ++ inputUnits (oneHot n w)))) := by
  obtain ⟨p₀, hp₀⟩ := np_circuit_form hL
  let P : Polynomial ℕ := (5 * p₀ + Polynomial.X * Polynomial.C (Fintype.card α) + 1) *
    (Polynomial.X * Polynomial.C (Fintype.card α) + 2 * p₀ + 1)
  refine ⟨P, fun n hn => ?_⟩
  obtain ⟨Z, hZ, f, ⟨s, hs, C, rfl⟩, hf⟩ := hp₀ n hn
  have hP : P.eval n = (5 * p₀.eval n + n * Fintype.card α + 1) * (n * Fintype.card α + 2 * p₀.eval n + 1) := by
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_one, Polynomial.eval_ofNat]
  have hφ := length_tseitinCNF_le C
  refine ⟨n * Fintype.card α + Z + s, tseitinCNF C, ?_, ?_, fun w hw => ⟨?_, ?_⟩⟩
  · rw [hP]
    calc n * Fintype.card α + Z + s ≤ 1 * (n * Fintype.card α + 2 * p₀.eval n + 1) := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · rw [hP]
    calc (tseitinCNF C).length ≤ (5 * p₀.eval n + n * Fintype.card α + 1) * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  · rw [length_encodeCNF, List.length_append, length_inputUnits, hP]
    exact Nat.mul_le_mul (by omega) (by omega)
  · rw [hf w hw, sat_fixed_iff]

end

end Pnp.CookLevin
