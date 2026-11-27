import Pnp.TM2.Projection

/-!
# Polynomial-time `TM2` machines compose (M25)

Mathlib states `Turing.TM2ComputableInPolyTime.comp` only as a `proof_wanted`, and the upstream
Clay formalization takes it as the hypothesis
`ClayPVersusNP.Support.PolynomialTimeComputableComposition`. Here it is proved.

Given machines `M₁` (for `f`) and `M₂` (for `g`), the composite machine `compTM` has the stacks
of both plus one scratch stack, and works in four phases:

1. run `M₁` (its `halt` statements are replaced by a jump to phase 2);
2. pop `M₁`'s output stack onto the scratch stack (translating the alphabet);
3. pop the scratch stack onto `M₂`'s input stack (restoring the order);
4. run `M₂`.

The running time is polynomial because a machine's output is short: each step pushes at most
`C` symbols, with `C` the largest number of `push`es in one statement (`npush`, `size_run`), so
`|f a| ≤ |a| + C · time₁(|a|)` (`length_output_le`).

* `comp`: `TM2ComputableInPolyTime ea eb f → TM2ComputableInPolyTime eb ec g →
  TM2ComputableInPolyTime ea ec (g ∘ f)` (any encodings).
* `polynomialTimeComputableComposition`: the upstream hypothesis.
* Unconditional versions of upstream consequences: `reducible_source_in_p`, `reducible_trans`,
  `npComplete_transfer`.
-/

namespace Pnp.TM2Comp

open Turing Millennium Computability Pnp.TM2Proj

noncomputable section

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

/-! ## Outputs are short -/

/-- The largest number of `push`es along one execution of a statement. -/
def npush {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => npush q + 1
  | .peek _ _ q => npush q
  | .pop _ _ q => npush q
  | .load _ q => npush q
  | .branch _ q₁ q₂ => max (npush q₁) (npush q₂)
  | .goto _ => 0
  | .halt => 0

/-- Total size of a family of stacks. -/
def size {K : Type} [Fintype K] {Γ : K → Type} (S : ∀ k, List (Γ k)) : ℕ := ∑ k, (S k).length

theorem size_update {K : Type} [Fintype K] [DecidableEq K] {Γ : K → Type}
    (S : ∀ k, List (Γ k)) (k : K) (l : List (Γ k)) :
    size (Function.update S k l) + (S k).length = size S + l.length := by
  unfold size
  have h : ∀ j, (Function.update S k l j).length =
      Function.update (fun j => (S j).length) k l.length j := by
    intro j
    by_cases hj : j = k
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp_rw [h]
  rw [Finset.sum_update_of_mem (Finset.mem_univ k),
    ← Finset.sum_sdiff (Finset.subset_univ {k}) (f := fun j => (S j).length),
    Finset.sum_singleton]
  ring

theorem size_stepAux {K : Type} [Fintype K] [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    size (TM2.stepAux q v S).stk ≤ size S + npush q := by
  induction q generalizing v S with
  | push k f q ih =>
    have := size_update S k (f v :: S k)
    simp only [List.length_cons] at this
    have := ih v (Function.update S k (f v :: S k))
    simp only [TM2.stepAux, npush]
    omega
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have h1 := size_update S k (S k).tail
    have h2 : (S k).tail.length ≤ (S k).length := by simp
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    simp only [TM2.stepAux, npush]
    omega
  | load f q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, npush]
    cases f v
    · exact (ih₂ v S).trans (by simp)
    · exact (ih₁ v S).trans (by simp)
  | goto f => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

/-- The push bound of a machine. -/
def pushBound (M : FinTM2) : ℕ :=
  Finset.univ.sup fun l => npush (M.m l)

theorem npush_le (M : FinTM2) (l : M.Λ) : npush (M.m l) ≤ pushBound M := by
  exact Finset.le_sup (f := fun l => npush (M.m l)) (Finset.mem_univ l)

theorem size_run (M : FinTM2) (t : ℕ) (c c' : M.Cfg) (h : runF M.step t (some c) = some c') :
    size c'.stk ≤ size c.stk + pushBound M * t := by
  induction t generalizing c with
  | zero =>
    have : c = c' := Option.some_injective _ h
    subst this; exact Nat.le_add_right _ _
  | succ t ih =>
    rw [runF_succ] at h
    rcases c with ⟨_ | l, v, S⟩
    · rw [show M.step ⟨none, v, S⟩ = none from rfl, runF_none] at h
      exact absurd h (by simp)
    · have h1 := ih _ h
      have h2 := size_stepAux (M.m l) v S
      have h3 := npush_le M l
      rw [Nat.mul_succ]
      calc size c'.stk ≤ size (TM2.stepAux (M.m l) v S).stk + pushBound M * t := h1
        _ ≤ size S + npush (M.m l) + pushBound M * t := by omega
        _ ≤ size S + (pushBound M * t + pushBound M) := by omega

theorem size_update_nil (M : FinTM2) (k : M.K) (s : List (M.Γ k)) :
    size (Function.update (fun j => ([] : List (M.Γ j))) k s) = s.length := by
  have := size_update (fun j => ([] : List (M.Γ j))) k s
  simp only [List.length_nil, add_zero] at this
  rw [this]
  simp [size]

/-- **Outputs are short**: `|f a| ≤ |a| + C · time(|a|)`. -/
theorem length_output_le {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length + pushBound h.tm * h.time.eval (ea a).length := by
  rcases h.outputsFun a with ⟨⟨t, ht⟩, htle⟩
  have hs := size_run h.tm t _ _ ht
  rw [haltList_stk, initList_stk] at hs
  rw [size_update_nil, size_update_nil, List.length_map, List.length_map] at hs
  calc (eb (f a)).length ≤ (ea a).length + pushBound h.tm * t := hs
    _ ≤ _ := by gcongr

/-! ## The composite machine -/

section Machine

variable (M₁ M₂ : FinTM2)

/-- Stack indices: `M₁`'s, `M₂`'s, and one scratch stack. -/
abbrev KC := M₁.K ⊕ (M₂.K ⊕ Unit)

/-- Stack alphabets. -/
abbrev ΓC : KC M₁ M₂ → Type
  | .inl k => M₁.Γ k
  | .inr (.inl k) => M₂.Γ k
  | .inr (.inr _) => M₂.Γ M₂.k₀

/-- Labels: `M₁`'s, `M₂`'s, and the two copy loops. -/
abbrev ΛC := M₁.Λ ⊕ (M₂.Λ ⊕ Bool)

/-- States. -/
abbrev σC := M₁.σ × M₂.σ × Option (M₂.Γ M₂.k₀)

abbrev CfgC := TM2.Cfg (ΓC M₁ M₂) (ΛC M₁ M₂) (σC M₁ M₂)

/-- Stacks of the composite machine. -/
def stkC (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (a : List (M₂.Γ M₂.k₀)) :
    ∀ k : KC M₁ M₂, List (ΓC M₁ M₂ k)
  | .inl k => S₁ k
  | .inr (.inl k) => S₂ k
  | .inr (.inr _) => a

variable {M₁ M₂}

@[simp] theorem stkC_inl (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (a) (k : M₁.K) :
    stkC M₁ M₂ S₁ S₂ a (Sum.inl k) = S₁ k := rfl

@[simp] theorem stkC_inr (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (a) (k : M₂.K) :
    stkC M₁ M₂ S₁ S₂ a (Sum.inr (Sum.inl k)) = S₂ k := rfl

@[simp] theorem stkC_aux (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (a) (u : Unit) :
    stkC M₁ M₂ S₁ S₂ a (Sum.inr (Sum.inr u)) = a := rfl

theorem update_stkC_inl (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (a) (k : M₁.K)
    (l : List (M₁.Γ k)) :
    Function.update (stkC M₁ M₂ S₁ S₂ a) (Sum.inl k) l = stkC M₁ M₂ (Function.update S₁ k l) S₂ a := by
  funext j
  rcases j with j | j | j
  · by_cases h : j = k
    · subst h; simp [stkC]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [stkC, Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem update_stkC_inr (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (a) (k : M₂.K)
    (l : List (M₂.Γ k)) :
    Function.update (stkC M₁ M₂ S₁ S₂ a) (Sum.inr (Sum.inl k)) l =
      stkC M₁ M₂ S₁ (Function.update S₂ k l) a := by
  funext j
  rcases j with j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h; simp [stkC]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [stkC, Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

theorem update_stkC_aux (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (a l) :
    Function.update (stkC M₁ M₂ S₁ S₂ a) (Sum.inr (Sum.inr ())) l = stkC M₁ M₂ S₁ S₂ l := by
  funext j
  rcases j with j | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · simp [stkC]

variable (M₁ M₂)

/-- Lift a statement of `M₁`; `halt` becomes a jump to the first copy loop. -/
def liftS₁ : TM2.Stmt M₁.Γ M₁.Λ M₁.σ → TM2.Stmt (ΓC M₁ M₂) (ΛC M₁ M₂) (σC M₁ M₂)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (liftS₁ q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (liftS₁ q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (liftS₁ q)
  | .load a q => .load (fun s => (a s.1, s.2)) (liftS₁ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (liftS₁ q₁) (liftS₁ q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

/-- Lift a statement of `M₂`. -/
def liftS₂ : TM2.Stmt M₂.Γ M₂.Λ M₂.σ → TM2.Stmt (ΓC M₁ M₂) (ΛC M₁ M₂) (σC M₁ M₂)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun s => f s.2.1) (liftS₂ q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (liftS₂ q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (liftS₂ q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (liftS₂ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (liftS₂ q₁) (liftS₂ q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .halt

/-- Labels of `M₁` inside the composite machine (halting moves on to copying). -/
def lab₁ : Option M₁.Λ → Option (ΛC M₁ M₂)
  | none => some (Sum.inr (Sum.inr false))
  | some l => some (Sum.inl l)

/-- Lift of a configuration of `M₁`. -/
def lift₁ (c : M₁.Cfg) (v₂ : M₂.σ) (S₂ : ∀ k, List (M₂.Γ k)) : CfgC M₁ M₂ :=
  ⟨lab₁ M₁ M₂ c.l, (c.var, v₂, none), stkC M₁ M₂ c.stk S₂ []⟩

/-- Lift of a configuration of `M₂`. -/
def lift₂ (c : M₂.Cfg) (v₁ : M₁.σ) (S₁ : ∀ k, List (M₁.Γ k)) : CfgC M₁ M₂ :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (v₁, c.var, none), stkC M₁ M₂ S₁ c.stk []⟩

variable {M₁ M₂}

theorem stepAux_liftS₁ (q : TM2.Stmt M₁.Γ M₁.Λ M₁.σ) (v₁ : M₁.σ) (v₂ : M₂.σ)
    (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) :
    TM2.stepAux (liftS₁ M₁ M₂ q) (v₁, v₂, none) (stkC M₁ M₂ S₁ S₂ []) =
      lift₁ M₁ M₂ (TM2.stepAux q v₁ S₁) v₂ S₂ := by
  induction q generalizing v₁ S₁ with
  | push k f q ih =>
    simp only [liftS₁, TM2.stepAux]
    rw [show stkC M₁ M₂ S₁ S₂ [] (Sum.inl k) = S₁ k from rfl, update_stkC_inl, ih]
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [liftS₁, TM2.stepAux]
    rw [show stkC M₁ M₂ S₁ S₂ [] (Sum.inl k) = S₁ k from rfl, update_stkC_inl, ih]
  | load f q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftS₁, TM2.stepAux]
    cases f v₁ <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

theorem stepAux_liftS₂ (q : TM2.Stmt M₂.Γ M₂.Λ M₂.σ) (v₁ : M₁.σ) (v₂ : M₂.σ)
    (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) :
    TM2.stepAux (liftS₂ M₁ M₂ q) (v₁, v₂, none) (stkC M₁ M₂ S₁ S₂ []) =
      lift₂ M₁ M₂ (TM2.stepAux q v₂ S₂) v₁ S₁ := by
  induction q generalizing v₂ S₂ with
  | push k f q ih =>
    simp only [liftS₂, TM2.stepAux]
    rw [show stkC M₁ M₂ S₁ S₂ [] (Sum.inr (Sum.inl k)) = S₂ k from rfl, update_stkC_inr, ih]
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [liftS₂, TM2.stepAux]
    rw [show stkC M₁ M₂ S₁ S₂ [] (Sum.inr (Sum.inl k)) = S₂ k from rfl, update_stkC_inr, ih]
  | load f q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftS₂, TM2.stepAux]
    cases f v₂ <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

variable (M₁ M₂) (tr : M₁.Γ M₁.k₁ → M₂.Γ M₂.k₀) (d : Option (M₂.Γ M₂.k₀))

/-- The program of the composite machine. With `d = none` (empty alphabet) the copy loops are
skipped. -/
def progC : ΛC M₁ M₂ → TM2.Stmt (ΓC M₁ M₂) (ΛC M₁ M₂) (σC M₁ M₂)
  | .inl l => liftS₁ M₁ M₂ (M₁.m l)
  | .inr (.inl l) => liftS₂ M₁ M₂ (M₂.m l)
  | .inr (.inr false) =>
    match d with
    | none => .goto fun _ => Sum.inr (Sum.inl M₂.main)
    | some d₀ =>
      .pop (Sum.inl M₁.k₁) (fun s o => (s.1, s.2.1, o.map tr))
        (.branch (fun s => s.2.2.isSome)
          (.push (Sum.inr (Sum.inr ())) (fun s => s.2.2.getD d₀)
            (.goto fun _ => Sum.inr (Sum.inr false)))
          (.goto fun _ => Sum.inr (Sum.inr true)))
  | .inr (.inr true) =>
    match d with
    | none => .goto fun _ => Sum.inr (Sum.inl M₂.main)
    | some d₀ =>
      .pop (Sum.inr (Sum.inr ())) (fun s o => (s.1, s.2.1, o))
        (.branch (fun s => s.2.2.isSome)
          (.push (Sum.inr (Sum.inl M₂.k₀)) (fun s => s.2.2.getD d₀)
            (.goto fun _ => Sum.inr (Sum.inr true)))
          (.goto fun _ => Sum.inr (Sum.inl M₂.main)))

/-- The step function of the composite machine. -/
abbrev stepC : CfgC M₁ M₂ → Option (CfgC M₁ M₂) := TM2.step (progC M₁ M₂ tr d)

theorem run_lift₁ (v₂ : M₂.σ) (S₂ : ∀ k, List (M₂.Γ k)) (t : ℕ) (c c' : M₁.Cfg)
    (h : runF M₁.step t (some c) = some c') :
    runF (stepC M₁ M₂ tr d) t (some (lift₁ M₁ M₂ c v₂ S₂)) = some (lift₁ M₁ M₂ c' v₂ S₂) := by
  induction t generalizing c with
  | zero => rw [Option.some_injective _ h]; rfl
  | succ t ih =>
    rw [runF_succ] at h ⊢
    rcases c with ⟨_ | l, v, S⟩
    · rw [show M₁.step ⟨none, v, S⟩ = none from rfl, runF_none] at h
      exact absurd h (by simp)
    · rw [show M₁.step ⟨some l, v, S⟩ = some (TM2.stepAux (M₁.m l) v S) from rfl] at h
      rw [show stepC M₁ M₂ tr d (lift₁ M₁ M₂ ⟨some l, v, S⟩ v₂ S₂) =
        some (TM2.stepAux (liftS₁ M₁ M₂ (M₁.m l)) (v, v₂, none) (stkC M₁ M₂ S S₂ [])) from rfl,
        stepAux_liftS₁]
      exact ih _ h

theorem run_lift₂ (v₁ : M₁.σ) (S₁ : ∀ k, List (M₁.Γ k)) (t : ℕ) (c : M₂.Cfg) :
    runF (stepC M₁ M₂ tr d) t (some (lift₂ M₁ M₂ c v₁ S₁)) =
      (runF M₂.step t (some c)).map fun c' => lift₂ M₁ M₂ c' v₁ S₁ := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    rw [runF_succ, runF_succ]
    rcases c with ⟨_ | l, v, S⟩
    · show runF (stepC M₁ M₂ tr d) t none = Option.map _ (runF M₂.step t none)
      rw [runF_none, runF_none]; rfl
    · rw [show M₂.step ⟨some l, v, S⟩ = some (TM2.stepAux (M₂.m l) v S) from rfl]
      rw [show stepC M₁ M₂ tr d (lift₂ M₁ M₂ ⟨some l, v, S⟩ v₁ S₁) =
        some (TM2.stepAux (liftS₂ M₁ M₂ (M₂.m l)) (v₁, v, none) (stkC M₁ M₂ S₁ S [])) from rfl,
        stepAux_liftS₂]
      exact ih _

/-- First copy loop: `M₁`'s output, reversed and translated, onto the scratch stack. -/
theorem run_copy₁ (d₀ : M₂.Γ M₂.k₀) (v₁ : M₁.σ) (v₂ : M₂.σ) (S₂ : ∀ k, List (M₂.Γ k))
    (L : List (M₁.Γ M₁.k₁)) : ∀ (S₁ : ∀ k, List (M₁.Γ k)) (_ : S₁ M₁.k₁ = L)
    (x : Option (M₂.Γ M₂.k₀)) (acc : List (M₂.Γ M₂.k₀)),
    runF (stepC M₁ M₂ tr (some d₀)) (L.length + 1)
      (some ⟨some (Sum.inr (Sum.inr false)), (v₁, v₂, x), stkC M₁ M₂ S₁ S₂ acc⟩) =
      some ⟨some (Sum.inr (Sum.inr true)), (v₁, v₂, none),
        stkC M₁ M₂ (Function.update S₁ M₁.k₁ []) S₂ (L.reverse.map tr ++ acc)⟩ := by
  induction L with
  | nil =>
    intro S₁ hS x acc
    rw [List.length_nil, runF_succ]
    show some (TM2.stepAux (progC M₁ M₂ tr (some d₀) (Sum.inr (Sum.inr false))) (v₁, v₂, x)
      (stkC M₁ M₂ S₁ S₂ acc)) = _
    simp only [progC, TM2.stepAux, update_stkC_inl, stkC_inl, hS, List.tail_nil]
    rfl
  | cons y L ih =>
    intro S₁ hS x acc
    rw [List.length_cons, runF_succ]
    show runF (stepC M₁ M₂ tr (some d₀)) (L.length + 1)
      (some (TM2.stepAux (progC M₁ M₂ tr (some d₀) (Sum.inr (Sum.inr false))) (v₁, v₂, x)
        (stkC M₁ M₂ S₁ S₂ acc))) = _
    simp only [progC, TM2.stepAux, update_stkC_inl, update_stkC_aux, stkC_inl, hS,
      List.tail_cons, stkC_aux]
    change runF (stepC M₁ M₂ tr (some d₀)) (L.length + 1)
      (some ⟨some (Sum.inr (Sum.inr false)), (v₁, v₂, some (tr y)),
        stkC M₁ M₂ (Function.update S₁ M₁.k₁ L) S₂ (tr y :: acc)⟩) = _
    rw [ih _ (Function.update_self _ _ _), Function.update_idem]
    simp

/-- Second copy loop: the scratch stack onto `M₂`'s input stack. -/
theorem run_copy₂ (d₀ : M₂.Γ M₂.k₀) (v₁ : M₁.σ) (v₂ : M₂.σ) (S₁ : ∀ k, List (M₁.Γ k))
    (u : List (M₂.Γ M₂.k₀)) : ∀ (S₂ : ∀ k, List (M₂.Γ k)) (ks : List (M₂.Γ M₂.k₀))
    (_ : S₂ M₂.k₀ = ks) (x : Option (M₂.Γ M₂.k₀)),
    runF (stepC M₁ M₂ tr (some d₀)) (u.length + 1)
      (some ⟨some (Sum.inr (Sum.inr true)), (v₁, v₂, x), stkC M₁ M₂ S₁ S₂ u⟩) =
      some ⟨some (Sum.inr (Sum.inl M₂.main)), (v₁, v₂, none),
        stkC M₁ M₂ S₁ (Function.update S₂ M₂.k₀ (u.reverse ++ ks)) []⟩ := by
  induction u with
  | nil =>
    intro S₂ ks hS x
    rw [List.length_nil, runF_succ]
    show some (TM2.stepAux (progC M₁ M₂ tr (some d₀) (Sum.inr (Sum.inr true))) (v₁, v₂, x)
      (stkC M₁ M₂ S₁ S₂ [])) = _
    simp only [progC, TM2.stepAux, update_stkC_aux, stkC_aux, List.tail_nil]
    rw [show (Function.update S₂ M₂.k₀ ([].reverse ++ ks)) = S₂ by
      rw [List.reverse_nil, List.nil_append, ← hS, Function.update_eq_self]]
    rfl
  | cons y u ih =>
    intro S₂ ks hS x
    rw [List.length_cons, runF_succ]
    show runF (stepC M₁ M₂ tr (some d₀)) (u.length + 1)
      (some (TM2.stepAux (progC M₁ M₂ tr (some d₀) (Sum.inr (Sum.inr true))) (v₁, v₂, x)
        (stkC M₁ M₂ S₁ S₂ (y :: u)))) = _
    simp only [progC, TM2.stepAux, update_stkC_aux, update_stkC_inr, stkC_aux, List.tail_cons,
      stkC_inr, hS]
    change runF (stepC M₁ M₂ tr (some d₀)) (u.length + 1)
      (some ⟨some (Sum.inr (Sum.inr true)), (v₁, v₂, some y),
        stkC M₁ M₂ S₁ (Function.update S₂ M₂.k₀ (y :: ks)) u⟩) = _
    rw [ih _ _ (Function.update_self _ _ _), Function.update_idem]
    simp

/-- The composite machine. -/
def compTM : FinTM2 where
  K := KC M₁ M₂
  k₀ := Sum.inl M₁.k₀
  k₁ := Sum.inr (Sum.inl M₂.k₁)
  Γ := ΓC M₁ M₂
  Λ := ΛC M₁ M₂
  main := Sum.inl M₁.main
  σ := σC M₁ M₂
  initialState := (M₁.initialState, M₂.initialState, none)
  Γk₀Fin := M₁.Γk₀Fin
  m := progC M₁ M₂ tr d

theorem update_nil_nil {K : Type} [DecidableEq K] {Γ : K → Type} (k : K) :
    Function.update (fun j => ([] : List (Γ j))) k [] = fun _ => [] :=
  Function.update_eq_self k _

/-- All four phases, at the level of configurations. -/
theorem comp_run (hd : d = none → IsEmpty (M₂.Γ M₂.k₀)) (in₁ : List (M₁.Γ M₁.k₀))
    (out₁ : List (M₁.Γ M₁.k₁)) (t₁ : ℕ)
    (h₁ : runF M₁.step t₁ (some (initList M₁ in₁)) = some (haltList M₁ out₁))
    (out₂ : List (M₂.Γ M₂.k₁)) (t₂ : ℕ)
    (h₂ : runF M₂.step t₂ (some (initList M₂ (out₁.map tr))) = some (haltList M₂ out₂)) :
    ∃ t ≤ t₂ + 2 * (out₁.length + 1) + t₁,
      runF (stepC M₁ M₂ tr d) t
        (some (lift₁ M₁ M₂ (initList M₁ in₁) M₂.initialState fun _ => [])) =
        some (lift₂ M₁ M₂ (haltList M₂ out₂) M₁.initialState fun _ => []) := by
  have e₁ := run_lift₁ M₁ M₂ tr d M₂.initialState (fun _ => []) t₁ _ _ h₁
  have hlift : lift₁ M₁ M₂ (haltList M₁ out₁) M₂.initialState (fun _ => []) =
      ⟨some (Sum.inr (Sum.inr false)), (M₁.initialState, M₂.initialState, none),
        stkC M₁ M₂ (haltList M₁ out₁).stk (fun _ => []) []⟩ := rfl
  have hin₂ : ∀ L : List (M₂.Γ M₂.k₀), (⟨some (Sum.inr (Sum.inl M₂.main)),
      (M₁.initialState, M₂.initialState, none),
      stkC M₁ M₂ (fun _ => []) (Function.update (fun _ => []) M₂.k₀ L) []⟩ : CfgC M₁ M₂) =
      lift₂ M₁ M₂ (initList M₂ L) M₁.initialState (fun _ => []) := by
    intro L
    simp only [lift₂, initList_stk]
    rfl
  have hout : (haltList M₁ out₁).stk M₁.k₁ = out₁ := by
    rw [haltList_stk, Function.update_self]
  rcases d with _ | d₀
  · -- no copying needed: the alphabet is empty
    have hE := hd rfl
    have hnil : out₁ = [] := by
      rcases out₁ with _ | ⟨y, _⟩
      · rfl
      · exact (hE.false (tr y)).elim
    subst hnil
    refine ⟨t₂ + 1 + t₁, by omega, ?_⟩
    rw [runF_add, runF_add, e₁, hlift, runF_succ]
    show runF _ t₂ (some (TM2.stepAux (progC M₁ M₂ tr none (Sum.inr (Sum.inr false)))
      (M₁.initialState, M₂.initialState, none)
      (stkC M₁ M₂ (haltList M₁ []).stk (fun _ => []) []))) = _
    simp only [progC, TM2.stepAux]
    rw [haltList_stk, update_nil_nil]
    rw [show (fun _ => [] : ∀ k, List (M₂.Γ k)) = Function.update (fun _ => []) M₂.k₀ [] from
      (update_nil_nil _).symm]
    rw [List.map_nil] at h₂
    rw [hin₂, run_lift₂, h₂]
    rfl
  · refine ⟨t₂ + (out₁.length + 1) + (out₁.length + 1) + t₁, by omega, ?_⟩
    rw [runF_add, runF_add, runF_add, e₁, hlift,
      run_copy₁ M₁ M₂ tr d₀ _ _ _ out₁ _ hout, List.append_nil,
      show out₁.length = (out₁.reverse.map tr).length by simp,
      run_copy₂ M₁ M₂ tr d₀ _ _ _ _ _ [] rfl]
    rw [haltList_stk, Function.update_idem, update_nil_nil, List.append_nil, List.map_reverse,
      List.reverse_reverse, hin₂, run_lift₂, h₂]
    rfl

theorem initList_compTM (s : List (M₁.Γ M₁.k₀)) :
    (initList (compTM M₁ M₂ tr d) s : CfgC M₁ M₂) =
      lift₁ M₁ M₂ (initList M₁ s) M₂.initialState (fun _ => []) := by
  show (⟨some (Sum.inl M₁.main), (M₁.initialState, M₂.initialState, none), _⟩ : CfgC M₁ M₂) =
    ⟨some (Sum.inl M₁.main), (M₁.initialState, M₂.initialState, none),
      stkC M₁ M₂ (initList M₁ s).stk (fun _ => []) []⟩
  congr 1
  funext k
  rcases k with k | k | u
  · by_cases hk : k = M₁.k₀
    · subst hk; simp [initList, stkC, compTM]
    · simp [initList, stkC, hk, compTM]
  · simp [stkC, compTM]
  · simp [stkC, compTM]

theorem haltList_compTM (s : List (M₂.Γ M₂.k₁)) :
    (haltList (compTM M₁ M₂ tr d) s : CfgC M₁ M₂) =
      lift₂ M₁ M₂ (haltList M₂ s) M₁.initialState (fun _ => []) := by
  show (⟨none, (M₁.initialState, M₂.initialState, none), _⟩ : CfgC M₁ M₂) =
    ⟨none, (M₁.initialState, M₂.initialState, none),
      stkC M₁ M₂ (fun _ => []) (haltList M₂ s).stk []⟩
  congr 1
  funext k
  rcases k with k | k | u
  · simp [stkC, compTM]
  · by_cases hk : k = M₂.k₁
    · subst hk; simp [haltList, stkC, compTM]
    · simp [haltList, stkC, hk, compTM]
  · simp [stkC, compTM]

end Machine

/-! ## Composition of polynomial-time computable functions -/

/-- The time polynomial of the composite machine. -/
def compTime (T₁ T₂ : Polynomial ℕ) (C : ℕ) : Polynomial ℕ :=
  T₁ + 2 * (Polynomial.X + (C : Polynomial ℕ) * T₁) + 2 +
    T₂.comp (Polynomial.X + (C : Polynomial ℕ) * T₁)

theorem eval_compTime (T₁ T₂ : Polynomial ℕ) (C n : ℕ) :
    (compTime T₁ T₂ C).eval n =
      T₁.eval n + 2 * (n + C * T₁.eval n) + 2 + T₂.eval (n + C * T₁.eval n) := by
  simp [compTime, Polynomial.eval_comp]

theorem comp_outputs {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ} (h₁ : TM2ComputableInPolyTime ea eb f)
    (h₂ : TM2ComputableInPolyTime eb ec g) (d : Option (h₂.tm.Γ h₂.tm.k₀))
    (hd : d = none → IsEmpty (h₂.tm.Γ h₂.tm.k₀)) (a : α) :
    ∃ t ≤ (compTime h₁.time h₂.time (pushBound h₁.tm)).eval (ea a).length,
      runF (stepC h₁.tm h₂.tm (fun x => h₂.inputAlphabet.symm (h₁.outputAlphabet x)) d) t
        (some (initList (compTM h₁.tm h₂.tm
          (fun x => h₂.inputAlphabet.symm (h₁.outputAlphabet x)) d)
          (List.map h₁.inputAlphabet.invFun (ea a)))) =
        some (haltList (compTM h₁.tm h₂.tm
          (fun x => h₂.inputAlphabet.symm (h₁.outputAlphabet x)) d)
          (List.map h₂.outputAlphabet.invFun (ec (g (f a))))) := by
  have hlen := length_output_le h₁ a
  rcases h₁.outputsFun a with ⟨⟨t₁, ht₁⟩, ht₁le⟩
  rcases h₂.outputsFun (f a) with ⟨⟨t₂, ht₂⟩, ht₂le⟩
  have hmap : (List.map h₁.outputAlphabet.invFun (eb (f a))).map
      (fun x => h₂.inputAlphabet.symm (h₁.outputAlphabet x)) =
      List.map h₂.inputAlphabet.invFun (eb (f a)) := by
    rw [List.map_map]
    congr 1
    funext b
    simp
  change runF h₂.tm.step t₂ _ = _ at ht₂
  rw [← hmap] at ht₂
  change runF h₁.tm.step t₁ _ = _ at ht₁
  obtain ⟨t, htle, hrun⟩ := comp_run h₁.tm h₂.tm _ d hd _ _ t₁ ht₁ _ t₂ ht₂
  refine ⟨t, ?_, ?_⟩
  · rw [eval_compTime]
    simp only [List.length_map] at htle
    have h2m : h₂.time.eval (eb (f a)).length ≤
        h₂.time.eval ((ea a).length + pushBound h₁.tm * h₁.time.eval (ea a).length) :=
      polynomial_eval_mono _ hlen
    have : t₂ ≤ h₂.time.eval (eb (f a)).length := ht₂le
    have : t₁ ≤ h₁.time.eval (ea a).length := ht₁le
    nlinarith
  · rw [initList_compTM, haltList_compTM]
    exact hrun

open Classical in
/-- **Polynomial-time computable functions compose** (Mathlib's `proof_wanted`
`Turing.TM2ComputableInPolyTime.comp`). -/
def comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ} (h₁ : TM2ComputableInPolyTime ea eb f)
    (h₂ : TM2ComputableInPolyTime eb ec g) : TM2ComputableInPolyTime ea ec (g ∘ f) :=
  letI d : Option (h₂.tm.Γ h₂.tm.k₀) :=
    if hne : Nonempty (h₂.tm.Γ h₂.tm.k₀) then some (Classical.choice hne) else none
  have hd : d = none → IsEmpty (h₂.tm.Γ h₂.tm.k₀) := by
    intro h
    by_cases hne : Nonempty (h₂.tm.Γ h₂.tm.k₀)
    · simp [d, hne] at h
    · exact not_nonempty_iff.1 hne
  { tm := compTM h₁.tm h₂.tm (fun x => h₂.inputAlphabet.symm (h₁.outputAlphabet x)) d
    inputAlphabet := h₁.inputAlphabet
    outputAlphabet := h₂.outputAlphabet
    time := compTime h₁.time h₂.time (pushBound h₁.tm)
    outputsFun := fun a =>
      { steps := Classical.choose (comp_outputs h₁ h₂ d hd a)
        evals_in_steps := (Classical.choose_spec (comp_outputs h₁ h₂ d hd a)).2
        steps_le_m := (Classical.choose_spec (comp_outputs h₁ h₂ d hd a)).1 } }

theorem nonempty_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ} (h₁ : TM2ComputableInPolyTime ea eb f)
    (h₂ : TM2ComputableInPolyTime eb ec g) : Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)) :=
  ⟨comp h₁ h₂⟩

/-- The upstream hypothesis `PolynomialTimeComputableComposition` holds. -/
theorem polynomialTimeComputableComposition :
    ClayPVersusNP.Support.PolynomialTimeComputableComposition :=
  fun h₁ h₂ => nonempty_comp h₁ h₂

/-- Cook, Proposition 1(a), unconditionally: `L₁ ≤ₚ L₂` and `L₂ ∈ P` give `L₁ ∈ P`. -/
theorem reducible_source_in_p {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) (h : PolynomialTimeReducible ea eb L₁ L₂)
    (hP : InPolynomialTime eb L₂) : InPolynomialTime ea L₁ :=
  PolynomialTimeReducible.source_in_p ea eb L₁ L₂ polynomialTimeComputableComposition h hP

/-- Transitivity of `≤ₚ`, unconditionally. -/
theorem reducible_trans {α β γ : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (ec : FinEncoding γ) (L₁ : Language α) (L₂ : Language β) (L₃ : Language γ)
    (h₁₂ : PolynomialTimeReducible ea eb L₁ L₂) (h₂₃ : PolynomialTimeReducible eb ec L₂ L₃) :
    PolynomialTimeReducible ea ec L₁ L₃ :=
  PolynomialTimeReducible.trans ea eb ec L₁ L₂ L₃ polynomialTimeComputableComposition h₁₂ h₂₃

/-- Cook, Proposition 1(b), unconditionally. -/
theorem npComplete_transfer {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (L₁ : Language α) (L₂ : Language β) (h₁ : NondeterministicPolynomialTimeComplete ea L₁)
    (h₂ : InNondeterministicPolynomialTime eb L₂) (h₁₂ : PolynomialTimeReducible ea eb L₁ L₂) :
    NondeterministicPolynomialTimeComplete eb L₂ :=
  NondeterministicPolynomialTimeComplete.transfer ea eb L₁ L₂ polynomialTimeComputableComposition
    h₁ h₂ h₁₂

/-- `P = NP` (the Clay statement) is equivalent to `NP ⊆ P`, unconditionally. -/
theorem clay_iff_hard_direction :
    ClayPVersusNP ↔ ClayPVersusNP.Formulations.HardDirection :=
  ClayPVersusNP.iff_hard_direction polynomialTimeComputableComposition

/-- An `NP`-complete language in `P` gives `P = NP`, unconditionally. -/
theorem clay_of_npComplete_in_p {alphabet : Type} [Fintype alphabet] [Nontrivial alphabet]
    {L : Language (List alphabet)}
    (hComplete : NondeterministicPolynomialTimeComplete (fin_encoding_string alphabet) L)
    (hP : InPolynomialTime (fin_encoding_string alphabet) L) : ClayPVersusNP :=
  ClayPVersusNP.nondeterministic_polynomial_time_complete_in_polynomial_time
    polynomialTimeComputableComposition hComplete hP

/-- Contrapositive: if `P ≠ NP`, no `NP`-complete language is in `P`. -/
theorem not_inP_of_npComplete {alphabet : Type} [Fintype alphabet] [Nontrivial alphabet]
    (hNeg : ¬ ClayPVersusNP) {L : Language (List alphabet)}
    (hComplete : NondeterministicPolynomialTimeComplete (fin_encoding_string alphabet) L) :
    ¬ InPolynomialTime (fin_encoding_string alphabet) L :=
  fun hP => hNeg (clay_of_npComplete_in_p hComplete hP)

end

end Pnp.TM2Comp
