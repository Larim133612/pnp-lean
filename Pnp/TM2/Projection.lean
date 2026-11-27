import Pnp.Upstream.Millennium
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Deciders as verifiers in the official two-stack machine model (M24)

The upstream Clay formalization proves the easy inclusion `P ⊆ NP` only under the hypothesis
`ClayPVersusNP.Support.PolynomialTimeComputableComposition` (closure of Mathlib's
`TM2ComputableInPolyTime` under composition, a `proof_wanted` in Mathlib). The only composition
it needs is "first project `w#y` to `w`, then run a decider on `w`". Here that particular
composite machine is built by hand, so no hypothesis is left.

Given a polynomial-time `FinTM2` machine `M` computing `f : List α → δ`, the machine `projTM M`
has the stacks of `M` plus two new ones (`inr false`: the input `w#y`, `inr true`: a scratch
stack) and works in three phases:

1. pop the input `w#y` symbol by symbol, pushing the left symbols (those of `w`) onto the scratch
   stack, discarding the separator and the right symbols; this leaves `w` reversed;
2. pop the scratch stack, pushing each symbol (translated by `M`'s input alphabet) onto `M`'s
   input stack; this leaves exactly `M`'s initial configuration on `w`;
3. run `M`, every statement lifted to the bigger stack, label and state types.

All new stacks are empty when `M` halts, so the final configuration is the official halting
configuration. The running time is `time_M(|w|) + |w| + |w#y| + 2`.

* `projComp`: the composite machine as a `TM2ComputableInPolyTime` for `fun p => f p.1`.
* `polynomialTimeCheckingRelation_fst`: a language in `P` is a checking relation ignoring `y`.
* `deciderAsVerifier`: the upstream hypothesis `ClayPVersusNP.Support.DeciderAsVerifier`.
* `p_subset_np`: the official `P ⊆ NP`, unconditionally.
-/

namespace Pnp.TM2Proj

open Turing Millennium Computability

noncomputable section

theorem polynomial_eval_mono (P : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : P.eval a ≤ P.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

variable (M : FinTM2) (P : Type)

/-- Stack alphabets of the composite machine: those of `M`, and `P` for the two new stacks. -/
abbrev Γ' : M.K ⊕ Bool → Type
  | .inl k => M.Γ k
  | .inr _ => P

/-- Stacks of the composite machine from stacks `S` of `M` and the contents of the new stacks. -/
def stk3 (S : ∀ k, List (M.Γ k)) (a b : List P) : ∀ k : M.K ⊕ Bool, List (Γ' M P k)
  | .inl k => S k
  | .inr false => a
  | .inr true => b

@[simp] theorem stk3_inl (S : ∀ k, List (M.Γ k)) (a b : List P) (k : M.K) :
    stk3 M P S a b (Sum.inl k) = S k := rfl

@[simp] theorem stk3_false (S : ∀ k, List (M.Γ k)) (a b : List P) :
    stk3 M P S a b (Sum.inr false) = a := rfl

@[simp] theorem stk3_true (S : ∀ k, List (M.Γ k)) (a b : List P) :
    stk3 M P S a b (Sum.inr true) = b := rfl

theorem hd_false (S : ∀ k, List (M.Γ k)) (a b : List P) :
    (stk3 M P S a b (Sum.inr false)).head? = a.head? := rfl

theorem tl_false (S : ∀ k, List (M.Γ k)) (a b : List P) :
    (stk3 M P S a b (Sum.inr false)).tail = a.tail := rfl

theorem hd_true (S : ∀ k, List (M.Γ k)) (a b : List P) :
    (stk3 M P S a b (Sum.inr true)).head? = b.head? := rfl

theorem tl_true (S : ∀ k, List (M.Γ k)) (a b : List P) :
    (stk3 M P S a b (Sum.inr true)).tail = b.tail := rfl

/-- Lift a statement of `M` to the composite machine. -/
def liftS : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (Γ' M P) (M.Λ ⊕ Bool) (M.σ × Option P)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (liftS q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (liftS q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (liftS q)
  | .load a q => .load (fun s => (a s.1, s.2)) (liftS q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (liftS q₁) (liftS q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .halt

/-- The lift of a configuration of `M`, with given contents of the new stacks. -/
def liftG (c : M.Cfg) (x : Option P) (a b : List P) :
    TM2.Cfg (Γ' M P) (M.Λ ⊕ Bool) (M.σ × Option P) :=
  ⟨c.l.map Sum.inl, (c.var, x), stk3 M P c.stk a b⟩

variable {M P}

theorem update_stk3_inl (S : ∀ k, List (M.Γ k)) (a b : List P) (k : M.K) (l : List (M.Γ k)) :
    Function.update (stk3 M P S a b) (Sum.inl k) l = stk3 M P (Function.update S k l) a b := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h; simp [stk3]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [stk3, Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]
    cases j <;> rfl

theorem update_stk3_false (S : ∀ k, List (M.Γ k)) (a b l : List P) :
    Function.update (stk3 M P S a b) (Sum.inr false) l = stk3 M P S l b := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · cases j
    · simp [stk3]
    · rw [Function.update_of_ne (by simp)]; rfl

theorem update_stk3_true (S : ∀ k, List (M.Γ k)) (a b l : List P) :
    Function.update (stk3 M P S a b) (Sum.inr true) l = stk3 M P S a l := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · cases j
    · rw [Function.update_of_ne (by simp)]; rfl
    · simp [stk3]

theorem stepAux_liftS (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (x : Option P)
    (S : ∀ k, List (M.Γ k)) (a b : List P) :
    TM2.stepAux (liftS M P q) (v, x) (stk3 M P S a b) =
      liftG M P (TM2.stepAux q v S) x a b := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftS, TM2.stepAux]
    rw [show stk3 M P S a b (Sum.inl k) = S k from rfl, update_stk3_inl, ih]
  | peek k f q ih =>
    simp only [liftS, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    simp only [liftS, TM2.stepAux]
    rw [show stk3 M P S a b (Sum.inl k) = S k from rfl, update_stk3_inl, ih]
  | load f q ih =>
    simp only [liftS, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [liftS, TM2.stepAux]
    cases f v <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

section Machine

variable (M) {α γ : Type} (e : M.Γ M.k₀ ≃ α) [Inhabited (M.Γ M.k₀)]

/-- Is the popped symbol a left (input `w`) symbol? -/
def isL : Option (α ⊕ γ) → Bool
  | some (Sum.inl _) => true
  | _ => false

/-- Translate a popped left symbol into `M`'s input alphabet. -/
def trS : Option (α ⊕ γ) → M.Γ M.k₀
  | some (Sum.inl a) => e.symm a
  | _ => default

/-- The program of the composite machine. -/
def prog : M.Λ ⊕ Bool → TM2.Stmt (Γ' M (α ⊕ γ)) (M.Λ ⊕ Bool) (M.σ × Option (α ⊕ γ))
  | .inl l => liftS M _ (M.m l)
  | .inr false =>
    .pop (Sum.inr false) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isL s.2)
          (.push (Sum.inr true) (fun s => s.2.getD (Sum.inl (e default)))
            (.goto fun _ => Sum.inr false))
          (.goto fun _ => Sum.inr false))
        (.goto fun _ => Sum.inr true))
  | .inr true =>
    .pop (Sum.inr true) (fun s o => (s.1, o))
      (.branch (fun s => isL s.2)
        (.push (Sum.inl M.k₀) (fun s => trS M e s.2) (.goto fun _ => Sum.inr true))
        (.goto fun _ => Sum.inl M.main))

/-- Iterating a partial step function. -/
def runF {σ : Type} (f : σ → Option σ) (n : ℕ) (c : Option σ) : Option σ :=
  (flip Option.bind f)^[n] c

theorem runF_succ {σ : Type} (f : σ → Option σ) (n : ℕ) (c : σ) :
    runF f (n + 1) (some c) = runF f n (f c) := by
  rw [runF, Function.iterate_succ_apply]; rfl

theorem runF_none {σ : Type} (f : σ → Option σ) (n : ℕ) : runF f n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runF, Function.iterate_succ_apply]; exact ih

theorem runF_add {σ : Type} (f : σ → Option σ) (m n : ℕ) (c : Option σ) :
    runF f (m + n) c = runF f m (runF f n c) := by
  rw [runF, Function.iterate_add_apply]; rfl

/-- The step function of the composite machine. -/
abbrev step' : TM2.Cfg (Γ' M (α ⊕ γ)) (M.Λ ⊕ Bool) (M.σ × Option (α ⊕ γ)) →
    Option (TM2.Cfg (Γ' M (α ⊕ γ)) (M.Λ ⊕ Bool) (M.σ × Option (α ⊕ γ))) :=
  TM2.step (prog M e)

theorem step_lift (c : M.Cfg) :
    step' M e (liftG M (α ⊕ γ) c none [] []) =
      (M.step c).map fun c' => liftG M (α ⊕ γ) c' none [] [] := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (liftS M _ (M.m l)) (v, none) (stk3 M _ S [] [])) = _
    rw [stepAux_liftS]; rfl

theorem run_lift (n : ℕ) (c : M.Cfg) :
    runF (step' M e) n (some (liftG M (α ⊕ γ) c none [] [])) =
      (runF M.step n (some c)).map fun c' => liftG M (α ⊕ γ) c' none [] [] := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runF_succ, runF_succ, step_lift]
    rcases h : M.step c with _ | c'
    · exact (runF_none (step' M e) n).trans (by rw [runF_none]; rfl)
    · exact ih c'

/-- The empty stacks of `M`. -/
def emp : ∀ k, List (M.Γ k) := fun _ => []

/-- Phase 1: strip the input. -/
theorem run_phase1 (v : M.σ) (rest aux : List (α ⊕ γ)) (x : Option (α ⊕ γ)) :
    runF (step' M e) (rest.length + 1)
      (some ⟨some (Sum.inr false), (v, x), stk3 M _ (emp M) rest aux⟩) =
      some ⟨some (Sum.inr true), (v, none),
        stk3 M _ (emp M) [] ((rest.filter Sum.isLeft).reverse ++ aux)⟩ := by
  induction rest generalizing aux x with
  | nil =>
    rw [List.length_nil, runF_succ]
    show some (TM2.stepAux (prog M e (Sum.inr false)) (v, x) (stk3 M _ (emp M) [] aux)) = _
    simp only [prog, TM2.stepAux, update_stk3_false]
    rfl
  | cons p rest ih =>
    rw [List.length_cons, runF_succ]
    show runF (step' M e) (rest.length + 1)
      (some (TM2.stepAux (prog M e (Sum.inr false)) (v, x) (stk3 M _ (emp M) (p :: rest) aux))) = _
    rcases p with a | g
    · simp only [prog, TM2.stepAux, update_stk3_false, update_stk3_true]
      change runF (step' M e) (rest.length + 1)
        (some ⟨some (Sum.inr false), (v, some (Sum.inl a)),
          stk3 M _ (emp M) rest (Sum.inl a :: aux)⟩) = _
      rw [ih]
      simp
    · simp only [prog, TM2.stepAux, update_stk3_false]
      change runF (step' M e) (rest.length + 1)
        (some ⟨some (Sum.inr false), (v, some (Sum.inr g)), stk3 M _ (emp M) rest aux⟩) = _
      rw [ih]
      simp

/-- Phase 2: move `w` onto `M`'s input stack. -/
theorem run_phase2 (v : M.σ) (u : List α) (ks : List (M.Γ M.k₀)) (x : Option (α ⊕ γ)) :
    runF (step' M e) (u.length + 1)
      (some ⟨some (Sum.inr true), (v, x),
        stk3 M _ (Function.update (emp M) M.k₀ ks) [] (u.map Sum.inl)⟩) =
      some ⟨some (Sum.inl M.main), (v, none),
        stk3 M _ (Function.update (emp M) M.k₀ (u.reverse.map e.symm ++ ks)) [] []⟩ := by
  induction u generalizing ks x with
  | nil =>
    rw [List.length_nil, runF_succ]
    show some (TM2.stepAux (prog M e (Sum.inr true)) (v, x)
      (stk3 M _ (Function.update (emp M) M.k₀ ks) [] [])) = _
    simp only [prog, TM2.stepAux, update_stk3_true]
    rfl
  | cons a u ih =>
    rw [List.length_cons, runF_succ]
    show runF (step' M e) (u.length + 1)
      (some (TM2.stepAux (prog M e (Sum.inr true)) (v, x)
        (stk3 M _ (Function.update (emp M) M.k₀ ks) [] (Sum.inl a :: u.map Sum.inl)))) = _
    simp only [prog, TM2.stepAux, update_stk3_true, stk3_inl, Function.update_self,
      update_stk3_inl, Function.update_idem]
    change runF (step' M e) (u.length + 1)
      (some ⟨some (Sum.inr true), (v, some (Sum.inl a)),
        stk3 M _ (Function.update (emp M) M.k₀ (e.symm a :: ks)) [] (u.map Sum.inl)⟩) = _
    rw [ih]
    simp

theorem initList_stk (T : FinTM2) (s : List (T.Γ T.k₀)) :
    (initList T s).stk = Function.update (fun _ => []) T.k₀ s := by
  funext k
  by_cases h : k = T.k₀
  · subst h; simp [initList]
  · simp [initList, h]

/-- All three phases. -/
theorem run_all (rest : List (α ⊕ γ)) (w : List α) (hfilt : rest.filter Sum.isLeft = w.map Sum.inl)
    (t : ℕ) (c : M.Cfg)
    (hM : runF M.step t (some (initList M (w.map e.symm))) = some c) :
    runF (step' M e) (t + (w.length + 1) + (rest.length + 1))
      (some ⟨some (Sum.inr false), (M.initialState, none), stk3 M _ (emp M) rest []⟩) =
      some (liftG M _ c none [] []) := by
  have hstart : (⟨some (Sum.inl M.main), (M.initialState, none),
      stk3 M _ (Function.update (emp M) M.k₀ ((w.reverse.reverse).map e.symm ++ [])) [] []⟩ :
        TM2.Cfg (Γ' M (α ⊕ γ)) (M.Λ ⊕ Bool) (M.σ × Option (α ⊕ γ))) =
      liftG M _ (initList M (w.map e.symm)) none [] [] := by
    simp only [liftG, initList_stk, List.reverse_reverse, List.append_nil]
    rfl
  rw [runF_add, runF_add, run_phase1, hfilt, List.append_nil, ← List.map_reverse,
    show w.length = w.reverse.length from (List.length_reverse).symm]
  rw [show (emp M) = Function.update (emp M) M.k₀ [] by simp [emp]]
  rw [run_phase2, hstart, run_lift, hM]
  rfl

variable [Fintype α] [Fintype γ]

/-- The composite machine: strip the right half of `w#y`, then run `M` on `w`. -/
def projTM : FinTM2 :=
  letI := M.kFin
  letI := M.ΛFin
  letI := M.σFin
  { K := M.K ⊕ Bool
    k₀ := Sum.inr false
    k₁ := Sum.inl M.k₁
    Γ := Γ' M (α ⊕ γ)
    Λ := M.Λ ⊕ Bool
    main := Sum.inr false
    σ := M.σ × Option (α ⊕ γ)
    initialState := (M.initialState, none)
    Γk₀Fin := (inferInstance : Fintype (α ⊕ γ))
    m := prog M e }

end Machine

theorem haltList_stk (T : FinTM2) (s : List (T.Γ T.k₁)) :
    (haltList T s).stk = Function.update (fun _ => []) T.k₁ s := by
  funext k
  by_cases h : k = T.k₁
  · subst h; simp [haltList]
  · simp [haltList, h]

theorem stk3_emp (M : FinTM2) (P : Type) :
    stk3 M P (fun _ => []) [] [] = fun _ => [] := by
  funext k; rcases k with k | (_ | _) <;> rfl

/-- **Deciders run on the left half of `w#y`**, in the official machine model: a polynomial-time
`TM2` machine for `f` gives one for `(w, y) ↦ f w` on the Cook pair encoding. -/
def projComp {α β δ Γo : Type} [Fintype α] [Nonempty α] (eb : FinEncoding β)
    (eo : δ → List Γo) {f : List α → δ}
    (h : TM2ComputableInPolyTime (fin_encoding_string α).encode eo f) :
    TM2ComputableInPolyTime (pair_encoding (fin_encoding_string α) eb).encode eo
      (fun p => f p.1) := by
  letI := eb.ΓFin
  let M := h.tm
  let e : M.Γ M.k₀ ≃ α := h.inputAlphabet
  letI : Inhabited (M.Γ M.k₀) := ⟨e.symm (Classical.arbitrary α)⟩
  refine
    { tm := projTM M (γ := Option eb.Γ) e
      inputAlphabet := Equiv.refl _
      outputAlphabet := h.outputAlphabet
      time := h.time + 2 * Polynomial.X + 2
      outputsFun := fun p => ?_ }
  obtain ⟨w, y⟩ := p
  have hM := h.outputsFun w
  let enc : List (α ⊕ Option eb.Γ) := w.map Sum.inl ++ Sum.inr none :: (eb.encode y).map
    (fun b => Sum.inr (some b))
  have henc : (pair_encoding (fin_encoding_string α) eb).encode (w, y) = enc := rfl
  have hlen : enc.length = w.length + 1 + (eb.encode y).length := by simp [enc]; omega
  have hfilt : enc.filter Sum.isLeft = w.map Sum.inl := by
    simp [enc, List.filter_append, List.filter_map, Function.comp_def]
  let out := List.map h.outputAlphabet.invFun (eo (f w))
  have hhalt : (some (liftG M (α ⊕ Option eb.Γ) (haltList M out) none [] []) :
      Option (projTM M (γ := Option eb.Γ) e).Cfg) =
      Option.map (haltList (projTM M (γ := Option eb.Γ) e)) (some out) := by
    simp only [Option.map_some]
    congr 1
    show (⟨none, (M.initialState, none), stk3 M _ (haltList M out).stk [] []⟩ :
      TM2.Cfg (Γ' M (α ⊕ Option eb.Γ)) (M.Λ ⊕ Bool) (M.σ × Option (α ⊕ Option eb.Γ))) =
      ⟨none, (M.initialState, none), (haltList (projTM M (γ := Option eb.Γ) e) out).stk⟩
    congr 1
    funext k
    rcases k with k | (_ | _)
    · by_cases hk : k = M.k₁
      · subst hk; simp [haltList, stk3, projTM]
      · simp [haltList, stk3, hk, projTM]
    · simp [haltList, stk3, projTM]
    · simp [haltList, stk3, projTM]
  have hinit : initList (projTM M (γ := Option eb.Γ) e)
      (List.map (Equiv.refl ((projTM M (γ := Option eb.Γ) e).Γ
        (projTM M (γ := Option eb.Γ) e).k₀)).invFun enc) =
      ⟨some (Sum.inr false), (M.initialState, none), stk3 M _ (emp M) enc []⟩ := by
    show (⟨some (Sum.inr false), (M.initialState, none), _⟩ :
      TM2.Cfg (Γ' M (α ⊕ Option eb.Γ)) (M.Λ ⊕ Bool) (M.σ × Option (α ⊕ Option eb.Γ))) = _
    congr 1
    funext k
    rcases k with k | (_ | _)
    · simp [stk3, emp, projTM]
    · simp [stk3, projTM]
    · simp [stk3, projTM]
  refine
    { steps := hM.steps + (w.length + 1) + (enc.length + 1)
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · rw [henc]
    refine Eq.trans ?_ hhalt
    refine (congrArg (fun c => runF (step' M e) (hM.steps + (w.length + 1) + (enc.length + 1))
      (some c)) hinit).trans ?_
    have := hM.evals_in_steps
    change runF M.step hM.steps (some (initList M (List.map e.symm w))) =
      some (haltList M out) at this
    exact run_all M e enc w hfilt _ _ this
  · have h1 : hM.steps ≤ h.time.eval w.length := hM.steps_le_m
    have h2 : h.time.eval w.length ≤ h.time.eval enc.length :=
      polynomial_eval_mono _ (by omega)
    show _ ≤ (h.time + 2 * Polynomial.X + 2).eval enc.length
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega

/-- A language in `P` is a polynomial-time checking relation that ignores its certificate. -/
theorem polynomialTimeCheckingRelation_fst {α β : Type} [Fintype α] [Nonempty α]
    (eb : FinEncoding β) {L : Language (List α)}
    (hL : InPolynomialTime (fin_encoding_string α) L) :
    PolynomialTimeCheckingRelation (fin_encoding_string α) eb (fun w _ => L w) := by
  obtain ⟨f, hf, hfL⟩ := hL
  exact ⟨fun p => f p.1, projComp eb _ hf, fun p => hfL p.1⟩

/-- The upstream hypothesis `DeciderAsVerifier` holds. -/
theorem deciderAsVerifier : ClayPVersusNP.Support.DeciderAsVerifier := by
  intro alphabet _ _ L hL
  exact polynomialTimeCheckingRelation_fst _ hL

/-- **`P ⊆ NP`** for the official classes, with no composition hypothesis. -/
theorem p_subset_np (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (L : Language (List alphabet)) (hL : InPolynomialTime (fin_encoding_string alphabet) L) :
    InNondeterministicPolynomialTime (fin_encoding_string alphabet) L :=
  PolynomialTimeContainedInNondeterministicPolynomialTime.certificate_verifier deciderAsVerifier
    alphabet L hL

end

end Pnp.TM2Proj
