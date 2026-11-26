import Mathlib.Computability.TuringMachine.Computable

/-!
# Locality facts for Mathlib's TM2 machines

Turing-machine-side ingredients for `P ⊆ P/poly`.

1. *Normal form of `stepAux`*: executing a statement `q` replaces the top `P k` cells of each
   stack `k` by a word `W k`; the new control data `l', v'` and `W`, `P` depend only on the
   state and the top `depth q` cells of each stack (`stepAux_eq_nf`, `nf_congr`), and
   `(W k).length ≤ depth q`, `P k ≤ depth q`.  Cell-level description: `stk_getElem?_nf`.
2. *Finite reachable alphabet*: `pushable tm k` is finite, and the family
   `A tm k = pushable tm k ∪ (everything, if k = k₀)` is invariant.
3. *Total step* `step'` and the time/space bound for `TM2OutputsInTime`.
-/

namespace Pnp.PPoly

open Turing Turing.TM2 Function

section Generic

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}

/-! ### Depth and the symbolic executor -/

/-- Number of stack operations (`push`/`peek`/`pop`) along the longest path of a statement. -/
def depth : Stmt Γ Λ σ → ℕ
  | .push _ _ q => depth q + 1
  | .peek _ _ q => depth q + 1
  | .pop _ _ q => depth q + 1
  | .load _ q => depth q
  | .branch _ q₁ q₂ => max (depth q₁) (depth q₂)
  | .goto _ => 0
  | .halt => 0

/-- Normal-form data of one `stepAux` execution: new label, new state, for every stack the
word `W k` that was put on top, and the number `P k` of old cells removed from the top. -/
structure NF (Γ : K → Type*) (Λ σ : Type*) where
  l : Option Λ
  var : σ
  W : ∀ k, List (Γ k)
  P : K → ℕ

/-- The stacks `W k ++ (S k).drop (P k)`. -/
def view (W : ∀ k, List (Γ k)) (P : K → ℕ) (S : ∀ k, List (Γ k)) : ∀ k, List (Γ k) :=
  fun k => W k ++ (S k).drop (P k)

/-- Rebuild a configuration from normal-form data and the old stacks. -/
def NF.apply (r : NF Γ Λ σ) (S : ∀ k, List (Γ k)) : Cfg Γ Λ σ :=
  ⟨r.l, r.var, view r.W r.P S⟩

/-- Symbolic execution of a statement on the virtual stacks `view W P S`. -/
def go (S : ∀ k, List (Γ k)) : Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → (K → ℕ) → NF Γ Λ σ
  | .push k f q, v, W, P => go S q v (update W k (f v :: W k)) P
  | .peek k f q, v, W, P => go S q (f v (view W P S k).head?) W P
  | .pop k f q, v, W, P =>
      go S q (f v (view W P S k).head?) (update W k (W k).tail)
        (if (W k).isEmpty then update P k (P k + 1) else P)
  | .load a q, v, W, P => go S q (a v) W P
  | .branch f q₁ q₂, v, W, P => cond (f v) (go S q₁ v W P) (go S q₂ v W P)
  | .goto f, v, W, P => ⟨some (f v), v, W, P⟩
  | .halt, v, W, P => ⟨none, v, W, P⟩

/-- Normal form of `stepAux q v S`. -/
def nf (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) : NF Γ Λ σ :=
  go S q v (fun _ => []) (fun _ => 0)

theorem view_push (W : ∀ k, List (Γ k)) (P : K → ℕ) (S : ∀ k, List (Γ k)) (k : K)
    (x : Γ k) : update (view W P S) k (x :: view W P S k) = view (update W k (x :: W k)) P S := by
  funext j
  by_cases h : j = k
  · subst h; simp [view]
  · simp [view, update_of_ne h]

theorem view_pop (W : ∀ k, List (Γ k)) (P : K → ℕ) (S : ∀ k, List (Γ k)) (k : K) :
    update (view W P S) k (view W P S k).tail =
      view (update W k (W k).tail) (if (W k).isEmpty then update P k (P k + 1) else P) S := by
  funext j
  by_cases h : j = k
  · subst h
    rcases hW : W j with _ | ⟨a, w⟩
    · simp [view, hW, List.tail_drop]
    · simp [view, hW]
  · rcases hW : W k with _ | ⟨a, w⟩ <;> simp [view, update_of_ne h]

/-- `stepAux` on virtual stacks is computed by `go`. -/
theorem stepAux_view (S : ∀ k, List (Γ k)) :
    ∀ (q : Stmt Γ Λ σ) (v : σ) (W : ∀ k, List (Γ k)) (P : K → ℕ),
      stepAux q v (view W P S) = (go S q v W P).apply S
  | .push k f q, v, W, P => by
      rw [stepAux, view_push]; exact stepAux_view S q _ _ _
  | .peek k f q, v, W, P => by
      rw [stepAux]; exact stepAux_view S q _ _ _
  | .pop k f q, v, W, P => by
      rw [stepAux, view_pop]; exact stepAux_view S q _ _ _
  | .load a q, v, W, P => by
      rw [stepAux]; exact stepAux_view S q _ _ _
  | .branch f q₁ q₂, v, W, P => by
      rw [stepAux, go]
      cases f v
      · exact stepAux_view S q₂ _ _ _
      · exact stepAux_view S q₁ _ _ _
  | .goto f, v, W, P => rfl
  | .halt, v, W, P => rfl

omit [DecidableEq K] in
theorem view_nil_zero (S : ∀ k, List (Γ k)) : view (fun _ => []) (fun _ => 0) S = S := by
  funext k; simp [view]

/-- `stepAux` is reconstructed from its normal form. -/
theorem stepAux_eq_nf_apply (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    stepAux q v S = (nf q v S).apply S := by
  conv_lhs => rw [← view_nil_zero S]
  exact stepAux_view S q v _ _

omit [DecidableEq K] in
theorem head?_view_congr {S S' : ∀ k, List (Γ k)} (W : ∀ k, List (Γ k)) (P : K → ℕ) (k : K)
    (h : (S k)[P k]? = (S' k)[P k]?) : (view W P S k).head? = (view W P S' k).head? := by
  rcases hW : W k with _ | ⟨a, w⟩
  · simpa [view, hW, List.head?_drop] using h
  · simp [view, hW]

/-- `go` only reads the cells `P k, …, P k + depth q - 1` of the old stacks. -/
theorem go_congr {S S' : ∀ k, List (Γ k)} :
    ∀ (q : Stmt Γ Λ σ) (v : σ) (W : ∀ k, List (Γ k)) (P : K → ℕ),
      (∀ k i, i < P k + depth q → (S k)[i]? = (S' k)[i]?) → go S q v W P = go S' q v W P
  | .push k f q, v, W, P, h => by
      simp only [go]
      exact go_congr q _ _ _ fun j i hi => h j i (by simp [depth]; omega)
  | .peek k f q, v, W, P, h => by
      simp only [go]
      rw [head?_view_congr W P k (h k _ (by simp [depth]))]
      exact go_congr q _ _ _ fun j i hi => h j i (by simp [depth]; omega)
  | .pop k f q, v, W, P, h => by
      simp only [go]
      rw [head?_view_congr W P k (h k _ (by simp [depth]))]
      refine go_congr q _ _ _ fun j i hi => h j i ?_
      simp only [depth]
      split_ifs at hi
      · by_cases hj : j = k
        · subst hj; simp at hi; omega
        · simp [update_of_ne hj] at hi; omega
      · omega
  | .load a q, v, W, P, h => by
      simp only [go]
      exact go_congr q _ _ _ fun j i hi => h j i (by simpa [depth] using hi)
  | .branch f q₁ q₂, v, W, P, h => by
      simp only [go]
      rw [go_congr q₁ v W P fun j i hi => h j i (by simp [depth]; omega),
        go_congr q₂ v W P fun j i hi => h j i (by simp [depth]; omega)]
  | .goto f, v, W, P, _ => rfl
  | .halt, v, W, P, _ => rfl

/-- The normal form only depends on the top `N ≥ depth q` cells of every stack. -/
theorem nf_congr {q : Stmt Γ Λ σ} {N : ℕ} (hN : depth q ≤ N) (v : σ)
    {S S' : ∀ k, List (Γ k)} (h : ∀ k, (S k).take N = (S' k).take N) : nf q v S = nf q v S' := by
  refine go_congr q v _ _ fun k i hi => ?_
  have hi' : i < N := by simp at hi; omega
  rw [← List.getElem?_take_of_lt hi', h k, List.getElem?_take_of_lt hi']

theorem nf_take {q : Stmt Γ Λ σ} {N : ℕ} (hN : depth q ≤ N) (v : σ) (S : ∀ k, List (Γ k)) :
    nf q v (fun k => (S k).take N) = nf q v S :=
  nf_congr hN v fun k => by simp

/-- **Normal form of `stepAux`.** For any `N ≥ depth q`, `stepAux q v S` is obtained from the
normal-form data `nf q v (fun k => (S k).take N)` (which only sees the top `N` cells). -/
theorem stepAux_eq_nf {q : Stmt Γ Λ σ} {N : ℕ} (hN : depth q ≤ N) (v : σ)
    (S : ∀ k, List (Γ k)) :
    stepAux q v S = (nf q v (fun k => (S k).take N)).apply S := by
  rw [nf_take hN, stepAux_eq_nf_apply]

theorem go_W_length (S : ∀ k, List (Γ k)) :
    ∀ (q : Stmt Γ Λ σ) (v : σ) (W : ∀ k, List (Γ k)) (P : K → ℕ) (k : K),
      ((go S q v W P).W k).length ≤ (W k).length + depth q
  | .push k' f q, v, W, P, k => by
      simp only [go, depth]
      refine (go_W_length S q _ _ _ k).trans ?_
      by_cases hk : k = k'
      · subst hk; simp; omega
      · simp [update_of_ne hk]
  | .peek k' f q, v, W, P, k => by
      simp only [go, depth]; have := go_W_length S q (f v (view W P S k').head?) W P k; omega
  | .pop k' f q, v, W, P, k => by
      simp only [go, depth]
      refine (go_W_length S q _ _ _ k).trans ?_
      by_cases hk : k = k'
      · subst hk; simp; omega
      · simp [update_of_ne hk]
  | .load a q, v, W, P, k => by
      simp only [go, depth]; exact go_W_length S q _ W P k
  | .branch f q₁ q₂, v, W, P, k => by
      simp only [go, depth]
      have h₁ := go_W_length S q₁ v W P k
      have h₂ := go_W_length S q₂ v W P k
      cases f v <;> simp <;> omega
  | .goto f, v, W, P, k => by simp [go]
  | .halt, v, W, P, k => by simp [go]

theorem go_P_le (S : ∀ k, List (Γ k)) :
    ∀ (q : Stmt Γ Λ σ) (v : σ) (W : ∀ k, List (Γ k)) (P : K → ℕ) (k : K),
      (go S q v W P).P k ≤ P k + depth q
  | .push k' f q, v, W, P, k => by
      simp only [go, depth]; have := go_P_le S q v (update W k' (f v :: W k')) P k; omega
  | .peek k' f q, v, W, P, k => by
      simp only [go, depth]; have := go_P_le S q (f v (view W P S k').head?) W P k; omega
  | .pop k' f q, v, W, P, k => by
      simp only [go, depth]
      refine (go_P_le S q _ _ _ k).trans ?_
      split_ifs
      · by_cases hk : k = k'
        · subst hk; simp; omega
        · simp [update_of_ne hk]
      · omega
  | .load a q, v, W, P, k => by
      simp only [go, depth]; exact go_P_le S q _ W P k
  | .branch f q₁ q₂, v, W, P, k => by
      simp only [go, depth]
      have h₁ := go_P_le S q₁ v W P k
      have h₂ := go_P_le S q₂ v W P k
      cases f v <;> simp <;> omega
  | .goto f, v, W, P, k => by simp [go]
  | .halt, v, W, P, k => by simp [go]

theorem nf_W_length (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((nf q v S).W k).length ≤ depth q := by
  have := go_W_length S q v (fun _ => []) (fun _ => 0) k
  simp only [List.length_nil, zero_add] at this
  exact this

theorem nf_P_le (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    (nf q v S).P k ≤ depth q := by
  have := go_P_le S q v (fun _ => []) (fun _ => 0) k
  simp only [zero_add] at this
  exact this

omit [DecidableEq K] in
/-- Cell-level description of `view`. -/
theorem view_getElem? (W : ∀ k, List (Γ k)) (P : K → ℕ) (S : ∀ k, List (Γ k)) (k : K)
    (i : ℕ) :
    (view W P S k)[i]? =
      if i < (W k).length then (W k)[i]? else (S k)[i - (W k).length + P k]? := by
  unfold view
  split_ifs with h
  · exact List.getElem?_append_left h
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
    congr 1; omega

/-- **Cell lemma.** Cell `i` of stack `k` after `stepAux q v S` is either cell `i` of `W k`, or
old cell `i - |W k| + P k`, where `W, P` come from `nf` of the top `N ≥ depth q` cells. -/
theorem stk_getElem?_stepAux {q : Stmt Γ Λ σ} {N : ℕ} (hN : depth q ≤ N) (v : σ)
    (S : ∀ k, List (Γ k)) (k : K) (i : ℕ) :
    let r := nf q v (fun k => (S k).take N)
    ((stepAux q v S).stk k)[i]? =
      if i < (r.W k).length then (r.W k)[i]? else (S k)[i - (r.W k).length + r.P k]? := by
  intro r
  rw [stepAux_eq_nf hN]
  exact view_getElem? _ _ _ k i

theorem stepAux_length_le (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((stepAux q v S).stk k).length ≤ (S k).length + depth q := by
  rw [stepAux_eq_nf_apply]
  have := nf_W_length q v S k
  simp only [NF.apply, view, List.length_append, List.length_drop]
  omega

/-! ### Pushed values -/

/-- All values that a statement can push (as a set of sigma-pairs `⟨k, x⟩`). -/
def pushSet : Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, Γ k)) ∪ pushSet q
  | .peek _ _ q => pushSet q
  | .pop _ _ q => pushSet q
  | .load _ q => pushSet q
  | .branch _ q₁ q₂ => pushSet q₁ ∪ pushSet q₂
  | .goto _ => ∅
  | .halt => ∅

omit [DecidableEq K] in
theorem pushSet_finite [Finite σ] : ∀ q : Stmt Γ Λ σ, (pushSet q).Finite
  | .push _ _ q => (Set.finite_range _).union (pushSet_finite q)
  | .peek _ _ q => pushSet_finite q
  | .pop _ _ q => pushSet_finite q
  | .load _ q => pushSet_finite q
  | .branch _ q₁ q₂ => (pushSet_finite q₁).union (pushSet_finite q₂)
  | .goto _ => Set.finite_empty
  | .halt => Set.finite_empty

/-- If every pushable value of `q` and every old stack element lies in `B`, so does every
stack element after `stepAux q v S`. -/
theorem stepAux_mem (B : ∀ k, Set (Γ k)) :
    ∀ (q : Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)),
      (∀ s ∈ pushSet q, s.2 ∈ B s.1) → (∀ k, ∀ x ∈ S k, x ∈ B k) →
        ∀ k, ∀ x ∈ (stepAux q v S).stk k, x ∈ B k
  | .push k' f q, v, S, hq, hS => by
      rw [stepAux]
      refine stepAux_mem B q _ _ (fun s hs => hq s (Or.inr hs)) fun j x hx => ?_
      by_cases hj : j = k'
      · subst hj
        simp only [update_self, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hq ⟨j, f v⟩ (Or.inl ⟨v, rfl⟩)
        · exact hS j x hx
      · rw [update_of_ne hj] at hx; exact hS j x hx
  | .peek k' f q, v, S, hq, hS => by
      rw [stepAux]; exact stepAux_mem B q _ _ hq hS
  | .pop k' f q, v, S, hq, hS => by
      rw [stepAux]
      refine stepAux_mem B q _ _ hq fun j x hx => ?_
      by_cases hj : j = k'
      · subst hj
        simp only [update_self] at hx
        exact hS j x (List.mem_of_mem_tail hx)
      · rw [update_of_ne hj] at hx; exact hS j x hx
  | .load a q, v, S, hq, hS => by
      rw [stepAux]; exact stepAux_mem B q _ _ hq hS
  | .branch f q₁ q₂, v, S, hq, hS => by
      rw [stepAux]
      cases f v
      · exact stepAux_mem B q₂ _ _ (fun s hs => hq s (Or.inr hs)) hS
      · exact stepAux_mem B q₁ _ _ (fun s hs => hq s (Or.inl hs)) hS
  | .goto f, v, S, _, hS => hS
  | .halt, v, S, _, hS => hS

end Generic

/-! ### Specialization to `FinTM2` -/

section FinTM2

variable (tm : FinTM2)

attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin FinTM2.kFin

/-- Maximal depth of the statements of the machine. -/
def D : ℕ := Finset.univ.sup fun l => depth (tm.m l)

theorem depth_le_D (l : tm.Λ) : depth (tm.m l) ≤ D tm :=
  Finset.le_sup (f := fun l => depth (tm.m l)) (Finset.mem_univ l)

/-- Stack lengths grow by at most `D tm` per step. -/
theorem step_length_le {c c' : tm.Cfg} (h : tm.step c = some c') (k : tm.K) :
    ((c' : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤ ((c : Cfg tm.Γ tm.Λ tm.σ).stk k).length + D tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [FinTM2.step] at h
  | some l =>
    simp only [FinTM2.step, TM2.step] at h
    obtain rfl := Option.some.inj h
    exact (stepAux_length_le _ _ _ k).trans (by have := depth_le_D tm l; simp; omega)

/-- The values that the machine can ever push on stack `k`. -/
def pushable (k : tm.K) : Set (tm.Γ k) :=
  {x | (⟨k, x⟩ : Σ k, tm.Γ k) ∈ ⋃ l, pushSet (tm.m l)}

theorem pushable_finite (k : tm.K) : (pushable tm k).Finite :=
  (Set.finite_iUnion fun l => pushSet_finite (tm.m l)).preimage
    (sigma_mk_injective (i := k)).injOn

/-- The reachable alphabet of stack `k`: pushable values, plus everything for the input stack. -/
def A (k : tm.K) : Set (tm.Γ k) := {x | x ∈ pushable tm k ∨ k = tm.k₀}

theorem A_finite (k : tm.K) : (A tm k).Finite := by
  by_cases hk : k = tm.k₀
  · subst hk; exact Set.toFinite _
  · exact (pushable_finite tm k).subset fun x hx => hx.resolve_right hk

instance A.finite (k : tm.K) : Finite (A tm k) := (A_finite tm k).to_subtype

/-- A (noncomputable) `Fintype` structure on the reachable alphabet. -/
noncomputable instance A.fintype (k : tm.K) : Fintype (A tm k) := Fintype.ofFinite _

/-- The invariant: every stack element lies in the reachable alphabet. -/
def StkInA (S : ∀ k, List (tm.Γ k)) : Prop := ∀ k, ∀ x ∈ S k, x ∈ A tm k

theorem stepAux_stkInA (l : tm.Λ) (v : tm.σ) {S : ∀ k, List (tm.Γ k)} (hS : StkInA tm S) :
    StkInA tm (stepAux (tm.m l) v S).stk :=
  stepAux_mem (A tm) (tm.m l) v S
    (fun _ hs => Or.inl (Set.mem_iUnion.2 ⟨l, hs⟩)) hS

theorem step_stkInA {c c' : tm.Cfg} (h : tm.step c = some c')
    (hc : StkInA tm (c : Cfg tm.Γ tm.Λ tm.σ).stk) : StkInA tm (c' : Cfg tm.Γ tm.Λ tm.σ).stk := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [FinTM2.step] at h
  | some l =>
    simp only [FinTM2.step, TM2.step] at h
    obtain rfl := Option.some.inj h
    exact stepAux_stkInA tm l v hc

theorem initList_stk (s : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm s : Cfg tm.Γ tm.Λ tm.σ).stk k) =
      if h : k = tm.k₀ then h ▸ s else [] := by
  simp only [initList]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem initList_stkInA (s : List (tm.Γ tm.k₀)) :
    StkInA tm (initList tm s : Cfg tm.Γ tm.Λ tm.σ).stk := by
  intro k x hx
  rw [initList_stk] at hx
  split_ifs at hx with h
  · exact Or.inr h
  · simp at hx

theorem initList_length_le (s : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm s : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤ s.length := by
  rw [initList_stk]
  split_ifs with h
  · subst h; rfl
  · simp

/-! ### Total step -/

/-- The total step function: `step` where defined, identity on halted configurations. -/
def step' (c : tm.Cfg) : tm.Cfg := (tm.step c).getD c

theorem step'_of_step {c c' : tm.Cfg} (h : tm.step c = some c') : step' tm c = c' := by
  unfold step'; rw [h]; rfl

theorem step_eq_none_iff (c : tm.Cfg) :
    tm.step c = none ↔ (c : Cfg tm.Γ tm.Λ tm.σ).l = none := by
  obtain ⟨l, v, S⟩ := c
  cases l
  · exact iff_of_true rfl rfl
  · exact iff_of_false (by simp [FinTM2.step]) (by simp)

theorem step'_of_halted {c : tm.Cfg} (h : (c : Cfg tm.Γ tm.Λ tm.σ).l = none) : step' tm c = c := by
  unfold step'; rw [(step_eq_none_iff tm c).2 h]; rfl

theorem step'_eq_stepAux (l : tm.Λ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    step' tm (⟨some l, v, S⟩ : Cfg tm.Γ tm.Λ tm.σ) = stepAux (tm.m l) v S := rfl

theorem step'_length_le (c : tm.Cfg) (k : tm.K) :
    ((step' tm c : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤
      ((c : Cfg tm.Γ tm.Λ tm.σ).stk k).length + D tm := by
  cases h : tm.step c with
  | none => rw [step'_of_halted tm ((step_eq_none_iff tm c).1 h)]; omega
  | some c' => rw [step'_of_step tm h]; exact step_length_le tm h k

theorem step'_stkInA {c : tm.Cfg} (hc : StkInA tm (c : Cfg tm.Γ tm.Λ tm.σ).stk) :
    StkInA tm (step' tm c : Cfg tm.Γ tm.Λ tm.σ).stk := by
  cases h : tm.step c with
  | none => rwa [step'_of_halted tm ((step_eq_none_iff tm c).1 h)]
  | some c' => rw [step'_of_step tm h]; exact step_stkInA tm h hc

theorem iterate_step'_length_le (s : List (tm.Γ tm.k₀)) (t : ℕ) (k : tm.K) :
    (((step' tm)^[t] (initList tm s) : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤
      s.length + t * D tm := by
  induction t with
  | zero => simpa using initList_length_le tm s k
  | succ t ih =>
    rw [iterate_succ_apply']
    have := step'_length_le tm ((step' tm)^[t] (initList tm s)) k
    rw [Nat.succ_mul]; omega

theorem iterate_step'_stkInA (s : List (tm.Γ tm.k₀)) (t : ℕ) :
    StkInA tm ((step' tm)^[t] (initList tm s) : Cfg tm.Γ tm.Λ tm.σ).stk := by
  induction t with
  | zero => exact initList_stkInA tm s
  | succ t ih => rw [iterate_succ_apply']; exact step'_stkInA tm ih

theorem iterate_step'_of_evals {n : ℕ} {a b : tm.Cfg}
    (h : (flip bind tm.step)^[n] (some a) = some b) : (step' tm)^[n] a = b := by
  induction n generalizing a with
  | zero => simpa using h
  | succ n ih =>
    rw [iterate_succ_apply] at h
    rw [iterate_succ_apply]
    have e : (flip bind tm.step) (some a) = tm.step a := rfl
    rw [e] at h
    cases hs : tm.step a with
    | none =>
      have : ∀ m, (flip bind tm.step)^[m] (none : Option tm.Cfg) = none := by
        intro m; induction m with
        | zero => rfl
        | succ m ihm => rw [iterate_succ_apply]; exact ihm
      rw [hs, this] at h; exact absurd h (by simp)
    | some a' =>
      rw [step'_of_step tm hs]
      rw [hs] at h; exact ih h

theorem haltList_l (s : List (tm.Γ tm.k₁)) : (haltList tm s : Cfg tm.Γ tm.Λ tm.σ).l = none := rfl

/-- **Main theorem of part 3.** A run in time `T` is `T` iterations of the total step, and all
intermediate configurations have stack lengths at most `|input| + T * D`. -/
theorem outputsInTime_step' {s : List (tm.Γ tm.k₀)} {s' : List (tm.Γ tm.k₁)} {T : ℕ}
    (h : TM2OutputsInTime tm s (some s') T) :
    (step' tm)^[T] (initList tm s) = haltList tm s' ∧
      ∀ t ≤ T, ∀ k, (((step' tm)^[t] (initList tm s) : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤
        s.length + T * D tm := by
  refine ⟨?_, fun t ht k => (iterate_step'_length_le tm s t k).trans ?_⟩
  · have hn := iterate_step'_of_evals tm h.evals_in_steps
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h.steps_le_m
    rw [hd, add_comm, iterate_add_apply, hn]
    exact iterate_fixed (step'_of_halted tm (haltList_l tm s')) d
  · have := Nat.mul_le_mul_right (D tm) ht; omega

end FinTM2

end Pnp.PPoly
