import Pnp.Circuits.Multi

/-!
# One-hot encodings and dependence-based junta bounds

* `oneHot n w`: the one-hot encoding of a string `w` of length `n` over a finite alphabet.
* `decOH`: decoding of a one-hot block (the unique true bit, a default otherwise).
* `decWord n x`: decoding of a whole one-hot string; `decWord n (oneHot n w) = w`.
* `hasCircuitOfSize_dep`, `hasMCircuitOfSize_dep`: a function whose outputs each depend only on
  the inputs indexed by a fixed finite type `Dep` has small circuits.
-/

namespace Pnp.PPoly

open Pnp.Circuits

/-- One-hot encoding of a string of length `n`: bit `(i, a)` says "the i-th symbol is a". -/
noncomputable def oneHot {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) (w : List α) :
    Fin (n * Fintype.card α) → Bool := fun j =>
  let p := finProdFinEquiv.symm j
  decide (w[p.1.val]? = some ((Fintype.equivFin α).symm p.2))

open Classical in
/-- Decode a one-hot block: some position carrying `true`, or the default `d`. -/
noncomputable def decOH {β : Type*} (f : β → Bool) (d : β) : β :=
  if h : ∃ b, f b = true then h.choose else d

theorem decOH_spec {β : Type*} {f : β → Bool} (d : β) {b₀ : β} (h : ∀ b, f b = true ↔ b = b₀) :
    decOH f d = b₀ := by
  unfold decOH
  rw [dif_pos ⟨b₀, (h b₀).2 rfl⟩]
  exact (h _).1 (Exists.choose_spec (p := fun b => f b = true) _)

/-- Decode a one-hot string of length `n`. -/
noncomputable def decWord {α : Type} [Fintype α] [Nonempty α] (n : ℕ)
    (x : Fin (n * Fintype.card α) → Bool) : List α :=
  List.ofFn fun i : Fin n =>
    decOH (fun a : α => x (finProdFinEquiv (i, Fintype.equivFin α a))) (Classical.arbitrary α)

theorem decWord_oneHot {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (w : List α) (hw : w.length = n) : decWord n (oneHot n w) = w := by
  subst hw
  refine List.ext_getElem (by simp [decWord]) fun i h₁ h₂ => ?_
  simp only [decWord, List.getElem_ofFn]
  refine decOH_spec _ fun a => ?_
  simp [oneHot, List.getElem?_eq_getElem h₂, eq_comm]

theorem decWord_getElem?_congr {α : Type} [Fintype α] [Nonempty α] {n : ℕ}
    {x y : Fin (n * Fintype.card α) → Bool} (i : ℕ)
    (h : ∀ hi : i < n, ∀ a : α, x (finProdFinEquiv (⟨i, hi⟩, Fintype.equivFin α a)) =
      y (finProdFinEquiv (⟨i, hi⟩, Fintype.equivFin α a))) :
    (decWord n x)[i]? = (decWord n y)[i]? := by
  simp only [decWord, List.getElem?_ofFn]
  split_ifs with hi
  · congr 2
    funext a
    exact h hi a
  · rfl

/-- **Juntas via dependence.** If `f` only depends on the inputs `ι d`, `d : Dep`, then `f` has
a circuit with `juntaSize (card Dep)` gates. -/
theorem hasCircuitOfSize_dep {N : ℕ} (hN : 0 < N) {Dep : Type*} [Fintype Dep]
    (f : (Fin N → Bool) → Bool) (ι : Dep → Fin N)
    (hf : ∀ x y, (∀ d, x (ι d) = y (ι d)) → f x = f y) :
    HasCircuitOfSize f (juntaSize (Fintype.card Dep)) := by
  classical
  let e := Fintype.equivFin Dep
  refine hasCircuitOfSize_of_junta hN f (fun i => ι (e.symm i))
    (fun z => f (fun p => if h : ∃ d, ι d = p then z (e h.choose) else false))
    fun x => hf _ _ fun d => ?_
  have h : ∃ d', ι d' = ι d := ⟨d, rfl⟩
  simp only [dif_pos h, Equiv.symm_apply_apply]
  exact (congrArg x h.choose_spec).symm

/-- **Local maps via dependence.** -/
theorem hasMCircuitOfSize_dep {N M : ℕ} (hN : 0 < N) {Dep : Type*} [Fintype Dep]
    (F : (Fin N → Bool) → (Fin M → Bool)) (ι : Fin M → Dep → Fin N)
    (hF : ∀ j x y, (∀ d, x (ι j d) = y (ι j d)) → F x j = F y j) :
    HasMCircuitOfSize F (M * juntaSize (Fintype.card Dep)) :=
  hasMCircuitOfSize_of_forall F fun j =>
    hasCircuitOfSize_dep hN (fun x => F x j) (ι j) fun x y h => hF j x y h

end Pnp.PPoly
