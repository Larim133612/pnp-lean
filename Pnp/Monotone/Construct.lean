import Pnp.Monotone.Clique

/-!
# Monotone circuits for CLIQUE exist (non-vacuity)

The lower bounds of `Razborov.lean` / `LowerBound.lean` are statements about every
monotone circuit computing `CLIQUE(m,k)`. To make sure they are not vacuous we show
that such circuits exist: for `2 ≤ k ≤ m`, the standard DNF
`⋁_{|K| = k} ⋀_{u < v ∈ K} x_{uv}` is realised by a monotone circuit reading the graph
through the standard labelling `stdLab m` (`exists_computesClique`).

(The hypotheses are needed: for `k ≤ 1`, or `k > m`, CLIQUE is a constant function, and
monotone circuits without constant gates compute neither constant on graph inputs:
the empty graph is fed as all-`false`, the complete graph as all-`true`.)

Construction: monotone formulas (`MForm`) are compiled into circuits by appending one
gate at a time (`MForm.exists_wire`), and the functions computed by formulas are closed
under nonempty finite ORs and ANDs (`mcomp_any`, `mcomp_all`).
-/

namespace Pnp.Monotone

open Finset

/-! ## Compiling monotone formulas into circuits -/

/-- Monotone formulas over input variables `Fin N`. -/
inductive MForm (N : ℕ) where
  | var : Fin N → MForm N
  | gate : Bool → MForm N → MForm N → MForm N

/-- Evaluation of a monotone formula (`true` = AND, `false` = OR). -/
def MForm.eval {N : ℕ} : MForm N → (Fin N → Bool) → Bool
  | .var i, x => x i
  | .gate o φ ψ, x => gateOp o (φ.eval x) (ψ.eval x)

/-- Some wire of the gate list `g` computes `f`. -/
def Wired {N s : ℕ} (g : MGates N s) (f : (Fin N → Bool) → Bool) : Prop :=
  ∃ w : Fin (N + s), ∀ x, evalWires x gateOp s g w = f x

lemma evalWires_castAdd {α : Type*} {N : ℕ} (x : Fin N → α) (op : Bool → α → α → α) :
    ∀ (s : ℕ) (g : MGates N s) (i : Fin N), evalWires x op s g (Fin.castAdd s i) = x i := by
  intro s
  induction s with
  | zero => intro g i; rfl
  | succ s ih =>
    intro g i
    have : (Fin.castAdd (s + 1) i : Fin (N + (s + 1))) = (Fin.castAdd s i).castSucc :=
      Fin.ext rfl
    rw [this, evalWires_succ_castSucc, ih]

/-- Appending one gate. -/
def snocGate {N s : ℕ} (g : MGates N s) (gt : MGate (N + s)) : MGates N (s + 1) :=
  Fin.snoc (α := fun i : Fin (s + 1) => MGate (N + i.val)) g gt

lemma wired_snocGate {N s : ℕ} (g : MGates N s) (gt : MGate (N + s)) {f} (hf : Wired g f) :
    Wired (snocGate g gt) f := by
  obtain ⟨w, hw⟩ := hf
  refine ⟨w.castSucc, fun x => ?_⟩
  rw [evalWires_succ_castSucc]
  have : (fun j : Fin s => snocGate g gt j.castSucc) = g := by
    funext j; simp [snocGate]
  rw [this, hw]

lemma wired_snocGate_last {N s : ℕ} (g : MGates N s) (o : Bool) (w₁ w₂ : Fin (N + s)) :
    Wired (snocGate g (o, w₁, w₂))
      (fun x => gateOp o (evalWires x gateOp s g w₁) (evalWires x gateOp s g w₂)) := by
  refine ⟨Fin.last (N + s), fun x => ?_⟩
  rw [evalWires_succ_last]
  have h1 : (fun j : Fin s => snocGate g (o, w₁, w₂) j.castSucc) = g := by
    funext j; simp [snocGate]
  have h2 : snocGate g (o, w₁, w₂) (Fin.last s) = (o, w₁, w₂) := by simp [snocGate]
  rw [h1, h2]

/-- Every monotone formula can be added to any gate list, keeping what it computes. -/
theorem MForm.exists_wire {N : ℕ} (φ : MForm N) :
    ∀ (s : ℕ) (g : MGates N s), ∃ (s' : ℕ) (g' : MGates N s'),
      (∀ f, Wired g f → Wired g' f) ∧ Wired g' φ.eval := by
  induction φ with
  | var i =>
    intro s g
    exact ⟨s, g, fun _ h => h, Fin.castAdd s i, fun x => evalWires_castAdd x gateOp s g i⟩
  | gate o φ ψ ihφ ihψ =>
    intro s g
    obtain ⟨s₁, g₁, hg₁, hφ⟩ := ihφ s g
    obtain ⟨s₂, g₂, hg₂, hψ⟩ := ihψ s₁ g₁
    obtain ⟨w₁, hw₁⟩ := hg₂ _ hφ
    obtain ⟨w₂, hw₂⟩ := hψ
    refine ⟨s₂ + 1, snocGate g₂ (o, w₁, w₂),
      fun f hf => wired_snocGate _ _ (hg₂ f (hg₁ f hf)), ?_⟩
    obtain ⟨w, hw⟩ := wired_snocGate_last g₂ o w₁ w₂
    exact ⟨w, fun x => by rw [hw]; simp only [hw₁, hw₂]; rfl⟩

/-- Every monotone formula is computed by a monotone circuit. -/
theorem MForm.exists_circuit {N : ℕ} (φ : MForm N) :
    ∃ (s : ℕ) (C : MCircuit N s), C.eval = φ.eval := by
  obtain ⟨s, g, -, w, hw⟩ := φ.exists_wire 0 (fun i => i.elim0)
  exact ⟨s, (g, w), funext hw⟩

/-! ## Closure properties -/

/-- `f` is computed by some monotone formula. -/
def MComp {N : ℕ} (f : (Fin N → Bool) → Bool) : Prop := ∃ φ : MForm N, φ.eval = f

lemma mcomp_var {N : ℕ} (i : Fin N) : MComp (fun x => x i) := ⟨.var i, rfl⟩

lemma mcomp_gate {N : ℕ} (o : Bool) {f g : (Fin N → Bool) → Bool} (hf : MComp f)
    (hg : MComp g) : MComp (fun x => gateOp o (f x) (g x)) := by
  obtain ⟨φ, rfl⟩ := hf
  obtain ⟨ψ, rfl⟩ := hg
  exact ⟨.gate o φ ψ, rfl⟩

lemma mcomp_congr {N : ℕ} {f g : (Fin N → Bool) → Bool} (hf : MComp f) (h : ∀ x, f x = g x) :
    MComp g := by
  rw [← funext h]; exact hf

/-- Nonempty finite ORs of formula-computable functions are formula-computable. -/
lemma mcomp_any {N : ℕ} {ι : Type*} [DecidableEq ι] {t : Finset ι} (ht : t.Nonempty)
    (f : ι → (Fin N → Bool) → Bool) (hf : ∀ i ∈ t, MComp (f i)) :
    MComp (fun x => decide (∃ i ∈ t, f i x = true)) := by
  induction ht using Finset.Nonempty.cons_induction with
  | singleton a => exact mcomp_congr (hf a (mem_singleton_self a)) fun x => by simp
  | cons a t hat ht ih =>
    have ih' := ih fun i hi => hf i (mem_cons.2 (Or.inr hi))
    refine mcomp_congr (mcomp_gate false (hf a (mem_cons_self a t)) ih') fun x => ?_
    simp

/-- Nonempty finite ANDs of formula-computable functions are formula-computable. -/
lemma mcomp_all {N : ℕ} {ι : Type*} [DecidableEq ι] {t : Finset ι} (ht : t.Nonempty)
    (f : ι → (Fin N → Bool) → Bool) (hf : ∀ i ∈ t, MComp (f i)) :
    MComp (fun x => decide (∀ i ∈ t, f i x = true)) := by
  induction ht using Finset.Nonempty.cons_induction with
  | singleton a => exact mcomp_congr (hf a (mem_singleton_self a)) fun x => by simp
  | cons a t hat ht ih =>
    have ih' := ih fun i hi => hf i (mem_cons.2 (Or.inr hi))
    refine mcomp_congr (mcomp_gate true (hf a (mem_cons_self a t)) ih') fun x => ?_
    simp

/-! ## A monotone circuit for CLIQUE -/

variable {m : ℕ}

/-- The input wire of `stdLab m` carrying the pair `u < v`. -/
noncomputable def stdIdx (p : Fin m × Fin m) (h : p.1 < p.2) : Fin (Fintype.card (EdgeIdx m)) :=
  Fintype.equivFin (EdgeIdx m) ⟨p, h⟩

lemma stdLab_stdIdx (p : Fin m × Fin m) (h : p.1 < p.2) : stdLab m (stdIdx p h) = p := by
  simp [stdLab, stdIdx]

/-- The edge variable of a pair (defaulting to `true` on pairs that are not `u < v`). -/
noncomputable def edgeVar (p : Fin m × Fin m) (x : Fin (Fintype.card (EdgeIdx m)) → Bool) :
    Bool :=
  if h : p.1 < p.2 then x (stdIdx p h) else true

/-- The ordered pairs `u < v` inside `K`. -/
def pairsOf (K : Finset (Fin m)) : Finset (Fin m × Fin m) :=
  (K ×ˢ K).filter fun p => p.1 < p.2

lemma pairsOf_nonempty {K : Finset (Fin m)} (hK : 2 ≤ K.card) : (pairsOf K).Nonempty := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (by omega : 1 < K.card)
  rcases lt_or_gt_of_ne huv with h | h
  · exact ⟨(u, v), by simp [pairsOf, hu, hv, h]⟩
  · exact ⟨(v, u), by simp [pairsOf, hu, hv, h]⟩

lemma isClique_iff_pairsOf (G : SimpleGraph (Fin m)) (K : Finset (Fin m)) :
    G.IsClique (K : Set (Fin m)) ↔ ∀ p ∈ pairsOf K, G.Adj p.1 p.2 := by
  constructor
  · intro h p hp
    simp only [pairsOf, mem_filter, mem_product] at hp
    exact h (mem_coe.2 hp.1.1) (mem_coe.2 hp.1.2) hp.2.ne
  · intro h u hu v hv huv
    rcases lt_or_gt_of_ne huv with hl | hl
    · exact h (u, v) (by simp [pairsOf, mem_coe.1 hu, mem_coe.1 hv, hl])
    · exact (h (v, u) (by simp [pairsOf, mem_coe.1 hu, mem_coe.1 hv, hl])).symm

lemma edgeVar_graphInput (G : SimpleGraph (Fin m)) (p : Fin m × Fin m) (h : p.1 < p.2) :
    edgeVar p (graphInput (stdLab m) G) = true ↔ G.Adj p.1 p.2 := by
  rw [edgeVar, dif_pos h, graphInput_eq_true, stdLab_stdIdx]

/-- **Non-vacuity of the CLIQUE lower bounds.** For `2 ≤ k ≤ m` there is a monotone
circuit computing `CLIQUE(m,k)` through the standard (off-diagonal) labelling `stdLab m`. -/
theorem exists_computesClique {k : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m) :
    ∃ s, ∃ C : MCircuit (Fintype.card (EdgeIdx m)) s, ComputesClique (stdLab m) k C := by
  classical
  have hne : (posTests m k).Nonempty := by
    rw [← card_pos, card_posTests]; exact Nat.choose_pos hkm
  have hcomp := mcomp_any hne (fun K x => decide (∀ p ∈ pairsOf K, edgeVar p x = true))
    fun K hK => by
      refine mcomp_congr (mcomp_all (pairsOf_nonempty (by rw [mem_posTests.1 hK]; exact hk))
        (fun p x => edgeVar p x) fun p hp => ?_) fun x => Bool.eq_iff_iff.2 (by simp)
      have hlt : p.1 < p.2 := (mem_filter.1 hp).2
      exact mcomp_congr (mcomp_var (stdIdx p hlt)) fun x => by simp [edgeVar, hlt]
  obtain ⟨φ, hφ⟩ := hcomp
  obtain ⟨s, C, hC⟩ := φ.exists_circuit
  refine ⟨s, C, fun G => ?_⟩
  rw [hC, hφ]
  simp only [decide_eq_true_eq, HasClique, mem_posTests]
  constructor
  · rintro ⟨K, hK, hall⟩
    refine ⟨K, (isClique_iff_pairsOf G K).2 fun p hp => ?_, hK⟩
    exact (edgeVar_graphInput G p (mem_filter.1 hp).2).1 (hall p hp)
  · rintro ⟨K, hcl, hK⟩
    refine ⟨K, hK, fun p hp => ?_⟩
    exact (edgeVar_graphInput G p (mem_filter.1 hp).2).2 ((isClique_iff_pairsOf G K).1 hcl p hp)

/-- Non-vacuity with the general interface: there are `N`, an off-diagonal labelling and a
monotone circuit computing `CLIQUE(m,k)`, for all `2 ≤ k ≤ m`. -/
theorem exists_offDiag_computesClique {k : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m) :
    ∃ (N s : ℕ) (lab : Fin N → Fin m × Fin m) (C : MCircuit N s),
      OffDiag lab ∧ ComputesClique lab k C := by
  obtain ⟨s, C, hC⟩ := exists_computesClique hk hkm
  exact ⟨_, s, stdLab m, C, stdLab_offDiag m, hC⟩

end Pnp.Monotone
