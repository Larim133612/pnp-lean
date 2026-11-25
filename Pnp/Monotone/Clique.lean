import Pnp.Monotone.Circuit

/-!
# CLIQUE, test graphs, clique indicators and approximators (M3b, part 2)

**Graph inputs.** A monotone circuit `C : MCircuit N s` reads a graph
`G : SimpleGraph (Fin m)` through an *edge labelling* `lab : Fin N → Fin m × Fin m`:
input wire `i` carries `G.Adj (lab i).1 (lab i).2` (`graphInput`). We do not fix a
particular enumeration of the `m choose 2` edges: every theorem is stated for an
arbitrary labelling with off-diagonal labels (`OffDiag lab`), which includes the
standard encoding (`stdLab`, one wire per pair `u < v`) and is strictly more general
(repeated or reversed edges are allowed). This keeps the later counting arguments free
of any bookkeeping about edge enumerations: they only ever see graphs, `Finset`s of
vertices and colourings.

**Tests.** Positive tests are `K ∈ posTests m k` (the `k`-subsets of `Fin m`), read as the
graph `cliqueGraph K` (a clique on `K`, no other edges). Negative tests are all
colourings `c : Fin m → Fin (k - 1)`, read as the complete `(k-1)`-partite graph
`colorGraph c` (`u ~ v ↔ c u ≠ c v`). Negative tests are indexed by colourings, *with
multiplicity*, as in Razborov's counting.

**Approximators.** `A : Finset (Finset (Fin m))` is read as `⋁_{X ∈ A} ⌈X⌉` where
`⌈X⌉ G` says `X` is a clique of `G` (`approxSem`).
-/

namespace Pnp.Monotone

open Finset

variable {m : ℕ}

/-! ## Graph inputs and CLIQUE -/

/-- The input vector fed to the circuit for the graph `G`, via the labelling `lab`. -/
noncomputable def graphInput {N : ℕ} (lab : Fin N → Fin m × Fin m) (G : SimpleGraph (Fin m)) :
    Fin N → Bool :=
  fun i => by classical exact decide (G.Adj (lab i).1 (lab i).2)

lemma graphInput_eq_true {N : ℕ} (lab : Fin N → Fin m × Fin m) (G : SimpleGraph (Fin m))
    (i : Fin N) : graphInput lab G i = true ↔ G.Adj (lab i).1 (lab i).2 := by
  simp [graphInput]

/-- All labels are genuine edges (not loops). -/
def OffDiag {N : ℕ} (lab : Fin N → Fin m × Fin m) : Prop := ∀ i, (lab i).1 ≠ (lab i).2

/-- Index type of the standard encoding: pairs `u < v`. -/
abbrev EdgeIdx (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}

/-- The standard labelling: one input wire per unordered pair, enumerated arbitrarily. -/
noncomputable def stdLab (m : ℕ) : Fin (Fintype.card (EdgeIdx m)) → Fin m × Fin m :=
  fun i => ((Fintype.equivFin (EdgeIdx m)).symm i).1

lemma stdLab_offDiag (m : ℕ) : OffDiag (stdLab m) :=
  fun i => ((Fintype.equivFin (EdgeIdx m)).symm i).2.ne

/-- `CLIQUE(m,k)`: the graph contains a `k`-clique. (Equivalently `¬ G.CliqueFree k`.) -/
def HasClique (k : ℕ) (G : SimpleGraph (Fin m)) : Prop := ∃ K : Finset (Fin m), G.IsNClique k K

lemma hasClique_iff_not_cliqueFree (k : ℕ) (G : SimpleGraph (Fin m)) :
    HasClique k G ↔ ¬ G.CliqueFree k := by
  simp [HasClique, SimpleGraph.CliqueFree]

/-- The circuit `C` (reading graphs via `lab`) computes `CLIQUE(m,k)`. -/
def ComputesClique {N s : ℕ} (lab : Fin N → Fin m × Fin m) (k : ℕ) (C : MCircuit N s) : Prop :=
  ∀ G : SimpleGraph (Fin m), C.eval (graphInput lab G) = true ↔ HasClique k G

/-! ## Test graphs -/

/-- Positive test graph: a clique on `K` and no other edges. -/
def cliqueGraph (K : Finset (Fin m)) : SimpleGraph (Fin m) where
  Adj u v := u ≠ v ∧ u ∈ K ∧ v ∈ K
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Negative test graph: the complete multipartite graph of the colouring `c`. -/
def colorGraph {r : ℕ} (c : Fin m → Fin r) : SimpleGraph (Fin m) where
  Adj u v := c u ≠ c v
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

@[simp] lemma cliqueGraph_adj (K : Finset (Fin m)) (u v : Fin m) :
    (cliqueGraph K).Adj u v ↔ u ≠ v ∧ u ∈ K ∧ v ∈ K := Iff.rfl

@[simp] lemma colorGraph_adj {r : ℕ} (c : Fin m → Fin r) (u v : Fin m) :
    (colorGraph c).Adj u v ↔ c u ≠ c v := Iff.rfl

/-- The positive tests: all `k`-subsets of the vertex set. -/
def posTests (m k : ℕ) : Finset (Finset (Fin m)) := powersetCard k univ

lemma mem_posTests {k : ℕ} {K : Finset (Fin m)} : K ∈ posTests m k ↔ K.card = k := by
  simp [posTests]

lemma card_posTests (m k : ℕ) : (posTests m k).card = m.choose k := by
  simp [posTests]

/-- CLIQUE is true on every positive test. -/
theorem hasClique_cliqueGraph {k : ℕ} {K : Finset (Fin m)} (hK : K.card = k) :
    HasClique k (cliqueGraph K) :=
  ⟨K, ⟨fun _ hu _ hv huv => ⟨huv, hu, hv⟩, hK⟩⟩

/-- A clique of `colorGraph c` is a set on which `c` is injective. -/
lemma isClique_colorGraph_iff {r : ℕ} (c : Fin m → Fin r) (X : Set (Fin m)) :
    (colorGraph c).IsClique X ↔ Set.InjOn c X := by
  constructor
  · intro h u hu v hv huv
    by_contra hne
    exact h hu hv hne huv
  · intro h u hu v hv huv hc
    exact huv (h hu hv hc)

/-- CLIQUE is false on every negative test (pigeonhole), for `k ≥ 1`. -/
theorem not_hasClique_colorGraph {k : ℕ} (hk : 1 ≤ k) (c : Fin m → Fin (k - 1)) :
    ¬ HasClique k (colorGraph c) := by
  rintro ⟨K, hK⟩
  have hinj : Set.InjOn c (K : Set (Fin m)) := (isClique_colorGraph_iff c _).1 hK.isClique
  have := card_le_card_of_injOn c (fun _ _ => mem_univ _) hinj
  rw [card_univ, Fintype.card_fin, hK.card_eq] at this
  omega

/-- A set of at least two vertices is a clique of `cliqueGraph K` iff it lies in `K`. -/
lemma isClique_cliqueGraph_iff (K X : Finset (Fin m)) (hX : 2 ≤ X.card) :
    (cliqueGraph K).IsClique (X : Set (Fin m)) ↔ X ⊆ K := by
  constructor
  · intro h u hu
    obtain ⟨v, hv, hvu⟩ : ∃ v ∈ X, v ≠ u := by
      by_contra hc
      push Not at hc
      have : X ⊆ {u} := fun v hv => mem_singleton.2 (hc v hv)
      have := card_le_card this
      simp at this
      omega
    exact (h (mem_coe.2 hu) (mem_coe.2 hv) hvu.symm).2.1
  · intro h u hu v hv huv
    exact ⟨huv, h hu, h hv⟩

/-! ## Clique indicators and approximators -/

/-- The clique indicator `⌈X⌉`: `X` is a clique of `G`. -/
noncomputable def cliqueInd (X : Finset (Fin m)) (G : SimpleGraph (Fin m)) : Bool := by
  classical exact decide (G.IsClique (X : Set (Fin m)))

lemma cliqueInd_eq_true (X : Finset (Fin m)) (G : SimpleGraph (Fin m)) :
    cliqueInd X G = true ↔ G.IsClique (X : Set (Fin m)) := by
  simp [cliqueInd]

/-- An approximator `A` read as the OR of the clique indicators of its members. -/
noncomputable def approxSem (A : Finset (Finset (Fin m))) (G : SimpleGraph (Fin m)) : Bool := by
  classical exact decide (∃ X ∈ A, G.IsClique (X : Set (Fin m)))

lemma approxSem_eq_true (A : Finset (Finset (Fin m))) (G : SimpleGraph (Fin m)) :
    approxSem A G = true ↔ ∃ X ∈ A, G.IsClique (X : Set (Fin m)) := by
  simp [approxSem]

lemma approxSem_eq_false (A : Finset (Finset (Fin m))) (G : SimpleGraph (Fin m)) :
    approxSem A G = false ↔ ∀ X ∈ A, ¬ G.IsClique (X : Set (Fin m)) := by
  simp [approxSem]

/-- The input approximator of wire `i`: the single edge `{u, v}` it reads. -/
def inputApprox {N : ℕ} (lab : Fin N → Fin m × Fin m) (i : Fin N) : Finset (Finset (Fin m)) :=
  {{(lab i).1, (lab i).2}}

/-- Input wires are approximated exactly (on every graph), for off-diagonal labels. -/
lemma approxSem_inputApprox {N : ℕ} {lab : Fin N → Fin m × Fin m} (hlab : OffDiag lab)
    (G : SimpleGraph (Fin m)) (i : Fin N) :
    approxSem (inputApprox lab i) G = graphInput lab G i := by
  rw [Bool.eq_iff_iff, approxSem_eq_true, graphInput_eq_true]
  simp only [inputApprox, mem_singleton, exists_eq_left, coe_pair]
  rw [SimpleGraph.isClique_pair]
  exact ⟨fun h => h (hlab i), fun h _ => h⟩

/-- The exact OR of two approximators is their union. -/
lemma approxSem_union (A B : Finset (Finset (Fin m))) (G : SimpleGraph (Fin m)) :
    approxSem (A ∪ B) G = (approxSem A G || approxSem B G) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, approxSem_eq_true, approxSem_eq_true,
    approxSem_eq_true]
  simp only [mem_union]
  constructor
  · rintro ⟨X, hX | hX, h⟩
    · exact Or.inl ⟨X, hX, h⟩
    · exact Or.inr ⟨X, hX, h⟩
  · rintro (⟨X, hX, h⟩ | ⟨X, hX, h⟩)
    · exact ⟨X, Or.inl hX, h⟩
    · exact ⟨X, Or.inr hX, h⟩

/-! ## The approximation method for CLIQUE -/

/-- **Approximation method for CLIQUE.** Let `C` be a monotone circuit of size `s`
computing `CLIQUE(m,k)` (`k ≥ 1`), reading graphs through off-diagonal labels `lab`.
Approximate input wire `i` by its edge `{u, v}`, and gate kind `o` (`true` = AND,
`false` = OR) by `aop o`, preserving an invariant `Good`. If, on `Good` approximators,
each approximate step causes at most `dPos` positive errors (on `k`-cliques) and
`dNeg` negative errors (on colourings `Fin m → Fin (k-1)`) relative to the exact
AND/OR of the input approximators, then the final approximator `A` is `Good`,
is false on at most `s * dPos` positive tests and true on at most `s * dNeg` colourings.

Later milestones choose `aop` (plucking via `erdos_rado`) and `Good` (at most `L`
sets, each of size at most `ℓ`), bound `dPos`, `dNeg`, and show that every `Good`
approximator has many errors of one kind, forcing `s` to be large. -/
theorem clique_approximation {N s k : ℕ} (hk : 1 ≤ k) {lab : Fin N → Fin m × Fin m}
    (hlab : OffDiag lab) (C : MCircuit N s) (hC : ComputesClique lab k C)
    (aop : Bool → Finset (Finset (Fin m)) → Finset (Finset (Fin m)) → Finset (Finset (Fin m)))
    (Good : Finset (Finset (Fin m)) → Prop)
    (hGin : ∀ i, Good (inputApprox lab i)) (hGop : ∀ o a c, Good a → Good c → Good (aop o a c))
    (dPos dNeg : ℕ)
    (hstepP : ∀ o a c, Good a → Good c →
      ((posTests m k).filter fun K =>
        gateOp o (approxSem a (cliqueGraph K)) (approxSem c (cliqueGraph K)) = true ∧
          approxSem (aop o a c) (cliqueGraph K) = false).card ≤ dPos)
    (hstepQ : ∀ o a c, Good a → Good c →
      ((univ : Finset (Fin m → Fin (k - 1))).filter fun f =>
        gateOp o (approxSem a (colorGraph f)) (approxSem c (colorGraph f)) = false ∧
          approxSem (aop o a c) (colorGraph f) = true).card ≤ dNeg) :
    Good (C.approx (inputApprox lab) aop) ∧
      ((posTests m k).filter fun K =>
        approxSem (C.approx (inputApprox lab) aop) (cliqueGraph K) = false).card ≤ s * dPos ∧
      ((univ : Finset (Fin m → Fin (k - 1))).filter fun f =>
        approxSem (C.approx (inputApprox lab) aop) (colorGraph f) = true).card ≤ s * dNeg :=
  approximation_method C (fun K => graphInput lab (cliqueGraph K))
    (fun f => graphInput lab (colorGraph f))
    (fun a K => approxSem a (cliqueGraph K)) (fun a f => approxSem a (colorGraph f))
    (inputApprox lab) aop Good hGin hGop (posTests m k) univ dPos dNeg
    (fun _ _ i => approxSem_inputApprox hlab _ i) (fun _ _ i => approxSem_inputApprox hlab _ i)
    hstepP hstepQ
    (fun K hK => (hC _).2 (hasClique_cliqueGraph (mem_posTests.1 hK)))
    (fun f _ => by
      have := (hC (colorGraph f)).not.2 (not_hasClique_colorGraph hk f)
      simpa using this)

end Pnp.Monotone
