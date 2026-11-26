import Pnp.Algebrization.Collapse
import Pnp.Algebrization.Diagonal

/-!
# The algebrization barrier (Aaronson–Wigderson, 2008)

Aaronson and Wigderson call an inclusion `C ⊆ D` *algebrizing* if `C^A ⊆ D^Ã` for every
oracle `A` and every low-degree extension `Ã` of `A`, and a separation `C ⊄ D`
algebrizing if `C^Ã ⊄ D^A` for all such `A, Ã`.  (The side that receives the extension
`Ã` is the one that is made stronger.)  Known non-relativizing results such as
`IP = PSPACE` algebrize.

We prove, in the oracle stack-machine model of `Pnp.Oracle.Machine` with the algebraic
oracles of `Pnp.Algebrization.Extension`:

* `exists_ext_NPA_subset_P`: some `A, Ã` have `NP^Ã ⊆ P^A`; so the separation
  `P ≠ NP` does not algebrize.
* `exists_ext_NP_not_subset_PA`: some `A, Ã` have `NP^A ⊄ P^Ã`; so the inclusion
  `NP ⊆ P` (i.e. `P = NP`) does not algebrize.

Hence (`algebrization_barrier`) any proof of `P ≠ NP` or of `P = NP` must use
techniques that do not algebrize.

Caveats: the theorems are about our oracle model (prime fields only, our query
encoding); the model is not formally proved equivalent to the upstream unrelativized
classes, and "a proof technique algebrizes" is a meta-level notion that is not itself
formalized.
-/

namespace Pnp.Algebrize

open Pnp.Relativize

/-- The separation `NP ⊄ P` algebrizes: `NP^Ã ⊄ P^A` for every oracle and extension. -/
def SeparationAlgebrizes : Prop :=
  ∀ (A : Oracle) (Ã : AlgOracle), IsExtension A Ã → ¬ NPA Ã ⊆ P A

/-- The inclusion `NP ⊆ P` algebrizes: `NP^A ⊆ P^Ã` for every oracle and extension. -/
def InclusionAlgebrizes : Prop :=
  ∀ (A : Oracle) (Ã : AlgOracle), IsExtension A Ã → NP A ⊆ PA Ã

/-- **Aaronson–Wigderson.** Both `NP^Ã ⊆ P^A` and `NP^A ⊄ P^Ã` occur for suitable
oracles `A` with multiquadratic extensions `Ã`. -/
theorem aaronson_wigderson :
    (∃ (A : Oracle) (Ã : AlgOracle), IsExtension A Ã ∧ NPA Ã ⊆ P A) ∧
      (∃ (A : Oracle) (Ã : AlgOracle), IsExtension A Ã ∧ ¬ NP A ⊆ PA Ã) :=
  ⟨exists_ext_NPA_subset_P, exists_ext_NP_not_subset_PA⟩

/-- **Algebrization barrier.** Neither the separation `P ≠ NP` nor the collapse
`P = NP` algebrizes. -/
theorem algebrization_barrier : ¬ SeparationAlgebrizes ∧ ¬ InclusionAlgebrizes := by
  obtain ⟨⟨A, Ã, hA, hsub⟩, ⟨B, Bt, hB, hnot⟩⟩ := aaronson_wigderson
  exact ⟨fun h => h A Ã hA hsub, fun h => hnot (h B Bt hB)⟩

/-- Sanity check: the zero polynomials form a (multiquadratic) extension of the empty
oracle, so `IsExtension` is satisfiable. -/
theorem isExtension_empty : IsExtension ∅ (fun _ _ => 0) := by
  intro p _ m
  refine ⟨fun i => by simp, fun z => by simp⟩

end Pnp.Algebrize
