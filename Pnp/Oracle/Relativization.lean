import Pnp.Oracle.BGS
import Pnp.Oracle.BGSA

/-!
# The relativization barrier (Baker–Gill–Solovay, 1975)

There is an oracle `A` with `P^A = NP^A` and an oracle `B` with `P^B ≠ NP^B`
(in the oracle stack-machine model of `Pnp.Oracle.Machine`). Consequently the
answer to "`P^O = NP^O`?" is not the same for all oracles: an argument whose
conclusion holds uniformly for every oracle cannot settle P vs NP in this model.
-/

namespace Pnp.Relativize

/-- **Baker–Gill–Solovay, part 1:** an oracle collapsing `NP` to `P`. -/
theorem exists_oracle_P_eq_NP : ∃ A : Oracle, P A = NP A := by
  obtain ⟨A, hA⟩ := exists_oracle_NP_subset_P
  exact ⟨A, (P_subset_NP A).antisymm hA⟩

/-- **Baker–Gill–Solovay.** Both outcomes occur relative to some oracle. -/
theorem baker_gill_solovay :
    (∃ A : Oracle, P A = NP A) ∧ (∃ B : Oracle, P B ⊂ NP B) :=
  ⟨exists_oracle_P_eq_NP, exists_oracle_P_ssubset_NP⟩

/-- **Relativization barrier.** Neither `P^O = NP^O` nor `P^O ≠ NP^O` holds for
every oracle `O`; so no statement proved uniformly for all oracles decides it. -/
theorem relativization_barrier :
    ¬ (∀ O : Oracle, P O = NP O) ∧ ¬ (∀ O : Oracle, P O ≠ NP O) := by
  obtain ⟨A, hA⟩ := exists_oracle_P_eq_NP
  obtain ⟨B, hB⟩ := exists_oracle_P_ne_NP
  exact ⟨fun h => hB (h B), fun h => h A hA⟩

end Pnp.Relativize
