# pnp-lean

Lean 4 + Mathlib formalization work toward circuit lower bounds, in the context of P vs NP.

**Honest status:** this repository does *not* prove P ≠ NP. It formalizes known,
classical lower bounds as verified building blocks. Every theorem here builds with
no `sorry` and depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); CI checks this.

## Contents

| File | Result |
|---|---|
| `Pnp/Circuits/Basic.lean` | Boolean circuits (fan-in 2, full binary basis). **Shannon (1949):** for `n ≥ 5`, some `f : {0,1}ⁿ → {0,1}` has no circuit with `≤ 2ⁿ/(10n)` gates (`shannon_lower_bound`). |
| `Pnp/Formulas/Khrapchenko.lean` | De Morgan formulas. **Khrapchenko (1971):** if `F` is 1 on `A`, 0 on `B`, then `|E(A,B)|² ≤ L(F)·|A|·|B|` (`khrapchenko`). Corollary: every formula for PARITY on `n ≥ 1` bits has `≥ n²` leaves (`parity_formula_lower_bound`). |
| `Pnp/Monotone/Sunflower.lean` | **Erdős–Rado sunflower lemma (1960):** a family of sets of size `≤ ℓ` with more than `ℓ!(p-1)^ℓ` members contains a sunflower with `p` petals (`erdos_rado`). Engine of Razborov's method (M3). |
| `Pnp/Monotone/Circuit.lean` | Monotone circuits (AND/OR straight-line programs); they compute monotone functions (`MCircuit.eval_monotone`). **Abstract approximation method:** if each approximate gate step makes `≤ dPos` positive / `≤ dNeg` negative errors and inputs are exact, the output approximator errs on `≤ s·dPos` positive and `≤ s·dNeg` negative tests (`approximation_method`). |
| `Pnp/Monotone/Clique.lean` | CLIQUE(m,k) on graph inputs; positive tests (k-cliques) and negative tests (complete (k−1)-partite graphs of colourings, `not_hasClique_colorGraph` by pigeonhole); clique-indicator approximators; the approximation method specialised to CLIQUE (`clique_approximation`). |
| `Pnp/Monotone/Pluck.lean` | Plucking sunflowers (cores of size `≤ 1` normalised to `∅`). **Key counting lemma:** if sets `P i` (`i ∈ ι`, size `≤ ℓ`) pairwise meet inside `C`, at most `(ℓ²)^{|ι|}·r^{m-|ι|}` colourings `Fin m → Fin r` are injective on `C` but on no `P i` (`card_petal_collisions`). Plucking only shrinks sets (no positive errors), keeps sizes, reaches `≤ L` members for `L ≥ ℓ!(p-1)^ℓ` (`card_pluck_le`), and `n` steps cost `≤ n·(ℓ²)^p·r^{m-p}` negative errors (`card_negErr_pluck`). |
| `Pnp/Monotone/Razborov.lean` | Alon–Boppana approximate gates (`abAop`): per-gate errors `≤ L²·C(m-ℓ-1,k-ℓ-1)` positive (`abAop_posErr`) and `≤ L²·(ℓ²)^p·(k-1)^{m-p}` negative (`abAop_negErr`). **Razborov's theorem (Alon–Boppana form):** a monotone circuit with `s` gates computing CLIQUE(m,k) satisfies `C(m,k) ≤ s·L²·C(m-ℓ-1,k-ℓ-1)` or `(k-1)^m - ℓ²(k-1)^{m-1} ≤ s·L²·(ℓ²)^p·(k-1)^{m-p}`, `L = ℓ!(p-1)^ℓ` (`razborov_alon_boppana`). |
| `Pnp/Upstream/*.lean` | P vs NP problem statement from [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) (Apache-2.0), imports adapted. Target: `Millennium.ClayPVersusNP.Formulations.NegativeBranch`. |

## Roadmap

- [x] M1 Shannon counting lower bound
- [x] M2 Khrapchenko: de Morgan formulas for PARITY need `n²` leaves
- [ ] M3 Razborov: monotone circuit lower bound for CLIQUE
  - [x] M3a Erdős–Rado sunflower lemma
  - [x] M3b Monotone circuits, test graphs, abstract approximation method
  - [x] M3c Plucking and per-gate error bounds for Alon–Boppana approximators
  - [x] M3d Size inequality for monotone circuits computing CLIQUE
  - [ ] M3e Asymptotic parameter choice (`2^{Ω(√k)}`-type bound)
- [ ] M4 PARITY ∉ AC⁰

Known barriers (relativization, natural proofs, algebrization) mean none of these
techniques can by themselves separate P from NP.

## Build

```
lake exe cache get
lake build
```

Toolchain: Lean `v4.31.0`, Mathlib `v4.31.0`.
