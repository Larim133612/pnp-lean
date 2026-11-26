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
| `Pnp/Monotone/Construct.lean` | **Non-vacuity:** monotone formulas compile to monotone circuits (`MForm.exists_circuit`); for `2 ≤ k ≤ m` the DNF `⋁_{|K|=k} ⋀_{u<v∈K} x_{uv}` gives a monotone circuit computing CLIQUE(m,k) via the standard labelling (`exists_computesClique`, `exists_offDiag_computesClique`). (For `k ≤ 1` or `k > m` CLIQUE is constant and no constant-free monotone circuit computes it.) |
| `Pnp/Monotone/LowerBound.lean` | **Explicit superpolynomial bound (M3e):** with `K ℓ = 2ℓ⁶+1`, `M ℓ = 2ℓ⁴·K ℓ + ℓ ≤ 7ℓ¹⁰` and `p = ℓ+1`, every monotone circuit computing CLIQUE(M ℓ, K ℓ) (any off-diagonal labelling) has `≥ 2^ℓ` gates for `ℓ ≥ 2` (`monotone_clique_lower_bound`), i.e. size `2^{Ω(m^{1/10})}` in the number `m` of vertices; such circuits exist (`exists_circuit_clique_MK`); no bound `s ≤ c·m^d` holds for all `ℓ` (`monotone_clique_superpolynomial`). |
| `Pnp/AC0/Formula.lean`, `Pnp/AC0/Approx.lean` | AC⁰ formulas (literal leaves, unbounded fan-in AND/OR over `Fin t → Formula`; `size` = number of gates, `depth` = gates on longest path). **Razborov–Smolensky approximation (M4a):** for every `ℓ`, a formula `F` agrees with a polynomial over `𝔽₃` of total degree `≤ (2ℓ)^{depth F}` on all 0/1 inputs outside a set `E` with `|E|·2^ℓ ≤ size F·2ⁿ` (`ac0_approx`). Core: a nonzero vector has vanishing subset sum for at most half of all subsets (`card_sum_eq_zero_mul_two_le`), then double counting picks a good OR approximant (`or_step`); no probability. |
| `Pnp/AC0/Smolensky.lean` | **Smolensky's lemma (M4b):** if `P` over `𝔽₃` has total degree `≤ D`, it agrees with PARITY on at most `#{T ⊆ [n] : |T| ≤ n/2 + D} = ∑_{i ≤ n/2+D} C(n,i)` points of `{0,1}ⁿ` (`smolensky`, `smolensky_choose`); hence `2·|agree| ≤ 2ⁿ + 2(D+1)·C(n,⌊n/2⌋)` (`smolensky_tail`). Proof via `yᵢ = 1 + xᵢ ∈ {±1}`, multilinearisation (`yᵢ² = 1`), interpolation, and `3^|G| ≤ 3^#{small sets}`. |
| `Pnp/AC0/Parity.lean` | **PARITY ∉ AC⁰ (M4c).** Central binomial bound `C(n,⌊n/2⌋)²·(n+1) ≤ 4ⁿ` (`choose_half_sq_mul_le`). A formula `F` computing PARITY on `n` bits has `2^ℓ ≤ 4·size F` whenever `16·((2ℓ)^{depth F}+1)² ≤ n+1` (`parity_ac0_lower_bound`; depth-`≤ d` form `parity_ac0_lower_bound_of_depth_le`), i.e. size `2^{Ω(n^{1/(2d)})}`. For fixed `d, c, k`, for all large `n` every depth-`≤ d` formula for PARITY has `> c·n^k` gates (`parity_not_in_AC0`). Non-vacuity: a depth-`≤ 2` DNF computes PARITY for every `n` (`exists_parity_formula`). |
| `Pnp/Circuits/Multi.lean` | Multi-output circuits; sequential composition, iteration (`T` copies of a size-`s` map cost `T·s`), parallel combination; every function of `k` fixed input bits has a circuit of size `4·2^k` (`hasCircuitOfSize_junta`); hence a map whose every output bit depends on `k` input bits has size `≤ m·4·2^k` (`hasMCircuitOfSize_local`). |
| `Pnp/PPoly/TM2Local.lean` | Locality of Mathlib's two-stack (TM2) machines: one step replaces each stack `S k` by `W k ++ drop (P k) (S k)`, where `W, P` and the new control state depend only on the top `depth` cells (`stepAux_eq_nf`, `stk_getElem?_stepAux`); stack lengths grow by `≤ D` per step; reachable stack symbols lie in a finite set `A tm k` even when the stack alphabet type is infinite (`A_finite`, `iterate_step'_stkInA`); a run within time `T` is `T` iterations of a total step (`outputsInTime_step'`). |
| `Pnp/PPoly/Encode.lean`, `Pnp/PPoly/Simulate.lean` | One-hot encoding of strings and configurations (stacks as arrays of length `n + T·D + 1`); the encoded step is a local map; a machine running in polynomial time `time` is simulated by circuits of size given by an explicit polynomial (`simulate`). |
| `Pnp/PPoly/PPoly.lean`, `Pnp/PPoly/NonVacuity.lean` | **P ⊆ P/poly (M5).** `InPPoly L`: for every `n ≥ 1` a circuit of size `≤ p(n)` decides `L` on one-hot encoded strings of length `n`. Every language in the upstream class P (`InPolynomialTime`, Mathlib `TM2ComputableInPolyTime`) is in P/poly (`inPPoly_of_inPolynomialTime`). **Connection to the official statement:** if some language in the upstream NP has no polynomial-size circuits, then `Millennium.ClayPVersusNP.Formulations.NegativeBranch` (P ≠ NP) holds (`negativeBranch_of_not_inPPoly`). This is conditional: proving such a lower bound for an NP language is open. Non-vacuity (`NonVacuity.lean`): over every alphabet with two symbols some language is not in P/poly (`exists_not_inPPoly`, Shannon counting), and the trivial language is (`inPPoly_true`). |
| `Pnp/Upstream/*.lean` | P vs NP problem statement from [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) (Apache-2.0), imports adapted. Target: `Millennium.ClayPVersusNP.Formulations.NegativeBranch`. |

## Roadmap

- [x] M1 Shannon counting lower bound
- [x] M2 Khrapchenko: de Morgan formulas for PARITY need `n²` leaves
- [x] M3 Razborov: monotone circuit lower bound for CLIQUE
  - [x] M3a Erdős–Rado sunflower lemma
  - [x] M3b Monotone circuits, test graphs, abstract approximation method
  - [x] M3c Plucking and per-gate error bounds for Alon–Boppana approximators
  - [x] M3d Size inequality for monotone circuits computing CLIQUE
  - [x] M3e Explicit parameters: size `≥ 2^ℓ` for CLIQUE(`~4ℓ¹⁰`, `2ℓ⁶+1`), i.e. `2^{Ω(m^{1/10})}`; non-vacuity
- [x] M4 PARITY ∉ AC⁰
  - [x] M4a AC⁰ formulas are approximated by low-degree `𝔽₃` polynomials
  - [x] M4b Smolensky: degree-`D` `𝔽₃` polynomials agree with PARITY on `≤ ∑_{i ≤ n/2+D} C(n,i)` points
  - [x] M4c PARITY needs size `2^{Ω(n^{1/(2d)})}` at depth `d`; superpolynomial for every fixed depth
- [x] M5 P ⊆ P/poly for the upstream TM2 model, and "NP ⊄ P/poly ⇒ NegativeBranch"
  - [x] M5a multi-output circuits, composition, iteration, local maps
  - [x] M5b locality and finite reachable alphabet of TM2 steps
  - [x] M5c simulation of polynomial-time TM2 machines by polynomial-size circuits
  - [x] M5d non-vacuity: some language is not in P/poly

Known barriers (relativization, natural proofs, algebrization) mean none of these
techniques can by themselves separate P from NP.

## Build

```
lake exe cache get
lake build
```

Toolchain: Lean `v4.31.0`, Mathlib `v4.31.0`.
