import Pnp.Algebrization.Extension
import Pnp.Oracle.BGSA

/-!
# `P ≠ NP` does not algebrize, first half: `NP^Ã ⊆ P^A`

Aaronson and Wigderson (*Algebrization: A New Barrier in Complexity Theory*, Thm 5.1)
show that there is an oracle `A` and a multiquadratic extension `Ã` of `A` with
`NP^Ã ⊆ P^A`; hence no proof technique that *algebrizes* can separate `P` from `NP`.
They take `A` PSPACE-complete: then `Ã` (the multilinear extension) is computable in
PSPACE, so `NP^Ã ⊆ PSPACE = P^A`.

We prove the same statement (`exists_ext_NPA_subset_P`) without PSPACE, by the
self-referential padded oracle of our Baker–Gill–Solovay formalization
(`Pnp.Oracle.BGSA`), with one twist: the verifiers are run against `toOracle (mle O)`
rather than against `O` itself.

* `mle A`: the multilinear extension of `A`,
  `Ã_{p,m}(X) = ∑_{z ∈ {0,1}^m} A(z) ∏ᵢ (zᵢ Xᵢ + (1 - zᵢ)(1 - Xᵢ))`;
  `isExtension_mle` shows it is an extension in the sense of `IsExtension`.
* Locality (`toOracle_mle_congr_short`): the strings of length `< N` of
  `toOracle (mle O)` depend only on the strings of `O` of length `< N`, since a query
  about arity `m` is longer than `m`.
* For any transformer `Φ : Oracle → Oracle` with this locality property, the oracle
  `oracleT Φ e` (defined by well-founded recursion on length: `code i x T` is in it iff
  verifier `e i` accepts `x` with oracle `Φ (oracleT Φ e)`) satisfies
  `NP (Φ (oracleT Φ e)) ⊆ P (oracleT Φ e)` (`NP_subset_P_oracleT`).
-/

namespace Pnp.Algebrize

open Pnp.Relativize MvPolynomial Function Comb

/-! ### The multilinear extension -/

open Classical in
/-- The multilinear extension of a Boolean oracle `A`: over `Fld q` in `m` variables,
`∑_{z ∈ {0,1}^m, z ∈ A} ∏ᵢ (if zᵢ then Xᵢ else 1 - Xᵢ)`. -/
noncomputable def mle (A : Oracle) : AlgOracle := fun _ m =>
  ∑ z : Fin m → Bool, if List.ofFn z ∈ A then ∏ i, (if z i then X i else 1 - X i) else 0

theorem degreeOf_mle_le (A : Oracle) (q m : ℕ) (i : Fin m) :
    (mle A q m).degreeOf i ≤ 1 := by
  classical
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun z _ => ?_)
  split_ifs
  · refine (degreeOf_prod_le _ _ _).trans ?_
    calc ∑ j, degreeOf i (if z j then (X j : MvPolynomial (Fin m) (Fld q)) else 1 - X j)
        ≤ ∑ j : Fin m, if i = j then 1 else 0 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hX := degreeOf_X (R := Fld q) i j
          by_cases hz : z j
          · rw [if_pos hz, hX]
          · rw [if_neg hz]
            exact (degreeOf_sub_le _ _ _).trans (by rw [degreeOf_one, hX]; simp)
      _ = 1 := by simp
  · simp [degreeOf_zero]

theorem eval_mle (A : Oracle) (q m : ℕ) (z : Fin m → Bool) :
    eval (boolPt z) (mle A q m) = open Classical in if List.ofFn z ∈ A then 1 else 0 := by
  classical
  simp only [mle, map_sum]
  rw [Finset.sum_eq_single z]
  · split_ifs
    · rw [map_prod]
      refine Finset.prod_eq_one fun i _ => ?_
      cases h : z i <;> simp [boolPt, h]
    · simp
  · intro z' _ hz
    split_ifs
    · rw [map_prod]
      obtain ⟨i, hi⟩ : ∃ i, z' i ≠ z i := by
        by_contra h; push Not at h; exact hz (funext h)
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      cases h : z' i <;> cases h' : z i <;> simp_all [boolPt]
    · simp
  · simp

/-- The multilinear extension is a (multiquadratic) extension. -/
theorem isExtension_mle (A : Oracle) : IsExtension A (mle A) := by
  intro q m
  refine ⟨fun i => (degreeOf_mle_le A q m i).trans (by norm_num), fun z => ?_⟩
  rw [eval_mle]

/-! ### Locality -/

/-- `mle O p m` only depends on the strings of `O` of length `m`. -/
theorem mle_congr {O₁ O₂ : Oracle} {m : ℕ} (h : ∀ s : Str, s.length = m → (s ∈ O₁ ↔ s ∈ O₂))
    (p : ℕ) : mle O₁ p m = mle O₂ p m := by
  classical
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [h _ (List.length_ofFn)]

/-- The strings of length `< N` of `toOracle (mle O)` depend only on the strings of `O`
of length `< N`. -/
theorem toOracle_mle_congr_short {N : ℕ} {O₁ O₂ : Oracle}
    (hO : ∀ s : Str, s.length < N → (s ∈ O₁ ↔ s ∈ O₂)) :
    ∀ s : Str, s.length < N → (s ∈ toOracle (mle O₁) ↔ s ∈ toOracle (mle O₂)) := by
  intro s hs
  have key : ∀ p j xs, s = encQ p j xs → mle O₁ p xs.length = mle O₂ p xs.length := by
    rintro p j xs rfl
    exact mle_congr (fun t ht => hO t (by have := length_lt_length_encQ p j xs; omega)) p
  constructor
  · rintro ⟨p, j, xs, hxs, hs', ha⟩
    refine ⟨p, j, xs, hxs, hs', ?_⟩
    unfold answer at *
    rwa [← key p j xs hs']
  · rintro ⟨p, j, xs, hxs, hs', ha⟩
    refine ⟨p, j, xs, hxs, hs', ?_⟩
    unfold answer at *
    rwa [key p j xs hs']

/-! ### The self-referential oracle for a local transformer -/

section Transformer

/-- A transformer of oracles is *local* if the strings of length `< N` of `Φ O` depend
only on the strings of `O` of length `< N`. -/
def IsLocal (Φ : Oracle → Oracle) : Prop :=
  ∀ (N : ℕ) (O₁ O₂ : Oracle), (∀ s : Str, s.length < N → (s ∈ O₁ ↔ s ∈ O₂)) →
    ∀ s : Str, s.length < N → (s ∈ Φ O₁ ↔ s ∈ Φ O₂)

theorem isLocal_toOracle_mle : IsLocal (fun O => toOracle (mle O)) :=
  fun _ _ _ hO => toOracle_mle_congr_short hO

variable (Φ : Oracle → Oracle) (e : ℕ → Prog × ℕ)

/-- `q` is a code `code i x T` and verifier `e i` accepts `x` with oracle `Φ O`. -/
def TCond (q : Str) (O : Oracle) : Prop :=
  ∃ i x T, q = code i x T ∧ ∃ w : Str, w.length ≤ tb (e i).2 x.length ∧
    runFor (Φ O) (e i).1 (tb (e i).2 x.length) (.run (init [x, w])) = .done true

/-- Membership in the oracle, by well-founded recursion on length. -/
noncomputable def memT : Str → Prop :=
  (measure List.length).wf.fix fun q rec =>
    TCond Φ e q {s | ∃ h : s.length < q.length, rec s h}

/-- The oracle `A` (depending on the transformer `Φ` and the enumeration `e`). -/
def oracleT : Oracle := {q | memT Φ e q}

theorem memT_iff (q : Str) :
    memT Φ e q ↔ TCond Φ e q {s | s.length < q.length ∧ memT Φ e s} := by
  unfold memT
  rw [WellFounded.fix_eq]
  simp only [exists_prop]

theorem mem_oracleT_code (hΦ : IsLocal Φ) (i : ℕ) (x : Str) (T : ℕ)
    (hT : x.length + 2 * tb (e i).2 x.length ≤ (code i x T).length) :
    code i x T ∈ oracleT Φ e ↔ ∃ w : Str, w.length ≤ tb (e i).2 x.length ∧
      runFor (Φ (oracleT Φ e)) (e i).1 (tb (e i).2 x.length) (.run (init [x, w])) =
        .done true := by
  have hO : ∀ s : Str, s.length < (code i x T).length →
      (s ∈ {s : Str | s.length < (code i x T).length ∧ memT Φ e s} ↔ s ∈ oracleT Φ e) :=
    fun s hs => by simp [oracleT, hs]
  have hrun : ∀ w : Str, w.length ≤ tb (e i).2 x.length →
      runFor (Φ {s : Str | s.length < (code i x T).length ∧ memT Φ e s}) (e i).1
        (tb (e i).2 x.length) (.run (init [x, w])) =
      runFor (Φ (oracleT Φ e)) (e i).1 (tb (e i).2 x.length) (.run (init [x, w])) :=
    fun w hw => runFor_congr_short (hΦ _ _ _ hO) _ _ (x.length + w.length)
      (init_two_length x w) (by omega)
  change memT Φ e _ ↔ _
  rw [memT_iff]
  constructor
  · rintro ⟨i', x', T', hq, w, hw, hr⟩
    obtain ⟨rfl, rfl⟩ := code_inj hq
    exact ⟨w, hw, (hrun w hw) ▸ hr⟩
  · rintro ⟨w, hw, hr⟩
    exact ⟨i, x, T, rfl, w, hw, (hrun w hw).symm ▸ hr⟩

/-- For a local transformer `Φ`, `NP^{Φ(A)} ⊆ P^A` for the self-referential oracle `A`. -/
theorem NP_subset_P_oracleT (hΦ : IsLocal Φ) (he : Surjective e) :
    NP (Φ (oracleT Φ e)) ⊆ P (oracleT Φ e) := by
  rintro L ⟨p, k, hv⟩
  obtain ⟨i, hi⟩ := he (p, k)
  refine ⟨queryProg i (k + 1), 3 * (k + 1) + i + 11, fun x => ?_⟩
  obtain ⟨b, hb, hiff⟩ := queryProg_run (oracleT Φ e) i (k + 1) x
  refine ⟨b, runFor_mono hb (queryTime_le _ _ _), ?_⟩
  have hT : x.length + 2 * tb (e i).2 x.length ≤
      (code i x ((x.length + 2) ^ (k + 1))).length := by
    rw [code_length, hi, tb, pow_succ]
    dsimp only
    have : 2 * (x.length + 2) ^ k ≤ (x.length + 2) ^ k * (x.length + 2) := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  rw [hiff, mem_oracleT_code Φ e hΦ i x _ hT, hv x, hi]

end Transformer

/-- **`P ≠ NP` does not algebrize** (Aaronson–Wigderson, Thm 5.1, first half): there is
an oracle `A` and a multiquadratic extension `Ã` of `A` with `NP^Ã ⊆ P^A`. -/
theorem exists_ext_NPA_subset_P :
    ∃ (A : Oracle) (Ã : AlgOracle), IsExtension A Ã ∧ NPA Ã ⊆ P A := by
  obtain ⟨e, he⟩ := exists_surjective_nat (Prog × ℕ)
  let A := oracleT (fun O => toOracle (mle O)) e
  exact ⟨A, mle A, isExtension_mle A,
    NP_subset_P_oracleT (fun O => toOracle (mle O)) e isLocal_toOracle_mle he⟩

end Pnp.Algebrize
