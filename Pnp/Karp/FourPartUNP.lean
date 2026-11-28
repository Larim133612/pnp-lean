import Pnp.Karp.FourPartUVer
import Pnp.Karp.ThreePartUNP

/-!
# Unary 4-PARTITION ∈ NP (official definition)

The checking relation is `fpuv_vres w y = true` (`Pnp/Karp/FourPartUVer.lean`).  As for unary
3-PARTITION (`Pnp/Karp/ThreePartUNP.lean`, whose labelled-list lemmas `tpuv_ls`, `tpuv_sel_cert`,
`tpuv_ls_filter`, `tpuv_lab_ls`, `tpuv_unSum_labF` are reused), with four marks per group:

* `fpuv_fwd`: the certificate `bpv_cert` of a grouping into `m` groups of sum `B` is accepted
  with `4 m` marks;
* `fpuv_bwd`: an accepted certificate with `k` marks gives `4 ∣ k` and a grouping into `k / 4`
  groups of sum `B`;
* `fpuv_bnd_iff`: the bounds loop checks `B < 5 a ∧ 3 a < B` for every item;
* `fpuv_lang_iff`: `FPULang w ↔ ∃ y, |y| ≤ |w|² ∧ fpuv_vres w y`;
* `fpu_in_np`: `FPULang ∈ NP`, via `fpuv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.FourPartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.BinPacking Pnp.Karp.ThreePart Pnp.Karp.ThreePartU

/-! ## The bound check -/

theorem fpuv_bnd_iff (c : ℕ) : ∀ rows : List (List SatSym),
    fpuv_bnd c rows = true ↔ ∀ r ∈ rows, c < 5 * r.length ∧ 3 * r.length < c
  | [] => by simp [fpuv_bnd]
  | r :: rs => by
    simp only [fpuv_bnd, Bool.and_eq_true, decide_eq_true_eq, fpuv_bnd_iff c rs, List.mem_cons,
      forall_eq_or_imp]

/-! ## Grouping → certificate -/

theorem fpuv_fwd (c : ℕ) : ∀ (m b₀ : ℕ) (L : List (List SatSym × ℕ)),
    (∀ p ∈ L, b₀ ≤ p.2 ∧ p.2 < b₀ + m) →
    (∀ b, b₀ ≤ b → b < b₀ + m → tpuv_ls L b = c) →
    fpuv_go c (4 * m) (L.map Prod.fst) (bpv_cert b₀ m L) = true
  | 0, b₀, L, h1, _ => by
    rcases L with _ | ⟨p, L⟩
    · simp [fpuv_go]
    · have := h1 p (by simp); omega
  | m + 1, b₀, L, h1, h2 => by
    rw [show 4 * (m + 1) = 4 * m + 4 by ring]
    simp only [fpuv_go, bpv_cert]
    rw [Bool.and_eq_true, bpv_U_cert, bpv_rest_cert]
    refine ⟨?_, fpuv_fwd c m (b₀ + 1) _ ?_ ?_⟩
    · rw [decide_eq_true_eq, tpuv_sel_cert]
      exact h2 b₀ le_rfl (by omega)
    · intro p hp
      simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hp
      have := h1 p hp.1
      omega
    · intro b hb1 hb2
      rw [tpuv_ls_filter b₀ L b (by omega)]
      exact h2 b (by omega) (by omega)

/-! ## Certificate → grouping -/

theorem fpuv_bwd (c : ℕ) : ∀ (k : ℕ) (rows : List (List SatSym)) (R : Str),
    fpuv_go c k rows R = true → k % 4 = 0 ∧
    ∃ L : List (List SatSym × ℕ), L.map Prod.fst = rows ∧ (∀ p ∈ L, p.2 < k / 4) ∧
      ∀ b < k / 4, tpuv_ls L b = c
  | 0, rows, R, h => by
    have : rows = [] := by simpa [fpuv_go] using h
    subst this
    exact ⟨rfl, [], rfl, by simp, fun b hb => by omega⟩
  | 1, rows, R, h => by simp [fpuv_go] at h
  | 2, rows, R, h => by simp [fpuv_go] at h
  | 3, rows, R, h => by simp [fpuv_go] at h
  | k + 4, rows, R, h => by
    simp only [fpuv_go, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hk, L', h1, h2, h3⟩ := fpuv_bwd c k _ _ h.2
    have hk3 : (k + 4) / 4 = k / 4 + 1 := by omega
    obtain ⟨g1, g2, -, -⟩ := bpv_lab_spec (k / 4) rows R L' h1 h2
    obtain ⟨g3, g4⟩ := tpuv_lab_ls rows R L' h1
    refine ⟨by omega, _, g1, by rw [hk3]; exact g2, fun b hb => ?_⟩
    rw [hk3] at hb
    rcases b with _ | b
    · rw [g3]; exact h.1
    · rw [g4]; exact h3 b (by omega)

/-! ## The language -/

theorem fpuv_vres_iff (w : List SatSym) (y : Str) :
    fpuv_vres w y = true ↔ ∃ items Bv, clauses w = items ++ [Bv] ∧
      fpuv_bnd Bv.length items = true ∧ fpuv_go Bv.length items.length items y = true := by
  unfold fpuv_vres
  have key : ∀ items Bv, clauses w = items ++ [Bv] →
      (clauses w).reverse = Bv :: items.reverse := by
    intro items Bv h; rw [h]; simp
  rcases h : (clauses w).reverse with _ | ⟨Bv, rr⟩
  · simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro items Bv hc; rw [key items Bv hc] at h; simp at h
  · constructor
    · intro hg
      rw [Bool.and_eq_true] at hg
      exact ⟨rr.reverse, Bv, by rw [← List.reverse_reverse (clauses w), h]; simp, hg⟩
    · rintro ⟨items, Bv', hc, hb, hg⟩
      rw [key items Bv' hc] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hb, hg]

theorem fpuv_lang_iff (w : List SatSym) :
    FPULang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ fpuv_vres w y = true := by
  constructor
  · rintro ⟨items, Bv, hc, h3, hb, f, hf, hs⟩
    set L := bpv_labF items f
    set m := items.length / 4
    have hL : L.length = items.length := by
      rw [← List.length_map (f := Prod.fst), bpv_labF_fst]
    refine ⟨bpv_cert 0 m L, ?_, (fpuv_vres_iff w _).2 ⟨items, Bv, hc, ?_, ?_⟩⟩
    · have h1 := bpv_cert_length m 0 L
      have h2 := length_clauses_le w
      rw [hc] at h2
      simp only [List.length_append, List.length_cons, List.length_nil] at h2
      have : m * L.length ≤ w.length * w.length :=
        Nat.mul_le_mul (by omega) (by omega)
      rw [pow_two]; omega
    · rw [fpuv_bnd_iff]
      exact hb
    · have hn : items.length = 4 * m := by omega
      have := fpuv_fwd Bv.length m 0 L
        (fun p hp => ⟨Nat.zero_le _, by simpa using bpv_labF_lt _ items f hf p hp⟩)
        (fun b _ hb' => by
          rw [← tpuv_unSum_labF]; exact hs b (by omega))
      rwa [bpv_labF_fst, ← hn] at this
  · rintro ⟨y, -, hy⟩
    obtain ⟨items, Bv, hc, hb, hg⟩ := (fpuv_vres_iff w y).1 hy
    obtain ⟨h3, L, h1, h2, hs⟩ := fpuv_bwd Bv.length items.length items y hg
    rw [fpuv_bnd_iff] at hb
    subst h1
    refine ⟨L.map Prod.fst, Bv, hc, h3, hb, fun i => (L.getD i ([], 0)).2, ?_, ?_⟩
    · intro i hi
      have hi' : i < L.length := by simpa using hi
      show (L.getD i ([], 0)).2 < _
      rw [List.getD_eq_getElem _ _ hi']
      exact h2 _ (List.getElem_mem hi')
    · intro b hb'
      rw [tpuv_unSum_labF, bpv_labF_getD]
      exact hs b hb'

/-! ## Transfer to the official class -/

/-- **Unary 4-PARTITION ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem fpu_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      FPULang := by
  classical
  have hrun := fun z => ((fpuv_exec_ver z).mono (fpuv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg fpuv_ver) (tb 9 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg fpuv_ver, 9, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => fpuv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => fpuv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [fpuv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.FourPartU
