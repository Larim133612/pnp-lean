import Pnp.Karp.BinPackUVer
import Pnp.Karp.ThreePartUNP

/-!
# Unary BIN PACKING ∈ NP (official definition)

The checking relation is `bpuv_vres w y = true` (`Pnp/Karp/BinPackUVer.lean`).  As for binary
BIN PACKING (`Pnp/Karp/BinPackingNP.lean`), with the unary sums `tpuv_s` / `tpuv_ls`
(`Pnp/Karp/ThreePartUNP.lean`):

* `bpuv_fwd`: the certificate `bpv_cert` of a packing is accepted;
* `bpuv_bwd`: an accepted certificate yields a packing (`bpv_lab`);
* `bpuv_lang_iff`: `UBPLang w ↔ ∃ y, |y| ≤ |w|² ∧ bpuv_vres w y`;
* `ubp_in_np`: `UBPLang ∈ NP`.
-/

namespace Pnp.Karp.BinPackU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.BinPacking Pnp.Karp.ThreePart
  Pnp.Karp.ThreePartU

/-! ## Packing → certificate -/

theorem bpuv_fwd (c : ℕ) : ∀ (k b₀ : ℕ) (L : List (List SatSym × ℕ)),
    (∀ p ∈ L, b₀ ≤ p.2 ∧ p.2 < b₀ + k) →
    (∀ b, b₀ ≤ b → b < b₀ + k → tpuv_ls L b ≤ c) →
    bpuv_go c k (L.map Prod.fst) (bpv_cert b₀ k L) = true
  | 0, b₀, L, h1, _ => by
    rcases L with _ | ⟨p, L⟩
    · simp [bpuv_go]
    · have := h1 p (by simp); omega
  | k + 1, b₀, L, h1, h2 => by
    simp only [bpuv_go, bpv_cert, Bool.and_eq_true]
    rw [bpv_U_cert, bpv_rest_cert]
    refine ⟨?_, bpuv_fwd c k (b₀ + 1) _ ?_ ?_⟩
    · rw [decide_eq_true_eq, tpuv_sel_cert]
      exact h2 b₀ le_rfl (by omega)
    · intro p hp
      simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hp
      have := h1 p hp.1
      omega
    · intro b hb1 hb2
      rw [tpuv_ls_filter b₀ L b (by omega)]
      exact h2 b (by omega) (by omega)

/-! ## Certificate → packing -/

theorem bpuv_bwd (c : ℕ) : ∀ (k : ℕ) (rows : List (List SatSym)) (R : Str),
    bpuv_go c k rows R = true →
    ∃ L : List (List SatSym × ℕ), L.map Prod.fst = rows ∧ (∀ p ∈ L, p.2 < k) ∧
      ∀ b < k, tpuv_ls L b ≤ c
  | 0, rows, R, h => by
    have : rows = [] := by simpa [bpuv_go] using h
    subst this
    exact ⟨[], rfl, by simp, fun b hb => by omega⟩
  | k + 1, rows, R, h => by
    simp only [bpuv_go, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨L', h1, h2, h3⟩ := bpuv_bwd c k _ _ h.2
    obtain ⟨g1, g2, -, -⟩ := bpv_lab_spec k rows R L' h1 h2
    obtain ⟨g3, g4⟩ := tpuv_lab_ls rows R L' h1
    refine ⟨_, g1, g2, fun b hb => ?_⟩
    rcases b with _ | b
    · rw [g3]; exact h.1
    · rw [g4]; exact h3 b (by omega)

/-! ## The language -/

theorem bpuv_vres_iff (w : List SatSym) (y : Str) :
    bpuv_vres w y = true ↔ ∃ items C kr, clauses w = items ++ [C, kr] ∧
      bpuv_go C.length kr.length items y = true := by
  unfold bpuv_vres
  have key : ∀ items C kr, clauses w = items ++ [C, kr] →
      (clauses w).reverse = kr :: C :: items.reverse := by
    intro items C kr h; rw [h]; simp
  rcases h : (clauses w).reverse with _ | ⟨kr, _ | ⟨C, rr⟩⟩
  · simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro items C kr hc; rw [key items C kr hc] at h; simp at h
  · simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro items C kr hc; rw [key items C kr hc] at h; simp at h
  · constructor
    · intro hg
      exact ⟨rr.reverse, C, kr, by rw [← List.reverse_reverse (clauses w), h]; simp, hg⟩
    · rintro ⟨items, C', kr', hc, hg⟩
      rw [key items C' kr' hc] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simpa using hg

theorem bpuv_lang_iff (w : List SatSym) :
    UBPLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ bpuv_vres w y = true := by
  constructor
  · rintro ⟨items, C, kr, hc, f, hf, hb⟩
    set L := bpv_labF items f
    refine ⟨bpv_cert 0 kr.length L, ?_, (bpuv_vres_iff w _).2 ⟨items, C, kr, hc, ?_⟩⟩
    · have h1 := bpv_cert_length kr.length 0 L
      have hL : L.length = items.length := by
        rw [← List.length_map (f := Prod.fst), bpv_labF_fst]
      have h2 := length_clauses_le w
      have h3 := sum_length_le (clauses w)
      have h4 := length_trunc_le w
      have hkr : kr.length ≤ ((clauses w).map List.length).sum :=
        List.le_sum_of_mem (List.mem_map_of_mem (by rw [hc]; simp))
      rw [hc] at h2
      simp only [List.length_append, List.length_cons, List.length_nil] at h2
      unfold trunc at h4
      have : kr.length * L.length ≤ w.length * w.length :=
        Nat.mul_le_mul (by omega) (by omega)
      rw [pow_two]; omega
    · have := bpuv_fwd C.length kr.length 0 L
        (fun p hp => ⟨Nat.zero_le _, by simpa using bpv_labF_lt _ items f hf p hp⟩)
        (fun b _ hb' => by
          rw [← tpuv_unSum_labF]; exact hb b (by omega))
      rwa [bpv_labF_fst] at this
  · rintro ⟨y, -, hy⟩
    obtain ⟨items, C, kr, hc, hg⟩ := (bpuv_vres_iff w y).1 hy
    obtain ⟨L, h1, h2, h3⟩ := bpuv_bwd C.length kr.length items y hg
    subst h1
    refine ⟨L.map Prod.fst, C, kr, hc, fun i => (L.getD i ([], 0)).2, ?_, ?_⟩
    · intro i hi
      rw [List.length_map] at hi
      show (L.getD i ([], 0)).2 < _
      rw [List.getD_eq_getElem _ _ hi]
      exact h2 _ (List.getElem_mem hi)
    · intro b hb
      rw [tpuv_unSum_labF, bpv_labF_getD]
      exact h3 b hb

/-! ## Transfer to the official class -/

/-- **Unary BIN PACKING ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem ubp_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      UBPLang := by
  classical
  have hrun := fun z => ((bpuv_exec_ver z).mono (bpv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg bpuv_ver) (tb 8 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg bpuv_ver, 8, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => bpuv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => bpuv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [bpuv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.BinPackU
