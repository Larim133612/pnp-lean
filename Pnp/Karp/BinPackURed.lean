import Pnp.Karp.BinPackU
import Pnp.Karp.ThreePartUWf
import Pnp.Karp.ThreePartUTotal

/-!
# Unary BIN PACKING: correctness of the reduction from unary 3-PARTITION

* `bpr_sum_bins`: the bin sums of an assignment into `k` bins add up to the total size;
* `bpr_of_tpu`: a unary 3-PARTITION solution of `u` is a packing of `bpuT u` (`m` bins of
  capacity `B`);
* `bpr_tpu_of`: for the instances `TPUI w` (total size exactly `m B`, `tpu_total`) a packing
  into `m` bins of capacity `B` fills every bin exactly, i.e. it is a 3-partition;
* `sat_iff_bpu`: `SATLang w ↔ UBPLang (BPUI w)`.
-/

namespace Pnp.Karp.BinPackU

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM Pnp.Karp.ThreePart Pnp.Karp.ThreePartU

theorem bpr_ite_sum (a x : ℕ) : ∀ k : ℕ,
    ((List.range k).map fun b => if x = b then a else 0).sum = if x < k then a else 0
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, bpr_ite_sum a x k]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases h1 : x < k
    · have h2 : x ≠ k := by omega
      simp [h1, h2, show x < k + 1 by omega]
    · by_cases h2 : x = k
      · simp [h2]
      · simp [h1, h2, show ¬ x < k + 1 by omega]

/-- The bin sums add up to the total size. -/
theorem bpr_sum_bins (k : ℕ) : ∀ (items : List (List SatSym)) (f : ℕ → ℕ),
    (∀ i < items.length, f i < k) →
    ((List.range k).map (unSum items f)).sum = (items.map List.length).sum
  | [], f, _ => by simp [unSum]
  | r :: rs, f, hf => by
    have h0 := hf 0 (by simp)
    have ih := bpr_sum_bins k rs (fun i => f (i + 1)) fun i hi => hf (i + 1) (by simpa using hi)
    simp only [unSum]
    rw [List.sum_map_add, ih, bpr_ite_sum, if_pos h0, List.map_cons, List.sum_cons]

/-- Bins of capacity `B` whose sizes add up to `m B` are all full. -/
theorem bpr_full (g : ℕ → ℕ) (B : ℕ) : ∀ m : ℕ, (∀ b < m, g b ≤ B) →
    ((List.range m).map g).sum ≤ m * B ∧
      (((List.range m).map g).sum = m * B → ∀ b < m, g b = B)
  | 0, _ => by simp
  | m + 1, h => by
    obtain ⟨ih1, ih2⟩ := bpr_full g B m fun b hb => h b (by omega)
    have hm := h m (by omega)
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    refine ⟨by rw [add_mul, one_mul]; omega, fun hs b hb => ?_⟩
    rw [add_mul, one_mul] at hs
    rcases (show b < m ∨ b = m by omega) with hb' | rfl
    · exact ih2 (by omega) b hb'
    · omega

theorem bpr_clauses (u : List SatSym) :
    clauses (bpuT u) = clauses u ++ [uRow ((clauses u).length / 3)] := by
  unfold bpuT
  apply clauses_flatMap
  intro r hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · exact sep_not_mem_clauses u r hr
  · exact tpu_sep_nmem _

/-- A unary 3-PARTITION solution is a packing into `m` bins of capacity `B`. -/
theorem bpr_of_tpu (u : List SatSym) (h : TPULang u) : UBPLang (bpuT u) := by
  obtain ⟨items, Bv, hc, hmod, -, f, hf, hg⟩ := h
  refine ⟨items, Bv, uRow ((clauses u).length / 3), ?_, f, ?_, ?_⟩
  · rw [bpr_clauses, hc]; simp
  · intro i hi
    rw [tpu_uRow_len, hc, List.length_append, List.length_singleton]
    have := hf i hi; omega
  · intro b hb
    rw [tpu_uRow_len, hc, List.length_append, List.length_singleton] at hb
    rw [hg b (by omega)]

/-- A packing into `m` bins of capacity `B` of an instance of total size `m B` (sizes strictly
between `B / 4` and `B / 2`) is a 3-partition. -/
theorem bpr_tpu_gen (u : List SatSym) (I : List (List SatSym)) (Bv : List SatSym)
    (hcl : clauses u = I ++ [Bv]) (hmod : I.length % 3 = 0)
    (hbd : ∀ r ∈ I, Bv.length < 4 * r.length ∧ 2 * r.length < Bv.length)
    (htot : (I.map List.length).sum = I.length / 3 * Bv.length) (h : UBPLang (bpuT u)) :
    TPULang u := by
  obtain ⟨items, C, kr, hc, f, hf, hb⟩ := h
  rw [bpr_clauses, hcl, List.append_assoc, List.singleton_append] at hc
  obtain ⟨hi, hc2⟩ := List.append_inj' hc (by simp)
  simp only [List.cons.injEq, and_true] at hc2
  obtain ⟨hC, hkr⟩ := hc2
  subst hi hC hkr
  have hk : (uRow ((I ++ [Bv]).length / 3)).length = I.length / 3 := by
    rw [tpu_uRow_len, List.length_append, List.length_singleton]; omega
  rw [hk] at hf hb
  refine ⟨I, Bv, hcl, hmod, hbd, f, hf, ?_⟩
  have hsum := bpr_sum_bins _ I f hf
  rw [htot] at hsum
  exact (bpr_full _ _ _ hb).2 hsum

/-- For the instances `TPUI w`, a packing of `BPUI w` is a 3-partition. -/
theorem bpr_tpu_of (w : List SatSym) (h : UBPLang (BPUI w)) : TPULang (TPUI w) := by
  obtain ⟨hcl, hmod, hbd⟩ := tpui_wf w
  have htot := tpu_total (qB w) (tris w) (dr_tris_lt w)
  have hE := tpf_len_els (qB w) (tris w)
  refine bpr_tpu_gen _ _ _ hcl (by simpa using hmod) ?_ ?_ h
  · intro r hr
    simp only [List.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    rw [tpu_uRow_len, tpu_uRow_len]
    exact hbd x hx
  · simp only [List.map_map, Function.comp_def, List.length_map, tpu_uRow_len]
    rw [show (els (qB w) (tris w)).length / 3 = 4 * (tris w).length + 3 * qB w by omega, ← htot]

/-- **Unary BIN PACKING**: the reduction is correct. -/
theorem sat_iff_bpu (w : List SatSym) : SATLang w ↔ UBPLang (BPUI w) := by
  rw [sat_iff_tpu]
  exact ⟨bpr_of_tpu _, bpr_tpu_of w⟩

end Pnp.Karp.BinPackU
