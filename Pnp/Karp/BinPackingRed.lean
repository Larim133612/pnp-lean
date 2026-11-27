import Pnp.Karp.BinPacking
import Pnp.Karp.PartRed

/-!
# BIN PACKING: correctness of the reduction from PARTITION

`part_iff_bp`: a PARTITION instance `w` is a yes-instance iff its BIN PACKING instance
`BPI w` (items `clauses w`, capacity `⌊T / 2⌋`, two bins) is one.
-/

namespace Pnp.Karp.BinPacking

open Pnp.Relativize Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.Partition

theorem bpr_bv_tail (r : List SatSym) : bv r.tail = bv r / 2 := by
  cases r with
  | nil => rfl
  | cons s r => simp only [List.tail_cons, bv]; split_ifs <;> omega

theorem bpr_sel_bin : ∀ (rs : List (List SatSym)) (f : ℕ → ℕ) (y : List Bool),
    (∀ i < rs.length, y.getD i false = decide (f i = 0)) → selSum rs y = binSum rs f 0
  | [], _, _, _ => rfl
  | r :: rs, f, y, h => by
    have ih := bpr_sel_bin rs (fun i => f (i + 1)) y.tail (by
      intro i hi
      have := h (i + 1) (by simp; omega)
      cases y <;> simpa using this)
    have h0 := h 0 (by simp)
    simp only [selSum, binSum, ih]
    congr 1
    cases y with
    | nil => simp at h0; simp [h0]
    | cons b y =>
      simp at h0 ⊢
      cases b <;> simp at h0 ⊢ <;> simp [h0]

theorem bpr_bin_add : ∀ (rs : List (List SatSym)) (f : ℕ → ℕ),
    (∀ i < rs.length, f i < 2) → binSum rs f 0 + binSum rs f 1 = totSum rs
  | [], _, _ => rfl
  | r :: rs, f, h => by
    have ih := bpr_bin_add rs (fun i => f (i + 1)) (fun i hi => h (i + 1) (by simp; omega))
    have h0 := h 0 (by simp)
    simp only [binSum, totSum]
    rcases (by omega : f 0 = 0 ∨ f 0 = 1) with e | e <;> simp [e] <;> omega

/-- **Correctness of the reduction** PARTITION → BIN PACKING. -/
theorem part_iff_bp (w : List SatSym) : PartLang w ↔ BPLang (BPI w) := by
  unfold PartLang BPLang BPI
  set rs := clauses w with hrs
  have hsep : ∀ c ∈ rs ++ [(toRow (accRows [] rs)).tail, [zero, zero]], sep ∉ c := by
    intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | rfl | rfl
    · exact sep_not_mem_clauses w c hc
    · exact fun h => pr_sep_toRow _ (List.mem_of_mem_tail h)
    · simp
  rw [clauses_flatMap _ hsep]
  have hC : bv (toRow (accRows [] rs)).tail = totSum rs / 2 := by
    rw [bpr_bv_tail, pr_bv_toRow, pr_bval_acc]; simp [sv_bval]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨rs, _, _, rfl, fun i => if y.getD i false then 0 else 1, ?_, ?_⟩
    · intro i _; simp only [List.length_cons, List.length_nil]; split_ifs <;> omega
    · have hs := bpr_sel_bin rs (fun i => if y.getD i false then 0 else 1) y (by
        intro i _; cases y.getD i false <;> simp)
      have ha := bpr_bin_add rs (fun i => if y.getD i false then 0 else 1) (by
        intro i _; split_ifs <;> omega)
      intro b hb
      simp only [List.length_cons, List.length_nil] at hb
      rw [hC]
      rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> omega
  · rintro ⟨items, C, kr, h, f, hf, hb⟩
    have h' := List.append_inj' h.symm (by simp)
    obtain ⟨h1, h2⟩ := h'
    subst h1
    injection h2 with h3 h4
    injection h4 with h4 _
    subst h3; subst h4
    simp only [List.length_cons, List.length_nil] at hf hb
    have ha := bpr_bin_add rs f hf
    have b0 := hb 0 (by omega)
    have b1 := hb 1 (by omega)
    rw [hC] at b0 b1
    refine ⟨(List.range rs.length).map (fun i => decide (f i = 0)), ?_⟩
    rw [bpr_sel_bin rs f _ (by intro i hi; simp [hi])]
    omega

end Pnp.Karp.BinPacking
