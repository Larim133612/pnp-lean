import Pnp.Karp.ThreePartUArith
import Pnp.Karp.ThreePartRed

/-!
# Unary 3-PARTITION: correctness of the reduction instance

`sat_iff_tpu`: a formula `w` is satisfiable iff `TPUI w ∈ TPULang`.  The proofs are those of
M63 (`tp_of_cov`, `cov_of_tp`) with the binary values replaced by the unary ones; the group
structure is the same (`tpf_P1`–`tpf_P3`, `tpb_core`) because the rigidity `tpu_sum_iff` gives
the same intended groups `IsPat`.
-/

namespace Pnp.Karp.ThreePartU

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

theorem tpu_uRow_len (n : ℕ) : (uRow n).length = n := by simp [uRow]

theorem tpu_sep_nmem (n : ℕ) : sep ∉ uRow n := by simp [uRow]

theorem tpu_of_cov (q : ℕ) (hq : 2 ≤ q) (ts : List (ℕ × ℕ × ℕ))
    (hts : ∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (y : List Bool)
    (hy : ∀ p < 3 * q, covT q ts y p = 1) : TPULang (TPUW q ts) := by
  have hqM : q ≤ mT q ts := by unfold mT; omega
  have hgm : ∀ l < ts.length, ts.getD l (0, 0, 0) ∈ ts := fun l hl => by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _
  have hcr : ∀ l < ts.length, ∀ c < 3, crd (ts.getD l (0, 0, 0)) c < q := by
    intro l hl c hc
    have := hts _ (hgm l hl)
    interval_cases c <;> simp only [crd] <;> omega
  have hex : ∀ c < 3, ∀ e < q, ∃ l, l < ts.length ∧ y.getD l false = true ∧
      crd (ts.getD l (0, 0, 0)) c = e ∧ ∀ l' < ts.length, y.getD l' false = true →
        crd (ts.getD l' (0, 0, 0)) c = e → l' = l := by
    intro c hc e he
    have hc3 : c * q + e < 3 * q := by interval_cases c <;> omega
    obtain ⟨l, hl, hs, hp, hu⟩ := tpf_cov_one q _ ts y (hy _ hc3)
    have key : ∀ l' < ts.length, (c * q + e = (ts.getD l' (0, 0, 0)).1 ∨
        c * q + e = q + (ts.getD l' (0, 0, 0)).2.1 ∨
        c * q + e = 2 * q + (ts.getD l' (0, 0, 0)).2.2) ↔ crd (ts.getD l' (0, 0, 0)) c = e := by
      intro l' hl'
      have := hts _ (hgm l' hl')
      interval_cases c <;> simp only [crd] <;> omega
    exact ⟨l, hl, hs, (key l hl).1 hp, fun l' hl' hs' hc' => hu l' hl' hs' ((key l' hl').2 hc')⟩
  choose! ch hch using hex
  have hch' : ∀ c < 3, ∀ e < q, ch c e < ts.length ∧ y.getD (ch c e) false = true ∧
      crd (ts.getD (ch c e) (0, 0, 0)) c = e :=
    fun c hc e he => ⟨(hch c hc e he).1, (hch c hc e he).2.1, (hch c hc e he).2.2.1⟩
  have hu : ∀ c < 3, ∀ l < ts.length, y.getD l false = true →
      ch c (crd (ts.getD l (0, 0, 0)) c) = l :=
    fun c hc l hl hs => ((hch c hc _ (hcr l hl c hc)).2.2.2 l hl hs rfl).symm
  have P1 := tpf_P1 q ts.length (fun l => y.getD l false)
    (fun l c => crd (ts.getD l (0, 0, 0)) c) ch hq hcr hch' hu
  have P2 := tpf_P2 q ts.length (fun l => y.getD l false)
    (fun l c => crd (ts.getD l (0, 0, 0)) c) ch hq hcr hch' hu
  have hlen := tpf_len_els q ts
  unfold TPULang TPUW
  refine ⟨(els q ts).map (fun x => uRow (uval q (mT q ts) x)), uRow (uB (mT q ts)), ?_, ?_, ?_,
    tpf_f q ts.length (fun l => y.getD l false) (fun l c => crd (ts.getD l (0, 0, 0)) c) ch,
    ?_, ?_⟩
  · rw [clauses_flatMap]
    intro r hr
    rw [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨x, -, hx⟩ | hx
    · rw [← hx]; exact tpu_sep_nmem _
    · rw [hx]; exact tpu_sep_nmem _
  · rw [List.length_map, hlen]; omega
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    simpa [uRow] using tpu_el_bounds q _ hqM x (tpf_ok q hq ts hts x hx)
  · intro i hi
    rw [List.length_map, hlen] at hi ⊢
    have := (P1 i hi).1
    omega
  · intro g hg
    rw [List.length_map, hlen] at hg
    have hg' : g < 4 * ts.length + 3 * q := by omega
    rw [tpu_unSum_eq, List.length_map, hlen]
    obtain ⟨hnd, hmem⟩ := P2 g hg'
    have hperm : ((List.range (12 * ts.length + 9 * q)).filter fun i => decide
        (tpf_f q ts.length (fun l => y.getD l false) (fun l c => crd (ts.getD l (0, 0, 0)) c) ch i
          = g)).Perm (tpf_idx q ts.length (fun l => y.getD l false)
            (fun l c => crd (ts.getD l (0, 0, 0)) c) ch g) :=
      (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnd).mpr (by
      intro i
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨hi, rfl⟩; exact (P1 i hi).2
      · intro h; exact hmem i h)
    rw [(hperm.map _).sum_eq]
    rw [show ((tpf_idx q ts.length (fun l => y.getD l false)
        (fun l c => crd (ts.getD l (0, 0, 0)) c) ch g).map
          fun i => (((els q ts).map (fun x => uRow (uval q (mT q ts) x))).getD i []).length) =
        (((tpf_idx q ts.length (fun l => y.getD l false)
          (fun l c => crd (ts.getD l (0, 0, 0)) c) ch g).map
          fun i => (els q ts).getD i (El.cp 0 0 false)).map
            fun x => uval q (mT q ts) x) from by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      have hi' := (hmem i hi).1
      simp only [Function.comp]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hlen]; exact hi'),
        List.getElem_map, List.getD_eq_getElem _ _ (by rw [hlen]; exact hi'), tpu_uRow_len]]
    rw [tpu_uRow_len, tpu_sum_iff q _ hq hqM _ ?_]
    · exact tpf_P3 q hq ts y ch hcr hch' _ g hg'
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine tpf_ok q hq ts hts _ ?_
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact (hmem i hi).1)]
      exact List.getElem_mem _

theorem cov_of_tpu (q : ℕ) (hq : 2 ≤ q) (ts : List (ℕ × ℕ × ℕ))
    (hts : ∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (h : TPULang (TPUW q ts)) :
    ∃ y : List Bool, ∀ p < 3 * q, covT q ts y p = 1 := by
  have hqM : q ≤ mT q ts := by unfold mT; omega
  obtain ⟨items, Bv, hc, -, -, f, hf, hsum⟩ := h
  have hn := tpb_len q ts
  have hcl : clauses (TPUW q ts) = (els q ts).map (fun x => uRow (uval q (mT q ts) x)) ++ [uRow (uB (mT q ts))] := by
    unfold TPUW
    apply clauses_flatMap
    intro r hr
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨x, -, hx⟩ | hx
    · rw [← hx]; exact tpu_sep_nmem _
    · rw [hx]; exact tpu_sep_nmem _
  rw [hcl] at hc
  have hij := List.append_inj' hc.symm (by rw [List.length_singleton, List.length_singleton])
  have hi : items = (els q ts).map (fun x => uRow (uval q (mT q ts) x)) := hij.1
  have hBv : Bv = uRow (uB (mT q ts)) := (List.cons.inj hij.2).1
  subst hi
  rw [hBv, tpu_uRow_len] at hsum
  rw [List.length_map] at hf hsum
  refine tpb_core q hq ts hts f fun j hj => ?_
  have hg := hf j (by omega)
  have hs := hsum _ hg
  rw [tpu_unSum_eq, List.length_map] at hs
  refine (tpu_sum_iff q (mT q ts) hq hqM _ fun x hx => ?_).1 ?_
  · obtain ⟨k, hk, -, rfl⟩ := tpb_mem_G.1 hx
    exact tpb_ok q (by omega) ts hts _ (by omega)
  · rw [← hs, tpb_G, List.map_map]
    refine congrArg List.sum ?_
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_filter, List.mem_range] at hi
    simp [List.getD_eq_getElem?_getD, hi.1, Function.comp, tpu_uRow_len]


theorem tpu_empty (q : ℕ) (hq : q = 0) : TPULang (TPUW q []) := by
  subst hq
  refine ⟨[], uRow (uB (mT 0 [])), ?_, rfl, by simp, fun _ => 0, by simp, by simp⟩
  have : els 0 [] = [] := by simp [els]
  simp only [TPUW, this, List.map_nil, List.nil_append]
  rw [clauses_flatMap]
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  simp [uRow]

theorem sat_iff_tpu (w : List SatSym) : SATLang w ↔ TPULang (TPUI w) := by
  rw [sat_iff_covT]
  by_cases hm : mC w = 0
  · have hq : qB w = 0 := by simp [qB, hm]
    have ht : tris w = [] := by simp [tris, hm, hq]
    unfold TPUI
    rw [ht]
    simp only [hq, Nat.mul_zero, Nat.not_lt_zero, false_imp_iff,
      implies_true, exists_const, true_iff]
    exact tpu_empty 0 rfl
  · have hN : 1 ≤ NV w := by unfold NV; omega
    have hq : 2 ≤ qB w := by
      unfold qB
      rw [Nat.mul_assoc]
      have : 1 ≤ NV w * mC w := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hm)
      omega
    exact ⟨fun ⟨y, hy⟩ => tpu_of_cov _ hq _ (dr_tris_lt w) y hy,
      fun h => cov_of_tpu _ hq _ (dr_tris_lt w) h⟩

end Pnp.Karp.ThreePartU
