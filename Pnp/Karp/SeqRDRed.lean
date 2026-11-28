import Pnp.Karp.SeqRD
import Pnp.Karp.BinPackURed
import Pnp.Karp.ThreePartUArith

/-!
# Unary SEQUENCING WITH RELEASE TIMES AND DEADLINES: correctness of the reduction

* `srr_fwd`: a packing of the items into `m` bins of capacity `B` gives a schedule (items of
  bin `g` run back to back from `g (B + 1)`, separator `j` at `(j + 1) (B + 1) - 1`);
* `srr_bwd`: in a schedule the separators are forced, every item lies in a window
  `[g (B + 1), g (B + 1) + B)`, and disjoint intervals in a window have total length `≤ B`;
* `srr_gen`: `UBPLang (bpuT u) ↔ SRDLang (srdT u)` for `clauses u = items ++ [Bv]`, `3 ∣ |items|`;
* `sat_iff_srd`: `SATLang w ↔ SRDLang (SRDI w)`.
-/
namespace Pnp.Karp.SeqRD

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.ThreePartU Pnp.Karp.BinPackU

/-- The total size of the items `i < k` of group `g`. -/
def srr_ps (f : ℕ → ℕ) (g : ℕ) (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  (((List.range k).filter fun i => f i = g).map a).sum

theorem srr_ps_succ (f : ℕ → ℕ) (g : ℕ) (a : ℕ → ℕ) (k : ℕ) :
    srr_ps f g a (k + 1) = srr_ps f g a k + if f k = g then a k else 0 := by
  unfold srr_ps
  rw [List.range_succ, List.filter_append]
  by_cases h : f k = g <;> simp [h]

theorem srr_ps_mono (f : ℕ → ℕ) (g : ℕ) (a : ℕ → ℕ) {k l : ℕ} (h : k ≤ l) :
    srr_ps f g a k ≤ srr_ps f g a l := by
  induction l, h using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => rw [srr_ps_succ]; omega

theorem srr_ps_fin (f : ℕ → ℕ) (g : ℕ) (a : ℕ → ℕ) : ∀ k : ℕ,
    srr_ps f g a k = ∑ i ∈ (Finset.range k).filter (fun i => f i = g), a i
  | 0 => by simp [srr_ps]
  | k + 1 => by
    rw [srr_ps_succ, srr_ps_fin f g a k, Finset.range_add_one, Finset.filter_insert]
    by_cases h : f k = g
    · rw [if_pos h, if_pos h, Finset.sum_insert (by simp), add_comm]
    · rw [if_neg h, if_neg h, add_zero]

/-- Pairwise disjoint intervals `[s i, s i + a i)` inside `[lo, lo + B)` have total length
at most `B`. -/
theorem srr_disj_sum (S : Finset ℕ) (s a : ℕ → ℕ) (lo B : ℕ)
    (hin : ∀ i ∈ S, lo ≤ s i ∧ s i + a i ≤ lo + B)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → s i + a i ≤ s j ∨ s j + a j ≤ s i) :
    ∑ i ∈ S, a i ≤ B := by
  have hc : (S.biUnion fun i => Finset.Ico (s i) (s i + a i)).card = ∑ i ∈ S, a i := by
    rw [Finset.card_biUnion]
    · simp
    · intro i hi j hj hij
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_Ico] at hx hx'
      rcases hd i hi j hj hij with h | h <;> omega
  have hsub : (S.biUnion fun i => Finset.Ico (s i) (s i + a i)) ⊆ Finset.Ico lo (lo + B) := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_Ico] at hx ⊢
    obtain ⟨i, hi, h1, h2⟩ := hx
    have := hin i hi
    omega
  have := Finset.card_le_card hsub
  rw [hc] at this
  simpa using this


/-- (→) A packing gives a schedule. -/
theorem srr_fwd (n m B : ℕ) (a f : ℕ → ℕ) (hf : ∀ i < n, f i < m)
    (hb : ∀ g < m, srr_ps f g a n ≤ B) (L R D : ℕ → ℕ)
    (hI : ∀ i < n, L i = a i ∧ R i = 0 ∧ D i = m * (B + 1) - 1)
    (hS : ∀ j < m - 1, L (n + j) = 1 ∧ R (n + j) = (j + 1) * (B + 1) - 1 ∧
      D (n + j) = (j + 1) * (B + 1)) :
    ∃ s : ℕ → ℕ, (∀ i < n + (m - 1), R i ≤ s i ∧ s i + L i ≤ D i) ∧
      ∀ i < n + (m - 1), ∀ j < n + (m - 1), i ≠ j → s i + L i ≤ s j ∨ s j + L j ≤ s i := by
  let s : ℕ → ℕ := fun i =>
    if i < n then f i * (B + 1) + srr_ps f (f i) a i else (i - n + 1) * (B + 1) - 1
  have hpre : ∀ i < n, srr_ps f (f i) a i + a i ≤ B := fun i hi => by
    have h1 := srr_ps_succ f (f i) a i
    rw [if_pos rfl] at h1
    have h2 := srr_ps_mono f (f i) a (show i + 1 ≤ n by omega)
    have := hb (f i) (hf i hi)
    omega
  -- products as atoms
  have hmul : ∀ x y : ℕ, x ≤ y → x * (B + 1) ≤ y * (B + 1) := fun x y h =>
    Nat.mul_le_mul_right _ h
  have hsucc : ∀ x : ℕ, (x + 1) * (B + 1) = x * (B + 1) + B + 1 := fun x => by ring
  have hitem : ∀ i < n, f i * (B + 1) ≤ s i ∧ s i + a i ≤ f i * (B + 1) + B := fun i hi => by
    have := hpre i hi
    simp only [s, if_pos hi]; omega
  have hsep : ∀ k < m - 1, s (n + k) = (k + 1) * (B + 1) - 1 := fun k _ => by
    simp only [s, if_neg (show ¬ n + k < n by omega)]
    congr 2; omega
  have key : ∀ i j, i < j → j < n + (m - 1) → s i + L i ≤ s j ∨ s j + L j ≤ s i := by
    intro i j hij hj
    by_cases hjn : j < n
    · have hin : i < n := by omega
      rw [(hI i hin).1, (hI j hjn).1]
      have ii := hitem i hin
      have jj := hitem j hjn
      rcases lt_trichotomy (f i) (f j) with h | h | h
      · left
        have := hmul (f i + 1) (f j) h
        rw [hsucc] at this; omega
      · left
        have h1 := srr_ps_succ f (f i) a i
        rw [if_pos rfl] at h1
        have h2 := srr_ps_mono f (f i) a (show i + 1 ≤ j by omega)
        have hpi := hpre i hin
        simp only [s, if_pos hin, if_pos hjn, ← h]
        omega
      · right
        have := hmul (f j + 1) (f i) h
        rw [hsucc] at this; omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = n + k := ⟨j - n, by omega⟩
      have hk : k < m - 1 := by omega
      rw [(hS k hk).1, hsep k hk]
      have h1 := hsucc k
      by_cases hin : i < n
      · rw [(hI i hin).1]
        have ii := hitem i hin
        by_cases hg : k + 1 ≤ f i
        · right
          have := hmul _ _ hg; omega
        · left
          have := hmul (f i + 1) (k + 1) (by omega)
          rw [hsucc] at this; omega
      · obtain ⟨k', rfl⟩ : ∃ k', i = n + k' := ⟨i - n, by omega⟩
        have hk' : k' < m - 1 := by omega
        rw [(hS k' hk').1, hsep k' hk']
        left
        have := hmul (k' + 1 + 1) (k + 1) (by omega)
        rw [hsucc (k' + 1)] at this
        have := hsucc k'
        omega
  refine ⟨s, fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · by_cases hin : i < n
    · obtain ⟨h1, h2, h3⟩ := hI i hin
      rw [h1, h2, h3]
      have := hitem i hin
      have := hmul (f i + 1) m (hf i hin)
      rw [hsucc] at this
      exact ⟨Nat.zero_le _, by omega⟩
    · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
      have hk : k < m - 1 := by omega
      obtain ⟨h1, h2, h3⟩ := hS k hk
      rw [h1, h2, h3, hsep k hk]
      have := hsucc k
      omega
  · rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h hj
    · exact (key j i h hi).symm


/-- (←) A schedule gives a packing. -/
theorem srr_bwd (n m B : ℕ) (a : ℕ → ℕ) (hm : n = 0 ∨ 1 ≤ m) (L R D : ℕ → ℕ)
    (hI : ∀ i < n, L i = a i ∧ R i = 0 ∧ D i = m * (B + 1) - 1)
    (hS : ∀ j < m - 1, L (n + j) = 1 ∧ R (n + j) = (j + 1) * (B + 1) - 1 ∧
      D (n + j) = (j + 1) * (B + 1)) (s : ℕ → ℕ)
    (hs1 : ∀ i < n + (m - 1), R i ≤ s i ∧ s i + L i ≤ D i)
    (hs2 : ∀ i < n + (m - 1), ∀ j < n + (m - 1), i ≠ j → s i + L i ≤ s j ∨ s j + L j ≤ s i) :
    ∃ f : ℕ → ℕ, (∀ i < n, f i < m) ∧ ∀ g < m, srr_ps f g a n ≤ B := by
  rcases hm with rfl | hm
  · exact ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _), fun g _ => by simp [srr_ps]⟩
  have hmul : ∀ x y : ℕ, x ≤ y → x * (B + 1) ≤ y * (B + 1) := fun x y h =>
    Nat.mul_le_mul_right _ h
  have hsucc : ∀ x : ℕ, (x + 1) * (B + 1) = x * (B + 1) + B + 1 := fun x => by ring
  have hsep : ∀ k < m - 1, s (n + k) = (k + 1) * (B + 1) - 1 := fun k hk => by
    have := hs1 (n + k) (by omega)
    obtain ⟨h1, h2, h3⟩ := hS k hk
    rw [h1, h2, h3] at this
    have := hsucc k
    omega
  have hitem : ∀ i < n, s i / (B + 1) < m ∧ s i / (B + 1) * (B + 1) ≤ s i ∧
      s i + a i ≤ s i / (B + 1) * (B + 1) + B := fun i hi => by
    have h0 := hs1 i (by omega)
    obtain ⟨h1, h2, h3⟩ := hI i hi
    rw [h1, h2, h3] at h0
    have hdm := Nat.div_add_mod (s i) (B + 1)
    have hlt := Nat.mod_lt (s i) (show 0 < B + 1 by omega)
    rw [mul_comm] at hdm
    generalize s i / (B + 1) = g at hdm ⊢
    generalize s i % (B + 1) = r at hdm hlt
    have hgm : g < m := by
      by_contra hc
      have := hmul m g (by omega)
      have := hmul 1 m hm
      omega
    refine ⟨hgm, by omega, ?_⟩
    by_contra hc
    have hgs := hsucc g
    by_cases hg : g < m - 1
    · have := hs2 i (by omega) (n + g) (by omega) (by omega)
      rw [hsep g hg, (hS g hg).1, h1] at this
      omega
    · have := hmul m (g + 1) (by omega)
      omega
  refine ⟨fun i => s i / (B + 1), fun i hi => (hitem i hi).1, fun g _ => ?_⟩
  rw [srr_ps_fin]
  refine srr_disj_sum _ s a (g * (B + 1)) B (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hi, rfl⟩ := hi
    exact ⟨(hitem i hi).2.1, (hitem i hi).2.2⟩
  · simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    have := hs2 i (by omega) j (by omega) hij
    rwa [(hI i hi.1).1, (hI j hj.1).1] at this


/-- The rows of a task triple. -/
def srr_tr (t : ℕ × ℕ × ℕ) : List (List SatSym) := task t.1 t.2.1 t.2.2

theorem srr_rows : ∀ (ts : List (ℕ × ℕ × ℕ)) (i : ℕ),
    (ts.flatMap srr_tr).length = 3 * ts.length ∧
    tLen (ts.flatMap srr_tr) i = (ts.getD i (0, 0, 0)).1 ∧
    tRel (ts.flatMap srr_tr) i = (ts.getD i (0, 0, 0)).2.1 ∧
    tDl (ts.flatMap srr_tr) i = (ts.getD i (0, 0, 0)).2.2
  | [], i => by simp [tLen, tRel, tDl]
  | t :: ts, 0 => by
    simp [srr_tr, task, tLen, tRel, tDl, tpu_uRow_len, (srr_rows ts 0).1]; ring
  | t :: ts, i + 1 => by
    obtain ⟨h0, h1, h2, h3⟩ := srr_rows ts i
    simp only [tLen, tRel, tDl] at h1 h2 h3
    simp only [List.flatMap_cons, srr_tr, task, tLen, tRel, tDl, List.length_append, h0,
      List.length_cons, List.length_nil, List.getD_cons_succ]
    refine ⟨by ring, ?_, ?_, ?_⟩
    · rw [show 3 * (i + 1) = 3 * i + 2 + 1 by ring]; simpa using h1
    · rw [show 3 * (i + 1) + 1 = 3 * i + 1 + 2 + 1 by ring]; simpa using h2
    · rw [show 3 * (i + 1) + 2 = 3 * i + 2 + 2 + 1 by ring]; simpa using h3


theorem srr_ubp_iff (u : List SatSym) (items : List (List SatSym)) (Bv : List SatSym)
    (hcl : clauses u = items ++ [Bv]) (hmod : items.length % 3 = 0) :
    UBPLang (bpuT u) ↔ ∃ f : ℕ → ℕ, (∀ i < items.length, f i < items.length / 3) ∧
      ∀ g < items.length / 3, srr_ps f g (fun i => (items.getD i []).length) items.length ≤
        Bv.length := by
  have hk : (uRow ((items ++ [Bv]).length / 3)).length = items.length / 3 := by
    rw [tpu_uRow_len, List.length_append, List.length_singleton]; omega
  constructor
  · rintro ⟨items', C, kr, hc, f, hf, hb⟩
    rw [bpr_clauses, hcl, List.append_assoc, List.singleton_append] at hc
    obtain ⟨hi, hc2⟩ := List.append_inj' hc (by simp)
    simp only [List.cons.injEq, and_true] at hc2
    obtain ⟨hC, hkr⟩ := hc2
    subst hi hC hkr
    rw [hk] at hf hb
    exact ⟨f, hf, fun g hg => by have := hb g hg; rwa [tpu_unSum_eq] at this⟩
  · rintro ⟨f, hf, hb⟩
    refine ⟨items, Bv, uRow ((items ++ [Bv]).length / 3), ?_, f, ?_, ?_⟩
    · rw [bpr_clauses, hcl]; simp
    · rw [hk]; exact hf
    · rw [hk]; intro g hg; rw [tpu_unSum_eq]; exact hb g hg

theorem srr_gen (u : List SatSym) (items : List (List SatSym)) (Bv : List SatSym)
    (hcl : clauses u = items ++ [Bv]) (hmod : items.length % 3 = 0) :
    UBPLang (bpuT u) ↔ SRDLang (srdT u) := by
  rw [srr_ubp_iff u items Bv hcl hmod]
  set n := items.length with hn
  set B := Bv.length with hB
  set m := n / 3 with hm
  set ts : List (ℕ × ℕ × ℕ) := items.map (fun r => (r.length, 0, m * (B + 1) - 1)) ++
    (List.range (m - 1)).map (fun j => (1, (j + 1) * (B + 1) - 1, (j + 1) * (B + 1))) with hts
  have hsrd : clauses (srdT u) = ts.flatMap srr_tr := by
    have : srdT u = (ts.flatMap srr_tr).flatMap (· ++ [sep]) := by
      unfold srdT
      rw [hcl, List.dropLast_concat, List.getLastD_concat]
      simp [hts, List.flatMap_append, List.flatMap_map, srr_tr, hn, hB, hm]
    rw [this]
    apply clauses_flatMap
    intro c hc
    simp only [List.mem_flatMap, srr_tr, task, List.mem_cons, List.not_mem_nil, or_false] at hc
    obtain ⟨_, _, hc | hc | hc⟩ := hc <;> rw [hc] <;> exact tpu_sep_nmem _
  have hlen : (ts.flatMap srr_tr).length = 3 * (n + (m - 1)) := by
    rw [(srr_rows ts 0).1, hts]; simp [hn]
  have hI : ∀ i < n, tLen (ts.flatMap srr_tr) i = (items.getD i []).length ∧
      tRel (ts.flatMap srr_tr) i = 0 ∧ tDl (ts.flatMap srr_tr) i = m * (B + 1) - 1 := by
    intro i hi
    obtain ⟨-, h1, h2, h3⟩ := srr_rows ts i
    rw [h1, h2, h3]
    simp [hts, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi, ← hn]
  have hS : ∀ j < m - 1, tLen (ts.flatMap srr_tr) (n + j) = 1 ∧
      tRel (ts.flatMap srr_tr) (n + j) = (j + 1) * (B + 1) - 1 ∧
      tDl (ts.flatMap srr_tr) (n + j) = (j + 1) * (B + 1) := by
    intro j hj
    obtain ⟨-, h1, h2, h3⟩ := srr_rows ts (n + j)
    rw [h1, h2, h3]
    simp [hts, List.getD_eq_getElem?_getD, hj, ← hn]
  have hm1 : n = 0 ∨ 1 ≤ m := by omega
  unfold SRDLang
  rw [hsrd, hlen, show 3 * (n + (m - 1)) / 3 = n + (m - 1) by omega]
  constructor
  · rintro ⟨f, hf, hb⟩
    exact ⟨by omega, srr_fwd n m B _ f hf hb _ _ _ hI hS⟩
  · rintro ⟨-, s, hs1, hs2⟩
    exact srr_bwd n m B _ hm1 _ _ _ hI hS s hs1 hs2

/-- **Unary SEQUENCING WITH RELEASE TIMES AND DEADLINES**: the reduction is correct. -/
theorem sat_iff_srd (w : List SatSym) : SATLang w ↔ SRDLang (SRDI w) := by
  rw [sat_iff_bpu]
  obtain ⟨hcl, hmod, -⟩ := tpui_wf w
  exact srr_gen _ _ _ hcl (by simpa using hmod)

end Pnp.Karp.SeqRD
