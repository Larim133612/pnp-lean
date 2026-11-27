import Pnp.Karp.FeedbackArcVer
import Pnp.Karp.FeedbackVSNP

/-!
# FEEDBACK ARC SET ∈ NP (official definition)

The checking relation is `fav_vres w y = true` (`Pnp/Karp/FeedbackArcVer.lean`): the certificate
`y` is a sequence of unary blocks `true^ρ ++ [false]`, one per vertex (`fav_cert`).

* `fav_cnt_eq`, `fav_go_iff`: the verifier accepts iff every vertex `v < n` has a block and the
  number of `pos` entries `(i, j)`, `i ≠ j`, with `j` having a block and rank `i` ≥ rank `j`, is
  at most `|kr|`;
* `fav_lang_iff`: `FASLang w ↔ ∃ y, |y| ≤ |w|² ∧ fav_vres w y`.  Completeness: the rank of `v`
  is the number of vertices `a < n` that reach `v` outside `F`, so every counted entry is an arc
  of `F`.  Soundness: `F` is the set of counted entries; ranks increase strictly along the
  remaining arcs, so there is no cycle;
* `fas_in_np`: `FASLang ∈ NP`, via `fav_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.FeedbackArc

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.FeedbackVS

/-! ## Semantics of the verifier -/

theorem fav_cnt_eq (a : ℕ) (y : Str) : ∀ (r : List SatSym) (j : ℕ) (D : Str),
    fav_cnt a r (fav_nx^[j] y) D = ∑ t ∈ Finset.range r.length,
      if r.getD t zero = pos ∧ (D.drop t).head? ≠ some false ∧ fav_nx^[j + t] y ≠ [] ∧
        ¬ a < fav_rk (fav_nx^[j + t] y) then 1 else 0
  | [], j, D => by simp [fav_cnt]
  | s :: r, j, D => by
    have ih := fav_cnt_eq a y r (j + 1) D.tail
    rw [iterate_succ_apply'] at ih
    simp only [fav_cnt, ih, List.length_cons, Finset.sum_range_succ']
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun t _ => ?_
      simp only [List.getD_cons_succ, List.drop_tail, show j + 1 + t = j + (t + 1) by omega]
    · simp [fav_bad]

theorem fav_go_iff (y : Str) : ∀ (rows : List (List SatSym)) (c i : ℕ),
    fav_go y rows (fav_nx^[i] y) c i = true ↔
      (∀ v < rows.length, fav_nx^[i + v] y ≠ []) ∧
        (∑ v ∈ Finset.range rows.length, fav_cnt (fav_rk (fav_nx^[i + v] y)) (rows.getD v []) y
          (List.replicate (i + v) true ++ [false])) ≤ c
  | [], c, i => by simp [fav_go]
  | r :: rows, c, i => by
    have ih := fav_go_iff y rows
    have e' : ∀ v, i + 1 + v = i + (v + 1) := fun v => by omega
    simp only [List.length_cons, Finset.sum_range_succ', Nat.add_zero]
    unfold fav_go
    rw [← iterate_succ_apply' fav_nx i y, Bool.and_eq_true, decide_eq_true_iff, ih]
    simp only [e', List.getD_cons_succ, List.getD_cons_zero]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩
      refine ⟨fun v hv => ?_, by omega⟩
      rcases v with _ | v
      · simpa using h0
      · exact h2 v (by omega)
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by simpa using h1 0 (by omega), by omega⟩,
        fun v hv => h1 (v + 1) (by omega), by omega⟩

/-! ## Certificates -/

/-- The certificate of the ranks `L`. -/
def fav_cert (L : List ℕ) : Str := L.flatMap fun k => List.replicate k true ++ [false]

theorem fav_nx_cert (k : ℕ) (L : List ℕ) : fav_nx (fav_cert (k :: L)) = fav_cert L := by
  simp [fav_cert, fav_nx, fvv_units_rep]

theorem fav_rk_cert (k : ℕ) (L : List ℕ) : fav_rk (fav_cert (k :: L)) = k := by
  simp [fav_cert, fav_rk, fvv_units_rep]

theorem fav_nx_nil : ∀ k : ℕ, fav_nx^[k] [] = []
  | 0 => rfl
  | k + 1 => by rw [iterate_succ_apply]; exact fav_nx_nil k

theorem fav_iter_cert : ∀ (k : ℕ) (L : List ℕ), fav_nx^[k] (fav_cert L) = fav_cert (L.drop k)
  | 0, L => rfl
  | k + 1, [] => by simp [fav_cert, fav_nx_nil]
  | k + 1, p :: L => by rw [iterate_succ_apply, fav_nx_cert, fav_iter_cert k L]; rfl

theorem fav_cert_length (m : ℕ) : ∀ L : List ℕ, (∀ p ∈ L, p ≤ m) →
    (fav_cert L).length ≤ L.length * (m + 1)
  | [], _ => by simp [fav_cert]
  | p :: L, h => by
    have ih := fav_cert_length m L (fun q hq => h q (by simp [hq]))
    have hp := h p (by simp)
    have e : fav_cert (p :: L) = List.replicate p true ++ [false] ++ fav_cert L := by
      simp [fav_cert]
    rw [e]
    simp only [List.length_append, List.length_cons, List.length_replicate, List.length_nil]
    nlinarith

/-! ## Correctness -/

theorem fav_lang_iff (w : List SatSym) :
    FASLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ fav_vres w y = true := by
  classical
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have htr := length_trunc_le w
  unfold FASLang fav_vres
  rcases hc : clauses w with _ | ⟨kr, rows⟩
  · simp
  · rw [hc] at hsum
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    set n := rows.length
    -- the counted entries of row `v`
    let T : Str → ℕ → Finset ℕ := fun y v =>
      (Finset.range (rows.getD v []).length).filter fun t =>
        (rows.getD v []).getD t zero = pos ∧
          ((List.replicate v true ++ [false]).drop t).head? ≠ some false ∧
          fav_nx^[t] y ≠ [] ∧ ¬ fav_rk (fav_nx^[v] y) < fav_rk (fav_nx^[t] y)
    have hgo : ∀ y : Str, fav_go y rows y kr.length 0 = true ↔
        (∀ v < n, fav_nx^[v] y ≠ []) ∧ (∑ v ∈ Finset.range n, (T y v).card) ≤ kr.length := by
      intro y
      have h := fav_go_iff y rows kr.length 0
      simp only [Nat.zero_add, Function.iterate_zero, id] at h
      rw [h]
      refine and_congr Iff.rfl ?_
      have e : ∀ v, fav_cnt (fav_rk (fav_nx^[v] y)) (rows.getD v []) y
          (List.replicate v true ++ [false]) = (T y v).card := by
        intro v
        have := fav_cnt_eq (fav_rk (fav_nx^[v] y)) y (rows.getD v []) 0
          (List.replicate v true ++ [false])
        simp only [Function.iterate_zero, id, Nat.zero_add] at this
        rw [this, Finset.card_filter]
      rw [Finset.sum_congr rfl fun v _ => e v]
    have hlen : ∀ (v t : ℕ), (rows.getD v []).getD t zero = pos → t < (rows.getD v []).length := by
      intro v t hp
      by_contra h
      rw [List.getD_eq_default _ _ (by omega)] at hp
      exact absurd hp (by decide)
    constructor
    · rintro ⟨F, hcard, hac⟩
      let reach : ℕ → ℕ → Prop := Relation.TransGen (arcF rows F)
      let rank : ℕ → ℕ := fun v => ((Finset.range n).filter fun a => reach a v).card
      let L : List ℕ := (List.range n).map rank
      have hrank : ∀ v, rank v ≤ n := fun v =>
        (Finset.card_filter_le _ _).trans (by simp)
      have hB : ∀ v, fav_nx^[v] (fav_cert L) =
          if h : v < n then fav_cert (rank v :: L.drop (v + 1)) else [] := by
        intro v
        rw [fav_iter_cert]
        split_ifs with h
        · rw [List.drop_eq_getElem_cons (by simpa [L] using h)]
          simp [L]
        · rw [List.drop_eq_nil_of_le (by simp [L]; omega)]; rfl
      have hne : ∀ v, fav_nx^[v] (fav_cert L) ≠ [] ↔ v < n := by
        intro v
        rw [hB]
        split_ifs with h
        · simp [fav_cert, h]
        · simp [h]
      have hrk : ∀ v < n, fav_rk (fav_nx^[v] (fav_cert L)) = rank v := by
        intro v hv
        rw [hB, dif_pos hv, fav_rk_cert]
      have harc : ∀ a b, arcF rows F a b → rank a < rank b := by
        intro a b harc
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨a, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_range]
            exact ⟨harc.1, Relation.TransGen.single harc⟩
          · simp only [Finset.mem_filter, Finset.mem_range, not_and]
            exact fun _ => hac a
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
          exact ⟨hx.1, hx.2.tail harc⟩
      refine ⟨fav_cert L, ?_, ?_⟩
      · have := fav_cert_length n L (by
          intro p hp
          simp only [L, List.mem_map, List.mem_range] at hp
          obtain ⟨v, -, rfl⟩ := hp
          exact hrank v)
        simp only [L, List.length_map, List.length_range] at this
        calc (fav_cert L).length ≤ n * (n + 1) := this
          _ ≤ (n + 1) ^ 2 := by nlinarith
          _ ≤ w.length ^ 2 := Nat.pow_le_pow_left (by omega) 2
      · rw [hgo]
        refine ⟨fun v hv => (hne v).2 hv, ?_⟩
        rw [← Finset.card_sigma]
        refine le_trans (Finset.card_le_card_of_injOn (fun x => (x.1, x.2)) ?_ ?_) hcard
        · rintro ⟨v, t⟩ hx
          simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_range,
            Finset.mem_filter, T] at hx
          obtain ⟨hv, -, hp, hd, ht, hlt⟩ := hx
          rw [Ne, fvv_diag] at hd
          have htn := (hne t).1 ht
          rw [hrk v hv, hrk t htn] at hlt
          simp only [Finset.mem_coe]
          by_contra hF
          exact hlt (harc v t ⟨hv, htn, Ne.symm hd, hp, hF⟩)
        · rintro ⟨v, t⟩ - ⟨v', t'⟩ - h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rfl
    · rintro ⟨y, -, hy⟩
      obtain ⟨hne, hcnt⟩ := (hgo y).1 hy
      let F : Finset (ℕ × ℕ) := ((Finset.range n).sigma (T y)).image fun x => (x.1, x.2)
      refine ⟨F, ?_, ?_⟩
      · exact (Finset.card_image_le).trans ((Finset.card_sigma _ _).trans_le hcnt)
      · let rank : ℕ → ℕ := fun v => fav_rk (fav_nx^[v] y)
        have hlt : ∀ a b, arcF rows F a b → rank a < rank b := by
          rintro a b ⟨ha, hb, hab, hp, hF⟩
          by_contra hc
          apply hF
          refine Finset.mem_image.2 ⟨⟨a, b⟩, ?_, rfl⟩
          simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, T]
          refine ⟨ha, hlen a b hp, hp, ?_, hne b hb, hc⟩
          rw [Ne, fvv_diag]; exact Ne.symm hab
        intro u hu
        have key : ∀ a b, Relation.TransGen (arcF rows F) a b → rank a < rank b := by
          intro a b h
          induction h with
          | single h => exact hlt _ _ h
          | tail _ h ih => exact ih.trans (hlt _ _ h)
        exact lt_irrefl _ (key u u hu)

/-! ## Transfer to the official class -/

/-- **FEEDBACK ARC SET ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem fas_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      FASLang := by
  classical
  have hrun := fun z => ((fav_exec_ver z).mono (fvv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg fav_ver) (tb 7 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg fav_ver, 7, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => fav_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => fav_vres w y = true, 2, hR, fun w => ?_⟩
  rw [fav_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.FeedbackArc
