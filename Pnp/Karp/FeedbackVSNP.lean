import Pnp.Karp.FeedbackVSVer
import Pnp.Karp.CliqueNP

/-!
# FEEDBACK VERTEX SET ∈ NP (official definition)

The checking relation is `fvv_vres w y = true` (`Pnp/Karp/FeedbackVSVer.lean`): the certificate
`y` is a sequence of blocks `f :: true^ρ ++ [false]`, one per vertex (`fvv_cert`).

* `fvv_go_iff`, `fvv_rowOk_iff`: the verifier accepts iff at most `|kr|` vertices `v < n` are
  unchecked (block missing or starting with `true`) and every `pos` entry `(i, j)`, `i ≠ j`,
  between checked vertices has rank `i` < rank `j`;
* `fvv_lang_iff`: `FVSLang w ↔ ∃ y, |y| ≤ |w|² ∧ fvv_vres w y`.  Soundness: ranks increase
  strictly along arcs outside `F`, so there is no cycle.  Completeness: the rank of `v` is the
  number of vertices `a < n` that reach `v`;
* `fvs_in_np`: `FVSLang ∈ NP`, via `fvv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.FeedbackVS

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics of the verifier -/

theorem fvv_rowOk_iff (a : ℕ) (y : Str) : ∀ (r : List SatSym) (j : ℕ) (D : Str),
    fvv_rowOk a r (fvv_nx^[j] y) D = true ↔ ∀ t < r.length, r.getD t zero = pos →
      (D.drop t).head? ≠ some false → (fvv_nx^[j + t] y).head? = some false →
        a < fvv_rk (fvv_nx^[j + t] y)
  | [], j, D => by simp [fvv_rowOk]
  | s :: r, j, D => by
    have ih := fvv_rowOk_iff a y r (j + 1) D.tail
    rw [iterate_succ_apply'] at ih
    simp only [fvv_rowOk, Bool.and_eq_true, Bool.not_eq_true', fvv_bad, decide_eq_false_iff_not,
      ih, List.length_cons]
    constructor
    · rintro ⟨h0, h1⟩ t ht
      rcases t with _ | t
      · simp only [List.getD_cons_zero, List.drop_zero, Nat.add_zero]
        intro hp hd hf
        by_contra hc
        exact h0 ⟨hp, hd, hf, hc⟩
      · simp only [List.getD_cons_succ]
        intro hp hd hf
        have := h1 t (by omega) hp (by simpa [List.drop_tail] using hd)
          (by rw [show j + (t + 1) = j + 1 + t by omega] at hf; exact hf)
        rwa [show j + 1 + t = j + (t + 1) by omega] at this
    · intro h
      refine ⟨fun ⟨hp, hd, hf, hc⟩ => hc (h 0 (by omega) (by simpa using hp)
        (by simpa using hd) (by simpa using hf)), fun t ht hp hd hf => ?_⟩
      have := h (t + 1) (by omega) (by simpa using hp) (by simpa [List.drop_tail] using hd)
        (by rw [show j + (t + 1) = j + 1 + t by omega]; exact hf)
      rwa [show j + (t + 1) = j + 1 + t by omega] at this

theorem fvv_go_iff (y : Str) : ∀ (rows : List (List SatSym)) (c i : ℕ),
    fvv_go y rows (fvv_nx^[i] y) c i = true ↔
      (∑ v ∈ Finset.range rows.length,
          if (fvv_nx^[i + v] y).head? = some false then 0 else 1) ≤ c ∧
        ∀ v < rows.length, (fvv_nx^[i + v] y).head? = some false →
          fvv_rowOk (fvv_rk (fvv_nx^[i + v] y)) (rows.getD v []) y
            (List.replicate (i + v) true ++ [false]) = true
  | [], c, i => by simp [fvv_go]
  | r :: rows, c, i => by
    have ih := fvv_go_iff y rows
    have e' : ∀ v, i + 1 + v = i + (v + 1) := fun v => by omega
    simp only [List.length_cons, Finset.sum_range_succ', Nat.add_zero]
    unfold fvv_go
    rw [← iterate_succ_apply' fvv_nx i y]
    by_cases hF : (fvv_nx^[i] y).head? = some false
    · simp only [hF, ↓reduceIte, Bool.and_eq_true]
      rw [ih]
      simp only [e']
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨by omega, fun v hv => ?_⟩
        rcases v with _ | v
        · intro _; simpa using h0
        · intro h; simpa using h2 v (by omega) h
      · rintro ⟨h1, h2⟩
        refine ⟨by simpa [hF] using h2 0 (by omega), by omega, fun v hv h => ?_⟩
        simpa using h2 (v + 1) (by omega) h
    · simp only [hF, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
      rw [ih]
      simp only [e']
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨by omega, fun v hv => ?_⟩
        rcases v with _ | v
        · intro h; exact absurd (by simpa using h) hF
        · intro h; simpa using h2 v (by omega) h
      · rintro ⟨h1, h2⟩
        refine ⟨by omega, by omega, fun v hv h => ?_⟩
        simpa using h2 (v + 1) (by omega) h

theorem fvv_diag (i t : ℕ) :
    ((List.replicate i true ++ [false]).drop t).head? = some false ↔ t = i := by
  rw [List.head?_drop]
  by_cases h1 : t < i
  · rw [List.getElem?_append_left (by simpa using h1)]
    simp [h1]; omega
  · rw [List.getElem?_append_right (by simpa using h1)]
    simp only [List.length_replicate]
    rcases Nat.lt_or_ge (t - i) 1 with h | h
    · have : t = i := by omega
      simp [this]
    · rw [List.getElem?_eq_none (by simpa using h)]
      simp; omega

/-! ## Certificates -/

/-- The certificate of the blocks `(f, ρ)`. -/
def fvv_cert (L : List (Bool × ℕ)) : Str :=
  L.flatMap fun p => p.1 :: (List.replicate p.2 true ++ [false])

theorem fvv_units_rep (rest : Str) : ∀ k : ℕ,
    fvv_units (List.replicate k true ++ false :: rest) = (k, rest)
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, fvv_units, fvv_units_rep rest k]

theorem fvv_nx_cert (p : Bool × ℕ) (L : List (Bool × ℕ)) :
    fvv_nx (fvv_cert (p :: L)) = fvv_cert L := by
  simp [fvv_cert, fvv_nx, fvv_units_rep]

theorem fvv_rk_cert (p : Bool × ℕ) (L : List (Bool × ℕ)) :
    fvv_rk (fvv_cert (p :: L)) = p.2 := by
  simp [fvv_cert, fvv_rk, fvv_units_rep]

theorem fvv_nx_nil : ∀ k : ℕ, fvv_nx^[k] [] = []
  | 0 => rfl
  | k + 1 => by rw [iterate_succ_apply]; exact fvv_nx_nil k

theorem fvv_iter_cert : ∀ (k : ℕ) (L : List (Bool × ℕ)),
    fvv_nx^[k] (fvv_cert L) = fvv_cert (L.drop k)
  | 0, L => rfl
  | k + 1, [] => by simp [fvv_cert, fvv_nx_nil]
  | k + 1, p :: L => by rw [iterate_succ_apply, fvv_nx_cert, fvv_iter_cert k L]; rfl

theorem fvv_cert_length (m : ℕ) : ∀ L : List (Bool × ℕ), (∀ p ∈ L, p.2 ≤ m) →
    (fvv_cert L).length ≤ L.length * (m + 2)
  | [], _ => by simp [fvv_cert]
  | p :: L, h => by
    have ih := fvv_cert_length m L (fun q hq => h q (by simp [hq]))
    have hp := h p (by simp)
    have e : fvv_cert (p :: L) = p.1 :: (List.replicate p.2 true ++ [false]) ++ fvv_cert L := by
      simp [fvv_cert]
    rw [e]
    simp only [List.length_append, List.length_cons, List.length_replicate, List.length_nil]
    nlinarith

/-! ## Correctness -/

theorem fvv_lang_iff (w : List SatSym) :
    FVSLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ fvv_vres w y = true := by
  classical
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have htr := length_trunc_le w
  unfold FVSLang fvv_vres
  rcases hc : clauses w with _ | ⟨kr, rows⟩
  · simp
  · rw [hc] at hsum
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    set n := rows.length
    have hgo := fvv_go_iff
    constructor
    · rintro ⟨F, hcard, hF, hac⟩
      let reach : ℕ → ℕ → Prop := Relation.TransGen (arcOut rows F)
      let rank : ℕ → ℕ := fun v => ((Finset.range n).filter fun a => reach a v).card
      let L : List (Bool × ℕ) := (List.range n).map fun v => (decide (v ∈ F), rank v)
      have hrank : ∀ v, rank v ≤ n := fun v =>
        (Finset.card_filter_le _ _).trans (by simp)
      have hB : ∀ v, fvv_nx^[v] (fvv_cert L) =
          if h : v < n then fvv_cert ((decide (v ∈ F), rank v) :: L.drop (v + 1))
          else [] := by
        intro v
        rw [fvv_iter_cert]
        split_ifs with h
        · rw [List.drop_eq_getElem_cons (by simpa [L] using h)]
          simp [L]
        · rw [List.drop_eq_nil_of_le (by simp [L]; omega)]; rfl
      have hhead : ∀ v, (fvv_nx^[v] (fvv_cert L)).head? = some false ↔ v < n ∧ v ∉ F := by
        intro v
        rw [hB]
        split_ifs with h
        · simp [fvv_cert, h]
        · simp [h]
      have hrk : ∀ v < n, fvv_rk (fvv_nx^[v] (fvv_cert L)) = rank v := by
        intro v hv
        rw [hB, dif_pos hv, fvv_rk_cert]
      refine ⟨fvv_cert L, ?_, ?_⟩
      · have := fvv_cert_length n L (by
          intro p hp
          simp only [L, List.mem_map, List.mem_range] at hp
          obtain ⟨v, -, rfl⟩ := hp
          exact hrank v)
        simp only [L, List.length_map, List.length_range] at this
        calc (fvv_cert L).length ≤ n * (n + 2) := this
          _ ≤ (n + 1) ^ 2 := by nlinarith
          _ ≤ w.length ^ 2 := Nat.pow_le_pow_left (by omega) 2
      · have h0 := (hgo (fvv_cert L) rows kr.length 0).2
        simp only [Nat.zero_add, Function.iterate_zero, id] at h0
        apply h0
        refine ⟨?_, fun v hv hvF => ?_⟩
        · have e : (∑ v ∈ Finset.range n,
              if (fvv_nx^[v] (fvv_cert L)).head? = some false then 0 else 1) = F.card := by
            rw [show F = (Finset.range n).filter (· ∈ F) by
              ext x; simp only [Finset.mem_filter, Finset.mem_range]
              exact ⟨fun h => ⟨hF x h, h⟩, fun h => h.2⟩]
            rw [Finset.card_filter]
            refine Finset.sum_congr rfl fun x hx => ?_
            have hx' : x < n := Finset.mem_range.1 hx
            by_cases hxF : x ∈ F
            · rw [if_neg (by rw [hhead]; tauto), if_pos (by simpa using hxF)]
            · rw [if_pos (by rw [hhead]; exact ⟨hx', hxF⟩), if_neg (by simpa using hxF)]
          rw [e]; exact hcard
        · obtain ⟨-, hvF'⟩ := (hhead v).1 hvF
          have h1 := (fvv_rowOk_iff (fvv_rk (fvv_nx^[v] (fvv_cert L))) (fvv_cert L)
            (rows.getD v []) 0 (List.replicate v true ++ [false])).2
          simp only [Function.iterate_zero, id, Nat.zero_add] at h1
          apply h1
          intro t ht hp hd ht'
          rw [Ne, fvv_diag] at hd
          obtain ⟨htn, htF⟩ := (hhead t).1 ht'
          rw [hrk v hv, hrk t htn]
          have harc : arcOut rows F v t := ⟨hv, htn, hvF', htF, Ne.symm hd, hp⟩
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨v, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_range]
              exact ⟨hv, Relation.TransGen.single harc⟩
            · simp only [Finset.mem_filter, Finset.mem_range, not_and]
              exact fun _ => hac v
          · intro a ha
            simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
            exact ⟨ha.1, ha.2.tail harc⟩
    · rintro ⟨y, -, hy⟩
      have h0 := (hgo y rows kr.length 0).1
      simp only [Nat.zero_add, Function.iterate_zero, id] at h0
      obtain ⟨hcnt, hrow⟩ := h0 hy
      let B : ℕ → Str := fun v => fvv_nx^[v] y
      let F : Finset ℕ := (Finset.range n).filter fun v => (B v).head? ≠ some false
      refine ⟨F, ?_, ?_, ?_⟩
      · rw [Finset.card_filter]
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) hcnt
        by_cases h : (B x).head? = some false
        · rw [if_neg (by simpa using h), if_pos h]
        · rw [if_pos h, if_neg h]
      · intro v hv; exact Finset.mem_range.1 (Finset.mem_filter.1 hv).1
      · have hlt : ∀ a b, arcOut rows F a b → fvv_rk (B a) < fvv_rk (B b) := by
          rintro a b ⟨ha, hb, haF, hbF, hab, hp⟩
          have ha' : (B a).head? = some false := by
            by_contra h; exact haF (Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, h⟩)
          have hb' : (B b).head? = some false := by
            by_contra h; exact hbF (Finset.mem_filter.2 ⟨Finset.mem_range.2 hb, h⟩)
          have hr := (fvv_rowOk_iff _ y (rows.getD a []) 0 _).1 (by
            simpa using hrow a ha ha')
          have hbl : b < (rows.getD a []).length := by
            by_contra h
            rw [List.getD_eq_default _ _ (by omega)] at hp
            exact absurd hp (by decide)
          simpa using hr b hbl hp (by rw [Ne, fvv_diag]; exact Ne.symm hab) (by simpa using hb')
        intro u hu
        have key : ∀ a b, Relation.TransGen (arcOut rows F) a b → fvv_rk (B a) < fvv_rk (B b) := by
          intro a b h
          induction h with
          | single h => exact hlt _ _ h
          | tail _ h ih => exact ih.trans (hlt _ _ h)
        exact lt_irrefl _ (key u u hu)

/-! ## Transfer to the official class -/

/-- **FEEDBACK VERTEX SET ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem fvs_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      FVSLang := by
  classical
  have hrun := fun z => ((fvv_exec_ver z).mono (fvv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg fvv_ver) (tb 7 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg fvv_ver, 7, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => fvv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => fvv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [fvv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.FeedbackVS
