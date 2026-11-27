import Pnp.Karp.M2Ver

/-!
# MAX 2-SAT ∈ NP (official definition)

The checking relation is `m2v_vres w y = true` (`Pnp/Karp/M2Ver.lean`): the certificate `y`
gives the variable values `y.getD · false`.

* `m2v_run_eq`: the main loop computes `m2v_ev` (an evaluation with an assignment);
* `m2v_ev_L`: on `rs` (each clause followed by `sep`), `m2v_ev` accepts iff every clause has at
  most two literals and at least `k` clauses are satisfied;
* `m2v_lang_iff`: `M2Lang w ↔ ∃ y, |y| ≤ |w| ∧ m2v_vres w y`;
* `m2_in_np`: `M2Lang ∈ NP`.
-/

namespace Pnp.Karp.NAE

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.ThreeSAT
  Pnp.Karp.Clique

/-! ## Evaluation with an assignment -/

/-- `m2v_run` with the certificate replaced by an assignment (`j`: position in the clause). -/
def m2v_ev (a : ℕ → Bool) : List SatSym → ℕ → Bool → ℕ → ℕ → Bool
  | [], _, _, _, k => decide (k = 0)
  | sep :: w, _, F, l, k => decide (l ≤ 2) && m2v_ev a w 0 false 0 (if F then k - 1 else k)
  | zero :: w, j, F, l, k => m2v_ev a w (j + 1) F l k
  | pos :: w, j, F, l, k => m2v_ev a w (j + 1) (F || a j) (l + 1) k
  | neg :: w, j, F, l, k => m2v_ev a w (j + 1) (F || !a j) (l + 1) k

theorem m2v_inv {y Y U : Str} {j : ℕ} (hy : U.reverse ++ Y = y) (hj : U.length ≤ j)
    (hj' : Y ≠ [] → U.length = j) :
    y.getD j false = Y.headD false ∧ (m2v_sU Y U).reverse ++ Y.tail = y ∧
      (m2v_sU Y U).length ≤ j + 1 ∧ (Y.tail ≠ [] → (m2v_sU Y U).length = j + 1) := by
  rcases Y with _ | ⟨b, Y⟩
  · refine ⟨?_, by simpa [m2v_sU] using hy, by simp [m2v_sU]; omega, by simp⟩
    rw [← hy]; simp only [List.append_nil]
    exact List.getD_eq_default _ _ (by simpa using hj)
  · have hj := hj' (by simp)
    refine ⟨?_, by simpa [m2v_sU] using hy, by simp [m2v_sU]; omega,
      fun _ => by simp [m2v_sU]; omega⟩
    rw [← hy, ← hj, ← List.length_reverse]
    simp [List.getD_eq_getElem?_getD]

theorem m2v_run_eq (y : Str) : ∀ (w : List SatSym) (Y U : Str) (F : Bool) (l k j : ℕ),
    U.reverse ++ Y = y → U.length ≤ j → (Y ≠ [] → U.length = j) →
    m2v_run w Y U F l k = m2v_ev (fun i => y.getD i false) w j F l k
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | sep :: w, Y, U, F, l, k, j, hy, _, _ => by
    simp only [m2v_run, m2v_ev]
    rw [m2v_run_eq y w _ [] false 0 _ 0 (by simpa using hy) (by simp) (by simp)]
  | zero :: w, Y, U, F, l, k, j, hy, hj, hj' => by
    obtain ⟨-, h2, h3, h4⟩ := m2v_inv hy hj hj'
    simp only [m2v_run, m2v_ev]
    exact m2v_run_eq y w _ _ _ _ _ _ h2 h3 h4
  | pos :: w, Y, U, F, l, k, j, hy, hj, hj' => by
    obtain ⟨h1, h2, h3, h4⟩ := m2v_inv hy hj hj'
    simp only [m2v_run, m2v_ev, h1]
    exact m2v_run_eq y w _ _ _ _ _ _ h2 h3 h4
  | neg :: w, Y, U, F, l, k, j, hy, hj, hj' => by
    obtain ⟨h1, h2, h3, h4⟩ := m2v_inv hy hj hj'
    simp only [m2v_run, m2v_ev, h1]
    exact m2v_run_eq y w _ _ _ _ _ _ h2 h3 h4

/-! ## Clause level -/

/-- The number of literals of a clause. -/
def m2v_lits (c : List SatSym) : ℕ := (c.filter (· ≠ zero)).length

/-- A clause is satisfied (as a Boolean). -/
def m2v_satB (a : ℕ → Bool) (c : List SatSym) : Bool := evalF a (c ++ [sep]) 0 false

theorem m2v_satB_iff (a : ℕ → Bool) {c : List SatSym} (hc : sep ∉ c) :
    m2v_satB a c = true ↔ ClauseSat a c := by
  have h := evalF_eq_clauses a (c ++ [sep]) [] false (by simp [ClauseSat])
  rw [clausesAux_block [] c [] hc] at h
  simpa [m2v_satB, clausesAux] using h

theorem m2v_ev_clause (a : ℕ → Bool) (w : List SatSym) : ∀ (c : List SatSym) (j : ℕ) (F : Bool)
    (l k : ℕ), sep ∉ c →
    m2v_ev a (c ++ sep :: w) j F l k = (decide (l + m2v_lits c ≤ 2) &&
      m2v_ev a w 0 false 0 (if evalF a (c ++ [sep]) j F then k - 1 else k))
  | [], j, F, l, k, _ => by simp [m2v_ev, evalF, m2v_lits]
  | s :: c, j, F, l, k, h => by
    have hs : s ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have hc : sep ∉ c := fun e => h (List.mem_cons_of_mem _ e)
    cases s with
    | sep => exact absurd rfl hs
    | zero =>
      simp only [List.cons_append, m2v_ev, evalF]
      rw [m2v_ev_clause a w c _ _ _ _ hc]
      simp [m2v_lits]
    | pos =>
      simp only [List.cons_append, m2v_ev, evalF]
      rw [m2v_ev_clause a w c _ _ _ _ hc]
      congr 1
      rw [decide_eq_decide]; simp [m2v_lits]; omega
    | neg =>
      simp only [List.cons_append, m2v_ev, evalF]
      rw [m2v_ev_clause a w c _ _ _ _ hc]
      congr 1
      rw [decide_eq_decide]; simp [m2v_lits]; omega

theorem m2v_ev_L (a : ℕ → Bool) : ∀ (L : List (List SatSym)) (k : ℕ), (∀ c ∈ L, sep ∉ c) →
    (m2v_ev a (L.flatMap (· ++ [sep])) 0 false 0 k = true ↔
      (∀ c ∈ L, m2v_lits c ≤ 2) ∧ k ≤ L.countP (m2v_satB a))
  | [], k, _ => by simp [m2v_ev]
  | c :: L, k, h => by
    have hc : sep ∉ c := h c (by simp)
    have hL : ∀ c ∈ L, sep ∉ c := fun c' hc' => h c' (by simp [hc'])
    rw [List.flatMap_cons, List.append_assoc, List.singleton_append,
      m2v_ev_clause a _ c 0 false 0 k hc, Bool.and_eq_true, m2v_ev_L a L _ hL,
      List.countP_cons, List.forall_mem_cons]
    have e : ∀ m, k - 1 ≤ m ↔ k ≤ m + 1 := fun m => by omega
    by_cases hs : m2v_satB a c = true
    · simp only [m2v_satB] at hs
      simp [hs, e, m2v_satB, and_assoc]
    · simp only [m2v_satB] at hs
      simp [hs, m2v_satB, and_assoc]

theorem m2v_countP_eq (p : List SatSym → Bool) : ∀ L : List (List SatSym),
    L.countP p = ((Finset.range L.length).filter fun i => p (L.getD i []) = true).card
  | [] => by simp
  | c :: L => by
    rw [List.countP_cons, m2v_countP_eq p L, Finset.card_filter, Finset.card_filter,
      List.length_cons, Finset.sum_range_succ']
    simp

/-- The count of satisfied clauses as in `M2Lang`. -/
theorem m2v_exS_iff (a : ℕ → Bool) (rs : List (List SatSym)) (hs : ∀ c ∈ rs, sep ∉ c) (K : ℕ) :
    (∃ S : Finset ℕ, K ≤ S.card ∧ ∀ i ∈ S, i < rs.length ∧ ClauseSat a (rs.getD i [])) ↔
      K ≤ rs.countP (m2v_satB a) := by
  have hmem : ∀ i < rs.length, sep ∉ rs.getD i [] := fun i hi =>
    hs _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  rw [m2v_countP_eq]
  constructor
  · rintro ⟨S, hK, hS⟩
    refine le_trans hK (Finset.card_le_card fun i hi => ?_)
    obtain ⟨h1, h2⟩ := hS i hi
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨h1, (m2v_satB_iff a (hmem i h1)).2 h2⟩
  · intro hK
    refine ⟨_, hK, fun i hi => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.1, (m2v_satB_iff a (hmem i hi.1)).1 hi.2⟩

/-! ## Short certificates -/

theorem m2v_cs_congr {a b : ℕ → Bool} {c : List SatSym} (h : ∀ i < c.length, a i = b i)
    (hc : ClauseSat a c) : ClauseSat b c := by
  obtain ⟨j, hj, hl⟩ := hc
  refine ⟨j, hj, ?_⟩
  generalize c.getD j zero = s at hl ⊢
  cases s <;> simp_all [litTrue, h j hj]

theorem m2v_len_mem : ∀ (L : List (List SatSym)) (c : List SatSym), c ∈ L →
    c.length ≤ (L.flatMap (· ++ [sep])).length
  | [], _, h => by simp at h
  | c' :: L, c, h => by
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · simp; omega
    · have := m2v_len_mem L c h; omega

theorem m2v_vres_iff (w : List SatSym) (y : Str) :
    m2v_vres w y = true ↔ ∃ rs kr, clauses w = rs ++ [kr] ∧ (∀ c ∈ rs, m2v_lits c ≤ 2) ∧
      kr.length ≤ rs.countP (m2v_satB (fun i => y.getD i false)) := by
  have hsep := sep_not_mem_clauses w
  unfold m2v_vres
  rcases hcw : (clauses w).reverse with _ | ⟨kr, rr⟩
  · have : clauses w = [] := List.reverse_eq_nil_iff.1 hcw
    simp [this]
  · have hcl : clauses w = rr.reverse ++ [kr] := by
      rw [← List.reverse_reverse (clauses w), hcw]; simp
    have hs : ∀ c ∈ rr.reverse, sep ∉ c := fun c hc => hsep c (by simp [hcl, hc])
    simp only []
    rw [m2v_run_eq y _ y [] false 0 _ 0 (by simp) (by simp) (by simp), m2v_ev_L _ _ _ hs, hcl]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨_, _, rfl, h1, h2⟩
    · rintro ⟨rs, kr', he, h1, h2⟩
      obtain ⟨rfl, h3⟩ := List.append_inj' he rfl
      obtain rfl : kr = kr' := List.singleton_inj.1 h3
      exact ⟨h1, h2⟩

theorem m2v_lang_iff (w : List SatSym) :
    M2Lang w ↔ ∃ y : Str, y.length ≤ w.length ∧ m2v_vres w y = true := by
  have hsep := sep_not_mem_clauses w
  have hcl : ∀ c ∈ clauses w, c.length ≤ w.length := fun c hc =>
    le_trans (m2v_len_mem _ c hc) (length_trunc_le w)
  unfold M2Lang
  constructor
  · rintro ⟨rs, kr, he, h2, a, S, hK, hS⟩
    let y : Str := (List.range w.length).map a
    have hy : ∀ i < w.length, a i = y.getD i false := fun i hi => by
      simp [y, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    have hs : ∀ c ∈ rs, sep ∉ c := fun c hc => hsep c (by simp [he, hc])
    refine ⟨y, by simp [y], (m2v_vres_iff w y).2 ⟨rs, kr, he, h2, ?_⟩⟩
    refine (m2v_exS_iff _ rs hs _).1 ⟨S, hK, fun i hi => ⟨(hS i hi).1, ?_⟩⟩
    have hi' := (hS i hi).1
    have hm : rs.getD i [] ∈ clauses w := by
      rw [he, List.getD_eq_getElem _ _ hi']; simp [List.getElem_mem hi']
    exact m2v_cs_congr (fun j hj => hy j (by have := hcl _ hm; omega)) (hS i hi).2
  · rintro ⟨y, -, h⟩
    obtain ⟨rs, kr, he, h2, h3⟩ := (m2v_vres_iff w y).1 h
    have hs : ∀ c ∈ rs, sep ∉ c := fun c hc => hsep c (by simp [he, hc])
    exact ⟨rs, kr, he, h2, _, (m2v_exS_iff _ rs hs _).2 h3⟩

/-! ## Transfer to the official class -/

/-- **MAX 2-SAT ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem m2_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      M2Lang := by
  classical
  have hrun := fun z => ((m2v_exec_ver z).mono (m2v_T_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg m2v_ver) (tb 5 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg m2v_ver, 5, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => m2v_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => m2v_vres w y = true, 1, hR, fun w => ?_⟩
  rw [m2v_lang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.NAE
