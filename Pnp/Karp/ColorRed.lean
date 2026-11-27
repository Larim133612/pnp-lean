import Pnp.Karp.Color

/-!
# Correctness of the reduction SAT ≤ 3-COLORING

`sat_iff_col : SATLang w ↔ ColLang (G w)` (graph `G w`: `Pnp/Karp/Color.lean`).

Both directions are proved by induction along `trunc w`, following the gadget rows
`gadAll L p (ann r t j)` and the evaluation `evalF a r j F` in parallel:

* colorable ⇒ SAT (`sound_aux`): with the assignment `a j := (c (3 + 2j) = c 0)`, if the running
  flag `F` is false then the accumulator input is colored `c 1`; the OR gadget propagates this,
  and the `o—F` edge at each `sep` position forces the flag to be true there;
* SAT ⇒ colorable (`compl_aux`): the explicit coloring `colr w a`, where the gadget vertices of
  position `p` are colored by `tri F l` (`F`: accumulator value, `l`: literal value).
-/

namespace Pnp.Karp.Color

open Pnp.CookLevin SatSym Pnp.Karp.Clique

theorem getD_rep_append (n k : ℕ) (l : List SatSym) :
    (List.replicate n zero ++ l).getD k zero = if k < n then zero else l.getD (k - n) zero := by
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]; simp [h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]; simp

theorem getD_cons_pos_iff (s : SatSym) (l : List SatSym) (k : ℕ) :
    (s :: l).getD k zero = pos ↔ (k = 0 ∧ s = pos) ∨ (k ≠ 0 ∧ l.getD (k - 1) zero = pos) := by
  rcases k with _ | k <;> simp

theorem ite_zero_eq_pos (c : Prop) [Decidable c] (x : SatSym) :
    (if c then zero else x) = pos ↔ ¬c ∧ x = pos := by
  split_ifs <;> simp_all

theorem getD_nil_pos (k : ℕ) : ([] : List SatSym).getD k zero = pos ↔ False := by simp

theorem xRow_pos (b j k : ℕ) (hb : 2 ≤ b) :
    (xRow b j).getD k zero = pos ↔ k = (if j = 0 then 1 else b - 1) ∨ k = b + 1 ∨ k = b + 2 := by
  unfold xRow
  split_ifs with hj
  · simp only [List.cons_append, List.nil_append, getD_cons_pos_iff, getD_rep_append,
      ite_zero_eq_pos, getD_nil_pos]
    simp; omega
  · simp only [getD_cons_pos_iff, getD_rep_append, ite_zero_eq_pos, getD_nil_pos]
    simp; omega

theorem yRow_pos (s : SatSym) (j k : ℕ) : (yRow s j).getD k zero = pos ↔ k = litCol s j := by
  unfold yRow
  simp only [getD_rep_append, ite_zero_eq_pos, getD_cons_pos_iff, getD_nil_pos]
  simp; omega

theorem oRow_pos (s : SatSym) (b k : ℕ) (hb : 2 ≤ b) :
    (oRow s b).getD k zero = pos ↔ k = 2 ∨ (s = sep ∧ k = 1) ∨ k = b + 1 := by
  unfold oRow
  simp only [List.cons_append, List.nil_append, getD_cons_pos_iff, getD_rep_append,
    ite_zero_eq_pos, getD_nil_pos]
  split_ifs with hs <;> simp [hs] <;> omega

theorem vpRow_pos (j k : ℕ) : (vpRow j).getD k zero = pos ↔ k = 2 ∨ k = 4 + 2 * j := by
  unfold vpRow
  simp only [List.cons_append, List.nil_append, getD_cons_pos_iff, getD_rep_append,
    ite_zero_eq_pos, getD_nil_pos]
  simp; omega

theorem vnRow_pos (k : ℕ) : vnRow.getD k zero = pos ↔ k = 2 := by
  unfold vnRow
  simp only [getD_cons_pos_iff, getD_nil_pos]
  simp; omega

theorem length_litRows (L : ℕ) : (litRows L).length = 2 * L := by
  induction L with
  | zero => rfl
  | succ L ih => simp [litRows, List.range_succ, List.flatMap_append] at ih ⊢; omega

theorem litRows_succ (L : ℕ) : litRows (L + 1) = litRows L ++ [vpRow L, vnRow] := by
  simp [litRows, List.range_succ, List.flatMap_append]

theorem getD_litRows (L m : ℕ) (hm : m < 2 * L) :
    (litRows L).getD m [] = if m % 2 = 0 then vpRow (m / 2) else vnRow := by
  induction L with
  | zero => omega
  | succ L ih =>
    rw [litRows_succ]
    by_cases h : m < 2 * L
    · rw [List.getD_append _ _ _ _ (by rw [length_litRows]; exact h), ih h]
    · rw [List.getD_append_right _ _ _ _ (by rw [length_litRows]; omega), length_litRows]
      have : m - 2 * L = 0 ∨ m - 2 * L = 1 := by omega
      rcases this with e | e <;> rw [e]
      · have h1 : m % 2 = 0 := by omega
        have h2 : m / 2 = L := by omega
        simp [h1, h2]
      · have h1 : m % 2 = 1 := by omega
        simp [h1]

theorem length_ann : ∀ (r : List SatSym) (t j : ℕ), (ann r t j).length = r.length
  | [], _, _ => rfl
  | sep :: r, t, j => by simp [ann, length_ann r]
  | zero :: r, t, j => by simp [ann, length_ann r]
  | pos :: r, t, j => by simp [ann, length_ann r]
  | neg :: r, t, j => by simp [ann, length_ann r]

theorem length_annW (w : List SatSym) : (annW w).length = (trunc w).length := length_ann _ _ _

theorem gRows_eq (w : List SatSym) :
    gRows w = (triRows ++ litRows (annW w).length) ++ gadAll (annW w).length 0 (annW w) := by
  simp [gRows]

theorem length_pre (L : ℕ) : (triRows ++ litRows L).length = base L 0 := by
  simp [length_litRows, triRows, base]; omega

/-- The three gadget rows inside the matrix. -/
theorem gad_rows {rows P : List (List SatSym)} {L p : ℕ} {a : SatSym × ℕ × ℕ}
    {A : List (SatSym × ℕ × ℕ)} (h : rows = P ++ gadAll L p (a :: A))
    (hP : P.length = base L p) :
    rows.getD (base L p) [] = xRow (base L p) a.2.2 ∧
    rows.getD (base L p + 1) [] = yRow a.1 a.2.2 ∧
    rows.getD (base L p + 2) [] = oRow a.1 (base L p) ∧
    rows = (P ++ gadRows L p a) ++ gadAll L (p + 1) A ∧
    (P ++ gadRows L p a).length = base L (p + 1) := by
  subst h
  simp only [gadAll, List.append_assoc]
  refine ⟨?_, ?_, ?_, trivial, ?_⟩
  · rw [List.getD_append_right _ _ _ _ (by omega), hP, Nat.sub_self]; simp [gadRows]
  · rw [List.getD_append_right _ _ _ _ (by omega), hP]; simp [gadRows]
  · rw [List.getD_append_right _ _ _ _ (by omega), hP]; simp [gadRows]
  · simp [gadRows, hP, base]; ring

theorem pre_rows (w : List SatSym) (i : ℕ) (hi : i < base (annW w).length 0) :
    (gRows w).getD i [] = (triRows ++ litRows (annW w).length).getD i [] := by
  rw [gRows_eq, List.getD_append _ _ _ _ (by rw [length_pre]; exact hi)]

theorem tri_rows (L i : ℕ) (hi : i < 3) :
    (triRows ++ litRows L).getD i [] = triRows.getD i [] :=
  List.getD_append _ _ _ _ (by simpa [triRows] using hi)

theorem lit_rows (L m : ℕ) (hm : m < 2 * L) :
    (triRows ++ litRows L).getD (3 + m) [] = if m % 2 = 0 then vpRow (m / 2) else vnRow := by
  rw [List.getD_append_right _ _ _ _ (by simp [triRows]), ← getD_litRows L m hm]
  simp [triRows]

theorem vp_row (w : List SatSym) (j : ℕ) (hj : j < (annW w).length) :
    (gRows w).getD (3 + 2 * j) [] = vpRow j := by
  rw [pre_rows w _ (by simp [base]; omega), lit_rows _ _ (by omega)]
  simp

theorem vn_row (w : List SatSym) (j : ℕ) (hj : j < (annW w).length) :
    (gRows w).getD (4 + 2 * j) [] = vnRow := by
  rw [pre_rows w _ (by simp [base]; omega), show 4 + 2 * j = 3 + (2 * j + 1) by omega,
    lit_rows _ _ (by omega)]
  simp [Nat.add_mod]

theorem fin3_or : ∀ x y o f : Fin 3, x ≠ f → y ≠ f → x ≠ y → x ≠ o → o ≠ y → o = f := by
  decide

theorem fin3_third : ∀ x a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → x ≠ a → x ≠ c → x = b := by
  decide

/-- The accumulator input of the gadget at position `p` (index `j` inside the clause). -/
def accV (L p j : ℕ) : ℕ := if j = 0 then 1 else base L p - 1

theorem accV_succ (L p j : ℕ) : accV L (p + 1) (j + 1) = base L p + 2 := by
  simp [accV, base]; omega

theorem ann_cons (s : SatSym) (r : List SatSym) (t j : ℕ) :
    ann (s :: r) t j = (s, t, j) :: ann r (if s = sep then t + 1 else t)
      (if s = sep then 0 else j + 1) := by
  cases s <;> simp [ann]

/-! ## Colorable ⇒ SAT -/

theorem sound_aux (w : List SatSym) (c : ℕ → Fin 3)
    (hc : ∀ i k, ((gRows w).getD i []).getD k zero = pos → c i ≠ c k)
    (h01 : c 0 ≠ c 1) (h02 : c 0 ≠ c 2) (h12 : c 1 ≠ c 2) :
    ∀ (r : List SatSym) (t j p : ℕ) (F : Bool) (P : List (List SatSym)),
    gRows w = P ++ gadAll (annW w).length p (ann r t j) → P.length = base (annW w).length p →
    j ≤ p → p + r.length = (annW w).length →
    (F = false → c (accV (annW w).length p j) = c 1) →
    evalF (fun j => decide (c (3 + 2 * j) = c 0)) r j F = true
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | s :: r, t, j, p, F, P, hrows, hP, hjp, hlen, hacc => by
    have hjL : j < (annW w).length := by simp at hlen; omega
    rw [ann_cons] at hrows
    obtain ⟨hx, hy, ho, hrows', hP'⟩ := gad_rows hrows hP
    have hlen' : p + 1 + r.length = (annW w).length := by simp at hlen; omega
    have ih := fun F => sound_aux w c hc h01 h02 h12 r _ _ (p + 1) F _ hrows' hP'
    have hb : 3 ≤ base (annW w).length p := by unfold base; omega
    have ex : ∀ k, (k = accV (annW w).length p j ∨ k = base (annW w).length p + 1 ∨
        k = base (annW w).length p + 2) → c (base (annW w).length p) ≠ c k := fun k hk =>
      hc _ k (by rw [hx]; exact (xRow_pos _ _ _ (by omega)).2 (by simpa [accV] using hk))
    have ey : c (base (annW w).length p + 1) ≠ c (litCol s j) :=
      hc _ _ (by rw [hy]; exact (yRow_pos _ _ _).2 rfl)
    have eo : ∀ k, (k = 2 ∨ (s = sep ∧ k = 1) ∨ k = base (annW w).length p + 1) →
        c (base (annW w).length p + 2) ≠ c k := fun k hk =>
      hc _ k (by rw [ho]; exact (oRow_pos _ _ _ (by omega)).2 hk)
    have hor : c (accV (annW w).length p j) = c 1 → c (litCol s j) = c 1 →
        c (base (annW w).length p + 2) = c 1 := fun h1 h2 =>
      fin3_or _ _ _ _ (h1 ▸ ex _ (Or.inl rfl)) (h2 ▸ ey) (ex _ (Or.inr (Or.inl rfl)))
        (ex _ (Or.inr (Or.inr rfl))) (eo _ (Or.inr (Or.inr rfl)))
    have vp := vp_row w j hjL
    have vn := vn_row w j hjL
    have e2 : c (3 + 2 * j) ≠ c 2 := hc _ _ (by rw [vp]; exact (vpRow_pos _ _).2 (Or.inl rfl))
    have e4 : c (3 + 2 * j) ≠ c (4 + 2 * j) :=
      hc _ _ (by rw [vp]; exact (vpRow_pos _ _).2 (Or.inr rfl))
    have e42 : c (4 + 2 * j) ≠ c 2 := hc _ _ (by rw [vn]; exact (vnRow_pos _).2 rfl)
    cases s
    · -- pos
      simp only [evalF]
      simp only [reduceCtorEq, ↓reduceIte] at ih
      refine ih _ (by omega) hlen' fun hF => ?_
      rw [Bool.or_eq_false_iff] at hF
      rw [accV_succ]
      refine hor (hacc hF.1) ?_
      have : c (3 + 2 * j) ≠ c 0 := by simpa using hF.2
      exact fin3_third _ _ _ _ h01 h02 h12 this e2
    · -- neg
      simp only [evalF]
      simp only [reduceCtorEq, ↓reduceIte] at ih
      refine ih _ (by omega) hlen' fun hF => ?_
      rw [Bool.or_eq_false_iff] at hF
      rw [accV_succ]
      refine hor (hacc hF.1) ?_
      have : c (3 + 2 * j) = c 0 := by simpa using hF.2
      exact fin3_third _ _ _ _ h01 h02 h12 (this ▸ e4.symm) e42
    · -- zero
      simp only [evalF]
      simp only [reduceCtorEq, ↓reduceIte] at ih
      refine ih _ (by omega) hlen' fun hF => ?_
      rw [accV_succ]
      exact hor (hacc hF) rfl
    · -- sep
      simp only [evalF, Bool.and_eq_true]
      simp only [↓reduceIte] at ih
      refine ⟨?_, ih _ (by omega) hlen' fun _ => by simp [accV]⟩
      cases F
      · exact absurd (hor (hacc rfl) rfl) (eo 1 (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · rfl

theorem evalF_iff (a : ℕ → Bool) (w : List SatSym) :
    evalF a w 0 false = true ↔ ∀ c ∈ clauses w, ClauseSat a c := by
  have := evalF_eq_clauses a w [] false (by simp [ClauseSat])
  simpa [clauses] using this

theorem evalF_trunc (a : ℕ → Bool) (w : List SatSym) :
    evalF a (trunc w) 0 false = true ↔ evalF a w 0 false = true := by
  rw [evalF_iff, evalF_iff, trunc, clauses_flatMap _ (sep_not_mem_clauses w)]

theorem tri_row0 (w : List SatSym) : (gRows w).getD 0 [] = [zero, pos, pos] := by
  rw [pre_rows w 0 (by simp [base]), tri_rows _ _ (by omega)]; rfl

theorem tri_row1 (w : List SatSym) : (gRows w).getD 1 [] = [zero, zero, pos] := by
  rw [pre_rows w 1 (by simp [base]; omega), tri_rows _ _ (by omega)]; rfl

theorem tri_row2 (w : List SatSym) : (gRows w).getD 2 [] = [] := by
  rw [pre_rows w 2 (by simp [base]; omega), tri_rows _ _ (by omega)]; rfl

/-- Colorable ⇒ SAT. -/
theorem sat_of_col (w : List SatSym) (h : ColLang (G w)) : SATLang w := by
  obtain ⟨c, hc⟩ := h
  rw [clauses_G] at hc
  have h01 : c 0 ≠ c 1 := hc 0 1 (by rw [tri_row0]; rfl)
  have h02 : c 0 ≠ c 2 := hc 0 2 (by rw [tri_row0]; rfl)
  have h12 : c 1 ≠ c 2 := hc 1 2 (by rw [tri_row1]; rfl)
  refine ⟨fun j => decide (c (3 + 2 * j) = c 0), ?_⟩
  rw [← evalF_trunc]
  exact sound_aux w c hc h01 h02 h12 (trunc w) 0 0 0 false _ (gRows_eq w) (length_pre _) le_rfl
    (by rw [length_annW]; simp) (fun _ => rfl)

/-! ## SAT ⇒ colorable -/

/-- The value of the literal input of a gadget. -/
def lv (a : ℕ → Bool) : SatSym → ℕ → Bool
  | pos, j => a j
  | neg, j => !a j
  | _, _ => false

/-- The colors of `x, y, o` of a gadget with accumulator value `F` and literal value `l`. -/
def tri (F l : Bool) : List (Fin 3) := if F then [1, 2, 0] else if l then [2, 1, 0] else [0, 2, 1]

/-- The colors of the gadget vertices (three per position). -/
def gcol (a : ℕ → Bool) : List SatSym → ℕ → Bool → List (Fin 3)
  | [], _, _ => []
  | pos :: r, j, F => tri F (a j) ++ gcol a r (j + 1) (F || a j)
  | neg :: r, j, F => tri F (!a j) ++ gcol a r (j + 1) (F || !a j)
  | zero :: r, j, F => tri F false ++ gcol a r (j + 1) F
  | sep :: r, _, F => tri F false ++ gcol a r 0 false

theorem gcol_cons (a : ℕ → Bool) (s : SatSym) (r : List SatSym) (j : ℕ) (F : Bool) :
    gcol a (s :: r) j F = tri F (lv a s j) ++ gcol a r (if s = sep then 0 else j + 1)
      (if s = sep then false else F || lv a s j) := by
  cases s <;> simp [gcol, lv]

theorem evalF_cons (a : ℕ → Bool) (s : SatSym) (r : List SatSym) (j : ℕ) (F : Bool) :
    evalF a (s :: r) j F = if s = sep then F && evalF a r 0 false
      else evalF a r (j + 1) (F || lv a s j) := by
  cases s <;> simp [evalF, lv]

/-- Colors of the literal vertices. -/
def litC (a : ℕ → Bool) (v : ℕ) : Fin 3 :=
  if (v - 3) % 2 = 0 then (if a ((v - 3) / 2) then 0 else 1)
  else (if a ((v - 3) / 2) then 1 else 0)

/-- The coloring of `G w` from the assignment `a`. -/
def colr (w : List SatSym) (a : ℕ → Bool) (v : ℕ) : Fin 3 :=
  if h : v < 3 then ⟨v, h⟩ else if v < base (annW w).length 0 then litC a v
  else (gcol a (trunc w) 0 false).getD (v - base (annW w).length 0) 0

theorem colr_vp (w : List SatSym) (a : ℕ → Bool) (j : ℕ) (hj : j < (annW w).length) :
    colr w a (3 + 2 * j) = if a j then 0 else 1 := by
  have h1 : ¬ 3 + 2 * j < 3 := by omega
  have h2 : 3 + 2 * j < base (annW w).length 0 := by simp [base]; omega
  have h3 : (3 + 2 * j - 3) % 2 = 0 := by omega
  have h4 : (3 + 2 * j - 3) / 2 = j := by omega
  simp only [colr, h1, h2, litC, h3, h4, dite_false, if_true]

theorem colr_vn (w : List SatSym) (a : ℕ → Bool) (j : ℕ) (hj : j < (annW w).length) :
    colr w a (4 + 2 * j) = if a j then 1 else 0 := by
  have h1 : ¬ 4 + 2 * j < 3 := by omega
  have h2 : 4 + 2 * j < base (annW w).length 0 := by simp [base]; omega
  have h3 : ¬ (4 + 2 * j - 3) % 2 = 0 := by omega
  have h4 : (4 + 2 * j - 3) / 2 = j := by omega
  simp only [colr, h1, h2, litC, h3, h4, dite_false, if_true, if_false]

theorem colr_lit (w : List SatSym) (a : ℕ → Bool) (s : SatSym) (j : ℕ)
    (hj : j < (annW w).length) : colr w a (litCol s j) = if lv a s j then 0 else 1 := by
  cases s
  · simp only [litCol, lv]; exact colr_vp w a j hj
  · simp only [litCol, lv, colr_vn w a j hj]
    exact (by decide : ∀ x : Bool, (if x then (1 : Fin 3) else 0) = if (!x) then 0 else 1) _
  · rfl
  · rfl

theorem colr_gad (w : List SatSym) (a : ℕ → Bool) (p e : ℕ) (Q : List (Fin 3))
    (l : List (Fin 3)) (hQ : ∃ R, gcol a (trunc w) 0 false = Q ++ l ++ R) (hl : Q.length = 3 * p)
    (he : e < l.length) : colr w a (base (annW w).length p + e) = l.getD e 0 := by
  obtain ⟨R, hR⟩ := hQ
  have h1 : ¬ base (annW w).length p + e < 3 := by simp [base]; omega
  have h2 : ¬ base (annW w).length p + e < base (annW w).length 0 := by simp [base]; omega
  simp only [colr, h1, h2, dite_false, if_false, hR]
  have : base (annW w).length p + e - base (annW w).length 0 = Q.length + e := by
    simp [base, hl]; omega
  rw [this, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ he]

theorem tri_facts (F l : Bool) :
    (tri F l).getD 0 0 ≠ (if F then 0 else 1) ∧ (tri F l).getD 0 0 ≠ (tri F l).getD 1 0 ∧
    (tri F l).getD 0 0 ≠ (tri F l).getD 2 0 ∧ (tri F l).getD 1 0 ≠ (if l then 0 else 1) ∧
    (tri F l).getD 2 0 ≠ 2 ∧ (tri F l).getD 2 0 ≠ (tri F l).getD 1 0 ∧
    (F = true → (tri F l).getD 2 0 ≠ 1) ∧ (tri F l).getD 2 0 = (if (F || l) then 0 else 1) := by
  cases F <;> cases l <;> decide

theorem length_tri (F l : Bool) : (tri F l).length = 3 := by unfold tri; split_ifs <;> rfl

theorem compl_aux (w : List SatSym) (a : ℕ → Bool) :
    ∀ (r : List SatSym) (t j p : ℕ) (F : Bool) (P : List (List SatSym)) (Q : List (Fin 3)),
    gRows w = P ++ gadAll (annW w).length p (ann r t j) → P.length = base (annW w).length p →
    gcol a (trunc w) 0 false = Q ++ gcol a r j F → Q.length = 3 * p →
    j ≤ p → p + r.length = (annW w).length → evalF a r j F = true →
    colr w a (accV (annW w).length p j) = (if F then 0 else 1) →
    ∀ i k, base (annW w).length p ≤ i → ((gRows w).getD i []).getD k zero = pos →
      colr w a i ≠ colr w a k
  | [], _, _, _, _, P, _, hrows, hP, _, _, _, _, _, _, i, k, hi, hk => by
    rw [hrows, List.getD_append_right _ _ _ _ (by omega)] at hk
    simp [gadAll, ann] at hk
  | s :: r, t, j, p, F, P, Q, hrows, hP, hQ, hQl, hjp, hlen, hev, hacc, i, k, hi, hk => by
    have hjL : j < (annW w).length := by simp at hlen; omega
    rw [ann_cons] at hrows
    obtain ⟨hx, hy, ho, hrows', hP'⟩ := gad_rows hrows hP
    rw [gcol_cons] at hQ
    have hQ' := hQ
    rw [← List.append_assoc] at hQ'
    have hQl' : (Q ++ tri F (lv a s j)).length = 3 * (p + 1) := by
      simp [hQl, length_tri]; ring
    have hlen' : p + 1 + r.length = (annW w).length := by simp at hlen; omega
    have hb : 3 ≤ base (annW w).length p := by unfold base; omega
    have hc : ∀ e < 3, colr w a (base (annW w).length p + e) = (tri F (lv a s j)).getD e 0 :=
      fun e he => colr_gad w a p e Q _ ⟨_, hQ'⟩ hQl (by rw [length_tri]; exact he)
    have c0 := hc 0 (by omega)
    have c1 := hc 1 (by omega)
    have c2 := hc 2 (by omega)
    simp only [Nat.add_zero] at c0
    have cl := colr_lit w a s j hjL
    have tf := tri_facts F (lv a s j)
    rw [evalF_cons] at hev
    by_cases hib : i < base (annW w).length p + 3
    · have : i = base (annW w).length p ∨ i = base (annW w).length p + 1 ∨
          i = base (annW w).length p + 2 := by omega
      rcases this with rfl | rfl | rfl
      · rw [hx, xRow_pos _ _ _ (by omega)] at hk
        rcases hk with hk | rfl | rfl
        · have : k = accV (annW w).length p j := by simpa [accV] using hk
          rw [this, hacc, c0]; exact tf.1
        · rw [c0, c1]; exact tf.2.1
        · rw [c0, c2]; exact tf.2.2.1
      · rw [hy, yRow_pos] at hk
        rw [hk, c1, cl]; exact tf.2.2.2.1
      · rw [ho, oRow_pos _ _ _ (by omega)] at hk
        rcases hk with rfl | ⟨rfl, rfl⟩ | rfl
        · rw [c2]; exact tf.2.2.2.2.1
        · simp only [↓reduceIte, Bool.and_eq_true] at hev
          rw [c2]; exact tf.2.2.2.2.2.2.1 hev.1
        · rw [c2, c1]; exact tf.2.2.2.2.2.1
    · refine compl_aux w a r _ _ (p + 1) _ _ _ hrows' hP' hQ' hQl' ?_ hlen' ?_ ?_ i k
        (by unfold base at *; omega) hk
      · split_ifs <;> omega
      · split_ifs at hev ⊢
        · simp only [Bool.and_eq_true] at hev; exact hev.2
        · exact hev
      · by_cases hs : s = sep
        · rw [if_pos hs, if_pos hs, show accV (annW w).length (p + 1) 0 = 1 by simp [accV]]
          rfl
        · rw [if_neg hs, if_neg hs, accV_succ, c2]; exact tf.2.2.2.2.2.2.2

theorem pre_ok (w : List SatSym) (a : ℕ → Bool) (i k : ℕ) (hi : i < base (annW w).length 0)
    (hk : ((gRows w).getD i []).getD k zero = pos) : colr w a i ≠ colr w a k := by
  have c0 : colr w a 0 = 0 := rfl
  have c1 : colr w a 1 = 1 := rfl
  have c2 : colr w a 2 = 2 := rfl
  rw [pre_rows w i hi] at hk
  by_cases h3 : i < 3
  · rw [tri_rows _ _ h3] at hk
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · have : k = 1 ∨ k = 2 := by
        simp only [triRows, List.getD_cons_zero, getD_cons_pos_iff, getD_nil_pos] at hk
        simp at hk; omega
      rcases this with rfl | rfl
      · rw [c0, c1]; decide
      · rw [c0, c2]; decide
    · have : k = 2 := by
        simp only [triRows, List.getD_cons_zero, List.getD_cons_succ, getD_cons_pos_iff,
          getD_nil_pos] at hk
        simp at hk; omega
      subst this; rw [c1, c2]; decide
    · simp [triRows] at hk
  · have hm : i - 3 < 2 * (annW w).length := by simp [base] at hi; omega
    have e := lit_rows (annW w).length (i - 3) hm
    rw [show 3 + (i - 3) = i by omega] at e
    rw [e] at hk
    split_ifs at hk with hpar
    · have hi' : i = 3 + 2 * ((i - 3) / 2) := by omega
      have hj : (i - 3) / 2 < (annW w).length := by omega
      rw [vpRow_pos] at hk
      rw [hi', colr_vp w a _ hj]
      rcases hk with rfl | rfl
      · rw [c2]; exact (by decide : ∀ x : Bool, (if x then (0 : Fin 3) else 1) ≠ 2) _
      · rw [colr_vn w a _ hj]
        exact (by decide : ∀ x : Bool, (if x then (0 : Fin 3) else 1) ≠ if x then 1 else 0) _
    · have hi' : i = 4 + 2 * ((i - 3) / 2) := by omega
      have hj : (i - 3) / 2 < (annW w).length := by omega
      rw [vnRow_pos] at hk
      rw [hi', colr_vn w a _ hj, hk, c2]
      exact (by decide : ∀ x : Bool, (if x then (1 : Fin 3) else 0) ≠ 2) _

/-- SAT ⇒ colorable. -/
theorem col_of_sat (w : List SatSym) (h : SATLang w) : ColLang (G w) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨colr w a, fun i k hk => ?_⟩
  rw [clauses_G] at hk
  by_cases hi : i < base (annW w).length 0
  · exact pre_ok w a i k hi hk
  · exact compl_aux w a (trunc w) 0 0 0 false _ [] (gRows_eq w) (length_pre _) rfl rfl le_rfl
      (by rw [length_annW]; simp) ((evalF_trunc a w).2 ha) rfl i k (by omega) hk

/-- **Correctness of the reduction SAT ≤ 3-COLORING.** -/
theorem sat_iff_col (w : List SatSym) : SATLang w ↔ ColLang (G w) :=
  ⟨col_of_sat w, sat_of_col w⟩

end Pnp.Karp.Color
