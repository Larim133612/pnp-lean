import Pnp.Karp.BinPackingVer
import Pnp.Karp.KnapNP

/-!
# BIN PACKING ∈ NP (official definition)

The checking relation is `bpv_vres w y = true` (`Pnp/Karp/BinPackingVer.lean`).

* packings are handled as *labelled item lists* `L : List (List SatSym × ℕ)` (item, bin), with
  the bin sums `bpv_bs`;
* `bpv_fwd`: the certificate `bpv_cert` of a packing (pass `b` selects the remaining items of
  bin `b`) is accepted;
* `bpv_bwd`: an accepted certificate yields a packing (`bpv_lab`: the items selected in the
  first pass go to bin `0`, the others to `1 +` their bin in the later passes);
* `bpv_lang_iff`: `BPLang w ↔ ∃ y, |y| ≤ |w|² ∧ bpv_vres w y`;
* `bp_in_np`: `BPLang ∈ NP`, via `bpv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.BinPacking

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack

/-! ## Labelled item lists -/

/-- The sum of the sizes of the items with label `b`. -/
def bpv_bs : List (List SatSym × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: L, b => (if p.2 = b then bv p.1 else 0) + bpv_bs L b

theorem bpv_A_val : ∀ (rows : List (List SatSym)) (R A : Str),
    sv_bval (bpv_A rows R A) = sv_bval A + selSum rows R
  | [], R, A => by simp [bpv_A, selSum]
  | r :: rs, R, A => by
    rw [bpv_A, bpv_A_val, selSum]
    cases h : R.headD false <;> simp only [h, if_true, Bool.false_eq_true, if_false] <;>
      simp [sv_bval_addL, sv_bval_bits] <;> omega

/-! ## Packing → certificate -/

/-- The certificate of a labelled list: pass `b` (from `b₀`) selects the items with label `b`. -/
def bpv_cert : ℕ → ℕ → List (List SatSym × ℕ) → Str
  | _, 0, _ => []
  | b₀, k + 1, L => L.map (fun p => decide (p.2 = b₀)) ++
      bpv_cert (b₀ + 1) k (L.filter (fun p => !decide (p.2 = b₀)))

section Fwd
variable (b₀ : ℕ) (R' : Str)

theorem bpv_sel_cert : ∀ L : List (List SatSym × ℕ),
    selSum (L.map Prod.fst) (L.map (fun p => decide (p.2 = b₀)) ++ R') = bpv_bs L b₀
  | [] => by simp [selSum, bpv_bs]
  | p :: L => by
    have ih := bpv_sel_cert L
    by_cases h : p.2 = b₀ <;> simp [selSum, bpv_bs, h, ih]

theorem bpv_U_cert : ∀ L : List (List SatSym × ℕ),
    bpv_U (L.map Prod.fst) (L.map (fun p => decide (p.2 = b₀)) ++ R') =
      (L.filter (fun p => !decide (p.2 = b₀))).map Prod.fst
  | [] => by simp [bpv_U]
  | p :: L => by
    have ih := bpv_U_cert L
    by_cases h : p.2 = b₀ <;> simp [bpv_U, h, ih]

theorem bpv_rest_cert : ∀ L : List (List SatSym × ℕ),
    bpv_rest (L.map Prod.fst) (L.map (fun p => decide (p.2 = b₀)) ++ R') = R'
  | [] => by simp [bpv_rest]
  | p :: L => by simp [bpv_rest, bpv_rest_cert L]

theorem bpv_bs_filter : ∀ (L : List (List SatSym × ℕ)) (b : ℕ), b ≠ b₀ →
    bpv_bs (L.filter (fun p => !decide (p.2 = b₀))) b = bpv_bs L b
  | [], _, _ => by simp [bpv_bs]
  | p :: L, b, hb => by
    have ih := bpv_bs_filter L b hb
    by_cases h : p.2 = b₀
    · have : p.2 ≠ b := by omega
      simp [bpv_bs, h, ih]
      intro e; exfalso; omega
    · simp [bpv_bs, h, ih]

end Fwd

theorem bpv_fwd (Cb : Str) : ∀ (k b₀ : ℕ) (L : List (List SatSym × ℕ)),
    (∀ p ∈ L, b₀ ≤ p.2 ∧ p.2 < b₀ + k) →
    (∀ b, b₀ ≤ b → b < b₀ + k → bpv_bs L b ≤ sv_bval Cb) →
    bpv_go Cb k (L.map Prod.fst) (bpv_cert b₀ k L) = true
  | 0, b₀, L, h1, _ => by
    rcases L with _ | ⟨p, L⟩
    · simp [bpv_go]
    · have := h1 p (by simp); omega
  | k + 1, b₀, L, h1, h2 => by
    simp only [bpv_go, bpv_cert, Bool.and_eq_true]
    rw [bpv_U_cert, bpv_rest_cert]
    refine ⟨?_, bpv_fwd Cb k (b₀ + 1) _ ?_ ?_⟩
    · rw [kv_le_iff, bpv_A_val, bpv_sel_cert]
      simpa [sv_bval] using h2 b₀ le_rfl (by omega)
    · intro p hp
      simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hp
      have := h1 p hp.1
      omega
    · intro b hb1 hb2
      rw [bpv_bs_filter b₀ L b (by omega)]
      exact h2 b (by omega) (by omega)

theorem bpv_cert_length : ∀ (k b₀ : ℕ) (L : List (List SatSym × ℕ)),
    (bpv_cert b₀ k L).length ≤ k * L.length
  | 0, _, _ => by simp [bpv_cert]
  | k + 1, b₀, L => by
    have ih := bpv_cert_length k (b₀ + 1) (L.filter (fun p => !decide (p.2 = b₀)))
    have hf := List.length_filter_le (fun p : List SatSym × ℕ => !decide (p.2 = b₀)) L
    have := Nat.mul_le_mul_left k hf
    simp only [bpv_cert, List.length_append, List.length_map]
    rw [Nat.succ_mul]
    omega

/-! ## Certificate → packing -/

/-- Labels from a pass: selected items get `0`, the others `1 +` their label in `L'`. -/
def bpv_lab : List (List SatSym) → Str → List (List SatSym × ℕ) → List (List SatSym × ℕ)
  | [], _, _ => []
  | r :: rs, R, L' =>
    if R.headD false then (r, 0) :: bpv_lab rs R.tail L'
    else (r, (L'.headD (r, 0)).2 + 1) :: bpv_lab rs R.tail L'.tail

theorem bpv_lab_spec (k : ℕ) : ∀ (rows : List (List SatSym)) (R : Str)
    (L' : List (List SatSym × ℕ)), L'.map Prod.fst = bpv_U rows R → (∀ q ∈ L', q.2 < k) →
    (bpv_lab rows R L').map Prod.fst = rows ∧ (∀ p ∈ bpv_lab rows R L', p.2 < k + 1) ∧
      bpv_bs (bpv_lab rows R L') 0 = selSum rows R ∧
      ∀ b, bpv_bs (bpv_lab rows R L') (b + 1) = bpv_bs L' b
  | [], R, L', hL, _ => by
    have : L' = [] := by simpa [bpv_U] using hL
    subst this
    simp [bpv_lab, bpv_bs, selSum]
  | r :: rs, R, L', hL, hk => by
    by_cases h : R.headD false = true
    · have h' : R.head?.getD false = true := by simpa using h
      simp only [bpv_U, h, if_true] at hL
      obtain ⟨h1, h2, h3, h4⟩ := bpv_lab_spec k rs R.tail L' hL hk
      refine ⟨by simp [bpv_lab, h', h1], ?_, by simp [bpv_lab, h', bpv_bs, selSum, h3], ?_⟩
      · intro p hp
        simp only [bpv_lab, h, if_true, List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp
        · exact h2 p hp
      · intro b
        simp [bpv_lab, h', bpv_bs, h4]
    · have h' : R.head?.getD false = false := by simpa using h
      simp only [bpv_U, h, Bool.false_eq_true, if_false] at hL
      rcases L' with _ | ⟨q, L''⟩
      · simp at hL
      · simp only [List.map_cons, List.cons.injEq] at hL
        obtain ⟨hq, hL⟩ := hL
        obtain ⟨h1, h2, h3, h4⟩ := bpv_lab_spec k rs R.tail L'' hL
          (fun q' hq' => hk q' (by simp [hq']))
        have hqk := hk q (by simp)
        refine ⟨by simp [bpv_lab, h', h1], ?_, by simp [bpv_lab, h', bpv_bs, selSum, h3], ?_⟩
        · intro p hp
          simp only [bpv_lab, h, Bool.false_eq_true, if_false, List.mem_cons,
            List.headD_cons, List.tail_cons] at hp
          rcases hp with rfl | hp
          · simp; omega
          · exact h2 p hp
        · intro b
          simp [bpv_lab, h', bpv_bs, h4, hq]

theorem bpv_bwd (Cb : Str) : ∀ (k : ℕ) (rows : List (List SatSym)) (R : Str),
    bpv_go Cb k rows R = true →
    ∃ L : List (List SatSym × ℕ), L.map Prod.fst = rows ∧ (∀ p ∈ L, p.2 < k) ∧
      ∀ b < k, bpv_bs L b ≤ sv_bval Cb
  | 0, rows, R, h => by
    have : rows = [] := by simpa [bpv_go] using h
    subst this
    exact ⟨[], rfl, by simp, fun b hb => by omega⟩
  | k + 1, rows, R, h => by
    simp only [bpv_go, Bool.and_eq_true] at h
    obtain ⟨L', h1, h2, h3⟩ := bpv_bwd Cb k _ _ h.2
    obtain ⟨g1, g2, g3, g4⟩ := bpv_lab_spec k rows R L' h1 h2
    refine ⟨_, g1, g2, fun b hb => ?_⟩
    rcases b with _ | b
    · have := h.1
      rw [kv_le_iff, bpv_A_val] at this
      simpa [sv_bval, g3] using this
    · rw [g4]; exact h3 b (by omega)

/-! ## Labelled lists and bin assignments -/

/-- The labelled list of the items `rows` put into bins by `f`. -/
def bpv_labF : List (List SatSym) → (ℕ → ℕ) → List (List SatSym × ℕ)
  | [], _ => []
  | r :: rs, f => (r, f 0) :: bpv_labF rs (fun i => f (i + 1))

theorem bpv_binSum_labF : ∀ (rows : List (List SatSym)) (f : ℕ → ℕ) (b : ℕ),
    binSum rows f b = bpv_bs (bpv_labF rows f) b
  | [], f, b => rfl
  | r :: rs, f, b => by simp [binSum, bpv_labF, bpv_bs, bpv_binSum_labF rs]

theorem bpv_labF_fst : ∀ (rows : List (List SatSym)) (f : ℕ → ℕ),
    (bpv_labF rows f).map Prod.fst = rows
  | [], f => rfl
  | r :: rs, f => by simp [bpv_labF, bpv_labF_fst rs]

theorem bpv_labF_lt (k : ℕ) : ∀ (rows : List (List SatSym)) (f : ℕ → ℕ),
    (∀ i < rows.length, f i < k) → ∀ p ∈ bpv_labF rows f, p.2 < k
  | [], f, _ => by simp [bpv_labF]
  | r :: rs, f, h => by
    intro p hp
    simp only [bpv_labF, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h 0 (by simp)
    · exact bpv_labF_lt k rs _ (fun i hi => h (i + 1) (by simp; omega)) p hp

theorem bpv_labF_getD : ∀ L : List (List SatSym × ℕ),
    bpv_labF (L.map Prod.fst) (fun i => (L.getD i ([], 0)).2) = L
  | [] => rfl
  | p :: L => by
    simp only [List.map_cons, bpv_labF, List.getD_cons_zero, List.getD_cons_succ]
    rw [bpv_labF_getD L]

/-! ## The language -/

theorem bpv_vres_iff (w : List SatSym) (y : Str) :
    bpv_vres w y = true ↔ ∃ items C kr, clauses w = items ++ [C, kr] ∧
      bpv_go (sv_bits C) kr.length items y = true := by
  unfold bpv_vres
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

theorem bpv_lang_iff (w : List SatSym) :
    BPLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ bpv_vres w y = true := by
  constructor
  · rintro ⟨items, C, kr, hc, f, hf, hb⟩
    set L := bpv_labF items f
    refine ⟨bpv_cert 0 kr.length L, ?_, (bpv_vres_iff w _).2 ⟨items, C, kr, hc, ?_⟩⟩
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
    · have := bpv_fwd (sv_bits C) kr.length 0 L
        (fun p hp => ⟨Nat.zero_le _, by simpa using bpv_labF_lt _ items f hf p hp⟩)
        (fun b _ hb' => by
          rw [sv_bval_bits, ← bpv_binSum_labF]; exact hb b (by omega))
      rwa [bpv_labF_fst] at this
  · rintro ⟨y, -, hy⟩
    obtain ⟨items, C, kr, hc, hg⟩ := (bpv_vres_iff w y).1 hy
    obtain ⟨L, h1, h2, h3⟩ := bpv_bwd (sv_bits C) kr.length items y hg
    subst h1
    refine ⟨L.map Prod.fst, C, kr, hc, fun i => (L.getD i ([], 0)).2, ?_, ?_⟩
    · intro i hi
      rw [List.length_map] at hi
      show (L.getD i ([], 0)).2 < _
      rw [List.getD_eq_getElem _ _ hi]
      exact h2 _ (List.getElem_mem hi)
    · intro b hb
      rw [bpv_binSum_labF, bpv_labF_getD, ← sv_bval_bits]
      exact h3 b hb

/-! ## Transfer to the official class -/

/-- **BIN PACKING ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem bp_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      BPLang := by
  classical
  have hrun := fun z => ((bpv_exec_ver z).mono (bpv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg bpv_ver) (tb 8 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg bpv_ver, 8, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => bpv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => bpv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [bpv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.BinPacking
