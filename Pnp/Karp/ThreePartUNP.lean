import Pnp.Karp.ThreePartUVer
import Pnp.Karp.BinPackingNP

/-!
# Unary 3-PARTITION ∈ NP (official definition)

The checking relation is `tpuv_vres w y = true` (`Pnp/Karp/ThreePartUVer.lean`).  Groupings are
handled as labelled item lists, as for BIN PACKING (`Pnp/Karp/BinPackingNP.lean`) and binary
3-PARTITION (`Pnp/Karp/ThreePartNP.lean`), with the unary group sums `tpuv_ls`:

* `tpuv_fwd`: the certificate `bpv_cert` of a grouping into `m` groups of sum `B` is accepted
  with `3 m` marks;
* `tpuv_bwd`: an accepted certificate with `k` marks gives `3 ∣ k` and a grouping into `k / 3`
  groups of sum `B`;
* `tpuv_bnd_iff`: the bounds loop checks `B < 4 a ∧ 2 a < B` for every item;
* `tpuv_lang_iff`: `TPULang w ↔ ∃ y, |y| ≤ |w|² ∧ tpuv_vres w y`;
* `tpu_in_np`: `TPULang ∈ NP`, via `tpuv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.ThreePartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.BinPacking Pnp.Karp.ThreePart

/-! ## Unary sums of labelled lists -/

/-- The total length of the items with label `b`. -/
def tpuv_ls : List (List SatSym × ℕ) → ℕ → ℕ
  | [], _ => 0
  | p :: L, b => (if p.2 = b then p.1.length else 0) + tpuv_ls L b

theorem tpuv_sel_cert (b₀ : ℕ) (R' : Str) : ∀ L : List (List SatSym × ℕ),
    tpuv_s (L.map Prod.fst) (L.map (fun p => decide (p.2 = b₀)) ++ R') = tpuv_ls L b₀
  | [] => by simp [tpuv_s, tpuv_ls]
  | p :: L => by
    have ih := tpuv_sel_cert b₀ R' L
    by_cases h : p.2 = b₀ <;> simp [tpuv_s, tpuv_ls, h, ih]

theorem tpuv_ls_filter (b₀ : ℕ) : ∀ (L : List (List SatSym × ℕ)) (b : ℕ), b ≠ b₀ →
    tpuv_ls (L.filter (fun p => !decide (p.2 = b₀))) b = tpuv_ls L b
  | [], _, _ => by simp [tpuv_ls]
  | p :: L, b, hb => by
    have ih := tpuv_ls_filter b₀ L b hb
    by_cases h : p.2 = b₀
    · have : p.2 ≠ b := by omega
      simp [tpuv_ls, h, ih]
      intro e; exfalso; omega
    · simp [tpuv_ls, h, ih]

theorem tpuv_lab_ls : ∀ (rows : List (List SatSym)) (R : Str)
    (L' : List (List SatSym × ℕ)), L'.map Prod.fst = bpv_U rows R →
    tpuv_ls (bpv_lab rows R L') 0 = tpuv_s rows R ∧
      ∀ b, tpuv_ls (bpv_lab rows R L') (b + 1) = tpuv_ls L' b
  | [], R, L', hL => by
    have : L' = [] := by simpa [bpv_U] using hL
    subst this
    simp [bpv_lab, tpuv_ls, tpuv_s]
  | r :: rs, R, L', hL => by
    by_cases h : R.headD false = true
    · have h' : R.head?.getD false = true := by simpa using h
      simp only [bpv_U, h, if_true] at hL
      obtain ⟨h3, h4⟩ := tpuv_lab_ls rs R.tail L' hL
      refine ⟨by simp [bpv_lab, h', tpuv_ls, tpuv_s, h3], ?_⟩
      intro b
      simp [bpv_lab, h', tpuv_ls, h4]
    · have h' : R.head?.getD false = false := by simpa using h
      simp only [bpv_U, h, Bool.false_eq_true, if_false] at hL
      rcases L' with _ | ⟨q, L''⟩
      · simp at hL
      · simp only [List.map_cons, List.cons.injEq] at hL
        obtain ⟨hq, hL⟩ := hL
        obtain ⟨h3, h4⟩ := tpuv_lab_ls rs R.tail L'' hL
        refine ⟨by simp [bpv_lab, h', tpuv_ls, tpuv_s, h3], ?_⟩
        intro b
        simp [bpv_lab, h', tpuv_ls, h4, hq]

theorem tpuv_unSum_labF : ∀ (rows : List (List SatSym)) (f : ℕ → ℕ) (b : ℕ),
    unSum rows f b = tpuv_ls (bpv_labF rows f) b
  | [], f, b => rfl
  | r :: rs, f, b => by simp [unSum, bpv_labF, tpuv_ls, tpuv_unSum_labF rs]

/-! ## The bound check -/

theorem tpuv_bnd_iff (c : ℕ) : ∀ rows : List (List SatSym),
    tpuv_bnd c rows = true ↔ ∀ r ∈ rows, c < 4 * r.length ∧ 2 * r.length < c
  | [] => by simp [tpuv_bnd]
  | r :: rs => by
    simp only [tpuv_bnd, Bool.and_eq_true, decide_eq_true_eq, tpuv_bnd_iff c rs, List.mem_cons,
      forall_eq_or_imp]

/-! ## Grouping → certificate -/

theorem tpuv_fwd (c : ℕ) : ∀ (m b₀ : ℕ) (L : List (List SatSym × ℕ)),
    (∀ p ∈ L, b₀ ≤ p.2 ∧ p.2 < b₀ + m) →
    (∀ b, b₀ ≤ b → b < b₀ + m → tpuv_ls L b = c) →
    tpuv_go c (3 * m) (L.map Prod.fst) (bpv_cert b₀ m L) = true
  | 0, b₀, L, h1, _ => by
    rcases L with _ | ⟨p, L⟩
    · simp [tpuv_go]
    · have := h1 p (by simp); omega
  | m + 1, b₀, L, h1, h2 => by
    rw [show 3 * (m + 1) = 3 * m + 3 by ring]
    simp only [tpuv_go, bpv_cert]
    rw [Bool.and_eq_true, bpv_U_cert, bpv_rest_cert]
    refine ⟨?_, tpuv_fwd c m (b₀ + 1) _ ?_ ?_⟩
    · rw [decide_eq_true_eq, tpuv_sel_cert]
      exact h2 b₀ le_rfl (by omega)
    · intro p hp
      simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hp
      have := h1 p hp.1
      omega
    · intro b hb1 hb2
      rw [tpuv_ls_filter b₀ L b (by omega)]
      exact h2 b (by omega) (by omega)

/-! ## Certificate → grouping -/

theorem tpuv_bwd (c : ℕ) : ∀ (k : ℕ) (rows : List (List SatSym)) (R : Str),
    tpuv_go c k rows R = true → k % 3 = 0 ∧
    ∃ L : List (List SatSym × ℕ), L.map Prod.fst = rows ∧ (∀ p ∈ L, p.2 < k / 3) ∧
      ∀ b < k / 3, tpuv_ls L b = c
  | 0, rows, R, h => by
    have : rows = [] := by simpa [tpuv_go] using h
    subst this
    exact ⟨rfl, [], rfl, by simp, fun b hb => by omega⟩
  | 1, rows, R, h => by simp [tpuv_go] at h
  | 2, rows, R, h => by simp [tpuv_go] at h
  | k + 3, rows, R, h => by
    simp only [tpuv_go, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hk, L', h1, h2, h3⟩ := tpuv_bwd c k _ _ h.2
    have hk3 : (k + 3) / 3 = k / 3 + 1 := by omega
    obtain ⟨g1, g2, -, -⟩ := bpv_lab_spec (k / 3) rows R L' h1 h2
    obtain ⟨g3, g4⟩ := tpuv_lab_ls rows R L' h1
    refine ⟨by omega, _, g1, by rw [hk3]; exact g2, fun b hb => ?_⟩
    rw [hk3] at hb
    rcases b with _ | b
    · rw [g3]; exact h.1
    · rw [g4]; exact h3 b (by omega)

/-! ## The language -/

theorem tpuv_vres_iff (w : List SatSym) (y : Str) :
    tpuv_vres w y = true ↔ ∃ items Bv, clauses w = items ++ [Bv] ∧
      tpuv_bnd Bv.length items = true ∧ tpuv_go Bv.length items.length items y = true := by
  unfold tpuv_vres
  have key : ∀ items Bv, clauses w = items ++ [Bv] →
      (clauses w).reverse = Bv :: items.reverse := by
    intro items Bv h; rw [h]; simp
  rcases h : (clauses w).reverse with _ | ⟨Bv, rr⟩
  · simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro items Bv hc; rw [key items Bv hc] at h; simp at h
  · constructor
    · intro hg
      rw [Bool.and_eq_true] at hg
      exact ⟨rr.reverse, Bv, by rw [← List.reverse_reverse (clauses w), h]; simp, hg⟩
    · rintro ⟨items, Bv', hc, hb, hg⟩
      rw [key items Bv' hc] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hb, hg]

theorem tpuv_lang_iff (w : List SatSym) :
    TPULang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ tpuv_vres w y = true := by
  constructor
  · rintro ⟨items, Bv, hc, h3, hb, f, hf, hs⟩
    set L := bpv_labF items f
    set m := items.length / 3
    have hL : L.length = items.length := by
      rw [← List.length_map (f := Prod.fst), bpv_labF_fst]
    refine ⟨bpv_cert 0 m L, ?_, (tpuv_vres_iff w _).2 ⟨items, Bv, hc, ?_, ?_⟩⟩
    · have h1 := bpv_cert_length m 0 L
      have h2 := length_clauses_le w
      rw [hc] at h2
      simp only [List.length_append, List.length_cons, List.length_nil] at h2
      have : m * L.length ≤ w.length * w.length :=
        Nat.mul_le_mul (by omega) (by omega)
      rw [pow_two]; omega
    · rw [tpuv_bnd_iff]
      exact hb
    · have hn : items.length = 3 * m := by omega
      have := tpuv_fwd Bv.length m 0 L
        (fun p hp => ⟨Nat.zero_le _, by simpa using bpv_labF_lt _ items f hf p hp⟩)
        (fun b _ hb' => by
          rw [← tpuv_unSum_labF]; exact hs b (by omega))
      rwa [bpv_labF_fst, ← hn] at this
  · rintro ⟨y, -, hy⟩
    obtain ⟨items, Bv, hc, hb, hg⟩ := (tpuv_vres_iff w y).1 hy
    obtain ⟨h3, L, h1, h2, hs⟩ := tpuv_bwd Bv.length items.length items y hg
    rw [tpuv_bnd_iff] at hb
    subst h1
    refine ⟨L.map Prod.fst, Bv, hc, h3, hb, fun i => (L.getD i ([], 0)).2, ?_, ?_⟩
    · intro i hi
      have hi' : i < L.length := by simpa using hi
      show (L.getD i ([], 0)).2 < _
      rw [List.getD_eq_getElem _ _ hi']
      exact h2 _ (List.getElem_mem hi')
    · intro b hb'
      rw [tpuv_unSum_labF, bpv_labF_getD]
      exact hs b hb'

/-! ## Transfer to the official class -/

/-- **Unary 3-PARTITION ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem tpu_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      TPULang := by
  classical
  have hrun := fun z => ((tpuv_exec_ver z).mono (tpuv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg tpuv_ver) (tb 8 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg tpuv_ver, 8, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => tpuv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => tpuv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [tpuv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.ThreePartU
