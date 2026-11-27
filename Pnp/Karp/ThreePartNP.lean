import Pnp.Karp.ThreePartVer
import Pnp.Karp.BinPackingNP

/-!
# 3-PARTITION ∈ NP (official definition)

The checking relation is `tpv_vres w y = true` (`Pnp/Karp/ThreePartVer.lean`).  Groupings are
handled as labelled item lists, as for BIN PACKING (`Pnp/Karp/BinPackingNP.lean`):

* `tpv_fwd`: the certificate `bpv_cert` of a grouping into `m` groups of sum `B` is accepted
  with `3 m` marks;
* `tpv_bwd`: an accepted certificate with `k` marks gives `3 ∣ k` and a grouping into `k / 3`
  groups of sum `B`;
* `tpv_bnd_iff`: the bounds loop checks `B < 4 a ∧ 2 a < B` for every item;
* `tpv_lang_iff`: `TPLang w ↔ ∃ y, |y| ≤ |w|² ∧ tpv_vres w y`;
* `tp_in_np`: `TPLang ∈ NP`, via `tpv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.ThreePart

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.BinPacking

/-! ## The bound check -/

theorem tpv_bval_cons (b : Bool) (A : Str) :
    sv_bval (b :: A) = (if b then 1 else 0) + 2 * sv_bval A := rfl

theorem tpv_ok_iff (C : Str) (r : List SatSym) :
    tpv_ok C r = true ↔ sv_bval C < 4 * bv r ∧ 2 * bv r < sv_bval C := by
  have hA : sv_bval (sv_addL false [] (sv_bits r)) = bv r := by
    rw [sv_bval_addL, sv_bval_bits]; simp [sv_bval]
  simp only [tpv_ok, tpv_okA, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
    kv_le_iff, tpv_bval_cons, hA]
  simp only [Bool.false_eq_true, if_false, zero_add, not_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, by omega⟩

theorem tpv_bnd_iff (C : Str) : ∀ rows : List (List SatSym),
    tpv_bnd C rows = true ↔ ∀ r ∈ rows, sv_bval C < 4 * bv r ∧ 2 * bv r < sv_bval C
  | [] => by simp [tpv_bnd]
  | r :: rs => by
    simp only [tpv_bnd, Bool.and_eq_true, tpv_ok_iff, tpv_bnd_iff C rs, List.mem_cons,
      forall_eq_or_imp]

/-! ## Grouping → certificate -/

theorem tpv_eq_iff (A C : Str) :
    (kv_leF true A C && kv_leF true C A) = true ↔ sv_bval A = sv_bval C := by
  simp only [Bool.and_eq_true, kv_le_iff]; omega

theorem tpv_fwd (Cb : Str) : ∀ (m b₀ : ℕ) (L : List (List SatSym × ℕ)),
    (∀ p ∈ L, b₀ ≤ p.2 ∧ p.2 < b₀ + m) →
    (∀ b, b₀ ≤ b → b < b₀ + m → bpv_bs L b = sv_bval Cb) →
    tpv_go Cb (3 * m) (L.map Prod.fst) (bpv_cert b₀ m L) = true
  | 0, b₀, L, h1, _ => by
    rcases L with _ | ⟨p, L⟩
    · simp [tpv_go]
    · have := h1 p (by simp); omega
  | m + 1, b₀, L, h1, h2 => by
    rw [show 3 * (m + 1) = 3 * m + 3 by ring]
    simp only [tpv_go, bpv_cert]
    rw [Bool.and_eq_true, bpv_U_cert, bpv_rest_cert]
    refine ⟨?_, tpv_fwd Cb m (b₀ + 1) _ ?_ ?_⟩
    · rw [tpv_eq_iff, bpv_A_val, bpv_sel_cert]
      simpa [sv_bval] using h2 b₀ le_rfl (by omega)
    · intro p hp
      simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hp
      have := h1 p hp.1
      omega
    · intro b hb1 hb2
      rw [bpv_bs_filter b₀ L b (by omega)]
      exact h2 b (by omega) (by omega)

/-! ## Certificate → grouping -/

theorem tpv_bwd (Cb : Str) : ∀ (k : ℕ) (rows : List (List SatSym)) (R : Str),
    tpv_go Cb k rows R = true → k % 3 = 0 ∧
    ∃ L : List (List SatSym × ℕ), L.map Prod.fst = rows ∧ (∀ p ∈ L, p.2 < k / 3) ∧
      ∀ b < k / 3, bpv_bs L b = sv_bval Cb
  | 0, rows, R, h => by
    have : rows = [] := by simpa [tpv_go] using h
    subst this
    exact ⟨rfl, [], rfl, by simp, fun b hb => by omega⟩
  | 1, rows, R, h => by simp [tpv_go] at h
  | 2, rows, R, h => by simp [tpv_go] at h
  | k + 3, rows, R, h => by
    simp only [tpv_go, Bool.and_eq_true] at h
    obtain ⟨hk, L', h1, h2, h3⟩ := tpv_bwd Cb k _ _ h.2
    have hk3 : (k + 3) / 3 = k / 3 + 1 := by omega
    obtain ⟨g1, g2, g3, g4⟩ := bpv_lab_spec (k / 3) rows R L' h1 h2
    refine ⟨by omega, _, g1, by rw [hk3]; exact g2, fun b hb => ?_⟩
    rw [hk3] at hb
    rcases b with _ | b
    · have := h.1
      rw [← Bool.and_eq_true, tpv_eq_iff, bpv_A_val] at this
      simpa [sv_bval, g3] using this
    · rw [g4]; exact h3 b (by omega)

/-! ## The language -/

theorem tpv_vres_iff (w : List SatSym) (y : Str) :
    tpv_vres w y = true ↔ ∃ items Bv, clauses w = items ++ [Bv] ∧
      tpv_bnd (sv_bits Bv) items = true ∧ tpv_go (sv_bits Bv) items.length items y = true := by
  unfold tpv_vres
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

theorem tpv_lang_iff (w : List SatSym) :
    TPLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ tpv_vres w y = true := by
  constructor
  · rintro ⟨items, Bv, hc, h3, hb, f, hf, hs⟩
    set L := bpv_labF items f
    set m := items.length / 3
    have hL : L.length = items.length := by
      rw [← List.length_map (f := Prod.fst), bpv_labF_fst]
    refine ⟨bpv_cert 0 m L, ?_, (tpv_vres_iff w _).2 ⟨items, Bv, hc, ?_, ?_⟩⟩
    · have h1 := bpv_cert_length m 0 L
      have h2 := length_clauses_le w
      rw [hc] at h2
      simp only [List.length_append, List.length_cons, List.length_nil] at h2
      have : m * L.length ≤ w.length * w.length :=
        Nat.mul_le_mul (by omega) (by omega)
      rw [pow_two]; omega
    · rw [tpv_bnd_iff]
      intro r hr
      rw [sv_bval_bits]; exact hb r hr
    · have hn : items.length = 3 * m := by omega
      have := tpv_fwd (sv_bits Bv) m 0 L
        (fun p hp => ⟨Nat.zero_le _, by simpa using bpv_labF_lt _ items f hf p hp⟩)
        (fun b _ hb' => by
          rw [sv_bval_bits, ← bpv_binSum_labF]; exact hs b (by omega))
      rwa [bpv_labF_fst, ← hn] at this
  · rintro ⟨y, -, hy⟩
    obtain ⟨items, Bv, hc, hb, hg⟩ := (tpv_vres_iff w y).1 hy
    obtain ⟨h3, L, h1, h2, hs⟩ := tpv_bwd (sv_bits Bv) items.length items y hg
    rw [tpv_bnd_iff] at hb
    subst h1
    refine ⟨L.map Prod.fst, Bv, hc, h3, fun r hr => by rw [← sv_bval_bits]; exact hb r hr,
      fun i => (L.getD i ([], 0)).2, ?_, ?_⟩
    · intro i hi
      have hi' : i < L.length := by simpa using hi
      show (L.getD i ([], 0)).2 < _
      rw [List.getD_eq_getElem _ _ hi']
      exact h2 _ (List.getElem_mem hi')
    · intro b hb'
      rw [bpv_binSum_labF, bpv_labF_getD, ← sv_bval_bits]
      exact hs b hb'

/-! ## Transfer to the official class -/

/-- **3-PARTITION ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem tp_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      TPLang := by
  classical
  have hrun := fun z => ((tpv_exec_ver z).mono (tpv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg tpv_ver) (tb 8 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg tpv_ver, 8, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => tpv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => tpv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [tpv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.ThreePart
