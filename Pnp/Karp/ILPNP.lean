import Pnp.Karp.ILPVer
import Pnp.Karp.KnapNP

/-!
# 0-1 INTEGER PROGRAMMING ∈ NP (official definition)

The checking relation is `ilv_vres w y = true` (`Pnp/Karp/ILPVer.lean`).

* `ilv_pg_iff`: the pair loop accepts iff `A + Σ selected N-chunks ≤ L + Σ selected P-chunks`
  (pairs as in `Knapsack.pairs`; `kv_le_iff`, `sv_bval_addL`);
* `ilv_row_iff`: the verdict on a row is `rowOK r (true :: y)`;
* `ilv_ilpLang_iff`: `ILPLang w ↔ ∃ y, |y| ≤ |w| ∧ ilv_vres w y` (bits of `x` beyond the number
  of pairs of a row are never read, so `x` can be cut to `|w|` bits);
* `ilp_in_np`: `ILPLang ∈ NP`, via `ilv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.ILP

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack

theorem ilv_bval_acc (A : Str) (e : List SatSym) : sv_bval (ilv_acc A e) = sv_bval A + bv e := by
  simp [ilv_acc, sv_bval_addL, sv_bval_bits]

theorem ilv_pg_iff : ∀ (cs : List (List SatSym)) (Z L A : Str),
    ilv_pg cs Z L A = true ↔
      sv_bval A + selSum ((pairs cs).map Prod.snd) Z ≤
        sv_bval L + selSum ((pairs cs).map Prod.fst) Z
  | [], Z, L, A => by simp [ilv_pg, pairs, selSum, kv_le_iff]
  | [a], Z, L, A => by
    simp only [ilv_pg, pairs, List.map_cons, List.map_nil, selSum, kv_le_iff]
    cases Z.headD false <;> simp [ilv_bval_acc, bv]
  | [a, b], Z, L, A => by
    simp only [ilv_pg, pairs, List.map_cons, List.map_nil, selSum, kv_le_iff]
    cases Z.headD false <;> simp [ilv_bval_acc]
  | a :: b :: c :: cs, Z, L, A => by
    rw [ilv_pg, ilv_pg_iff (c :: cs)]
    simp only [pairs, List.map_cons, selSum]
    cases Z.headD false <;> simp [ilv_bval_acc]
    omega

theorem ilv_row_iff (y : Str) (r : List SatSym) : ilv_row y r = true ↔ rowOK r (true :: y) := by
  unfold ilv_row rowOK
  rw [ilv_pg_iff]
  simp [sv_bval]

theorem ilv_ichunks_length : ∀ r : List SatSym, (ichunks r).length ≤ r.length + 1 := by
  intro r
  have := ilv_ichunks_len r
  omega

theorem ilv_rowOK_take (r : List SatSym) (x : List Bool) (n : ℕ)
    (hn : (pairs (ichunks r)).length ≤ n + 1) :
    rowOK r (true :: x.take n) ↔ rowOK r (true :: x) := by
  unfold rowOK
  have key : ∀ l : List (List SatSym), l.length ≤ n + 1 →
      selSum l (true :: x.take n) = selSum l (true :: x) := by
    intro l hl
    rw [← sv_selSum_take l (true :: x.take n), ← sv_selSum_take l (true :: x)]
    congr 1
    rcases l with _ | ⟨c, l⟩
    · simp
    · simp only [List.length_cons, List.take_succ_cons, List.take_take] at hl ⊢
      rw [min_eq_left (by omega)]
  rw [key _ (by simpa using hn), key _ (by simpa using hn)]

theorem ilv_ilpLang_iff (w : List SatSym) :
    ILPLang w ↔ ∃ y : Str, y.length ≤ w.length ∧ ilv_vres w y = true := by
  unfold ILPLang ilv_vres
  simp only [List.all_eq_true, ilv_row_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x.take w.length, by simp, fun r hr => (ilv_rowOK_take r x w.length ?_).mpr (hx r hr)⟩
    have h1 := kv_pairs_length (ichunks r)
    have h2 := ilv_ichunks_length r
    have h3 : r.length ≤ ((clauses w).map List.length).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hr)
    have h4 := sum_length_le (clauses w)
    have h5 := length_trunc_le w
    have h6 : (trunc w).length = ((clauses w).flatMap (· ++ [sep])).length := rfl
    omega
  · rintro ⟨y, -, hy⟩
    exact ⟨y, hy⟩

/-! ## Transfer to the official class -/

/-- **0-1 INTEGER PROGRAMMING ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem ilp_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      ILPLang := by
  classical
  have hrun := fun z => ((ilv_exec_ver z).mono (ilv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg ilv_ver) (tb 9 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg ilv_ver, 9, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => ilv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => ilv_vres w y = true, 1, hR, fun w => ?_⟩
  rw [ilv_ilpLang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.ILP
