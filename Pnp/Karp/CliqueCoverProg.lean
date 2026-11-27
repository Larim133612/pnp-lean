import Pnp.Karp.CliqueCover
import Pnp.Karp.ColorProg
import Pnp.Karp.DHamProg

/-!
# CLIQUE COVER: the reduction program and SAT ≤ₚ CLIQUE COVER

`CCI w = cmap (ccHdr ++ symG (G w))` is computed as a composition of three polynomial-time
computable functions:

1. the 3-COLORING graph `Color.G` (`Pnp/Karp/ColorProg.lean`, program `Color.redCmd`);
2. `fun x => ccHdr ++ symG x`, computed by `ccp_redCmd`: the symmetrization program
   `dp_redCmd` (`Pnp/Karp/DHamProg.lean`) with one extra straight-line command that prints the
   header row `ccHdr` onto the (still empty) output stack `0` right after parsing;
3. the symbol complement `IndSet.cmap` (`Pnp/Karp/IndSet.lean`).

`sat_le_cc_of` (given the correctness `SATLang w ↔ CCLang (CCI w)`) follows with
`Pnp.TM2Comp.comp`.
-/

namespace Pnp.Karp.CliqueCover

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.Ham

/-- `dp_main`, run on a state whose output stack already holds `rv E`. -/
theorem ccp_ex_main (rows : List (List SatSym)) (hsep : ∀ r ∈ rows, sep ∉ r)
    (E : List SatSym) :
    ∃ s : hv_HS, ExecLe dp_main (hv_s0 (rv E) (enc rows)).st (.norm s.st)
      (18 * (enc rows).length + 10 * rows.length + 20 +
        rows.length * (dp_Pr rows rows.length + 1)) ∧
      s.R = rv (E ++ dp_rows rows 0 rows.length) := by
  have h1 := hv_ex_copy (a := 1) (b := 3) (by decide) (by decide) (by decide)
    (hv_s0 (rv E) (enc rows)).st rfl
  simp only [hv_st1, hv_st3, hv_u3, List.append_nil] at h1
  have h2 := hv_ex_cntL (rows.flatMap (· ++ [sep])) {hv_s0 (rv E) (enc rows) with Q := enc rows}
    (by simp [enc])
  rw [hv_count_sep rows hsep] at h2
  simp only [List.append_nil] at h2
  set s2 : hv_HS := {hv_s0 (rv E) (enc rows) with Q := [], N := List.replicate rows.length true}
  have h3 := hv_ex_copy (a := 4) (b := 5) (by decide) (by decide) (by decide) s2.st rfl
  simp only [hv_st4, hv_st5, hv_u5] at h3
  have h4 := ExecLe.push 6 true {s2 with I := s2.N ++ s2.I}.st
  rw [hv_u6] at h4
  have h5 := dp_ex_outL rows hsep rows.length 0 {s2 with I := s2.N ++ s2.I, X := true :: s2.X} E
    (by omega) (by simp [s2]) rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
  have hall := h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm h5)))
  refine ⟨_, hall.cast rfl ?_, rfl⟩
  have hl : (rows.flatMap (· ++ [sep])).length ≤ (enc rows).length := by
    simp only [enc, length_flatMap_ic]; omega
  have hsl := sum_length_le rows
  simp [s2]
  omega

/-- The program: `dp_redCmd` with the header row `ccHdr` printed right after parsing. -/
def ccp_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 1) (.seq (pushList 0 (rv ccHdr)) dp_main)))

/-- The time bound. -/
def ccp_Tred (L : ℕ) : ℕ := dp_Tred L + 9

theorem ccp_exec_redCmd (x : Str) : ∃ σ', ExecLe ccp_redCmd (init [x]).stk (.norm σ')
    (ccp_Tred x.length) ∧
    σ' 0 = ((ccHdr ++ symG (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ₁ := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := exec_trimC_word 4 w σ₁ (by simp [σ₁, he 4 (by decide)])
  set σ₂ := update σ₁ 4 (((trunc w).flatMap ic).reverse)
  have p3 := exec_move (a := 4) (b := 1) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 4 []) 1 ((σ₂ 4).reverse ++ σ₂ 1) =
      (hv_s0 [] (enc (clauses w))).st := by
    funext j
    by_cases hj : j < 19
    · interval_cases j <;> simp [σ₂, σ₁, he, enc, trunc, hv_HS.st]
    · rw [hv_st_big _ _ (by omega)]
      simp [σ₂, σ₁, he j (by omega), show j ≠ 0 by omega, show j ≠ 1 by omega,
        show j ≠ 4 by omega]
  rw [hσ] at p3
  have ph := exec_pushList 0 (rv ccHdr) (hv_s0 [] (enc (clauses w))).st
  rw [hv_u0, hv_st0, List.append_nil] at ph
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  obtain ⟨s, p4, hs⟩ := ccp_ex_main (clauses w) (sep_not_mem_clauses w) ccHdr
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm
    ((ExecLe.of ph).seq_norm p4)))).cast rfl ?_, ?_⟩
  · have htl : (σ₂ 4).length = 2 * (trunc w).length := by
      simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
    have hen : (enc (clauses w)).length = 2 * (trunc w).length := by
      simp only [enc, trunc, length_flatMap_ic]
    have hh : (rv ccHdr).length = 8 := rfl
    simp only [dp_Pr, dp_P, hv_Tsc_eq, htl, hen, hh, ccp_Tred]
    have hb := dp_bound x.length (clauses w).length (trunc w).length
      ((clauses w).map List.length).sum (by omega) (by omega) (by omega)
    omega
  · rw [hv_st0, hs, dp_rows, dp_out_eq]; rfl

theorem ccp_Tred_le (n : ℕ) : ccp_Tred n ≤ tb 15 n := by
  unfold ccp_Tred dp_Tred tb
  have h11 : 2 ^ 11 ≤ (n + 2) ^ 11 := Nat.pow_le_pow_left (by omega) 11
  have e : (n + 2) ^ 15 = (n + 2) ^ 11 * (n + 2) ^ 4 := by ring
  rw [e]
  have h4 : 1 ≤ (n + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have : 2009 ≤ (n + 2) ^ 11 := le_trans (by norm_num) h11
  nlinarith

/-- `fun x => ccHdr ++ symG x` is polynomial-time computable. -/
theorem ccp_hdrSym_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    (fun x => ccHdr ++ symG x)) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    ccp_redCmd 0 15 (fun x => ccHdr ++ symG (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := ccp_exec_redCmd x
      exact ⟨σ', h1.mono (ccp_Tred_le _), h2⟩)
    (fun x => ccHdr ++ symG x)
    (fun t => (congrArg (fun x => ccHdr ++ symG x) (FunBridge.dec2_flatMap_ic t)).symm)

/-- The 3-COLORING graph `Color.G` is polynomial-time computable. -/
theorem ccp_G_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    Color.G) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    Color.redCmd 1 11 (fun x => Color.G (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := Color.exec_redCmd x
      exact ⟨σ', h1.mono (Color.Tred_le _), h2⟩)
    Color.G (fun t => (congrArg Color.G (FunBridge.dec2_flatMap_ic t)).symm)

/-! ## The reduction -/

/-- **SAT ≤ₚ CLIQUE COVER** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `CCI`. -/
theorem sat_le_cc_of (h : ∀ w, SATLang w ↔ CCLang (CCI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang CCLang := by
  obtain ⟨hG⟩ := ccp_G_computable
  obtain ⟨hS⟩ := ccp_hdrSym_computable
  obtain ⟨hc⟩ := IndSet.cmap_computable
  exact ⟨IndSet.cmap ∘ (fun x => ccHdr ++ symG x) ∘ Color.G,
    Pnp.TM2Comp.comp (Pnp.TM2Comp.comp hG hS) hc, h⟩

end Pnp.Karp.CliqueCover
