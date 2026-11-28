import Pnp.Karp.ThreePartUProgE

/-!
# Unary 3-PARTITION reduction program, part F: the main phase, the program, computability

`tpup_main` reads the header (`QQ = false^q`), counts the rows (`false^K` on stack `6`),
builds the constants (`tpup_kC`), sets the tag suffix, prints the triple rows, the three
gadget blocks and the bound row.  `tpup_redCmd` parses the input word first (as M63's
`tpp_redCmd`); `tpup_F_computable` follows with the time bound `tb 150`.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.ThreePartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.BinPacking Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

/-! ## The main phase -/

def tpup_main : Cmd :=
  .seq tpp_hdC (.seq tpp_cnC (.seq tpup_kC (.seq tpp_setC (.seq tpup_rowL (.seq (tpup_gadC 0)
    (.seq (tpup_gadC 1) (.seq (tpup_gadC 2) (tpup_blkC tpup_bSp))))))))

def tpup_s0 (Mn : Str) : tpup_S :=
  ⟨[], Mn, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], fun _ => []⟩

theorem tpup_kT_le (R V : ℕ) (hR : 1 ≤ R) (hV : 2 * R ^ 8 ≤ V) : tpup_kT R ≤ 400 * (V + 1) ^ 2 := by
  have h1 : R ≤ R ^ 8 := Nat.le_self_pow (by norm_num) R
  have h2 : R ^ 9 = R * R ^ 8 := by ring
  have h3 : R * R ^ 8 ≤ V * V := Nat.mul_le_mul (by omega) (by omega)
  unfold tpup_kT tpup_powT
  rw [show R * (5 * (2 * R ^ 8) + 5) = 10 * (R * R ^ 8) + 5 * R by ring]
  nlinarith

/-- The time bound of the main phase (`V` the stack bound for `M = 4 N`, `Z = 5 N + 5`). -/
def tpup_Tm (N : ℕ) : ℕ := 20000 * (N + 2) * (tpup_V (4 * N) (5 * N + 5) + 1) ^ 2

theorem tpup_V_mono {M M' Z : ℕ} (h : M ≤ M') : tpup_V M Z ≤ tpup_V M' Z := by
  unfold tpup_V
  have : uR M ≤ uR M' := by unfold uR uL; omega
  have := Nat.pow_le_pow_left this 8
  omega

theorem tpup_ex_main (cl : List (List SatSym)) (hsep : ∀ r ∈ cl, sep ∉ r) (N : ℕ)
    (hN : (cl.flatMap (· ++ [sep])).length ≤ N) :
    ∃ s : tpup_S, ExecLe tpup_main (tpup_s0 ((cl.flatMap (· ++ [sep])).flatMap ic)).st
      (.norm s.st) (tpup_Tm N) ∧ s.R = rv (tpup_Fc cl) := by
  set q := (cl.headD []).length with hq
  set rows := cl.tail with hrows
  set K := rows.length with hK
  set M := K + 3 * q with hMd
  set Z := 5 * N + 5 with hZ
  have hrows_sep : ∀ r ∈ rows, sep ∉ r := fun r hr => hsep r (List.mem_of_mem_tail hr)
  have hcl : cl = [] ∨ cl = (cl.headD []) :: rows := by
    rcases cl with _ | ⟨c, L⟩
    · left; rfl
    · right; rfl
  have hqN : q ≤ N := by
    rcases hcl with h | h
    · simp [hq, h]
    · have := tpp_len_le cl (cl.headD []) (by rw [h]; exact List.mem_cons_self); omega
  have hKN : K ≤ N := by
    have := tpp_cnt_le cl
    have : K ≤ cl.length := by simp [hK, hrows]
    omega
  have hrZ : ∀ r ∈ rows, sep ∉ r ∧ r.length ≤ Z := fun r hr =>
    ⟨hrows_sep r hr, by
      have := tpp_len_le rows r hr
      have : (rows.flatMap (· ++ [sep])).length ≤ N := by
        rcases hcl with h | h
        · simp [hrows, h]
        · rw [h] at hN; simp only [List.flatMap_cons, List.length_append] at hN; omega
      omega⟩
  -- header
  set s1 : tpup_S := {tpup_s0 ((rows.flatMap (· ++ [sep])).flatMap ic) with QQ := List.replicate q false}
  have p1 : ExecLe tpp_hdC (tpup_s0 ((cl.flatMap (· ++ [sep])).flatMap ic)).st (.norm s1.st)
      (4 * N + 4) := by
    rcases hcl with h | h
    · have e : ((cl.flatMap (· ++ [sep])).flatMap ic) = [] := by rw [h]; rfl
      rw [e]
      refine (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast ?_ (by omega)
      congr 1; simp [s1, tpup_s0, hrows, hq, h]
    · have e : (cl.flatMap (· ++ [sep])).flatMap ic =
          (cl.headD [] ++ [sep]).flatMap ic ++ (rows.flatMap (· ++ [sep])).flatMap ic := by
        conv_lhs => rw [h]
        simp
      have := tpp_ex_rdL (k := 4) (by norm_num) (fun _ => false) (cl.headD [])
        ((rows.flatMap (· ++ [sep])).flatMap ic) (tpup_s0 ((cl.flatMap (· ++ [sep])).flatMap ic)).st
        (hsep _ (by rw [h]; exact List.mem_cons_self)) e
      refine this.cast ?_ (by omega)
      congr 1; simp [s1, tpup_s0, hq]
  -- counting
  have hLN : (rows.flatMap (· ++ [sep])).length ≤ N := by
    rcases hcl with h | h
    · simp [hrows, h]
    · rw [h] at hN; simp only [List.flatMap_cons, List.length_append] at hN; omega
  set L := rows.flatMap (· ++ [sep])
  have p2a := ExecLe.of (exec_copyVia (a := 1) (b := 2) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) s1.st rfl)
  have p2b := tpp_ex_cnL L (update s1.st 2 (s1.st 1 ++ s1.st 2)) (by simp [s1, tpup_s0, L])
  rw [tpp_count_sep rows hrows_sep] at p2b
  set s2 : tpup_S := {s1 with SUF := List.replicate K false}
  have p2 : ExecLe tpp_cnC s1.st (.norm s2.st) (15 * N + 10) := by
    refine (p2a.seq_norm p2b).cast ?_ ?_
    · congr 1; simp [s2, s1, tpup_s0]; rfl
    · have : (s1.st 1).length = 2 * L.length := length_flatMap_ic L
      rw [this]
      omega
  -- constants
  obtain ⟨σk, p3, hkf, hKH⟩ := tpup_ex_kC q K s2.st rfl rfl rfl rfl
    (fun j hj _ => by rw [tpup_st_big _ _ hj]; rfl)
  set s3 : tpup_S := {s2 with K := σk}
  have e3 : σk = s3.st := by
    funext j; by_cases h : j < 18
    · rw [hkf j h]; interval_cases j <;> rfl
    · rw [tpup_st_big _ _ (by omega)]
  rw [e3] at p3
  have hK3 : tpup_KH s3.K q M := hKH
  -- setup
  have p4a := ExecLe.of (exec_copyVia (a := 4) (b := 6) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) s3.st rfl)
  have p4b := ExecLe.of (exec_copyVia (a := 4) (b := 6) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) (update s3.st 6 (s3.st 4 ++ s3.st 6)) (by simp [s3, s2, s1, tpup_s0]))
  have p4c := ExecLe.of (exec_copyVia (a := 4) (b := 6) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) (update (update s3.st 6 (s3.st 4 ++ s3.st 6)) 6
      ((update s3.st 6 (s3.st 4 ++ s3.st 6)) 4 ++ (update s3.st 6 (s3.st 4 ++ s3.st 6)) 6))
    (by simp [s3, s2, s1, tpup_s0]))
  have p4d := tpp_ex_pop1 6 M (update (update (update s3.st 6 (s3.st 4 ++ s3.st 6)) 6
      ((update s3.st 6 (s3.st 4 ++ s3.st 6)) 4 ++ (update s3.st 6 (s3.st 4 ++ s3.st 6)) 6)) 6
      ((update (update s3.st 6 (s3.st 4 ++ s3.st 6)) 6
      ((update s3.st 6 (s3.st 4 ++ s3.st 6)) 4 ++ (update s3.st 6 (s3.st 4 ++ s3.st 6)) 6)) 4 ++
      (update (update s3.st 6 (s3.st 4 ++ s3.st 6)) 6
      ((update s3.st 6 (s3.st 4 ++ s3.st 6)) 4 ++ (update s3.st 6 (s3.st 4 ++ s3.st 6)) 6)) 6))
    (by simp [s3, s2, s1, tpup_s0, hMd]; try ring_nf)
  set s4 : tpup_S := {s3 with SUF := List.replicate (M - 1 - 0) false}
  have p4 : ExecLe tpp_setC s3.st (.norm s4.st) (15 * N + 20) := by
    refine (p4a.seq_norm (p4b.seq_norm (p4c.seq_norm p4d))).cast ?_ ?_
    · congr 1; simp [s4, s3, s2, s1, tpup_s0]
    · simp [s3, s2, s1]; omega
  -- rows
  have hqZ : q ≤ Z := by omega
  have p5 := tpup_ex_rowL q M Z hqZ rows 0 s4 [] hrZ (by omega) rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hK3
  set E1 := tpup_rowsO q M rows 0
  set s5 : tpup_S := {s4 with Mn := [], PRE := List.replicate (0 + rows.length) false, SUF := List.replicate (M - 1 - (0 + rows.length)) false, R := rv ([] ++ E1)}
  -- gadgets
  have hqM : q ≤ M := by omega
  have p6 := tpup_ex_gadC 0 q M Z (K + 0 * q) 0 hqM s5 ([] ++ E1) rfl (by omega) rfl rfl rfl rfl
    (by simp [s5, hK]) (by simp [s5, hK]) rfl rfl rfl hK3
  set E2 := (List.range q).flatMap fun e => tpup_gEl q M 0 (K + 0 * q + e) e
  set s6 : tpup_S := {s5 with GP := List.replicate q false, PRE := List.replicate (K + 0 * q + q) false, SUF := List.replicate (M - 1 - (K + 0 * q + q)) false, R := rv ([] ++ E1 ++ E2)}
  have p7 := tpup_ex_gadC 1 q M Z (K + 1 * q) q hqM s6 ([] ++ E1 ++ E2) rfl (by omega) rfl rfl rfl
    rfl (by simp [s6]; try ring_nf) (by simp [s6]; try ring_nf) rfl rfl rfl hK3
  set E3 := (List.range q).flatMap fun e => tpup_gEl q M 1 (K + 1 * q + e) e
  set s7 : tpup_S := {s6 with GP := List.replicate q false, PRE := List.replicate (K + 1 * q + q) false, SUF := List.replicate (M - 1 - (K + 1 * q + q)) false, R := rv ([] ++ E1 ++ E2 ++ E3)}
  have p8 := tpup_ex_gadC 2 q M Z (K + 2 * q) q hqM s7 ([] ++ E1 ++ E2 ++ E3) rfl (by omega) rfl
    rfl rfl rfl (by simp [s7]; try ring_nf) (by simp [s7]; try ring_nf) rfl rfl rfl hK3
  set E4 := (List.range q).flatMap fun e => tpup_gEl q M 2 (K + 2 * q + e) e
  set s8 : tpup_S := {s7 with GP := List.replicate q false, PRE := List.replicate (K + 2 * q + q) false, SUF := List.replicate (M - 1 - (K + 2 * q + q)) false, R := rv ([] ++ E1 ++ E2 ++ E3 ++ E4)}
  -- bound row
  set V := tpup_V M Z
  have hRV : uR M ≤ V := by have := tpup_R_le_W M; unfold V tpup_V; omega
  have h21 : (s8.st 21).length = tpup_fc q M 21 := by
    rw [tpup_st_big _ _ (by norm_num), hK3.2.2.2.1]; simp [tpup_fc]
  have h22 : (s8.st 22).length = tpup_fc q M 22 := by
    rw [tpup_st_big _ _ (by norm_num), hK3.2.2.2.2.1]; simp [tpup_fc]
  have hf21 : tpup_fc q M 21 ≤ V := by
    have := tpup_uL_le M; simp [tpup_fc]; omega
  have hf22 : tpup_fc q M 22 ≤ V := by
    have := tpup_R_pos M; simp [tpup_fc]; omega
  have p9 := tpup_ex_blkC (tpup_fc q M) (uR M) V tpup_bSp s8.st ([] ++ E1 ++ E2 ++ E3 ++ E4)
    rfl rfl rfl (tpup_QH_of hK3 (fun j hj => tpup_st_big _ _ hj) (by unfold V tpup_V; omega))
    (fun ds hds => by
      simp only [tpup_bSp, List.mem_singleton] at hds
      subst hds
      refine ⟨by simp, fun d hd => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        refine ⟨by simp, fun c hc => ?_⟩ <;> simp at hc <;> subst hc <;>
        first
          | exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, h21, hf21⟩
          | exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, h22, hf22⟩)
  have eB : tpup_blkO (tpup_fc q M) (uR M) tpup_bSp = tpup_bO q M := rfl
  rw [eB] at p9
  refine ⟨_, (p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm (p5.seq_norm (p6.seq_norm
    (p7.seq_norm (p8.seq_norm p9)))))))).cast (by rw [tpup_u0]) ?_, ?_⟩
  · have h1 : tpup_bSp.length = 1 := rfl
    rw [h1]
    have hK' : rows.length = K := rfl
    rw [hK']
    have hVN : V ≤ tpup_V (4 * N) (5 * N + 5) := tpup_V_mono (by omega)
    have hkT := tpup_kT_le (uR M) V (tpup_R_pos M) (by unfold V tpup_V; omega)
    have hX : (V + 1) ^ 2 ≤ (tpup_V (4 * N) (5 * N + 5) + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hX1 : 1 ≤ (V + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    unfold tpup_Tm tpup_rowT
    generalize (V + 1) ^ 2 = X at hX hX1 hkT ⊢
    generalize (tpup_V (4 * N) (5 * N + 5) + 1) ^ 2 = XN at hX ⊢
    have b1 : K * (3000 * X + 2) ≤ N * (3002 * XN) := Nat.mul_le_mul hKN (by omega)
    have b2 : q * (3000 * X + 1) ≤ N * (3002 * XN) := Nat.mul_le_mul hqN (by omega)
    have b3 : 1 ≤ XN := le_trans hX1 hX
    nlinarith
  · show _ = rv (tpup_rowsO q M rows 0 ++ tpup_gadO q K M 0 ++ tpup_gadO q K M 1 ++
      tpup_gadO q K M 2 ++ tpup_bO q M)
    simp only [s8, E1, E2, E3, E4, tpup_gadO, tpup_gEl, List.nil_append, List.append_assoc]

end Pnp.Karp.ThreePartU
