import Pnp.Karp.ThreePartUProgB

/-!
# Unary 3-PARTITION reduction program, part C: the triple rows
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.ThreePartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.BinPacking Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

/-- The length bound of the stacks. -/
def tpup_V (M Z : ℕ) : ℕ := 2 * uR M ^ 8 + Z

def tpup_rowT (V : ℕ) : ℕ := 3000 * (V + 1) ^ 2

/-! ## One triple row -/

def tpup_rowB : Cmd :=
  .seq (tpp_rdL 8 tpp_bb) (.seq (tpp_spC 11) (.seq (tpp_spC 10) (.seq (move 8 9)
    (.seq (tpup_psL 9 14) (.seq (tpup_psL 10 16) (.seq (tpup_psL 11 17)
    (.seq (tpup_blkC tpup_rowSp) (.seq (drain 9) (.seq (drain 10) (.seq (drain 11)
    (.seq (drain 14) (.seq (drain 16) (.seq (drain 17)
    (.seq (.push 5 false) (tpp_pop1 6)))))))))))))))

theorem tpup_rowSp_CH {σ K : ℕ → Str} {q M V t : ℕ} {A B C : List Bool} (hK : tpup_KH K q M)
    (hσ : ∀ j, 18 ≤ j → σ j = K j) (hV : uR M ≤ V)
    (h5 : (σ 5).length = t) (h6 : (σ 6).length = M - 1 - t) (htM : t < M)
    (h14 : σ 14 = List.replicate (tpup_pf A) false) (h9 : σ 9 = tpup_sf A)
    (h16 : σ 16 = List.replicate (tpup_pf B) false) (h10 : σ 10 = tpup_sf B)
    (h17 : σ 17 = List.replicate (tpup_pf C) false) (h11 : σ 11 = tpup_sf C)
    (hA : A.length ≤ V) (hB : B.length ≤ V) (hC : C.length ≤ V) :
    ∀ ds ∈ tpup_rowSp, ds.length ≤ 9 ∧ tpup_CH σ (tpup_rc q M t A B C) V ds := by
  intro ds hds
  simp only [tpup_rowSp, List.mem_map] at hds
  obtain ⟨x, -, rfl⟩ := hds
  have hM := tpup_M_le M
  have pA := tpup_pf_le A; have sA := tpup_sf_le A
  have pB := tpup_pf_le B; have sB := tpup_sf_le B
  have pC := tpup_pf_le C; have sC := tpup_sf_le C
  refine ⟨by rw [tpup_sp_len], tpup_CH_sp tpup_ipR x hK hσ ?_ hV ?_ ?_ ?_⟩
  · intro j h1 h2; unfold tpup_rc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · simp [tpup_rc, h5]; omega
  · simp [tpup_rc, h6]; omega
  · intro c' hc'
    interval_cases c' <;> simp [tpup_ipR, tpup_rc, tpup_ok, h14, h9, h16, h10, h17, h11] <;> omega

theorem tpup_rowB_T {r q Z V a b c a' b' c' pa pb pc l : ℕ} (h1 : a' ≤ a) (h2 : b' ≤ b)
    (h3 : c' ≤ c) (h4 : pa ≤ a) (h5 : pb ≤ b) (h6 : pc ≤ c) (ha : a ≤ Z) (hb : b ≤ Z)
    (hc : c ≤ Z) (hr : r ≤ Z) (hq : q ≤ Z) (hl : l ≤ Z) (hZ : Z ≤ V) :
    4 * r + 4 + (8 * q + 6 + (8 * q + 6 + (2 * (l - q - q) + 2 + (2 * a + 2 + (2 * b + 2 +
      (2 * c + 2 + (12 * (200 * (V + 1) ^ 2) + 1 + (2 * a' + 2 + (2 * b' + 2 + (2 * c' + 2 +
      (2 * pa + 2 + (2 * pb + 2 + (2 * pc + 2 + (1 + 2)))))))))))))) ≤ 3000 * (V + 1) ^ 2 := by
  have hX : V + 1 ≤ (V + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  generalize (V + 1) ^ 2 = X at hX ⊢
  omega

theorem tpup_ex_rowB (q M t Z : ℕ) (r : List SatSym) (rest : Str) (s : tpup_S) (E : List SatSym)
    (hs : sep ∉ r) (hM : s.Mn = (r ++ [sep]).flatMap ic ++ rest) (hT : s.T = []) (hX : s.X = [])
    (hQ : s.QQ = List.replicate q false) (hP : s.PRE = List.replicate t false)
    (hS : s.SUF = List.replicate (M - 1 - t) false) (hT1 : s.T1 = []) (hRW : s.RW = [])
    (hA : s.A = []) (hB : s.B = []) (hC : s.C = []) (hAP : s.AP = []) (hBP : s.BP = [])
    (hCP : s.CP = []) (hCN : s.CN = []) (hR : s.R = rv E) (hK : tpup_KH s.K q M)
    (hZ1 : r.length ≤ Z) (hqZ : q ≤ Z) (htM : t < M) :
    ExecLe tpup_rowB s.st (.norm {s with Mn := rest, PRE := List.replicate (t + 1) false, SUF := List.replicate (M - 1 - t - 1) false, R := rv (E ++ tpup_rowO q M r t)}.st)
      (tpup_rowT (tpup_V M Z)) := by
  obtain ⟨R0, Mn0, T0, X0, QQ0, PRE0, SUF0, T10, RW0', A0, B0, C0, GP0, GS0, AP0, CN0, BP0, CP0,
    K0⟩ := s
  simp only at hM hT hX hQ hP hS hT1 hRW hA hB hC hAP hBP hCP hCN hR hK
  subst hM hT hX hQ hP hS hT1 hRW hA hB hC hAP hBP hCP hCN hR
  set s : tpup_S := ⟨rv E, (r ++ [sep]).flatMap ic ++ rest, [], [], List.replicate q false,
    List.replicate t false, List.replicate (M - 1 - t) false, [], [], [], [], [], GP0, GS0, [], [],
    [], [], K0⟩ with hs0
  have hM : s.Mn = (r ++ [sep]).flatMap ic ++ rest := rfl
  have hRW : s.RW = [] := rfl
  have hT : s.T = [] := rfl
  have hX : s.X = [] := rfl
  have hT1 : s.T1 = [] := rfl
  have hCN : s.CN = [] := rfl
  have hQ : s.QQ = List.replicate q false := rfl
  have hC : s.C = [] := rfl
  have hB : s.B = [] := rfl
  have hA : s.A = [] := rfl
  have hAP : s.AP = [] := rfl
  have hBP : s.BP = [] := rfl
  have hCP : s.CP = [] := rfl
  have hP : s.PRE = List.replicate t false := rfl
  have hS : s.SUF = List.replicate (M - 1 - t) false := rfl
  have hR : s.R = rv E := rfl
  set RW0 := (r.map tpp_bb).reverse with hRW0
  have p1 := tpp_ex_rdL (k := 8) (by norm_num) tpp_bb r rest s.st hs hM
  simp only [tpup_u1, tpup_st8, hRW, List.append_nil, tpup_u8] at p1
  set s1 : tpup_S := {s with Mn := rest, RW := RW0}
  have p2 := tpp_ex_spC (k := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num) q RW0
    s1.st (by simp [s1, hX]) (by simp [s1, hCN]) (by simp [s1, hQ]) (by simp [s1])
  simp only [tpup_u8, tpup_u11, tpup_st11, s1, hC, List.append_nil] at p2
  set s2 : tpup_S := {s with Mn := rest, RW := RW0.drop q, C := (RW0.take q).reverse}
  have p3 := tpp_ex_spC (k := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) q
    (RW0.drop q) s2.st (by simp [s2, hX]) (by simp [s2, hCN]) (by simp [s2, hQ]) (by simp [s2])
  simp only [tpup_u8, tpup_u10, tpup_st10, s2, hB, List.append_nil] at p3
  set s3 : tpup_S := {s with Mn := rest, RW := (RW0.drop q).drop q, C := (RW0.take q).reverse, B := ((RW0.drop q).take q).reverse}
  have p4 := exec_move (a := 8) (b := 9) (by norm_num) _ s3.st rfl
  simp only [tpup_u8, tpup_u9, tpup_st9, tpup_st8, s3, hA, List.append_nil] at p4
  set Aa := ((RW0.drop q).drop q).reverse
  set Bb := ((RW0.drop q).take q).reverse
  set Cc := (RW0.take q).reverse
  set s4 : tpup_S := {s with Mn := rest, RW := [], C := Cc, B := Bb, A := Aa}
  have p5 := tpup_ex_psL (k := 9) (p := 14) (by norm_num) Aa s4.st (by simp [s4])
  simp only [tpup_u9, tpup_u14, tpup_st14, s4, hAP, List.append_nil] at p5
  set s5 : tpup_S := {s with Mn := rest, RW := [], C := Cc, B := Bb, A := tpup_sf Aa, AP := List.replicate (tpup_pf Aa) false}
  have p6 := tpup_ex_psL (k := 10) (p := 16) (by norm_num) Bb s5.st (by simp [s5])
  simp only [tpup_u10, tpup_u16, tpup_st16, s5, hBP, List.append_nil] at p6
  set s6 : tpup_S := {s with Mn := rest, RW := [], C := Cc, B := tpup_sf Bb, A := tpup_sf Aa, AP := List.replicate (tpup_pf Aa) false, BP := List.replicate (tpup_pf Bb) false}
  have p7 := tpup_ex_psL (k := 11) (p := 17) (by norm_num) Cc s6.st (by simp [s6])
  simp only [tpup_u11, tpup_u17, tpup_st17, s6, hCP, List.append_nil] at p7
  set s7 : tpup_S := {s with Mn := rest, RW := [], C := tpup_sf Cc, B := tpup_sf Bb, A := tpup_sf Aa, AP := List.replicate (tpup_pf Aa) false, BP := List.replicate (tpup_pf Bb) false, CP := List.replicate (tpup_pf Cc) false}
  set V := tpup_V M Z
  have hRl : RW0.length = r.length := by simp [RW0]
  have hAl : Aa.length ≤ Z := by simp [Aa]; omega
  have hBl : Bb.length ≤ Z := by simp [Bb]; omega
  have hCl : Cc.length ≤ Z := by simp [Cc]; omega
  have hZV : Z ≤ V := by unfold V tpup_V; omega
  have hRV : uR M ≤ V := by have := tpup_R_le_W M; unfold V tpup_V; omega
  have p8 := tpup_ex_blkC (tpup_rc q M t Aa Bb Cc) (uR M) V tpup_rowSp s7.st E rfl rfl rfl
    (tpup_QH_of hK (fun j hj => tpup_st_big _ _ hj) (by unfold V tpup_V; omega))
    (tpup_rowSp_CH hK (fun j hj => tpup_st_big _ _ hj) hRV (by simp [s7, hP]) (by simp [s7, hS]) htM
      rfl rfl rfl rfl rfl rfl (by omega) (by omega) (by omega))
  simp only [tpup_u0] at p8
  have eO : tpup_blkO (tpup_rc q M t Aa Bb Cc) (uR M) tpup_rowSp = tpup_rowO q M r t := rfl
  rw [eO] at p8
  set s8 : tpup_S := {s7 with R := rv (E ++ tpup_rowO q M r t)}
  have p9 := exec_drain 9 _ s8.st rfl
  have p10 := exec_drain 10 _ (update s8.st 9 []) rfl
  have p11 := exec_drain 11 _ (update (update s8.st 9 []) 10 []) rfl
  have p12 := exec_drain 14 _ (update (update (update s8.st 9 []) 10 []) 11 []) rfl
  have p13 := exec_drain 16 _ (update (update (update (update s8.st 9 []) 10 []) 11 []) 14 []) rfl
  have p14 := exec_drain 17 _ (update (update (update (update (update s8.st 9 []) 10 []) 11 [])
    14 []) 16 []) rfl
  simp only [tpup_u9, tpup_u10, tpup_u11, tpup_u14, tpup_u16, tpup_u17] at p9 p10 p11 p12 p13 p14
  set s9 : tpup_S := {s8 with A := [], B := [], C := [], AP := [], BP := [], CP := []}
  have p15 := ExecLe.push 5 false s9.st
  simp only [tpup_u5, tpup_st5] at p15
  have p16 := tpp_ex_pop1 6 (M - 1 - t) {s9 with PRE := false :: s9.PRE}.st (by simp [s9, s8, s7, hS])
  simp only [tpup_u6] at p16
  refine (p1.seq_norm (p2.seq_norm (p3.seq_norm ((ExecLe.of p4).seq_norm (p5.seq_norm
    (p6.seq_norm (p7.seq_norm (p8.seq_norm ((ExecLe.of p9).seq_norm ((ExecLe.of p10).seq_norm
    ((ExecLe.of p11).seq_norm ((ExecLe.of p12).seq_norm ((ExecLe.of p13).seq_norm
    ((ExecLe.of p14).seq_norm (p15.seq_norm p16))))))))))))))).cast ?_ ?_
  · congr 1
  · have h12 : tpup_rowSp.length = 12 := rfl
    simp only [h12, s9, s8, s7, s6, s5, s4, s3, s2, s1, tpup_st9, tpup_st10, tpup_st11,
      tpup_st14, tpup_st16, tpup_st17, List.length_replicate, List.length_drop, List.length_reverse]
    unfold tpup_rowT
    exact tpup_rowB_T (tpup_sf_le Aa) (tpup_sf_le Bb) (tpup_sf_le Cc) (tpup_pf_le Aa)
      (tpup_pf_le Bb) (tpup_pf_le Cc) hAl hBl hCl hZ1 hqZ (hRl ▸ hZ1) hZV
