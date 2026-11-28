import Pnp.Karp.ThreePartUProgC

/-!
# Unary 3-PARTITION reduction program, part D: the row loop and the gadget loops
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.ThreePartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.BinPacking Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

/-! ## The row loop -/

def tpup_rowL : Cmd := .loop (tpp_pk 1 tpup_rowB)

theorem tpup_ex_rowL (q M Z : ℕ) (hqZ : q ≤ Z) :
    ∀ (rows : List (List SatSym)) (t : ℕ) (s : tpup_S) (E : List SatSym),
    (∀ r ∈ rows, sep ∉ r ∧ r.length ≤ Z) → t + rows.length ≤ M →
    s.Mn = (rows.flatMap (· ++ [sep])).flatMap ic → s.T = [] → s.X = [] →
    s.QQ = List.replicate q false → s.PRE = List.replicate t false →
    s.SUF = List.replicate (M - 1 - t) false → s.T1 = [] → s.RW = [] → s.A = [] →
    s.B = [] → s.C = [] → s.AP = [] → s.BP = [] → s.CP = [] → s.CN = [] → s.R = rv E →
    tpup_KH s.K q M →
    ExecLe tpup_rowL s.st (.norm {s with Mn := [], PRE := List.replicate (t + rows.length) false, SUF := List.replicate (M - 1 - (t + rows.length)) false, R := rv (E ++ tpup_rowsO q M rows t)}.st)
      (rows.length * (tpup_rowT (tpup_V M Z) + 2) + 2)
  | [], t, s, E, _, _, hM, _, _, _, hP, hS, _, _, _, _, _, _, _, _, _, hR, _ =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hM]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all [tpup_rowsO]) (by simp)
  | r :: rs, t, s, E, hr, ht, hM, hT, hX, hQ, hP, hS, hT1, hRW, hA, hB, hC, hAP, hBP, hCP, hCN,
      hR, hK => by
    have hM1 : s.Mn = (r ++ [sep]).flatMap ic ++ (rs.flatMap (· ++ [sep])).flatMap ic := by
      rw [hM]; simp
    have hne : s.Mn ≠ [] := by rw [hM1]; simp [ic]
    obtain ⟨b, M', hbm⟩ := List.exists_cons_of_ne_nil hne
    have hl : List.length (r :: rs) = rs.length + 1 := rfl
    have hrow := tpup_ex_rowB q M t Z r _ s E (hr r List.mem_cons_self).1 hM1 hT hX hQ hP
      hS hT1 hRW hA hB hC hAP hBP hCP hCN hR hK (hr r List.mem_cons_self).2 hqZ
      (by simp only [List.length_cons] at ht; omega)
    have hb := tpp_ex_pk (k := 1) s.st (by simpa using hbm) hrow
    have ih := tpup_ex_rowL q M Z hqZ rs (t + 1) {s with Mn := (rs.flatMap (· ++ [sep])).flatMap ic, PRE := List.replicate (t + 1) false, SUF := List.replicate (M - 1 - t - 1) false, R := rv (E ++ tpup_rowO q M r t)}
      (E ++ tpup_rowO q M r t)
      (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr')) (by simp only [List.length_cons] at ht; omega)
      rfl hT hX hQ rfl
      (by show List.replicate (M - 1 - t - 1) false = _; congr 1) hT1 hRW hA hB hC hAP hBP hCP
      hCN rfl hK
    refine (ExecLe.loop_norm hb ih).cast ?_ (by rw [hl]; ring_nf; omega)
    congr 1; cases s
    simp [tpup_rowsO, show t + 1 + rs.length = t + (rs.length + 1) by omega]

/-! ## The gadget loops -/

def tpup_gB (c : ℕ) : Cmd :=
  .seq (tpup_blkC (tpup_gadSp c)) (.seq (.push 12 false) (.seq (tpp_pop1 13)
    (.seq (.push 5 false) (tpp_pop1 6))))

theorem tpup_gadSp_CH {σ K : ℕ → Str} {q M V P e : ℕ} (c : ℕ) (hK : tpup_KH K q M)
    (hσ : ∀ j, 18 ≤ j → σ j = K j) (hV : uR M ≤ V)
    (h5 : σ 5 = List.replicate P false) (h6 : σ 6 = List.replicate (M - 1 - P) false)
    (h12 : σ 12 = List.replicate e false) (h13 : σ 13 = List.replicate (q - 1 - e) false)
    (hPM : P < M) (heq : e < q) (hqM : q ≤ M) :
    ∀ ds ∈ tpup_gadSp c, ds.length ≤ 9 ∧ tpup_CH σ (tpup_gc q M P e) V ds := by
  intro ds hds
  simp only [tpup_gadSp, List.mem_map] at hds
  obtain ⟨x, -, rfl⟩ := hds
  have hM := tpup_M_le M
  refine ⟨by rw [tpup_sp_len], tpup_CH_sp _ x hK hσ ?_ hV ?_ ?_ ?_⟩
  · intro j h1 h2; unfold tpup_gc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  · simp [tpup_gc, h5]; omega
  · simp [tpup_gc, h6]; omega
  · intro c' _
    simp [tpup_gc, tpup_ok, h12, h13]; omega

theorem tpup_ex_gB (c q M Z e P : ℕ) (s : tpup_S) (E : List SatSym) (hT : s.T = [])
    (hX : s.X = []) (hT1 : s.T1 = [])
    (hP : s.PRE = List.replicate P false) (hS : s.SUF = List.replicate (M - 1 - P) false)
    (hGP : s.GP = List.replicate e false) (hGS : s.GS = List.replicate (q - 1 - e) false)
    (hR : s.R = rv E) (hK : tpup_KH s.K q M)
    (heq : e < q) (hPM : P < M) (hqM : q ≤ M) :
    ExecLe (tpup_gB c) s.st (.norm {s with GP := List.replicate (e + 1) false, GS := List.replicate (q - 1 - (e + 1)) false, PRE := List.replicate (P + 1) false, SUF := List.replicate (M - 1 - (P + 1)) false, R := rv (E ++ tpup_blkO (tpup_gc q M P e) (uR M) (tpup_gadSp c))}.st)
      (tpup_rowT (tpup_V M Z)) := by
  set V := tpup_V M Z
  have hRV : uR M ≤ V := by have := tpup_R_le_W M; unfold V tpup_V; omega
  have p1 := tpup_ex_blkC (tpup_gc q M P e) (uR M) V (tpup_gadSp c) s.st E (by simp [hR])
    (by simp [hX]) (by simp [hT1])
    (tpup_QH_of hK (fun j hj => tpup_st_big _ _ hj) (by unfold V tpup_V; omega))
    (tpup_gadSp_CH c hK (fun j hj => tpup_st_big _ _ hj) hRV (by simp [hP]) (by simp [hS])
      (by simp [hGP]) (by simp [hGS]) hPM heq hqM)
  simp only [tpup_u0] at p1
  set s1 : tpup_S := {s with R := rv (E ++ tpup_blkO (tpup_gc q M P e) (uR M) (tpup_gadSp c))}
  have p2 := ExecLe.push 12 false s1.st
  simp only [tpup_u12, tpup_st12] at p2
  have p3 := tpp_ex_pop1 13 (q - 1 - e) {s1 with GP := false :: s1.GP}.st (by simp [s1, hGS])
  simp only [tpup_u13] at p3
  have p4 := ExecLe.push 5 false ({s1 with GP := false :: s1.GP, GS := List.replicate (q - 1 - e - 1) false} : tpup_S).st
  simp only [tpup_u5, tpup_st5] at p4
  have p5 := tpp_ex_pop1 6 (M - 1 - P) ({s1 with GP := false :: s1.GP, GS := List.replicate (q - 1 - e - 1) false, PRE := false :: s1.PRE} : tpup_S).st (by simp [s1, hS])
  simp only [tpup_u6] at p5
  refine (p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm p5)))).cast ?_ ?_
  · congr 1
    obtain ⟨R0, Mn0, T0, X0, QQ0, PRE0, SUF0, T10, RW0, A0, B0, C0, GP0, GS0, AP0, CN0, BP0, CP0,
      K0⟩ := s
    simp only at hGP hP ⊢
    subst hGP hP
    simp [s1, List.replicate_succ, show q - 1 - e - 1 = q - 1 - (e + 1) by omega,
      show M - 1 - P - 1 = M - 1 - (P + 1) by omega]
  · have h3 : (tpup_gadSp c).length = 3 := by simp [tpup_gadSp, gadBlk]
    rw [h3]; unfold tpup_rowT
    have hX2 : 1 ≤ (V + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    generalize (V + 1) ^ 2 = X at hX2 ⊢
    omega

def tpup_gL (c : ℕ) : Cmd := .loop (.pop 15 .brk (tpup_gB c) (tpup_gB c))

/-- The printed items of gadget element `e` (coordinate `c`, tag `P`). -/
def tpup_gEl (q M c P e : ℕ) : List SatSym := tpup_blkO (tpup_gc q M P e) (uR M) (tpup_gadSp c)

theorem tpup_ex_gL (c q M Z P0 : ℕ) (hqM : q ≤ M) : ∀ (n e : ℕ) (s : tpup_S)
    (E : List SatSym), s.CN = List.replicate n false → e + n ≤ q → P0 + e + n ≤ M →
    s.T = [] → s.X = [] → s.T1 = [] → s.PRE = List.replicate (P0 + e) false →
    s.SUF = List.replicate (M - 1 - (P0 + e)) false → s.GP = List.replicate e false →
    s.GS = List.replicate (q - 1 - e) false → s.R = rv E → tpup_KH s.K q M →
    ExecLe (tpup_gL c) s.st (.norm {s with CN := [], GP := List.replicate (e + n) false, GS := List.replicate (q - 1 - (e + n)) false, PRE := List.replicate (P0 + e + n) false, SUF := List.replicate (M - 1 - (P0 + e + n)) false, R := rv (E ++ (List.range n).flatMap fun i => tpup_gEl q M c (P0 + e + i) (e + i))}.st)
      (n * (tpup_rowT (tpup_V M Z) + 1) + 2)
  | 0, e, s, E, hCN, _, _, _, _, _, hP, hS, hGP, hGS, hR, _ =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hCN]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all) (by simp)
  | n + 1, e, s, E, hCN, hen, hPn, hT, hX, hT1, hP, hS, hGP, hGS, hR, hK => by
    have hb := tpup_ex_gB c q M Z e (P0 + e) {s with CN := List.replicate n false} E hT hX hT1
      hP hS hGP hGS hR hK (by omega) (by omega) hqM
    have hb' : ExecLe (.pop 15 .brk (tpup_gB c) (tpup_gB c)) s.st _
        (tpup_rowT (tpup_V M Z) + 1) :=
      ExecLe.pop_same (b := false) (s := List.replicate n false) (by simp [hCN, List.replicate_succ])
        (by rw [tpup_u15]; exact hb)
    have ih := tpup_ex_gL c q M Z P0 hqM n (e + 1) {s with CN := List.replicate n false, GP := List.replicate (e + 1) false, GS := List.replicate (q - 1 - (e + 1)) false, PRE := List.replicate (P0 + e + 1) false, SUF := List.replicate (M - 1 - (P0 + e + 1)) false, R := rv (E ++ tpup_gEl q M c (P0 + e) e)}
      _ rfl (by omega) (by omega) hT hX hT1 (by simp [Nat.add_assoc]) (by simp [Nat.add_assoc])
      rfl rfl rfl hK
    refine (ExecLe.loop_norm hb' ih).cast ?_ (by rw [Nat.succ_mul]; omega)
    congr 1; cases s
    simp only [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_zero,
      List.append_assoc]
    simp [tpup_gEl, show e + 1 + n = e + (n + 1) by omega,
      show P0 + e + 1 + n = P0 + e + (n + 1) by omega, Nat.add_assoc, Nat.add_comm 1]

def tpup_gadC (c : ℕ) : Cmd :=
  .seq (drain 12) (.seq (copyVia 4 13 3) (.seq (tpp_pop1 13) (.seq (copyVia 4 15 3) (tpup_gL c))))

theorem tpup_ex_gadC (c q M Z P0 g : ℕ) (hqM : q ≤ M) (s : tpup_S)
    (E : List SatSym) (hCN : s.CN = []) (hPM : P0 + q ≤ M) (hT : s.T = []) (hX : s.X = [])
    (hT1 : s.T1 = []) (hQ : s.QQ = List.replicate q false)
    (hP : s.PRE = List.replicate P0 false) (hS : s.SUF = List.replicate (M - 1 - P0) false)
    (hGP : s.GP = List.replicate g false) (hGS : s.GS = []) (hR : s.R = rv E)
    (hK : tpup_KH s.K q M) :
    ExecLe (tpup_gadC c) s.st (.norm {s with GP := List.replicate q false, PRE := List.replicate (P0 + q) false, SUF := List.replicate (M - 1 - (P0 + q)) false, R := rv (E ++ (List.range q).flatMap fun e => tpup_gEl q M c (P0 + e) e)}.st)
      (q * (tpup_rowT (tpup_V M Z) + 1) + 2 * g + 12 * q + 20) := by
  obtain ⟨R0, Mn0, T0, X0, QQ0, PRE0, SUF0, T10, RW0, A0, B0, C0, GP0, GS0, AP0, CN0, BP0, CP0,
    K0⟩ := s
  simp only at hCN hT hX hT1 hQ hP hS hGP hGS hR hK
  subst hCN hT hX hT1 hQ hP hS hGP hGS hR
  set s : tpup_S := ⟨rv E, Mn0, [], [], List.replicate q false, List.replicate P0 false,
    List.replicate (M - 1 - P0) false, [], RW0, A0, B0, C0, List.replicate g false, [], AP0, [],
    BP0, CP0, K0⟩ with hs0
  have hX : s.X = [] := rfl
  have hT : s.T = [] := rfl
  have hT1 : s.T1 = [] := rfl
  have hR : s.R = rv E := rfl
  have hP : s.PRE = List.replicate P0 false := rfl
  have hS : s.SUF = List.replicate (M - 1 - P0) false := rfl
  have hGP : s.GP = List.replicate g false := rfl
  have hQ : s.QQ = List.replicate q false := rfl
  have hGS : s.GS = [] := rfl
  have hCN : s.CN = [] := rfl
  have p1 := exec_drain 12 _ s.st rfl
  rw [tpup_u12] at p1
  have p2 := ExecLe.of (exec_copyVia (a := 4) (b := 13) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) {s with GP := []}.st (by simp [hX]))
  simp only [tpup_u13, tpup_st4, tpup_st13, hQ, hGS, List.append_nil] at p2
  have p3 := tpp_ex_pop1 13 q {s with GP := [], GS := List.replicate q false}.st rfl
  rw [tpup_u13] at p3
  have p4 := ExecLe.of (exec_copyVia (a := 4) (b := 15) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) {s with GP := [], GS := List.replicate (q - 1) false}.st (by simp [hX]))
  simp only [tpup_u15, tpup_st4, tpup_st15, hQ, hCN, List.append_nil] at p4
  have p5 := tpup_ex_gL c q M Z P0 hqM q 0 {s with GP := [], GS := List.replicate (q - 1) false, CN := List.replicate q false} E rfl (by omega) (by omega) hT hX hT1 (by simp [hP])
    (by simp [hS]) rfl (by simp) hR hK
  refine ((ExecLe.of p1).seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm p5)))).cast ?_ ?_
  · refine congrArg Res.norm (congrArg tpup_S.st ?_)
    simp [s]
  · rw [tpup_st12, hGP]; simp; omega

end Pnp.Karp.ThreePartU
