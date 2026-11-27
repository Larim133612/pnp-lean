import Pnp.Karp.DHam
import Pnp.Karp.HamVer

/-!
# DIRECTED HAMILTONIAN CYCLE ∈ NP: the verifier program

The verifier `dv_ver` is the undirected verifier `hv_ver` (`Pnp/Karp/HamVer.lean`) with the edge
check replaced: instead of `hv_edgeC` (two row-major scans, one per direction), `dv_edgeC` runs
only the scan `hv_scanP 6 7` with row flags `X` (the current block, `σᵢ`) and column template
`Y` (the next block, `σᵢ₊₁`), i.e. it checks that some `pos` entry `(u, v)` has `X[u]` and `Y[v]`:
an arc `σᵢ → σᵢ₊₁` (`dv_edgeB rows X Y = hv_goS Y rows X`).

All other parts (parsing, `hv_pre`, the block reading, the permutation check `hv_permC`) are
those of `hv_ver`.

`dv_exec_ver`: the program halts with `dv_vres (dec z).1 (dec z).2` within `hv_Tver |z|` steps.
-/

namespace Pnp.Karp.Ham

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## The one-direction edge check -/

/-- Some `pos` entry `(u, v)` has `X[u]` (row) and `Y[v]` (column). -/
def dv_edgeB (rows : List (List SatSym)) (X Y : Str) : Bool := hv_goS Y rows X

def dv_edgeC : Cmd := .seq (hv_scanP 6 7) (.pop 14 (.halt false) (.halt false) .skip)

theorem dv_ex_edgeC (rows : List (List SatSym)) (Nb : ℕ) (s : hv_HS)
    (hsep : ∀ r ∈ rows, sep ∉ r) (hM : s.M = enc rows) (hQ : s.Q = []) (hCC : s.CC = [])
    (hG : s.G = []) (hT : s.T = []) (hH : s.H = []) (hRF : s.RF = [])
    (hCT : s.CT = []) (hX : s.X.length ≤ Nb) (hY : s.Y.length ≤ Nb) :
    ExecLe dv_edgeC s.st (if dv_edgeB rows s.X s.Y then .norm s.st else .halt false)
      (10 * s.M.length + 52 * Nb + 2 * hv_Tsc Nb rows + 50) := by
  have h1 := hv_ex_scan67 rows Nb s false hsep hM hQ hCC hG hT (by simp [hH, CookLevin.fl])
    hRF hCT hX hY
  unfold dv_edgeB
  cases hb : hv_goS s.Y rows s.X
  · refine (h1.seq_norm (ExecLe.pop_nil ?_ (ExecLe.halt false _))).cast
      (by simp) (by omega)
    simp [hb, CookLevin.fl]
  · refine (h1.seq_norm (ExecLe.pop_cons (b := true) (s := []) ?_
      (ExecLe.skip _))).cast ?_ (by omega)
    · simp [hb, CookLevin.fl]
    · simp only [if_true]; congr 1; cases s; simp_all

/-! ## One step of the main loop -/

/-- Read the next block, check the current block and the edge, shift. -/
def dv_body : Cmd :=
  .seq hv_takeN (.seq hv_permC (.seq dv_edgeC (.seq (drain 6) (hv_mvo 7 6))))

theorem dv_ex_body (rows : List (List SatSym)) (n : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r)
    (s : hv_HS) (hi : hv_Inv rows n s) :
    ExecLe dv_body s.st
      (if hv_permOk s.X s.S && dv_edgeB rows s.X (hv_tk n s.R) then
        .norm {s with R := s.R.drop n, X := hv_tk n s.R, S := hv_orV s.X s.S}.st
      else .halt false) (hv_Tb n s.M.length (hv_Tsc n rows)) := by
  have h1 := hv_ex_takeN n s hi.hN hi.hK hi.hT hi.hY
  have h2 := hv_ex_permC {s with R := s.R.drop n, Y := hv_tk n s.R} hi.hXC hi.hF hi.hT
    (by simp [hi.hX, hi.hS])
  simp only at h2
  have h3 := dv_ex_edgeC rows n
    {s with R := s.R.drop n, Y := hv_tk n s.R, S := hv_orV s.X s.S} hsep hi.hM hi.hQ hi.hCC
    hi.hG hi.hT hi.hH hi.hRF hi.hCT (by simp [hi.hX]) (by simp [hv_length_tk])
  simp only at h3
  have h4 := hv_ex_drain 6 {s with R := s.R.drop n, Y := hv_tk n s.R, S := hv_orV s.X s.S}.st
  simp only [hv_u6, hv_st6] at h4
  have h5 := hv_ex_mvo (a := 7) (b := 6) (by decide) (by decide) (by decide)
    {s with R := s.R.drop n, Y := hv_tk n s.R, S := hv_orV s.X s.S, X := []}.st (by simpa using hi.hT)
  simp only [hv_u6, hv_st6, hv_u7, hv_st7, List.append_nil] at h5
  have hTb : 10 * n + 8 + (12 * s.X.length + 10 + (10 * s.M.length + 52 * n + 2 * hv_Tsc n rows +
      50 + (2 * s.X.length + 2 + (4 * (hv_tk n s.R).length + 4)))) ≤
      hv_Tb n s.M.length (hv_Tsc n rows) := by
    simp only [hv_Tb, hv_length_tk, hi.hX]; omega
  by_cases hp : hv_permOk s.X s.S = true
  · rw [if_pos hp] at h2
    by_cases he : dv_edgeB rows s.X (hv_tk n s.R) = true
    · rw [if_pos he] at h3
      rw [if_pos (by simp [hp, he])]
      refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm h5)))).cast ?_ hTb
      have hY := hi.hY
      congr 1; cases s; simp_all
    · rw [if_neg he] at h3
      rw [if_neg (by simp [hp, he])]
      exact (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3))).cast rfl (by omega)
  · rw [if_neg hp] at h2
    rw [if_neg (by simp [hp])]
    exact (h1.seq_norm (ExecLe.seq_halt h2)).cast rfl (by omega)

/-! ## The main loop -/

/-- The last iteration: check the last block against the copy `Z` of `B_0`. -/
def dv_finB : Cmd := .seq (drain 0) (.seq (hv_mvo 8 0) (.seq dv_body (.halt true)))

def dv_mainL : Cmd := .loop (.pop 5 dv_finB dv_body dv_body)

/-- What the main loop computes (`k`: the remaining ordinary iterations). -/
def dv_mainF (rows : List (List SatSym)) (n : ℕ) (Z : Str) : ℕ → Str → Str → Str → Bool
  | 0, _, X, S => hv_permOk X S && dv_edgeB rows X (hv_tk n Z)
  | k + 1, R, X, S => hv_permOk X S && dv_edgeB rows X (hv_tk n R) &&
      dv_mainF rows n Z k (R.drop n) (hv_tk n R) (hv_orV X S)

theorem dv_ex_mainL (rows : List (List SatSym)) (n Lr : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∀ (k : ℕ) (s : hv_HS), hv_Inv rows n s → s.I = List.replicate k true → s.R.length ≤ Lr →
    s.Z.length = n →
    ExecLe dv_mainL s.st (.halt (dv_mainF rows n s.Z k s.R s.X s.S))
      ((k + 1) * (hv_Tb n s.M.length (hv_Tsc n rows) + 1) + 2 * Lr + 4 * n + 10)
  | 0, s, hi, hI, hR, hZ => by
    have h1 := hv_ex_drain 0 s.st
    simp only [hv_u0, hv_st0] at h1
    have h2 := hv_ex_mvo (a := 8) (b := 0) (by decide) (by decide) (by decide)
      {s with R := []}.st (by simpa using hi.hT)
    simp only [hv_u0, hv_st0, hv_u8, hv_st8, List.append_nil] at h2
    have hi' : hv_Inv rows n {s with R := s.Z, Z := []} := by
      obtain ⟨⟩ := hi; constructor <;> assumption
    have h3 := dv_ex_body rows n hsep _ hi'
    simp only at h3
    have hfin : ExecLe dv_finB s.st (.halt (dv_mainF rows n s.Z 0 s.R s.X s.S))
        (2 * s.R.length + 2 + (4 * s.Z.length + 4 + (hv_Tb n s.M.length (hv_Tsc n rows) + 1))) := by
      simp only [dv_mainF, dv_finB]
      by_cases hc : (hv_permOk s.X s.S && dv_edgeB rows s.X (hv_tk n s.Z)) = true
      · rw [if_pos hc] at h3
        exact (h1.seq_norm (h2.seq_norm (h3.seq_norm (ExecLe.halt true _)))).cast (by simp [hc])
          le_rfl
      · rw [if_neg hc] at h3
        exact (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3))).cast
          (by simp only [Bool.not_eq_true] at hc; rw [hc]) (by omega)
    refine (ExecLe.loop_halt (ExecLe.pop_nil (by simpa using hI) hfin)).cast rfl ?_
    simp only [hZ]; omega
  | k + 1, s, hi, hI, hR, hZ => by
    have hb := dv_ex_body rows n hsep {s with I := List.replicate k true}
      (by obtain ⟨⟩ := hi; constructor <;> assumption)
    simp only at hb
    simp only [dv_mainF]
    by_cases hc : (hv_permOk s.X s.S && dv_edgeB rows s.X (hv_tk n s.R)) = true
    · rw [if_pos hc] at hb
      have hi' : hv_Inv rows n
          {s with I := List.replicate k true, R := s.R.drop n, X := hv_tk n s.R, S := hv_orV s.X s.S} := by
        obtain ⟨⟩ := hi; constructor <;> simp_all [hv_length_tk, hv_length_orV]
      have ih := dv_ex_mainL rows n Lr hsep k _ hi' rfl (by simp; omega) hZ
      simp only at ih
      rw [hc, Bool.true_and]
      refine (ExecLe.loop_norm (ExecLe.pop_cons (b := true) (s := List.replicate k true)
        (by simp [hI, List.replicate_succ]) (by simpa using hb)) ih).cast rfl ?_
      simp only [Nat.succ_mul]; omega
    · rw [if_neg hc] at hb
      rw [Bool.eq_false_iff.mpr hc, Bool.false_and]
      refine (ExecLe.loop_halt (ExecLe.pop_cons (b := true) (s := List.replicate k true)
        (by simp [hI, List.replicate_succ]) (by simpa using hb))).cast rfl ?_
      simp only [Nat.succ_mul]; omega
/-! ## The whole verifier -/
def dv_ver : Cmd := .seq phaseA (.seq (trimC 2) (.seq (move 2 1) (.seq hv_pre dv_mainL)))

/-- The answer of the verifier on `(w, y)`. -/
def dv_vres (w : List SatSym) (y : Str) : Bool :=
  decide (3 ≤ (clauses w).length) &&
    dv_mainF (clauses w) (clauses w).length (hv_tk (clauses w).length y)
      ((clauses w).length - 1) (y.drop (clauses w).length) (hv_tk (clauses w).length y)
      (List.replicate (clauses w).length false)

theorem dv_ex_run (rows : List (List SatSym)) (y : Str) (Lr : ℕ) (hy : y.length ≤ Lr)
    (hsep : ∀ r ∈ rows, sep ∉ r) :
    ExecLe (.seq hv_pre dv_mainL) (hv_s0 y (enc rows)).st
      (.halt (decide (3 ≤ rows.length) && dv_mainF rows rows.length (hv_tk rows.length y)
        (rows.length - 1) (y.drop rows.length) (hv_tk rows.length y)
        (List.replicate rows.length false)))
      (10 * (enc rows).length + 60 * rows.length + 3 * Lr + 70 +
        rows.length * (hv_Tb rows.length (enc rows).length (hv_Tsc rows.length rows) + 1)) := by
  set n := rows.length
  have h1 := hv_ex_copy (a := 1) (b := 3) (by decide) (by decide) (by decide)
    (hv_s0 y (enc rows)).st rfl
  simp only [hv_st1, hv_st3, hv_u3, List.append_nil] at h1
  have h2 := hv_ex_cntL (rows.flatMap (· ++ [sep])) {hv_s0 y (enc rows) with Q := enc rows}
    (by simp [enc])
  rw [hv_count_sep rows hsep] at h2
  simp only [List.append_nil] at h2
  set s2 : hv_HS := {hv_s0 y (enc rows) with Q := [], N := List.replicate n true}
  have h3 := hv_ex_chk3 n s2 rfl rfl rfl
  have hlen : (enc rows).length = 2 * ((rows.map List.length).sum + rows.length) := by
    simp only [enc, length_flatMap_ic]; rw [sum_length_le]
  by_cases hn : 3 ≤ n
  · rw [if_pos hn] at h3
    have h4 := hv_ex_initI n s2 rfl rfl rfl
    have h5 := hv_ex_initS n {s2 with I := List.replicate (n - 1) true} rfl rfl rfl
    simp only at h5
    have h6 := hv_ex_takeN n
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ []} rfl rfl rfl rfl
    simp only at h6
    have h7 := hv_ex_copy (a := 7) (b := 8) (by decide) (by decide) (by decide)
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := hv_tk n y}.st rfl
    simp only [hv_st7, hv_st8, hv_u8] at h7
    have h8 := hv_ex_mvo (a := 7) (b := 6) (by decide) (by decide) (by decide)
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := hv_tk n y, Z := hv_tk n y ++ []}.st rfl
    simp only [hv_st7, hv_st6, hv_u7, hv_u6] at h8
    set s9 : hv_HS := {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := [], Z := hv_tk n y ++ [], X := hv_tk n y ++ []}
    have hi : hv_Inv rows n s9 := by
      constructor <;> simp [s9, s2, hv_length_tk]
    have h9 := dv_ex_mainL rows n Lr hsep (n - 1) s9 hi rfl (by simp [s9]; omega)
      (by simp [s9, hv_length_tk])
    simp only [s9, s2, List.append_nil] at h3 h4 h5 h6 h7 h8 h9
    rw [show (n - 1 + 1) = n by omega] at h9
    refine (ExecLe.seq_norm (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm
      (h6.seq_norm (h7.seq_norm h8))))))) h9).cast (by simp [hn]) ?_
    simp [hv_length_tk]
    omega
  · rw [if_neg hn] at h3
    refine (ExecLe.seq_halt (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3)))).cast
      (by simp [hn]) ?_
    simp
    omega

/-- Time bound of the verifier. -/
theorem dv_exec_ver (z : Str) :
    ExecLe dv_ver (init [z]).stk (.halt (dv_vres (dec z).1 (dec z).2)) (hv_Tver z.length) := by
  have hl := dec_length z
  set w := (dec z).1
  set y := (dec z).2
  have h0 : (init [z]).stk 0 = z := rfl
  have he : ∀ j, j ≠ 0 → (init [z]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have hA := exec_phaseA z (init [z]).stk h0
  set σ₁ := update (update (init [z]).stk 0 y) 2 ((w.flatMap ic).reverse ++ (init [z]).stk 2)
  have hT := exec_trimC_word 2 w σ₁ (by simp [σ₁, he 2 (by decide)])
  set σ₂ := update σ₁ 2 (((trunc w).flatMap ic).reverse)
  have hM := exec_move (a := 2) (b := 1) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 2 []) 1 ((σ₂ 2).reverse ++ σ₂ 1) =
      (hv_s0 y (enc (clauses w))).st := by
    funext j
    by_cases hj : j < 19
    · interval_cases j <;> simp [σ₂, σ₁, he, enc, trunc, hv_HS.st]
    · rw [hv_st_big _ _ (by omega)]
      simp [σ₂, σ₁, he j (by omega), show j ≠ 0 by omega, show j ≠ 1 by omega,
        show j ≠ 2 by omega]
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hR := dv_ex_run (clauses w) y z.length (by omega) (sep_not_mem_clauses w)
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  have hen : (enc (clauses w)).length = 2 * (trunc w).length := by
    simp only [enc, trunc, length_flatMap_ic]
  refine (hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm hR))).cast rfl ?_
  rw [hv_Tsc_eq]
  simp only [hv_Tb, htl, hen]
  have hb := hv_bound z.length (clauses w).length (trunc w).length
    ((clauses w).map List.length).sum (by omega) (by omega) (by omega)
  omega

end Pnp.Karp.Ham
