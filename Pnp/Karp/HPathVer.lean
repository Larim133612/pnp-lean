import Pnp.Karp.HPath
import Pnp.Karp.HamVer

/-!
# HAMILTONIAN PATH ∈ NP: the verifier program

The verifier `pv2_ver` is the HAMILTONIAN CYCLE verifier `hv_ver` (`Pnp/Karp/HamVer.lean`) with
two changes:

* instead of the check `n ≥ 3` (`hv_chk3`), `pv2_chk0` accepts at once if `n = 0` (the empty
  ordering is a Hamiltonian path of the empty graph); no copy `Z` of `B_0` is kept;
* the last iteration `pv2_finB` only runs the permutation check `hv_permC` on the last block
  (no wrap-around edge back to `B_0`).

All other parts (parsing, counting the rows, the block reading, the loop body `hv_body` with its
permutation and (undirected) edge checks) are those of `hv_ver`.

`pv2_exec_ver`: the program halts with `pv2_vres (dec z).1 (dec z).2` within `hv_Tver |z|` steps.
-/

namespace Pnp.Karp.Ham

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## The check `n = 0` -/

/-- Accept at once if `n = 0` (stack `4` empty); otherwise leave the state unchanged. -/
def pv2_chk0 : Cmd := .pop 4 (.halt true) (.push 4 false) (.push 4 true)

theorem pv2_ex_chk0 (n : ℕ) (s : hv_HS) (hN : s.N = List.replicate n true) :
    ExecLe pv2_chk0 s.st (if n = 0 then .halt true else .norm s.st) 3 := by
  rcases n with _ | n
  · exact (ExecLe.pop_nil (by simpa using hN) (ExecLe.halt true _)).cast (by simp) (by omega)
  · refine (ExecLe.pop_cons (b := true) (s := List.replicate n true)
      (by simp [hN, List.replicate_succ]) (ExecLe.push 4 true _)).cast ?_ (by omega)
    simp only [hv_u4, hv_st4, Nat.add_one_ne_zero, if_false]
    congr 1; cases s; simp_all [List.replicate_succ]

/-! ## The main loop -/

/-- The last iteration: only the permutation check of the last block; accept. -/
def pv2_finB : Cmd := .seq hv_permC (.halt true)

def pv2_mainL : Cmd := .loop (.pop 5 pv2_finB hv_body hv_body)

/-- What the main loop computes (`k`: the remaining ordinary iterations). -/
def pv2_mainF (rows : List (List SatSym)) (n : ℕ) : ℕ → Str → Str → Str → Bool
  | 0, _, X, S => hv_permOk X S
  | k + 1, R, X, S => hv_permOk X S && hv_edgeB rows X (hv_tk n R) &&
      pv2_mainF rows n k (R.drop n) (hv_tk n R) (hv_orV X S)

theorem pv2_ex_mainL (rows : List (List SatSym)) (n Lr : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∀ (k : ℕ) (s : hv_HS), hv_Inv rows n s → s.I = List.replicate k true → s.R.length ≤ Lr →
    ExecLe pv2_mainL s.st (.halt (pv2_mainF rows n k s.R s.X s.S))
      ((k + 1) * (hv_Tb n s.M.length (hv_Tsc n rows) + 1) + 2 * Lr + 4 * n + 10)
  | 0, s, hi, hI, hR => by
    have h1 := hv_ex_permC s hi.hXC hi.hF hi.hT (by rw [hi.hS, hi.hX])
    have hfin : ExecLe pv2_finB s.st (.halt (pv2_mainF rows n 0 s.R s.X s.S))
        (12 * s.X.length + 10 + 1) := by
      simp only [pv2_mainF, pv2_finB]
      cases hc : hv_permOk s.X s.S
      · rw [hc] at h1
        exact (ExecLe.seq_halt h1).cast rfl (by omega)
      · rw [hc, if_pos rfl] at h1
        exact h1.seq_norm (ExecLe.halt true _)
    refine (ExecLe.loop_halt (ExecLe.pop_nil (by simpa using hI) hfin)).cast rfl ?_
    simp only [hi.hX, hv_Tb]; omega
  | k + 1, s, hi, hI, hR => by
    have hb := hv_ex_body rows n hsep {s with I := List.replicate k true}
      (by obtain ⟨⟩ := hi; constructor <;> assumption)
    simp only at hb
    simp only [pv2_mainF]
    by_cases hc : (hv_permOk s.X s.S && hv_edgeB rows s.X (hv_tk n s.R)) = true
    · rw [if_pos hc] at hb
      have hi' : hv_Inv rows n
          {s with I := List.replicate k true, R := s.R.drop n, X := hv_tk n s.R, S := hv_orV s.X s.S} := by
        obtain ⟨⟩ := hi; constructor <;> simp_all [hv_length_tk, hv_length_orV]
      have ih := pv2_ex_mainL rows n Lr hsep k _ hi' rfl (by simp; omega)
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

def pv2_pre : Cmd :=
  .seq (copyVia 1 3 10) (.seq hv_cntL (.seq pv2_chk0 (.seq hv_initI (.seq hv_initS
    (.seq hv_takeN (hv_mvo 7 6))))))

def pv2_ver : Cmd := .seq phaseA (.seq (trimC 2) (.seq (move 2 1) (.seq pv2_pre pv2_mainL)))

/-- The answer of the verifier on `(w, y)`. -/
def pv2_vres (w : List SatSym) (y : Str) : Bool :=
  decide ((clauses w).length = 0) ||
    pv2_mainF (clauses w) (clauses w).length ((clauses w).length - 1)
      (y.drop (clauses w).length) (hv_tk (clauses w).length y)
      (List.replicate (clauses w).length false)

theorem pv2_ex_run (rows : List (List SatSym)) (y : Str) (Lr : ℕ) (hy : y.length ≤ Lr)
    (hsep : ∀ r ∈ rows, sep ∉ r) :
    ExecLe (.seq pv2_pre pv2_mainL) (hv_s0 y (enc rows)).st
      (.halt (decide (rows.length = 0) || pv2_mainF rows rows.length
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
  have h3 := pv2_ex_chk0 n s2 rfl
  have hlen : (enc rows).length = 2 * ((rows.map List.length).sum + rows.length) := by
    simp only [enc, length_flatMap_ic]; rw [sum_length_le]
  by_cases hn : n = 0
  · rw [if_pos hn] at h3
    refine (ExecLe.seq_halt (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3)))).cast
      (by simp [hn]) ?_
    simp
    omega
  · rw [if_neg hn] at h3
    have h4 := hv_ex_initI n s2 rfl rfl rfl
    have h5 := hv_ex_initS n {s2 with I := List.replicate (n - 1) true} rfl rfl rfl
    simp only at h5
    have h6 := hv_ex_takeN n
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ []} rfl rfl rfl rfl
    simp only at h6
    have h8 := hv_ex_mvo (a := 7) (b := 6) (by decide) (by decide) (by decide)
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := hv_tk n y}.st rfl
    simp only [hv_st7, hv_st6, hv_u7, hv_u6] at h8
    set s9 : hv_HS := {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := [], X := hv_tk n y ++ []}
    have hi : hv_Inv rows n s9 := by
      constructor <;> simp [s9, s2, hv_length_tk]
    have h9 := pv2_ex_mainL rows n Lr hsep (n - 1) s9 hi rfl (by simp [s9]; omega)
    simp only [s9, s2, List.append_nil] at h3 h4 h5 h6 h8 h9
    rw [show (n - 1 + 1) = n by omega] at h9
    refine (ExecLe.seq_norm (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm
      (h6.seq_norm h8)))))) h9).cast (by simp [hn]) ?_
    simp [hv_length_tk]
    omega

/-- Time bound of the verifier. -/
theorem pv2_exec_ver (z : Str) :
    ExecLe pv2_ver (init [z]).stk (.halt (pv2_vres (dec z).1 (dec z).2)) (hv_Tver z.length) := by
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
  have hR := pv2_ex_run (clauses w) y z.length (by omega) (sep_not_mem_clauses w)
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
