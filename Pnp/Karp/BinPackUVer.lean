import Pnp.Karp.ThreePartUVer
import Pnp.Karp.BinPackU

/-!
# Unary BIN PACKING ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(rows `items ++ [C, kr]`, values are row lengths, `Pnp/Karp/BinPackU.lean`) and a certificate
`y : List Bool`.

The certificate is as for binary BIN PACKING (`Pnp/Karp/BinPackingVer.lean`): one pass per
bin (per symbol of `kr`); in each pass one certificate bit is popped per still unpacked item, a
set bit puts the item into the current bin.  Numbers are kept in unary (`tpuv_u`, as in
`Pnp/Karp/ThreePartUVer.lean`): adding an item is `tpuv_aL`, and the end-of-pass check
`A ≤ C` is the binary `bpv_fin` (`kv_leF true (tpuv_u a) (tpuv_u c) = decide (a ≤ c)`).

## Program (`bpuv_ver`)

`phaseA`, `trimC 2`, `m2v_kr0` (marks of `kr` on stack `10`), `tpuv_c0` (`tpuv_u |C|` on stack
`4`), `move 2 3`, then the main loop `bpuv_oL` (per mark: the pass `tpuv_iL`, then `bpv_fin`).
-/

namespace Pnp.Karp.BinPackU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.JobSeq Pnp.Karp.NAE Pnp.Karp.BinPacking
  Pnp.Karp.ThreePart Pnp.Karp.ThreePartU

/-! ## Semantics -/

/-- What the main loop computes (`c`: capacity, `k` passes, `rows`: unpacked items). -/
def bpuv_go (c : ℕ) : ℕ → List (List SatSym) → Str → Bool
  | 0, rows, _ => rows.isEmpty
  | k + 1, rows, R => decide (tpuv_s rows R ≤ c) && bpuv_go c k (bpv_U rows R) (bpv_rest rows R)

/-- The answer of the verifier on `(w, y)`. -/
def bpuv_vres (w : List SatSym) (y : Str) : Bool :=
  match (clauses w).reverse with
  | kr :: C :: rr => bpuv_go C.length kr.length rr.reverse y
  | _ => false

/-! ## The main loop -/

def bpuv_pass : Cmd := .seq tpuv_iL bpv_fin

def bpuv_oB : Cmd :=
  .pop 10 (.pop 3 (.halt true) (.halt false) (.halt false)) bpuv_pass bpuv_pass

def bpuv_oL : Cmd := .loop bpuv_oB

theorem bpuv_ex_oL {c : ℕ} (N : ℕ) (hc : c ≤ N) : ∀ (k : ℕ)
    (rows : List (List SatSym)) (R : Str), (∀ r ∈ rows, sep ∉ r) →
    (rows.map List.length).sum + rows.length ≤ N →
    ExecLe bpuv_oL (bpv_st R (enc rows) (tpuv_u c) [] (List.replicate k true) [])
      (.halt (bpuv_go c k rows R)) (bpv_To N k)
  | 0, rows, R, _, _ => by
    have h : ExecLe (Cmd.pop 3 (.halt true) (.halt false) (.halt false))
        (bpv_st R (enc rows) (tpuv_u c) [] (List.replicate 0 true) [])
        (.halt (bpuv_go c 0 rows R)) 2 := by
      rcases rows with _ | ⟨r, rows⟩
      · exact (ExecLe.pop_nil rfl (ExecLe.halt true _)).cast (by simp [bpuv_go]) (by omega)
      · obtain ⟨x, Q', hQ⟩ := kv_enc_ne r rows
        refine (ExecLe.pop_cons (r := .halt false) (T := 1) (b := x) (s := Q') hQ ?_).cast
          (by simp [bpuv_go]) (by omega)
        cases x <;> exact ExecLe.halt false _
    exact (ExecLe.loop_halt (ExecLe.pop_nil rfl h)).cast rfl (by unfold bpv_To; nlinarith)
  | k + 1, rows, R, hrows, hN => by
    have hT : bpv_To N (k + 1) = ((N + 1) * (16 * N + 30) + 30 * N + 30) + bpv_To N k := by
      simp [bpv_To]; ring
    rw [hT]
    have hA := tpuv_s_le rows R
    have hU := bpv_U_size rows R
    have hTi : bpv_Ti N rows ≤ (N + 1) * (16 * N + 30) :=
      Nat.mul_le_mul_right _ (by omega)
    have hI := tpuv_ex_iL (C := tpuv_u c) (K := List.replicate k true) N rows R 0 [] hrows
      (by omega)
    have hF := bpv_ex_fin (bpv_rest rows R) (tpuv_u c) (tpuv_u (tpuv_s rows R + 0))
      (List.replicate k true) ((enc (bpv_U rows R)).reverse ++ [])
    rw [tpuv_le_u] at hF
    have hEU := bpv_enc_length (bpv_U rows R)
    have hP : ExecLe bpuv_oB (bpv_st R (enc rows) (tpuv_u c) [] (List.replicate (k + 1) true) [])
        (if decide (tpuv_s rows R + 0 ≤ c) then
          .norm (bpv_st (bpv_rest rows R) (enc (bpv_U rows R)) (tpuv_u c) []
            (List.replicate k true) [])
          else .halt false)
        ((N + 1) * (16 * N + 30) + 30 * N + 30) := by
      refine ExecLe.pop_cons (b := true) (s := List.replicate k true) rfl ?_
      rw [bpv_u10]
      refine ((hI.seq_norm hF).cast (by simp) ?_)
      simp only [List.append_nil, List.length_reverse, tpuv_u_length] at *
      omega
    cases hr : decide (tpuv_s rows R + 0 ≤ c)
    · rw [hr] at hP
      exact (ExecLe.loop_halt hP).cast (by simp_all [bpuv_go]) (by omega)
    · rw [hr] at hP
      have ih := bpuv_ex_oL N hc k (bpv_U rows R) (bpv_rest rows R) (bpv_U_sep rows R hrows)
        (by omega)
      exact (ExecLe.loop_norm hP ih).cast (by simp_all [bpuv_go]) le_rfl

/-! ## The whole verifier -/

def bpuv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq m2v_kr0 (.seq tpuv_c0 (.seq (move 2 3) bpuv_oL))))

theorem bpuv_exec_ver (z : Str) :
    ExecLe bpuv_ver (init [z]).stk (.halt (bpuv_vres (dec z).1 (dec z).2)) (bpv_Tver z.length) := by
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
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ), ExecLe c σ₂ r T →
      ExecLe (.seq phaseA (.seq (trimC 2) c)) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + T)) :=
    fun c r T h => hA.seq_norm (hT.seq_norm h)
  have hTo : bpv_To z.length 0 ≤ bpv_To z.length z.length :=
    Nat.mul_le_mul_right _ (by omega)
  unfold bpuv_vres bpuv_ver
  rcases hcw : (clauses w).reverse with _ | ⟨kr, rr⟩
  · have h2 : σ₂ 2 = [] := by
      simp only [σ₂, update_self, trunc]
      rw [List.reverse_eq_nil_iff.1 hcw]; rfl
    refine (hpre _ _ _ (ExecLe.seq_halt (ExecLe.pop_nil h2 (ExecLe.halt false _)))).cast rfl ?_
    unfold bpv_Tver; omega
  · have hcl : clauses w = rr.reverse ++ [kr] := by
      rw [← List.reverse_reverse (clauses w), hcw]; simp
    set u := rr.reverse.flatMap (· ++ [sep])
    have htr : trunc w = u ++ (kr ++ [sep]) := by simp [trunc, hcl, u]
    have hsep : sep ∉ kr := sep_not_mem_clauses w kr (by simp [hcl])
    have hu : u = [] ∨ ∃ u', u = u' ++ [sep] := by
      rcases rr.reverse.eq_nil_or_concat with h | ⟨L, c, h⟩
      · left; simp only [u, h]; rfl
      · right; exact ⟨L.flatMap (· ++ [sep]) ++ c, by simp only [u, h]; simp⟩
    have h2 : σ₂ 2 = false :: false :: (rc kr.reverse ++ (u.flatMap ic).reverse) := by
      simp only [σ₂, update_self, htr, rc_eq]
      simp [List.flatMap_append, ic]
    set σ' := update σ₂ 2 (rc kr.reverse ++ (u.flatMap ic).reverse)
    have hK := m2v_ex_krL u hu kr.reverse σ' 0 (by simpa using hsep) (by simp [σ'])
      (by simp [σ', σ₂, σ₁, he 10 (by decide)])
    have hK0 : ExecLe m2v_kr0 σ₂ (.norm (update (update σ' 2 ((u.flatMap ic).reverse)) 10
        (List.replicate (kr.reverse.length + 0) true))) (4 * kr.reverse.length + 6 + 1 + 1) :=
      ExecLe.pop_cons (b := false) h2 (ExecLe.pop_cons (b := false)
        (s := rc kr.reverse ++ (u.flatMap ic).reverse) (by simp)
        (by simpa [σ', update_idem] using hK))
    set σ₃ := update (update σ' 2 ((u.flatMap ic).reverse)) 10
        (List.replicate (kr.reverse.length + 0) true)
    have hul : u.length + kr.length + 1 = (trunc w).length := by simp [htr]; omega
    rcases rr with _ | ⟨C, rr⟩
    · have h32 : σ₃ 2 = [] := by simp [σ₃, u]
      refine (hpre _ _ _ (hK0.seq_norm (ExecLe.seq_halt (ExecLe.pop_nil h32
        (ExecLe.halt false _))))).cast rfl ?_
      simp only [List.length_reverse] at *
      unfold bpv_Tver; omega
    · set u2 := rr.reverse.flatMap (· ++ [sep])
      have hu' : u = u2 ++ (C ++ [sep]) := by simp [u, u2]
      have hsepC : sep ∉ C := sep_not_mem_clauses w C (by simp [hcl])
      have hu2 : u2 = [] ∨ ∃ u', u2 = u' ++ [sep] := by
        rcases rr.reverse.eq_nil_or_concat with h | ⟨L, c, h⟩
        · left; simp only [u2, h]; rfl
        · right; exact ⟨L.flatMap (· ++ [sep]) ++ c, by simp only [u2, h]; simp⟩
      have h32 : σ₃ 2 = false :: false :: (rc C.reverse ++ (u2.flatMap ic).reverse) := by
        simp only [σ₃, update_self, update_of_ne (show (2 : ℕ) ≠ 10 by decide), hu', rc_eq]
        simp [List.flatMap_append, ic]
      set σ₄ := update σ₃ 2 (rc C.reverse ++ (u2.flatMap ic).reverse)
      have hC := tpuv_ex_cL u2 hu2 C.reverse σ₄ [] (by simpa using hsepC) (by simp [σ₄])
        (by simp [σ₄, σ₃, σ', σ₂, σ₁, he 4 (by decide)])
      have hC0 : ExecLe tpuv_c0 σ₃ (.norm (update (update σ₄ 2 ((u2.flatMap ic).reverse)) 4
          (tpuv_u C.reverse.length ++ []))) (4 * C.reverse.length + 6 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h32 (ExecLe.pop_cons (b := false)
          (s := rc C.reverse ++ (u2.flatMap ic).reverse) (by simp)
          (by simpa [σ₄, update_idem] using hC))
      set σ₅ := update (update σ₄ 2 ((u2.flatMap ic).reverse)) 4
          (tpuv_u C.reverse.length ++ [])
      have hM := exec_move (a := 2) (b := 3) (by decide) _ σ₅ rfl
      have hσ : update (update σ₅ 2 []) 3 ((σ₅ 2).reverse ++ σ₅ 3) =
          bpv_st y (enc rr.reverse) (tpuv_u C.length) [] (List.replicate kr.length true) [] := by
        funext j
        rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|j <;>
          simp [σ₅, σ₄, σ₃, σ', σ₂, σ₁, bpv_st, he, u2, enc]
      rw [hσ] at hM
      have hsum := sum_length_le rr.reverse
      have hu2l : u2.length = (rr.reverse.map List.length).sum + rr.reverse.length := by
        rw [hsum]
      have hu'l : u.length = u2.length + C.length + 1 := by simp [hu']; omega
      have hR := bpuv_ex_oL (c := C.length) z.length (by omega) kr.length
        rr.reverse y (fun r hr => sep_not_mem_clauses w r (by rw [hcl]; exact List.mem_append_left _ (by simp [hr])))
        (by omega)
      refine (hpre _ _ _ (hK0.seq_norm (hC0.seq_norm ((ExecLe.of hM).seq_norm hR)))).cast
        (by simp) ?_
      have hc : (u2.flatMap ic).length = 2 * u2.length := length_flatMap_ic u2
      have h52 : σ₅ 2 = (u2.flatMap ic).reverse := by simp [σ₅]
      have hk : bpv_To z.length kr.length ≤ bpv_To z.length z.length :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [h52, List.length_reverse, hc, bpv_Tver]
      omega

end Pnp.Karp.BinPackU
