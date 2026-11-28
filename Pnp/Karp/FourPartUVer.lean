import Pnp.Karp.ThreePartUVer
import Pnp.Karp.FourPartU

/-!
# Unary 4-PARTITION ∈ NP: the verifier program

The verifier of unary 3-PARTITION (`Pnp/Karp/ThreePartUVer.lean`) with two changes: the bound
check of an item `a` is `B < 5 a ∧ 3 a < B` (`fpuv_chk`), and every pass of the main loop pops
**four** marks (`fpuv_oB`), so that an accepted certificate with `k` marks has `4 ∣ k` and
`k / 4` groups.  The unary helpers (`tpuv_u`, `tpuv_aL`, `tpuv_cL`, `tpuv_iL`, `tpuv_pass`, …)
are reused.

## Program (`fpuv_ver`)

Stacks as in `bpv_st` (`0` certificate, `3` items, `4` the bound `B` in unary, `5` the
accumulator, `10` the unary pass counter, `12` the kept items); `13`–`16` are temporaries.

1. `phaseA`, `trimC 2`, `tpuv_c0`: read the last row `Bv` as `tpuv_u |Bv|` onto stack `4`;
   `move 2 3`: the code of the items is on stack `3`;
2. `copyVia 3 12 15`, the bounds loop `fpuv_bL` (per item: `tpuv_aL`, `fpuv_chk`: halt `false`
   unless `B < 5 a ∧ 3 a < B`, push a mark on stack `10`);
3. `fpuv_oL`: pop four marks per pass, run a pass `tpuv_iL` and check `A = B` (`tpv_fin`).
-/

namespace Pnp.Karp.FourPartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.JobSeq Pnp.Karp.NAE Pnp.Karp.BinPacking
  Pnp.Karp.ThreePart Pnp.Karp.ThreePartU

/-! ## The checking relation -/

/-- The bounds `c < 5 a ∧ 3 a < c` for every row. -/
def fpuv_bnd (c : ℕ) : List (List SatSym) → Bool
  | [] => true
  | r :: rs => (decide (c < 5 * r.length) && decide (3 * r.length < c)) && fpuv_bnd c rs

/-- `k` marks: `k / 4` passes, each selecting a group of unary sum `c`. -/
def fpuv_go (c : ℕ) : ℕ → List (List SatSym) → Str → Bool
  | 0, rows, _ => rows.isEmpty
  | 1, _, _ => false
  | 2, _, _ => false
  | 3, _, _ => false
  | k + 4, rows, R => decide (tpuv_s rows R = c) && fpuv_go c k (bpv_U rows R) (bpv_rest rows R)

/-- The checking relation of unary 4-PARTITION. -/
def fpuv_vres (w : List SatSym) (y : Str) : Bool :=
  match (clauses w).reverse with
  | [] => false
  | Bv :: rr => fpuv_bnd Bv.length rr.reverse &&
      fpuv_go Bv.length rr.reverse.length rr.reverse y

local macro "fpuv_stx" : tactic =>
  `(tactic| (funext j; rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|j <;>
    simp [bpv_st, update_apply]))


def fpuv_chk : Cmd :=
  .seq (copyVia 4 13 15) (.seq (copyVia 5 16 15) (.seq (copyVia 5 16 15) (.seq (copyVia 5 16 15)
    (.seq (copyVia 5 16 15) (.seq (copyVia 5 16 15)
    (tpv_test 16 13 (.seq (copyVia 4 13 15) (.seq (copyVia 5 16 15) (.seq (copyVia 5 16 15)
      (.seq (move 16 5) (tpv_test 13 5 (.push 10 true) (.halt false)))))) (.halt false)))))))

theorem fpuv_ex_chk (R Q K B : Str) (c a : ℕ) :
    ExecLe fpuv_chk (bpv_st R Q (tpuv_u c) (tpuv_u a) K B)
      (if decide (c < 5 * a) && decide (3 * a < c) then
        .norm (bpv_st R Q (tpuv_u c) [] (true :: K) B) else .halt false)
      (80 * (a + c) + 80) := by
  have hS0 : ∀ A, tpuv_S R Q (tpuv_u c) A K B [] [] = bpv_st R Q (tpuv_u c) A K B := by
    intro A; unfold tpuv_S; fpuv_stx
  have c13 : ∀ A X Y, ExecLe (copyVia 4 13 15) (tpuv_S R Q (tpuv_u c) A K B X Y)
      (.norm (tpuv_S R Q (tpuv_u c) A K B (tpuv_u c ++ X) Y)) (5 * c + 4) := by
    intro A X Y
    refine (ExecLe.of (exec_copyVia (a := 4) (b := 13) (t := 15) (by decide) (by decide)
      (by decide) _ (by simp [tpuv_S, bpv_st]))).cast ?_
      (by simp [tpuv_S, bpv_st, tpuv_u_length])
    congr 1; unfold tpuv_S; fpuv_stx
  have c16 : ∀ X m, ExecLe (copyVia 5 16 15) (tpuv_S R Q (tpuv_u c) (tpuv_u a) K B X (tpuv_u m))
      (.norm (tpuv_S R Q (tpuv_u c) (tpuv_u a) K B X (tpuv_u (a + m)))) (5 * a + 4) := by
    intro X m
    refine (ExecLe.of (exec_copyVia (a := 5) (b := 16) (t := 15) (by decide) (by decide)
      (by decide) _ (by simp [tpuv_S, bpv_st]))).cast ?_
      (by simp [tpuv_S, bpv_st, tpuv_u_length])
    congr 1; rw [← tpuv_u_add]; unfold tpuv_S; fpuv_stx
  have mv : ∀ A X Y, ExecLe (move 16 5) (tpuv_S R Q (tpuv_u c) A K B X Y)
      (.norm (tpuv_S R Q (tpuv_u c) (Y.reverse ++ A) K B X [])) (2 * Y.length + 2) := by
    intro A X Y
    refine (ExecLe.of (exec_move (a := 16) (b := 5) (by decide) Y _
      (by simp [tpuv_S]))).cast ?_ le_rfl
    congr 1; unfold tpuv_S; fpuv_stx
  have r1 : ∀ A X Y, update (update (tpuv_S R Q (tpuv_u c) A K B X Y) 16 []) 13 [] =
      bpv_st R Q (tpuv_u c) A K B := by
    intro A X Y; unfold tpuv_S; fpuv_stx
  have r2 : ∀ A X, update (update (tpuv_S R Q (tpuv_u c) A K B X []) 13 []) 5 [] =
      bpv_st R Q (tpuv_u c) [] K B := by
    intro A X; unfold tpuv_S; fpuv_stx
  have hP10 : ExecLe (.push 10 true) (bpv_st R Q (tpuv_u c) [] K B)
      (.norm (bpv_st R Q (tpuv_u c) [] (true :: K) B)) 1 :=
    (ExecLe.push 10 true _).cast (by rw [bpv_u10]; rfl) le_rfl
  have e2 : (tpuv_u (a + (a + 0))).reverse ++ tpuv_u a = tpuv_u (3 * a) := by
    rw [tpuv_u_rev, tpuv_u_add]; congr 1; omega
  have hcn : ExecLe (.seq (copyVia 4 13 15) (.seq (copyVia 5 16 15) (.seq (copyVia 5 16 15)
      (.seq (move 16 5) (tpv_test 13 5 (.push 10 true) (.halt false))))))
      (bpv_st R Q (tpuv_u c) (tpuv_u a) K B)
      (if decide (c ≤ 3 * a) then .halt false else .norm (bpv_st R Q (tpuv_u c) [] (true :: K) B))
      (5 * c + 4 + (5 * a + 4 + (5 * a + 4 + (2 * (2 * a) + 2 + (5 * (c + 3 * a) + 1 + 5))))) := by
    rw [← hS0]
    have m := mv (tpuv_u a) (tpuv_u c ++ []) (tpuv_u (a + (a + 0)))
    rw [e2] at m
    have t2 := tpv_ex_test (a := 13) (b := 5) (cn := .push 10 true) (ct := .halt false)
      (X := tpuv_u c ++ []) (Y := tpuv_u (3 * a)) (by decide) (by decide) (by decide)
      (σ := tpuv_S R Q (tpuv_u c) (tpuv_u (3 * a)) K B (tpuv_u c ++ []) [])
      (by simp [tpuv_S]) (by simp [tpuv_S, bpv_st]) (by simp [tpuv_S, bpv_st])
      (r := if decide (c ≤ 3 * a) then .halt false
        else .norm (bpv_st R Q (tpuv_u c) [] (true :: K) B)) (T := 1) (by
        rw [r2, List.append_nil, tpuv_le_u]
        by_cases h : c ≤ 3 * a
        · simp only [h, decide_true, if_true]; exact ExecLe.halt false _
        · simp only [h, decide_false, if_false, Bool.false_eq_true]; exact hP10)
    refine ((c13 _ _ _).seq_norm ((c16 _ 0).seq_norm ((c16 _ _).seq_norm
      (m.seq_norm t2)))).cast rfl ?_
    simp only [tpuv_u_length, List.length_append, List.length_nil]
    omega
  have t1 := tpv_ex_test (a := 16) (b := 13) (ct := .halt false)
    (cn := .seq (copyVia 4 13 15) (.seq (copyVia 5 16 15) (.seq (copyVia 5 16 15)
      (.seq (move 16 5) (tpv_test 13 5 (.push 10 true) (.halt false))))))
    (X := tpuv_u (a + (a + (a + (a + (a + 0)))))) (Y := tpuv_u c ++ []) (by decide) (by decide)
    (by decide)
    (σ := tpuv_S R Q (tpuv_u c) (tpuv_u a) K B (tpuv_u c ++ [])
      (tpuv_u (a + (a + (a + (a + (a + 0)))))))
    (by simp [tpuv_S]) (by simp [tpuv_S]) (by simp [tpuv_S, bpv_st])
    (r := if decide (c < 5 * a) && decide (3 * a < c) then
        .norm (bpv_st R Q (tpuv_u c) [] (true :: K) B) else .halt false)
    (T := 5 * c + 4 + (5 * a + 4 + (5 * a + 4 + (2 * (2 * a) + 2 + (5 * (c + 3 * a) + 1 + 5)))))
    (by
      rw [r1, List.append_nil, tpuv_le_u]
      by_cases h1 : a + (a + (a + (a + (a + 0)))) ≤ c
      · have : ¬ c < 5 * a := by omega
        simp only [h1, decide_true, if_true, this, decide_false, Bool.false_and,
          Bool.false_eq_true, if_false]
        exact (ExecLe.halt false _).cast rfl (by omega)
      · have : c < 5 * a := by omega
        simp only [h1, decide_false, Bool.false_eq_true, if_false, this, decide_true,
          Bool.true_and]
        refine hcn.cast ?_ le_rfl
        by_cases h2 : c ≤ 3 * a
        · have : ¬ 3 * a < c := by omega
          simp [h2, this]
        · have : 3 * a < c := by omega
          simp [h2, this])
  rw [← hS0]
  refine ((c13 _ _ _).seq_norm ((c16 _ 0).seq_norm ((c16 _ _).seq_norm ((c16 _ _).seq_norm
    ((c16 _ _).seq_norm ((c16 _ _).seq_norm t1)))))).cast rfl ?_
  simp only [tpuv_u_length, List.length_append, List.length_nil]
  omega

/-! ## The bounds loop -/

def fpuv_bB : Cmd := bpv_peek (.seq tpuv_aL fpuv_chk)

def fpuv_bL : Cmd := .loop fpuv_bB

/-- Cost of the bounds loop. -/
def fpuv_Tb (N : ℕ) (rows : List (List SatSym)) : ℕ := (rows.length + 1) * (200 * N + 200)

theorem fpuv_ex_bL {R : Str} {c : ℕ} (N : ℕ) (hc : c ≤ N) : ∀ (rows : List (List SatSym))
    (K B : Str), (∀ r ∈ rows, sep ∉ r) → (rows.map List.length).sum + rows.length ≤ N →
    ExecLe fpuv_bL (bpv_st R (enc rows) (tpuv_u c) [] K B)
      (if fpuv_bnd c rows then
        .norm (bpv_st R [] (tpuv_u c) [] (List.replicate rows.length true ++ K) B)
        else .halt false) (fpuv_Tb N rows)
  | [], K, B, _, _ =>
    (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [fpuv_bnd, enc]) (by simp [fpuv_Tb])
  | r :: rows, K, B, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hN
    obtain ⟨x, Q', hQ⟩ := kv_enc_ne r rows
    have hT : fpuv_Tb N (r :: rows) = (200 * N + 200) + fpuv_Tb N rows := by
      simp [fpuv_Tb]; ring
    rw [hT]
    rw [enc_cons] at hQ ⊢
    have ha := tpuv_ex_a (R := R) (C := tpuv_u c) (K := K) (enc rows) r [] B hr
    rw [List.append_nil] at ha
    have hc' := fpuv_ex_chk R (enc rows) K B c r.length
    have hb := bpv_ex_peek hQ (ha.seq_norm hc')
    cases hok : (decide (c < 5 * r.length) && decide (3 * r.length < c))
    · rw [hok] at hb
      exact (ExecLe.loop_halt hb).cast (by simp [fpuv_bnd, hok])
        (by omega)
    · rw [hok] at hb
      have ih := fpuv_ex_bL (R := R) N hc rows (true :: K) B hrs (by omega)
      refine (ExecLe.loop_norm (hb.cast rfl le_rfl) ih).cast ?_ ?_
      · simp [fpuv_bnd, hok, List.replicate_succ']
      · omega

/-! ## The main loop -/

def fpuv_oB : Cmd :=
  .pop 10 (.pop 3 (.halt true) (.halt false) (.halt false)) (.halt false)
    (.pop 10 (.halt false) (.halt false) (.pop 10 (.halt false) (.halt false)
      (.pop 10 (.halt false) (.halt false) tpuv_pass)))

def fpuv_oL : Cmd := .loop fpuv_oB

theorem fpuv_ex_oL {c : ℕ} (N : ℕ) (hc : c ≤ N) : ∀ (k : ℕ)
    (rows : List (List SatSym)) (R : Str), (∀ r ∈ rows, sep ∉ r) →
    (rows.map List.length).sum + rows.length ≤ N →
    ExecLe fpuv_oL (bpv_st R (enc rows) (tpuv_u c) [] (List.replicate k true) [])
      (.halt (fpuv_go c k rows R)) (tpv_To N k)
  | 0, rows, R, _, _ => by
    have h : ExecLe (Cmd.pop 3 (.halt true) (.halt false) (.halt false))
        (bpv_st R (enc rows) (tpuv_u c) [] (List.replicate 0 true) [])
        (.halt (fpuv_go c 0 rows R)) 2 := by
      rcases rows with _ | ⟨r, rows⟩
      · exact (ExecLe.pop_nil rfl (ExecLe.halt true _)).cast (by simp [fpuv_go]) (by omega)
      · obtain ⟨x, Q', hQ⟩ := kv_enc_ne r rows
        refine (ExecLe.pop_cons (r := .halt false) (T := 1) (b := x) (s := Q') hQ ?_).cast
          (by simp [fpuv_go]) (by omega)
        cases x <;> exact ExecLe.halt false _
    exact (ExecLe.loop_halt (ExecLe.pop_nil rfl h)).cast rfl (by unfold tpv_To; nlinarith)
  | 1, rows, R, _, _ => by
    refine (ExecLe.loop_halt (ExecLe.pop_cons (r := .halt false) (b := true) (s := []) rfl ?_)).cast
      (by simp [fpuv_go]) (show 3 ≤ tpv_To N 1 by unfold tpv_To; nlinarith)
    rw [bpv_u10, if_pos rfl]
    exact (ExecLe.pop_nil rfl (ExecLe.halt false _))
  | 2, rows, R, _, _ => by
    refine (ExecLe.loop_halt (ExecLe.pop_cons (r := .halt false) (b := true) (s := [true]) rfl
      ?_)).cast (by simp [fpuv_go]) (show 4 ≤ tpv_To N 2 by unfold tpv_To; nlinarith)
    rw [bpv_u10, if_pos rfl]
    refine ExecLe.pop_cons (b := true) (s := []) rfl ?_
    rw [bpv_u10, if_pos rfl]
    exact (ExecLe.pop_nil rfl (ExecLe.halt false _))
  | 3, rows, R, _, _ => by
    refine (ExecLe.loop_halt (ExecLe.pop_cons (r := .halt false) (b := true) (s := [true, true])
      rfl ?_)).cast (by simp [fpuv_go]) (show 5 ≤ tpv_To N 3 by unfold tpv_To; nlinarith)
    rw [bpv_u10, if_pos rfl]
    refine ExecLe.pop_cons (b := true) (s := [true]) rfl ?_
    rw [bpv_u10, if_pos rfl]
    refine ExecLe.pop_cons (b := true) (s := []) rfl ?_
    rw [bpv_u10, if_pos rfl]
    exact (ExecLe.pop_nil rfl (ExecLe.halt false _))
  | k + 4, rows, R, hrows, hN => by
    have hT : tpv_To N (k + 4) =
        ((N + 1) * (16 * N + 30) + 50 * N + 50) + (3 * ((N + 1) * (16 * N + 30) + 50 * N + 50)
          + tpv_To N k) := by
      simp [tpv_To]; ring
    rw [hT]
    have hA := tpuv_s_le rows R
    have hU := bpv_U_size rows R
    have hTi : bpv_Ti N rows ≤ (N + 1) * (16 * N + 30) :=
      Nat.mul_le_mul_right _ (by omega)
    have hI := tpuv_ex_iL (C := tpuv_u c) (K := List.replicate k true) N rows R 0 [] hrows
      (by omega)
    have hF := tpv_ex_fin (bpv_rest rows R) (tpuv_u c) (tpuv_u (tpuv_s rows R + 0))
      (List.replicate k true) ((enc (bpv_U rows R)).reverse ++ [])
    rw [tpuv_eq_u] at hF
    have hEU := bpv_enc_length (bpv_U rows R)
    have hP : ExecLe fpuv_oB (bpv_st R (enc rows) (tpuv_u c) [] (List.replicate (k + 4) true) [])
        (if decide (tpuv_s rows R + 0 = c) then
          .norm (bpv_st (bpv_rest rows R) (enc (bpv_U rows R)) (tpuv_u c) []
            (List.replicate k true) [])
          else .halt false)
        ((N + 1) * (16 * N + 30) + 50 * N + 50) := by
      refine ExecLe.pop_cons (b := true) (s := List.replicate (k + 3) true) rfl ?_
      rw [bpv_u10, if_pos rfl]
      refine ExecLe.pop_cons (b := true) (s := List.replicate (k + 2) true) rfl ?_
      rw [bpv_u10, if_pos rfl]
      refine ExecLe.pop_cons (b := true) (s := List.replicate (k + 1) true) rfl ?_
      rw [bpv_u10, if_pos rfl]
      refine ExecLe.pop_cons (b := true) (s := List.replicate k true) rfl ?_
      rw [bpv_u10, if_pos rfl]
      refine ((hI.seq_norm hF).cast (by simp) ?_)
      simp only [List.append_nil, List.length_reverse, tpuv_u_length] at *
      omega
    cases hr : decide (tpuv_s rows R + 0 = c)
    · rw [hr] at hP
      exact (ExecLe.loop_halt hP).cast (by simp_all [fpuv_go]) (by omega)
    · rw [hr] at hP
      have ih := fpuv_ex_oL N hc k (bpv_U rows R) (bpv_rest rows R) (bpv_U_sep rows R hrows)
        (by omega)
      exact (ExecLe.loop_norm hP ih).cast (by simp_all [fpuv_go]) (by omega)

/-! ## The whole verifier -/

def fpuv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq tpuv_c0 (.seq (move 2 3) (.seq (copyVia 3 12 15)
    (.seq fpuv_bL (.seq (move 12 13) (.seq (move 13 3) fpuv_oL)))))))

/-- Time bound of the verifier. -/
def fpuv_Tver (n : ℕ) : ℕ := 40 * n + 40 + (n + 1) * (200 * n + 200) + tpv_To n n

theorem fpuv_exec_ver (z : Str) :
    ExecLe fpuv_ver (init [z]).stk (.halt (fpuv_vres (dec z).1 (dec z).2))
      (fpuv_Tver z.length) := by
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
  have hTo : tpv_To z.length 0 ≤ tpv_To z.length z.length :=
    Nat.mul_le_mul_right _ (by omega)
  unfold fpuv_vres fpuv_ver
  rcases hcw : (clauses w).reverse with _ | ⟨Bv, rr⟩
  · have h2 : σ₂ 2 = [] := by
      simp only [σ₂, update_self, trunc]
      rw [List.reverse_eq_nil_iff.1 hcw]; rfl
    refine (hpre _ _ _ (ExecLe.seq_halt (ExecLe.pop_nil h2 (ExecLe.halt false _)))).cast rfl ?_
    unfold fpuv_Tver; omega
  · have hcl : clauses w = rr.reverse ++ [Bv] := by
      rw [← List.reverse_reverse (clauses w), hcw]; simp
    set u := rr.reverse.flatMap (· ++ [sep])
    have htr : trunc w = u ++ (Bv ++ [sep]) := by simp [trunc, hcl, u]
    have hsepC : sep ∉ Bv := sep_not_mem_clauses w Bv (by simp [hcl])
    have hu : u = [] ∨ ∃ u', u = u' ++ [sep] := by
      rcases rr.reverse.eq_nil_or_concat with h | ⟨L, c, h⟩
      · left; simp only [u, h]; rfl
      · right; exact ⟨L.flatMap (· ++ [sep]) ++ c, by simp only [u, h]; simp⟩
    have h2 : σ₂ 2 = false :: false :: (rc Bv.reverse ++ (u.flatMap ic).reverse) := by
      simp only [σ₂, update_self, htr, rc_eq]
      simp [List.flatMap_append, ic]
    set σ₄ := update σ₂ 2 (rc Bv.reverse ++ (u.flatMap ic).reverse)
    have hC := tpuv_ex_cL u hu Bv.reverse σ₄ [] (by simpa using hsepC) (by simp [σ₄])
      (by simp [σ₄, σ₂, σ₁, he 4 (by decide)])
    have hC0 : ExecLe tpuv_c0 σ₂ (.norm (update (update σ₄ 2 ((u.flatMap ic).reverse)) 4
        (tpuv_u Bv.reverse.length ++ []))) (4 * Bv.reverse.length + 6 + 1 + 1) :=
      ExecLe.pop_cons (b := false) h2 (ExecLe.pop_cons (b := false)
        (s := rc Bv.reverse ++ (u.flatMap ic).reverse) (by simp)
        (by simpa [σ₄, update_idem] using hC))
    set σ₅ := update (update σ₄ 2 ((u.flatMap ic).reverse)) 4
        (tpuv_u Bv.reverse.length ++ [])
    have hM := exec_move (a := 2) (b := 3) (by decide) _ σ₅ rfl
    set items := rr.reverse
    set C := tpuv_u Bv.length
    have hσ : update (update σ₅ 2 []) 3 ((σ₅ 2).reverse ++ σ₅ 3) =
        bpv_st y (enc items) C [] [] [] := by
      funext j
      rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|j <;>
        simp [σ₅, σ₄, σ₂, σ₁, bpv_st, he, u, enc, items, C]
    rw [hσ] at hM
    have hCp := ExecLe.of (exec_copyVia (a := 3) (b := 12) (t := 15) (by decide) (by decide)
      (by decide) (bpv_st y (enc items) C [] [] []) rfl)
    have hσ2 : update (bpv_st y (enc items) C [] [] []) 12
        (bpv_st y (enc items) C [] [] [] 3 ++ bpv_st y (enc items) C [] [] [] 12) =
        bpv_st y (enc items) C [] [] (enc items) := by fpuv_stx
    rw [hσ2] at hCp
    have hsum := sum_length_le items
    have l3 : (bpv_st y (enc items) C [] [] [] 3).length = (enc items).length := rfl
    have hug : (items.flatMap (· ++ [sep])).length = u.length := rfl
    have hul : u.length + Bv.length + 1 = (trunc w).length := by simp [htr]; omega
    have hCl : Bv.length ≤ z.length := by omega
    have hsep : ∀ r ∈ items, sep ∉ r := fun r hr =>
      sep_not_mem_clauses w r (by rw [hcl]; exact List.mem_append_left _ hr)
    have hB := fpuv_ex_bL (R := y) z.length hCl items [] (enc items) hsep (by omega)
    have hc : (u.flatMap ic).length = 2 * u.length := length_flatMap_ic u
    have h52 : σ₅ 2 = (u.flatMap ic).reverse := by simp [σ₅]
    have hEl : (enc items).length = 2 * u.length := by
      rw [bpv_enc_length]; omega
    have hTb : fpuv_Tb z.length items ≤ (z.length + 1) * (200 * z.length + 200) :=
      Nat.mul_le_mul_right _ (by omega)
    cases hb : fpuv_bnd Bv.length items
    · rw [hb] at hB
      refine (hpre _ _ _ (hC0.seq_norm ((ExecLe.of hM).seq_norm (hCp.seq_norm
        (ExecLe.seq_halt hB))))).cast
        (by have hb' : fpuv_bnd Bv.length rr.reverse = false := hb; simp [hb']) ?_
      simp only [h52, List.length_reverse, hc, fpuv_Tver, List.length_reverse] at *
      omega
    · rw [hb] at hB
      simp only [if_true] at hB
      have hM1 := exec_move (a := 12) (b := 13) (by decide) (enc items)
        (bpv_st y [] C [] (List.replicate items.length true ++ []) (enc items)) rfl
      have hM2 := exec_move (a := 13) (b := 3) (by decide) (enc items).reverse
        (update (update (bpv_st y [] C [] (List.replicate items.length true ++ [])
          (enc items)) 12 []) 13 ((enc items).reverse ++
            bpv_st y [] C [] (List.replicate items.length true ++ []) (enc items) 13))
        (by simp [bpv_st])
      have hσ3 : update (update (update (update (bpv_st y [] C [] (List.replicate items.length
          true ++ []) (enc items)) 12 []) 13 ((enc items).reverse ++
            bpv_st y [] C [] (List.replicate items.length true ++ []) (enc items) 13)) 13 [])
          3 ((enc items).reverse.reverse ++ (update (update (bpv_st y [] C []
            (List.replicate items.length true ++ []) (enc items)) 12 []) 13
              ((enc items).reverse ++ bpv_st y [] C [] (List.replicate items.length true ++ [])
                (enc items) 13)) 3) =
          bpv_st y (enc items) C [] (List.replicate items.length true) [] := by fpuv_stx
      rw [hσ3] at hM2
      have hR := fpuv_ex_oL (c := Bv.length) z.length hCl items.length items y hsep (by omega)
      refine (hpre _ _ _ (hC0.seq_norm ((ExecLe.of hM).seq_norm (hCp.seq_norm
        (hB.seq_norm ((ExecLe.of hM1).seq_norm ((ExecLe.of hM2).seq_norm hR))))))).cast
        (by have hb' : fpuv_bnd Bv.length rr.reverse = true := hb; simp [hb', items]) ?_
      have hk : tpv_To z.length items.length ≤ tpv_To z.length z.length :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [h52, List.length_reverse, hc, fpuv_Tver, List.length_reverse, hEl] at *
      omega

theorem fpuv_Tver_le (n : ℕ) : fpuv_Tver n ≤ tb 9 n := by
  unfold fpuv_Tver tpv_To tb
  have h5 : 2 ^ 5 ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have e : (n + 2) ^ 9 = (n + 2) ^ 4 * (n + 2) ^ 5 := by ring
  have e4 : (n + 2) ^ 4 = (n + 2) * (n + 2) * (n + 2) * (n + 2) := by ring
  have h1 : 40 * n + 40 + (n + 1) * (200 * n + 200) + (n + 1) * ((n + 1) * (16 * n + 30) +
      50 * n + 50) ≤ (n + 2) ^ 4 * 32 := by
    rw [e4]; nlinarith [Nat.zero_le (n * n * n * n), Nat.zero_le (n * n * n), Nat.zero_le (n * n)]
  rw [e]
  exact h1.trans (Nat.mul_le_mul_left _ (by simpa using h5))

end Pnp.Karp.FourPartU
