import Pnp.Karp.ThreePartVer
import Pnp.Karp.KnapNP
import Pnp.Karp.ThreePartU

/-!
# Unary 3-PARTITION ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(rows `items ++ [Bv]`, values are row lengths, `Pnp/Karp/ThreePartU.lean`) and a certificate
`y : List Bool`.

## Certificate

As for binary 3-PARTITION (`Pnp/Karp/ThreePartVer.lean`) and BIN PACKING: the certificate is
read in passes, one per group; in each pass one certificate bit is popped per item that is still
unassigned, a set bit puts the item into the current group.

## Numbers in unary

All numbers are kept as all-`true` stacks `tpuv_u n` (`n` copies of `true`).  Adding a row is
pushing one `true` per symbol (`tpuv_aL`); comparisons reuse `kv_cmpLoop` (`tpv_test`), since
`kv_leF true (tpuv_u a) (tpuv_u b) = decide (a ≤ b)` (`tpuv_le_u`); the end-of-pass check is
`tpv_fin` of M63.

## Program (`tpuv_ver`)

Stacks as in `bpv_st` (`0` certificate, `3` items, `4` the bound `B` in unary, `5` the
accumulator, `10` the unary pass counter, `12` the kept items); `13`–`16` are temporaries.

1. `phaseA`, `trimC 2`, `tpuv_c0`: read the last row `Bv` as `tpuv_u |Bv|` onto stack `4`;
   `move 2 3`: the code of the items is on stack `3`;
2. `copyVia 3 12 15`, the bounds loop `tpuv_bL` (per item: `tpuv_aL`, `tpuv_chk`: halt `false`
   unless `B < 4 a` and `2 a < B`; push a mark onto stack `10`); restore the items;
3. `tpuv_oL`: pop three marks per pass, run a pass `tpuv_iL` and check `A = B` (`tpv_fin`).
-/

namespace Pnp.Karp.ThreePartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.JobSeq Pnp.Karp.NAE Pnp.Karp.BinPacking
  Pnp.Karp.ThreePart

/-! ## Unary numbers -/

/-- The unary stack of `n`. -/
def tpuv_u (n : ℕ) : Str := List.replicate n true

theorem tpuv_u_length (n : ℕ) : (tpuv_u n).length = n := by simp [tpuv_u]

theorem tpuv_u_add (a b : ℕ) : tpuv_u a ++ tpuv_u b = tpuv_u (a + b) := by
  simp [tpuv_u, List.replicate_append_replicate]

theorem tpuv_u_succ (n : ℕ) (S : Str) : tpuv_u n ++ true :: S = tpuv_u (n + 1) ++ S := by
  simp [tpuv_u, List.replicate_succ']

theorem tpuv_u_rev (n : ℕ) : (tpuv_u n).reverse = tpuv_u n := by simp [tpuv_u]

theorem tpuv_bval_u : ∀ n : ℕ, sv_bval (tpuv_u n) + 1 = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    have ih := tpuv_bval_u n
    simp only [tpuv_u, List.replicate_succ, sv_bval, if_true] at ih ⊢
    rw [pow_succ]; omega

theorem tpuv_le_u (a b : ℕ) : kv_leF true (tpuv_u a) (tpuv_u b) = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, kv_le_iff, decide_eq_true_iff]
  have ha := tpuv_bval_u a
  have hb := tpuv_bval_u b
  have : 2 ^ a ≤ 2 ^ b ↔ a ≤ b := Nat.pow_le_pow_iff_right (by norm_num)
  omega

/-! ## Semantics -/

/-- The total length of the rows selected by `R`. -/
def tpuv_s : List (List SatSym) → Str → ℕ
  | [], _ => 0
  | r :: rs, R => (if R.headD false then r.length else 0) + tpuv_s rs R.tail

/-- The bound check of all items (`c` the bound). -/
def tpuv_bnd (c : ℕ) : List (List SatSym) → Bool
  | [] => true
  | r :: rs => (decide (c < 4 * r.length) && decide (2 * r.length < c)) && tpuv_bnd c rs

/-- What the main loop computes (`k` marks, three per pass). -/
def tpuv_go (c : ℕ) : ℕ → List (List SatSym) → Str → Bool
  | 0, rows, _ => rows.isEmpty
  | 1, _, _ => false
  | 2, _, _ => false
  | k + 3, rows, R => decide (tpuv_s rows R = c) && tpuv_go c k (bpv_U rows R) (bpv_rest rows R)

/-- The answer of the verifier on `(w, y)`. -/
def tpuv_vres (w : List SatSym) (y : Str) : Bool :=
  match (clauses w).reverse with
  | [] => false
  | Bv :: rr => tpuv_bnd Bv.length rr.reverse &&
      tpuv_go Bv.length rr.reverse.length rr.reverse y

theorem tpuv_s_le : ∀ (rows : List (List SatSym)) (R : Str),
    tpuv_s rows R ≤ (rows.map List.length).sum
  | [], _ => by simp [tpuv_s]
  | r :: rs, R => by
    have := tpuv_s_le rs R.tail
    simp only [tpuv_s, List.map_cons, List.sum_cons]
    split_ifs <;> omega

local macro "tpuv_stx" : tactic =>
  `(tactic| (funext j; rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|j <;>
    simp [bpv_st, update_apply]))

theorem tpuv_u5 {R Q C A K B : Str} (A' : Str) :
    update (bpv_st R Q C A K B) 5 A' = bpv_st R Q C A' K B := by tpuv_stx

/-! ## Adding a row in unary -/

/-- Pop one symbol code from stack `3`; at a `sep` stop, otherwise push `true` onto stack `5`. -/
def tpuv_aB : Cmd :=
  .pop 3 .brk (.pop 3 .brk .brk (.push 5 true)) (.pop 3 .brk (.push 5 true) (.push 5 true))

def tpuv_aL : Cmd := .loop tpuv_aB

theorem tpuv_ex_aG : ∀ (r : List SatSym) (σ : ℕ → Str) (Q' A : Str), sep ∉ r →
    σ 3 = r.flatMap ic ++ false :: false :: Q' → σ 5 = A →
    ExecLe tpuv_aL σ (.norm (update (update σ 3 Q') 5 (tpuv_u r.length ++ A)))
      (3 * r.length + 3)
  | [], σ, Q', A, _, h3, h5 => by
    have h3' : σ 3 = false :: false :: Q' := by simpa using h3
    refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := false)
      (s := Q') (by simp) (ExecLe.brk _)))).cast ?_ (by simp)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [tpuv_u]
  | s :: r, σ, Q', A, hr, h3, h5 => by
    have hs' : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ht : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    set rest := r.flatMap ic ++ false :: false :: Q'
    have ih := tpuv_ex_aG r (update (update σ 3 rest) 5 (true :: A)) Q' (true :: A) ht
      (by simp [rest]) (by simp)
    have hb : ExecLe tpuv_aB σ (.norm (update (update σ 3 rest) 5 (true :: A))) 3 := by
      cases s with
      | sep => exact absurd rfl hs'
      | zero =>
        have h' : σ 3 = false :: true :: rest := by simpa [ic, rest] using h3
        refine (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := true) (s := rest)
          (by simp) (ExecLe.push 5 true _))).cast ?_ le_rfl
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all
      | pos =>
        have h' : σ 3 = true :: false :: rest := by simpa [ic, rest] using h3
        refine (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := false) (s := rest)
          (by simp) (ExecLe.push 5 true _))).cast ?_ le_rfl
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all
      | neg =>
        have h' : σ 3 = true :: true :: rest := by simpa [ic, rest] using h3
        refine (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := true) (s := rest)
          (by simp) (ExecLe.push 5 true _))).cast ?_ le_rfl
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1
    rw [tpuv_u_succ]
    funext j; simp only [update_apply]; split_ifs <;> simp_all

theorem tpuv_ex_a {R C K : Str} (Q' : Str) (r : List SatSym) (A B : Str) (hr : sep ∉ r) :
    ExecLe tpuv_aL (bpv_st R (r.flatMap ic ++ false :: false :: Q') C A K B)
      (.norm (bpv_st R Q' C (tpuv_u r.length ++ A) K B)) (3 * r.length + 3) := by
  have h := tpuv_ex_aG r (bpv_st R (r.flatMap ic ++ false :: false :: Q') C A K B) Q' A hr rfl rfl
  rwa [bpv_u3, tpuv_u5] at h

/-! ## Reading the bound -/

/-- Loop body of `tpuv_cL`: pop one (reversed) symbol code; at a `sep` push it back and stop,
otherwise push `true` onto stack `4`. -/
def tpuv_cB : Cmd :=
  .pop 2 .brk (.pop 2 .brk (.seq (.push 2 false) (.seq (.push 2 false) .brk)) (.push 4 true))
    (.pop 2 .brk (.push 4 true) (.push 4 true))

def tpuv_cL : Cmd := .loop tpuv_cB

theorem tpuv_ex_cL (u : List SatSym) (hu : u = [] ∨ ∃ u', u = u' ++ [sep]) :
    ∀ (t : List SatSym) (σ : ℕ → Str) (S : Str), sep ∉ t → σ 2 = rc t ++ (u.flatMap ic).reverse →
    σ 4 = S →
    ExecLe tpuv_cL σ (.norm (update (update σ 2 ((u.flatMap ic).reverse)) 4
      (tpuv_u t.length ++ S))) (4 * t.length + 6)
  | [], σ, S, _, h, h4 => by
    rcases hu with rfl | ⟨u', rfl⟩
    · refine (ExecLe.loop_brk (ExecLe.pop_nil (by simpa [rc] using h) (ExecLe.brk _))).cast ?_
        (by simp)
      congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [rc, tpuv_u]
    · have h' : σ 2 = false :: false :: (u'.flatMap ic).reverse := by
        simpa [rc, List.flatMap_append, ic] using h
      refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := false)
        (s := (u'.flatMap ic).reverse)
        (by simp) ((ExecLe.push 2 false _).seq_norm ((ExecLe.push 2 false _).seq_norm
          (ExecLe.brk _)))))).cast ?_ (by simp)
      congr 1; funext j; simp only [update_apply]
      split_ifs <;> simp_all [List.flatMap_append, ic, tpuv_u]
  | s :: t, σ, S, hs, h, h4 => by
    have hs' : s ≠ sep := fun e => hs (e ▸ List.mem_cons_self ..)
    have ht : sep ∉ t := fun e => hs (List.mem_cons_of_mem _ e)
    set rest := rc t ++ (u.flatMap ic).reverse
    have ih := tpuv_ex_cL u hu t (update (update σ 2 rest) 4 (true :: S)) (true :: S) ht
      (by simp [rest]) (by simp)
    have hb : ExecLe tpuv_cB σ (.norm (update (update σ 2 rest) 4 (true :: S))) 3 := by
      cases s with
      | sep => exact absurd rfl hs'
      | zero =>
        have h' : σ 2 = true :: false :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := false) (s := rest) (by simp)
          (ExecLe.push 4 true _))).cast (by simp [h4]) le_rfl
      | neg =>
        have h' : σ 2 = true :: true :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := true) (s := rest) (by simp)
          (ExecLe.push 4 true _))).cast (by simp [h4]) le_rfl
      | pos =>
        have h' : σ 2 = false :: true :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := true) (s := rest) (by simp)
          (ExecLe.push 4 true _))).cast (by simp [h4]) le_rfl
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1
    rw [tpuv_u_succ]
    funext j; simp only [update_apply]; split_ifs <;> simp_all

/-- Pop the `sep` of the bound row (halt `false` if there is none), then read it. -/
def tpuv_c0 : Cmd :=
  .pop 2 (.halt false) (.pop 2 (.halt false) tpuv_cL (.halt false)) (.halt false)

/-! ## The bound check of one item -/

def tpuv_chk : Cmd :=
  .seq (copyVia 4 13 15) (.seq (copyVia 5 16 15) (.seq (copyVia 5 16 15) (.seq (copyVia 5 16 15)
    (.seq (copyVia 5 16 15)
    (tpv_test 16 13 (.seq (copyVia 4 13 15) (.seq (copyVia 5 16 15) (.seq (move 16 5)
      (tpv_test 13 5 (.push 10 true) (.halt false))))) (.halt false))))))

/-- The main-phase stacks with the temporaries `13`, `16`. -/
def tpuv_S (R Q C A K B X Y : Str) : ℕ → Str := update (update (bpv_st R Q C A K B) 13 X) 16 Y

theorem tpuv_ex_chk (R Q K B : Str) (c a : ℕ) :
    ExecLe tpuv_chk (bpv_st R Q (tpuv_u c) (tpuv_u a) K B)
      (if decide (c < 4 * a) && decide (2 * a < c) then
        .norm (bpv_st R Q (tpuv_u c) [] (true :: K) B) else .halt false)
      (60 * (a + c) + 60) := by
  have hS0 : ∀ A, tpuv_S R Q (tpuv_u c) A K B [] [] = bpv_st R Q (tpuv_u c) A K B := by
    intro A; unfold tpuv_S; tpuv_stx
  have c13 : ∀ A X Y, ExecLe (copyVia 4 13 15) (tpuv_S R Q (tpuv_u c) A K B X Y)
      (.norm (tpuv_S R Q (tpuv_u c) A K B (tpuv_u c ++ X) Y)) (5 * c + 4) := by
    intro A X Y
    refine (ExecLe.of (exec_copyVia (a := 4) (b := 13) (t := 15) (by decide) (by decide)
      (by decide) _ (by simp [tpuv_S, bpv_st]))).cast ?_
      (by simp [tpuv_S, bpv_st, tpuv_u_length])
    congr 1; unfold tpuv_S; tpuv_stx
  have c16 : ∀ X m, ExecLe (copyVia 5 16 15) (tpuv_S R Q (tpuv_u c) (tpuv_u a) K B X (tpuv_u m))
      (.norm (tpuv_S R Q (tpuv_u c) (tpuv_u a) K B X (tpuv_u (a + m)))) (5 * a + 4) := by
    intro X m
    refine (ExecLe.of (exec_copyVia (a := 5) (b := 16) (t := 15) (by decide) (by decide)
      (by decide) _ (by simp [tpuv_S, bpv_st]))).cast ?_
      (by simp [tpuv_S, bpv_st, tpuv_u_length])
    congr 1; rw [← tpuv_u_add]; unfold tpuv_S; tpuv_stx
  have mv : ∀ A X Y, ExecLe (move 16 5) (tpuv_S R Q (tpuv_u c) A K B X Y)
      (.norm (tpuv_S R Q (tpuv_u c) (Y.reverse ++ A) K B X [])) (2 * Y.length + 2) := by
    intro A X Y
    refine (ExecLe.of (exec_move (a := 16) (b := 5) (by decide) Y _
      (by simp [tpuv_S]))).cast ?_ le_rfl
    congr 1; unfold tpuv_S; tpuv_stx
  have r1 : ∀ A X Y, update (update (tpuv_S R Q (tpuv_u c) A K B X Y) 16 []) 13 [] =
      bpv_st R Q (tpuv_u c) A K B := by
    intro A X Y; unfold tpuv_S; tpuv_stx
  have r2 : ∀ A X, update (update (tpuv_S R Q (tpuv_u c) A K B X []) 13 []) 5 [] =
      bpv_st R Q (tpuv_u c) [] K B := by
    intro A X; unfold tpuv_S; tpuv_stx
  have hP10 : ExecLe (.push 10 true) (bpv_st R Q (tpuv_u c) [] K B)
      (.norm (bpv_st R Q (tpuv_u c) [] (true :: K) B)) 1 :=
    (ExecLe.push 10 true _).cast (by rw [bpv_u10]; rfl) le_rfl
  have e2 : (tpuv_u (a + 0)).reverse ++ tpuv_u a = tpuv_u (2 * a) := by
    rw [tpuv_u_rev, tpuv_u_add]; congr 1; omega
  have hcn : ExecLe (.seq (copyVia 4 13 15) (.seq (copyVia 5 16 15) (.seq (move 16 5)
      (tpv_test 13 5 (.push 10 true) (.halt false))))) (bpv_st R Q (tpuv_u c) (tpuv_u a) K B)
      (if decide (c ≤ 2 * a) then .halt false else .norm (bpv_st R Q (tpuv_u c) [] (true :: K) B))
      (5 * c + 4 + (5 * a + 4 + (2 * a + 2 + (5 * (c + 2 * a) + 1 + 5)))) := by
    rw [← hS0]
    have m := mv (tpuv_u a) (tpuv_u c ++ []) (tpuv_u (a + 0))
    rw [e2] at m
    have t2 := tpv_ex_test (a := 13) (b := 5) (cn := .push 10 true) (ct := .halt false)
      (X := tpuv_u c ++ []) (Y := tpuv_u (2 * a)) (by decide) (by decide) (by decide)
      (σ := tpuv_S R Q (tpuv_u c) (tpuv_u (2 * a)) K B (tpuv_u c ++ []) [])
      (by simp [tpuv_S]) (by simp [tpuv_S, bpv_st]) (by simp [tpuv_S, bpv_st])
      (r := if decide (c ≤ 2 * a) then .halt false
        else .norm (bpv_st R Q (tpuv_u c) [] (true :: K) B)) (T := 1) (by
        rw [r2, List.append_nil, tpuv_le_u]
        by_cases h : c ≤ 2 * a
        · simp only [h, decide_true, if_true]; exact ExecLe.halt false _
        · simp only [h, decide_false, if_false, Bool.false_eq_true]; exact hP10)
    refine ((c13 _ _ _).seq_norm ((c16 _ 0).seq_norm (m.seq_norm t2))).cast rfl ?_
    simp only [tpuv_u_length, List.length_append, List.length_nil]
    omega
  have t1 := tpv_ex_test (a := 16) (b := 13) (ct := .halt false)
    (cn := .seq (copyVia 4 13 15) (.seq (copyVia 5 16 15) (.seq (move 16 5)
      (tpv_test 13 5 (.push 10 true) (.halt false)))))
    (X := tpuv_u (a + (a + (a + (a + 0))))) (Y := tpuv_u c ++ []) (by decide) (by decide)
    (by decide)
    (σ := tpuv_S R Q (tpuv_u c) (tpuv_u a) K B (tpuv_u c ++ []) (tpuv_u (a + (a + (a + (a + 0))))))
    (by simp [tpuv_S]) (by simp [tpuv_S]) (by simp [tpuv_S, bpv_st])
    (r := if decide (c < 4 * a) && decide (2 * a < c) then
        .norm (bpv_st R Q (tpuv_u c) [] (true :: K) B) else .halt false)
    (T := 5 * c + 4 + (5 * a + 4 + (2 * a + 2 + (5 * (c + 2 * a) + 1 + 5)))) (by
      rw [r1, List.append_nil, tpuv_le_u]
      by_cases h1 : a + (a + (a + (a + 0))) ≤ c
      · have : ¬ c < 4 * a := by omega
        simp only [h1, decide_true, if_true, this, decide_false, Bool.false_and,
          Bool.false_eq_true, if_false]
        exact (ExecLe.halt false _).cast rfl (by omega)
      · have : c < 4 * a := by omega
        simp only [h1, decide_false, Bool.false_eq_true, if_false, this, decide_true,
          Bool.true_and]
        refine hcn.cast ?_ le_rfl
        by_cases h2 : c ≤ 2 * a
        · have : ¬ 2 * a < c := by omega
          simp [h2, this]
        · have : 2 * a < c := by omega
          simp [h2, this])
  rw [← hS0]
  refine ((c13 _ _ _).seq_norm ((c16 _ 0).seq_norm ((c16 _ _).seq_norm ((c16 _ _).seq_norm
    ((c16 _ _).seq_norm t1))))).cast rfl ?_
  simp only [tpuv_u_length, List.length_append, List.length_nil]
  omega

/-! ## The bounds loop -/

def tpuv_bB : Cmd := bpv_peek (.seq tpuv_aL tpuv_chk)

def tpuv_bL : Cmd := .loop tpuv_bB

/-- Cost of the bounds loop. -/
def tpuv_Tb (N : ℕ) (rows : List (List SatSym)) : ℕ := (rows.length + 1) * (130 * N + 130)

theorem tpuv_ex_bL {R : Str} {c : ℕ} (N : ℕ) (hc : c ≤ N) : ∀ (rows : List (List SatSym))
    (K B : Str), (∀ r ∈ rows, sep ∉ r) → (rows.map List.length).sum + rows.length ≤ N →
    ExecLe tpuv_bL (bpv_st R (enc rows) (tpuv_u c) [] K B)
      (if tpuv_bnd c rows then
        .norm (bpv_st R [] (tpuv_u c) [] (List.replicate rows.length true ++ K) B)
        else .halt false) (tpuv_Tb N rows)
  | [], K, B, _, _ =>
    (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [tpuv_bnd, enc]) (by simp [tpuv_Tb])
  | r :: rows, K, B, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hN
    obtain ⟨x, Q', hQ⟩ := kv_enc_ne r rows
    have hT : tpuv_Tb N (r :: rows) = (130 * N + 130) + tpuv_Tb N rows := by
      simp [tpuv_Tb]; ring
    rw [hT]
    rw [enc_cons] at hQ ⊢
    have ha := tpuv_ex_a (R := R) (C := tpuv_u c) (K := K) (enc rows) r [] B hr
    rw [List.append_nil] at ha
    have hc' := tpuv_ex_chk R (enc rows) K B c r.length
    have hb := bpv_ex_peek hQ (ha.seq_norm hc')
    cases hok : (decide (c < 4 * r.length) && decide (2 * r.length < c))
    · rw [hok] at hb
      exact (ExecLe.loop_halt hb).cast (by simp [tpuv_bnd, hok])
        (by omega)
    · rw [hok] at hb
      have ih := tpuv_ex_bL (R := R) N hc rows (true :: K) B hrs (by omega)
      refine (ExecLe.loop_norm (hb.cast rfl le_rfl) ih).cast ?_ ?_
      · simp [tpuv_bnd, hok, List.replicate_succ']
      · omega

/-! ## A pass -/

def tpuv_iB : Cmd := bpv_peek (.pop 0 bpv_cpL bpv_cpL tpuv_aL)

def tpuv_iL : Cmd := .loop tpuv_iB

theorem tpuv_ex_iL {C K : Str} (N : ℕ) : ∀ (rows : List (List SatSym)) (R : Str) (a : ℕ)
    (B : Str), (∀ r ∈ rows, sep ∉ r) → (rows.map List.length).sum + rows.length ≤ N →
    ExecLe tpuv_iL (bpv_st R (enc rows) C (tpuv_u a) K B)
      (.norm (bpv_st (bpv_rest rows R) [] C (tpuv_u (tpuv_s rows R + a)) K
        ((enc (bpv_U rows R)).reverse ++ B))) (bpv_Ti N rows)
  | [], R, a, B, _, _ =>
    (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [bpv_rest, tpuv_s, bpv_U, enc]) (by simp [bpv_Ti])
  | r :: rows, R, a, B, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hN
    obtain ⟨x, Q', hQ⟩ := kv_enc_ne r rows
    have hT : bpv_Ti N (r :: rows) = (16 * N + 30) + bpv_Ti N rows := by
      simp [bpv_Ti]; ring
    rw [hT]
    rw [enc_cons] at hQ ⊢
    rcases R with _ | ⟨_ | _, R'⟩
    · have ih := tpuv_ex_iL (C := C) (K := K) N rows [] a ((r.flatMap ic ++ [false, false]).reverse ++ B) hrs
        (by omega)
      have hb := ExecLe.pop_nil (k := 0) (cn := bpv_cpL) (cf := bpv_cpL) (ct := tpuv_aL) rfl
        (bpv_ex_cp (R := []) (C := C) (K := K) (enc rows) r (tpuv_u a) B hr)
      refine (ExecLe.loop_norm (bpv_ex_peek hQ hb) ih).cast ?_ (by omega)
      simp [bpv_rest, tpuv_s, bpv_U, enc_cons]
    · have ih := tpuv_ex_iL (C := C) (K := K) N rows R' a ((r.flatMap ic ++ [false, false]).reverse ++ B) hrs
        (by omega)
      have hb := ExecLe.pop_cons (k := 0) (cn := bpv_cpL) (cf := bpv_cpL) (ct := tpuv_aL)
        (b := false) (s := R')
        (σ := bpv_st (false :: R') (r.flatMap ic ++ false :: false :: enc rows) C (tpuv_u a) K B)
        rfl (by rw [bpv_u0]; exact bpv_ex_cp (enc rows) r (tpuv_u a) B hr)
      refine (ExecLe.loop_norm (bpv_ex_peek hQ hb) ih).cast ?_ (by omega)
      simp [bpv_rest, tpuv_s, bpv_U, enc_cons]
    · have ih := tpuv_ex_iL (C := C) (K := K) N rows R' (r.length + a) B hrs (by omega)
      have hb := ExecLe.pop_cons (k := 0) (cn := bpv_cpL) (cf := bpv_cpL) (ct := tpuv_aL)
        (b := true) (s := R')
        (σ := bpv_st (true :: R') (r.flatMap ic ++ false :: false :: enc rows) C (tpuv_u a) K B)
        rfl (by rw [bpv_u0, if_pos rfl]; exact tpuv_ex_a (enc rows) r _ B hr)
      rw [tpuv_u_add] at hb
      refine (ExecLe.loop_norm (bpv_ex_peek hQ hb) ih).cast ?_ (by omega)
      · simp only [bpv_rest, tpuv_s, bpv_U, List.headD_cons, if_true, List.tail_cons]
        congr 3; omega

/-! ## The main loop -/

def tpuv_pass : Cmd := .seq tpuv_iL tpv_fin

def tpuv_oB : Cmd :=
  .pop 10 (.pop 3 (.halt true) (.halt false) (.halt false)) (.halt false)
    (.pop 10 (.halt false) (.halt false) (.pop 10 (.halt false) (.halt false) tpuv_pass))

def tpuv_oL : Cmd := .loop tpuv_oB

theorem tpuv_eq_u (a c : ℕ) :
    (kv_leF true (tpuv_u a) (tpuv_u c) && kv_leF true (tpuv_u c) (tpuv_u a)) =
      decide (a = c) := by
  rw [tpuv_le_u, tpuv_le_u]
  by_cases h : a = c
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h' | h' <;> simp [h, Nat.not_le.2 h', le_of_lt h']

theorem tpuv_ex_oL {c : ℕ} (N : ℕ) (hc : c ≤ N) : ∀ (k : ℕ)
    (rows : List (List SatSym)) (R : Str), (∀ r ∈ rows, sep ∉ r) →
    (rows.map List.length).sum + rows.length ≤ N →
    ExecLe tpuv_oL (bpv_st R (enc rows) (tpuv_u c) [] (List.replicate k true) [])
      (.halt (tpuv_go c k rows R)) (tpv_To N k)
  | 0, rows, R, _, _ => by
    have h : ExecLe (Cmd.pop 3 (.halt true) (.halt false) (.halt false))
        (bpv_st R (enc rows) (tpuv_u c) [] (List.replicate 0 true) [])
        (.halt (tpuv_go c 0 rows R)) 2 := by
      rcases rows with _ | ⟨r, rows⟩
      · exact (ExecLe.pop_nil rfl (ExecLe.halt true _)).cast (by simp [tpuv_go]) (by omega)
      · obtain ⟨x, Q', hQ⟩ := kv_enc_ne r rows
        refine (ExecLe.pop_cons (r := .halt false) (T := 1) (b := x) (s := Q') hQ ?_).cast
          (by simp [tpuv_go]) (by omega)
        cases x <;> exact ExecLe.halt false _
    exact (ExecLe.loop_halt (ExecLe.pop_nil rfl h)).cast rfl (by unfold tpv_To; nlinarith)
  | 1, rows, R, _, _ => by
    refine (ExecLe.loop_halt (ExecLe.pop_cons (r := .halt false) (b := true) (s := []) rfl ?_)).cast
      (by simp [tpuv_go]) (show 3 ≤ tpv_To N 1 by unfold tpv_To; nlinarith)
    rw [bpv_u10, if_pos rfl]
    exact (ExecLe.pop_nil rfl (ExecLe.halt false _))
  | 2, rows, R, _, _ => by
    refine (ExecLe.loop_halt (ExecLe.pop_cons (r := .halt false) (b := true) (s := [true]) rfl
      ?_)).cast (by simp [tpuv_go]) (show 4 ≤ tpv_To N 2 by unfold tpv_To; nlinarith)
    rw [bpv_u10, if_pos rfl]
    refine ExecLe.pop_cons (b := true) (s := []) rfl ?_
    rw [bpv_u10, if_pos rfl]
    exact (ExecLe.pop_nil rfl (ExecLe.halt false _))
  | k + 3, rows, R, hrows, hN => by
    have hT : tpv_To N (k + 3) =
        ((N + 1) * (16 * N + 30) + 50 * N + 50) + (2 * ((N + 1) * (16 * N + 30) + 50 * N + 50)
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
    have hP : ExecLe tpuv_oB (bpv_st R (enc rows) (tpuv_u c) [] (List.replicate (k + 3) true) [])
        (if decide (tpuv_s rows R + 0 = c) then
          .norm (bpv_st (bpv_rest rows R) (enc (bpv_U rows R)) (tpuv_u c) []
            (List.replicate k true) [])
          else .halt false)
        ((N + 1) * (16 * N + 30) + 50 * N + 50) := by
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
      exact (ExecLe.loop_halt hP).cast (by simp_all [tpuv_go]) (by omega)
    · rw [hr] at hP
      have ih := tpuv_ex_oL N hc k (bpv_U rows R) (bpv_rest rows R) (bpv_U_sep rows R hrows)
        (by omega)
      exact (ExecLe.loop_norm hP ih).cast (by simp_all [tpuv_go]) (by omega)

/-! ## The whole verifier -/

def tpuv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq tpuv_c0 (.seq (move 2 3) (.seq (copyVia 3 12 15)
    (.seq tpuv_bL (.seq (move 12 13) (.seq (move 13 3) tpuv_oL)))))))

/-- Time bound of the verifier. -/
def tpuv_Tver (n : ℕ) : ℕ := 40 * n + 40 + (n + 1) * (130 * n + 130) + tpv_To n n

theorem tpuv_exec_ver (z : Str) :
    ExecLe tpuv_ver (init [z]).stk (.halt (tpuv_vres (dec z).1 (dec z).2))
      (tpuv_Tver z.length) := by
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
  unfold tpuv_vres tpuv_ver
  rcases hcw : (clauses w).reverse with _ | ⟨Bv, rr⟩
  · have h2 : σ₂ 2 = [] := by
      simp only [σ₂, update_self, trunc]
      rw [List.reverse_eq_nil_iff.1 hcw]; rfl
    refine (hpre _ _ _ (ExecLe.seq_halt (ExecLe.pop_nil h2 (ExecLe.halt false _)))).cast rfl ?_
    unfold tpuv_Tver; omega
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
        bpv_st y (enc items) C [] [] (enc items) := by tpuv_stx
    rw [hσ2] at hCp
    have hsum := sum_length_le items
    have l3 : (bpv_st y (enc items) C [] [] [] 3).length = (enc items).length := rfl
    have hug : (items.flatMap (· ++ [sep])).length = u.length := rfl
    have hul : u.length + Bv.length + 1 = (trunc w).length := by simp [htr]; omega
    have hCl : Bv.length ≤ z.length := by omega
    have hsep : ∀ r ∈ items, sep ∉ r := fun r hr =>
      sep_not_mem_clauses w r (by rw [hcl]; exact List.mem_append_left _ hr)
    have hB := tpuv_ex_bL (R := y) z.length hCl items [] (enc items) hsep (by omega)
    have hc : (u.flatMap ic).length = 2 * u.length := length_flatMap_ic u
    have h52 : σ₅ 2 = (u.flatMap ic).reverse := by simp [σ₅]
    have hEl : (enc items).length = 2 * u.length := by
      rw [bpv_enc_length]; omega
    have hTb : tpuv_Tb z.length items ≤ (z.length + 1) * (130 * z.length + 130) :=
      Nat.mul_le_mul_right _ (by omega)
    cases hb : tpuv_bnd Bv.length items
    · rw [hb] at hB
      refine (hpre _ _ _ (hC0.seq_norm ((ExecLe.of hM).seq_norm (hCp.seq_norm
        (ExecLe.seq_halt hB))))).cast
        (by have hb' : tpuv_bnd Bv.length rr.reverse = false := hb; simp [hb']) ?_
      simp only [h52, List.length_reverse, hc, tpuv_Tver, List.length_reverse] at *
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
          bpv_st y (enc items) C [] (List.replicate items.length true) [] := by tpuv_stx
      rw [hσ3] at hM2
      have hR := tpuv_ex_oL (c := Bv.length) z.length hCl items.length items y hsep (by omega)
      refine (hpre _ _ _ (hC0.seq_norm ((ExecLe.of hM).seq_norm (hCp.seq_norm
        (hB.seq_norm ((ExecLe.of hM1).seq_norm ((ExecLe.of hM2).seq_norm hR))))))).cast
        (by have hb' : tpuv_bnd Bv.length rr.reverse = true := hb; simp [hb', items]) ?_
      have hk : tpv_To z.length items.length ≤ tpv_To z.length z.length :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [h52, List.length_reverse, hc, tpuv_Tver, List.length_reverse, hEl] at *
      omega

theorem tpuv_Tver_le (n : ℕ) : tpuv_Tver n ≤ tb 8 n := by
  unfold tpuv_Tver tpv_To tb
  have h4 : 2 ^ 4 ≤ (n + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have e : (n + 2) ^ 8 = (n + 2) ^ 4 * (n + 2) ^ 4 := by ring
  have e4 : (n + 2) ^ 4 = (n + 2) * (n + 2) * (n + 2) * (n + 2) := by ring
  have h1 : 40 * n + 40 + (n + 1) * (130 * n + 130) + (n + 1) * ((n + 1) * (16 * n + 30) +
      50 * n + 50) ≤ (n + 2) ^ 4 * 16 := by
    rw [e4]; nlinarith [Nat.zero_le (n * n * n * n), Nat.zero_le (n * n * n), Nat.zero_le (n * n)]
  rw [e]
  exact h1.trans (Nat.mul_le_mul_left _ (by simpa using h4))

end Pnp.Karp.ThreePartU
