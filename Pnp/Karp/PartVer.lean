import Pnp.Karp.Partition

/-!
# PARTITION ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/Partition.lean`) and a certificate `y : List Bool` (bit `i` says whether row `i`
is in the first part; missing bits are `false`).  It reuses the SUBSET SUM verifier's
commands (`Pnp/Karp/SubVer.lean`) and its stack layout `sv_st R Q B A S c`:

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the accumulator `B` of the unselected rows;  `5`: the accumulator `A` of the selected
  rows;  `6`, `7`: sum bits and carry of the ripple-carry addition;  `8`, `9`: temporaries.

Program (`pv_ver`):
1. `phaseA`: parse the code of `w`; `trimC 2`: drop the unfinished tail; `move 2 3`;
2. `pv_mainLoop`: per row, pop a certificate bit; if it is set, add the row to `A`
   (`sv_addLoop`), otherwise swap the accumulators (`pv_swap`, four moves through `8`, `9`),
   add the row to `B` and swap back; at the end of the input compare `A` with `B`
   (`sv_eqLoop`).

`pv_exec_ver`: the program halts with `pv_vres (dec z).1 (dec z).2` on every input `z`,
within `pv_Tver |z| ≤ tb 6 |z|` steps.
-/

namespace Pnp.Karp.Partition

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

/-! ## Semantics -/

/-- What the main loop computes (`R`: unread certificate bits, `A`, `B`: the accumulators of
the selected and unselected rows). -/
def pv_go : List (List SatSym) → Str → Str → Str → Bool
  | [], _, A, B => sv_eqB A B
  | r :: rows, R, A, B =>
    if R.headD false then pv_go rows R.tail (sv_addL false A (sv_bits r)) B
    else pv_go rows R.tail A (sv_addL false B (sv_bits r))

/-- The answer of the verifier on `(w, y)`. -/
def pv_vres (w : List SatSym) (y : Str) : Bool := pv_go (clauses w) y [] []

/-! ## Swapping the accumulators -/

/-- Swap stacks `4` and `5` through the empty stacks `8` and `9`. -/
def pv_swap : Cmd := .seq (move 4 8) (.seq (move 5 9) (.seq (move 8 5) (move 9 4)))

theorem pv_ex_swap (R Q X Y : Str) :
    ExecLe pv_swap (sv_st R Q X Y [] false) (.norm (sv_st R Q Y X [] false))
      (4 * (X.length + Y.length) + 8) := by
  have h1 := exec_move (a := 4) (b := 8) (by decide) X (sv_st R Q X Y [] false) rfl
  have h2 := exec_move (a := 5) (b := 9) (by decide) Y (update (update (sv_st R Q X Y [] false) 4 []) 8 (X.reverse ++ sv_st R Q X Y [] false 8)) (by simp)
  have h3 := exec_move (a := 8) (b := 5) (by decide) X.reverse (update (update (update (update (sv_st R Q X Y [] false) 4 []) 8 (X.reverse ++ sv_st R Q X Y [] false 8)) 5 []) 9 (Y.reverse ++ (update (update (sv_st R Q X Y [] false) 4 []) 8 (X.reverse ++ sv_st R Q X Y [] false 8)) 9)) (by simp [sv_st])
  refine ((ExecLe.of h1).seq_norm ((ExecLe.of h2).seq_norm ((ExecLe.of h3).seq_norm
    (ExecLe.of (exec_move (a := 9) (b := 4) (by decide) Y.reverse _ (by simp [sv_st])))))).cast ?_ (by simp; omega)
  congr 1; funext j
  rcases j with _|_|_|_|_|_|_|_|_|_|j <;> simp [sv_st]

/-! ## The main loop -/

/-- Add the row to the accumulator `B` (stack `4`). -/
def pv_unsel : Cmd := .seq pv_swap (.seq sv_addLoop pv_swap)

def pv_mainB : Cmd := .pop 0 pv_unsel pv_unsel sv_addLoop

def pv_mainLoop : Cmd := .loop pv_mainB

theorem pv_eqB_comm (A B : Str) : sv_eqB B A = sv_eqB A B := by
  rw [Bool.eq_iff_iff, sv_eqB_iff, sv_eqB_iff]; omega

section Rows
variable {R : Str}

theorem pv_ex_unselRow (N : ℕ) (Q' : Str) (r : List SatSym) (A B : Str) (hr : sep ∉ r)
    (hN : A.length + B.length + r.length + 1 ≤ N) :
    ExecLe pv_unsel (sv_st R (r.flatMap ic ++ false :: false :: Q') B A [] false)
      (.norm (sv_st R Q' (sv_addL false B (sv_bits r)) A [] false))
      (7 * r.length + 16 * N + 36) := by
  have hl := sv_addL_length false B (sv_bits r)
  simp only [sv_bits, List.length_map] at hl
  have h1 := pv_ex_swap (R := R) (Q := r.flatMap ic ++ false :: false :: Q') B A
  have h2 := sv_ex_addRow (R := R) (T := A) N Q' r B [] false hr (by simp; omega)
  have h3 := pv_ex_swap (R := R) (Q := Q') A (sv_addL false B (sv_bits r))
  simp only [List.reverse_nil, List.nil_append] at h2
  refine (h1.seq_norm (h2.seq_norm h3)).cast rfl ?_
  simp only [sv_bits] at h3 ⊢
  omega

theorem pv_ex_end (A B : Str) :
    ExecLe pv_mainB (sv_st R [] B A [] false) (.halt (sv_eqB A B))
      (4 * (A.length + B.length) + 3 * (A.length + B.length) + 14) := by
  rcases R with _ | ⟨_ | _, R'⟩
  · refine (ExecLe.pop_nil rfl (ExecLe.seq_norm (pv_ex_swap _ _ B A)
      (ExecLe.seq_halt (sv_ex_addEnd (R := []) B [] false)))).cast
      (by rw [pv_eqB_comm]) (by omega)
  · refine (ExecLe.pop_cons (b := false) (s := R') rfl (by
      rw [sv_u0]
      exact ExecLe.seq_norm (pv_ex_swap _ _ B A)
        (ExecLe.seq_halt (sv_ex_addEnd (R := R') B [] false)))).cast
      (by rw [pv_eqB_comm]) (by omega)
  · refine (ExecLe.pop_cons (b := true) (s := R') rfl (by
      rw [sv_u0]
      exact sv_ex_addEnd (R := R') A [] false)).cast rfl (by omega)

/-- Cost of the main phase. -/
def pv_Trows (N : ℕ) (rows : List (List SatSym)) : ℕ := (rows.length + 1) * (23 * N + 40)

theorem pv_ex_rows (N : ℕ) : ∀ (rows : List (List SatSym)) (R A B : Str),
    (∀ r ∈ rows, sep ∉ r) →
    A.length + B.length + (rows.map List.length).sum + rows.length ≤ N →
    ExecLe pv_mainLoop (sv_st R (enc rows) B A [] false) (.halt (pv_go rows R A B))
      (pv_Trows N rows)
  | [], R, A, B, _, hN => by
    simp only [List.map_nil, List.sum_nil, List.length_nil] at hN
    exact (ExecLe.loop_halt (pv_ex_end (R := R) A B)).cast (by simp [pv_go])
      (by simp [pv_Trows]; omega)
  | r :: rows, R, A, B, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hN
    rw [enc_cons]
    have hl := sv_addL_length false B (sv_bits r)
    have hl' := sv_addL_length false A (sv_bits r)
    simp only [sv_bits, List.length_map] at hl hl'
    have hT : pv_Trows N (r :: rows) = (23 * N + 40) + pv_Trows N rows := by
      simp [pv_Trows]; ring
    rw [hT]
    rcases R with _ | ⟨_ | _, R'⟩
    · have ih := pv_ex_rows N rows [] A (sv_addL false B (sv_bits r)) hrs
        (by simp only [sv_bits] at *; omega)
      have hb := ExecLe.pop_nil (cf := pv_unsel) (ct := sv_addLoop) (k := 0) rfl
        (pv_ex_unselRow (R := []) N (enc rows) r A B hr (by omega))
      exact (ExecLe.loop_norm hb ih).cast (by simp [pv_go]) (by omega)
    · have ih := pv_ex_rows N rows R' A (sv_addL false B (sv_bits r)) hrs
        (by simp only [sv_bits] at *; omega)
      have hb := ExecLe.pop_cons (cn := pv_unsel) (cf := pv_unsel) (ct := sv_addLoop) (k := 0)
        (b := false) (s := R')
        (σ := sv_st (false :: R') (r.flatMap ic ++ false :: false :: enc rows) B A [] false) rfl
        (by rw [sv_u0]; exact pv_ex_unselRow N (enc rows) r A B hr (by omega))
      exact (ExecLe.loop_norm hb ih).cast (by simp [pv_go]) (by omega)
    · have ih := pv_ex_rows N rows R' (sv_addL false A (sv_bits r)) B hrs
        (by simp only [sv_bits] at *; omega)
      have hb : ExecLe pv_mainB
          (sv_st (true :: R') (r.flatMap ic ++ false :: false :: enc rows) B A [] false)
          (.norm (sv_st R' (enc rows) B (sv_addL false A (sv_bits r)) [] false))
          (7 * r.length + 8 * N + 21) :=
        ExecLe.pop_cons (b := true) (s := R') rfl (by
          rw [sv_u0]
          exact (sv_ex_addRow N (enc rows) r A [] false hr (by simp; omega)).cast
            (by simp) le_rfl)
      exact (ExecLe.loop_norm hb ih).cast (by simp [pv_go]) (by omega)

end Rows

/-! ## The whole verifier -/

def pv_ver : Cmd := .seq phaseA (.seq (trimC 2) (.seq (move 2 3) pv_mainLoop))

/-- Time bound of the verifier. -/
def pv_Tver (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (n + 1) * (23 * n + 40)

theorem pv_exec_ver (z : Str) :
    ExecLe pv_ver (init [z]).stk (.halt (pv_vres (dec z).1 (dec z).2)) (pv_Tver z.length) := by
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
  have hM := exec_move (a := 2) (b := 3) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 2 []) 3 ((σ₂ 2).reverse ++ σ₂ 3) =
      sv_st y (enc (clauses w)) [] [] [] false := by
    funext j
    simp only [σ₂, σ₁, sv_st, update_apply, enc, trunc, CookLevin.fl]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  have hR := pv_ex_rows z.length (clauses w) y [] [] (sep_not_mem_clauses w) (by simp; omega)
  have hc : (clauses w).length ≤ z.length := by omega
  refine (hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm hR))).cast rfl ?_
  simp only [htl, pv_Tver, pv_Trows]
  have : ((clauses w).length + 1) * (23 * z.length + 40) ≤ (z.length + 1) * (23 * z.length + 40) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem pv_Tver_le (n : ℕ) : pv_Tver n ≤ tb 6 n := by
  unfold pv_Tver tb
  have hm : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  norm_num at hm
  have e : (n + 2) ^ 6 = (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by ring
  have : 16 * (n + 2) ^ 2 ≤ (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by nlinarith
  nlinarith

end Pnp.Karp.Partition
