import Pnp.Karp.FeedbackArc
import Pnp.Karp.FeedbackVSVer

/-!
# FEEDBACK ARC SET ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/FeedbackArc.lean`, rows `kr :: rows`) and a certificate `y : List Bool`, read as a
sequence of unary *blocks* `true^ρ ++ [false]`, one per vertex (`ρ`: the rank of the vertex).
The block of vertex `v` starts at `fav_nx^[v] y`.  Every row must have a (nonempty) block, and
every `pos` entry `(i, j)` with `i ≠ j` whose column block is present and whose column rank is
not larger than the row rank consumes one unit of the budget `|kr|`.

The program reuses the stack layout `fvv_st` and most pieces of the FEEDBACK VERTEX SET
verifier (`Pnp/Karp/FeedbackVSVer.lean`); only the rank comparison (`fav_cL`: a failed
comparison pops the budget instead of rejecting), the column check and the row loop change.

`fav_exec_ver`: the program halts with `fav_vres (dec z).1 (dec z).2` on every input `z`,
within `fvv_Tver |z|` steps.
-/

namespace Pnp.Karp.FeedbackArc

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.HittingSet Pnp.Karp.DomSet Pnp.Karp.FeedbackVS

/-! ## Semantics -/

/-- Skip one block. -/
def fav_nx (Y : Str) : Str := (fvv_units Y).2

/-- The rank of the block on top. -/
def fav_rk (Y : Str) : ℕ := (fvv_units Y).1

/-- A counted entry: `pos`, not diagonal, the column block present, rank not larger. -/
def fav_bad (a : ℕ) (s : SatSym) (Y D : Str) : Bool :=
  decide (s = pos ∧ D.head? ≠ some false ∧ Y ≠ [] ∧ ¬ a < fav_rk Y)

/-- The number of counted entries of a row of rank `a`. -/
def fav_cnt (a : ℕ) : List SatSym → Str → Str → ℕ
  | [], _, _ => 0
  | s :: r, Y, D => (if fav_bad a s Y D then 1 else 0) + fav_cnt a r (fav_nx Y) D.tail

/-- What the row loop computes (`R`: the block of row `i`, `c`: the remaining budget). -/
def fav_go (y : Str) : List (List SatSym) → Str → ℕ → ℕ → Bool
  | [], _, _, _ => true
  | r :: rows, R, c, i =>
    decide (R ≠ [] ∧ fav_cnt (fav_rk R) r y (List.replicate i true ++ [false]) ≤ c) &&
      fav_go y rows (fav_nx R) (c - fav_cnt (fav_rk R) r y (List.replicate i true ++ [false]))
        (i + 1)

/-- The answer of the verifier on `(w, y)`. -/
def fav_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | kr :: rows => fav_go y rows y kr.length 0

theorem fav_nx_length (Y : Str) : (fav_nx Y).length ≤ Y.length := by
  have := fvv_units_length Y; unfold fav_nx; omega

theorem fav_rk_le (Y : Str) : fav_rk Y ≤ Y.length := by
  have := fvv_units_length Y; unfold fav_rk; omega

theorem fav_nx_iter_length : ∀ (k : ℕ) (Y : Str), (fav_nx^[k] Y).length ≤ Y.length
  | 0, _ => le_rfl
  | k + 1, Y => by
    rw [iterate_succ_apply]
    exact (fav_nx_iter_length k _).trans (fav_nx_length Y)

/-! ## Comparing ranks -/

def fav_cB : Cmd :=
  .pop 7 (.seq fvv_bud .brk) (.seq fvv_bud .brk)
    (.pop 4 (.seq fvv_su .brk) (.push 5 true) (.push 5 true))

def fav_cL : Cmd := .loop fav_cB

theorem fav_ex_bb (R y Q K T Y I D : Str) (c : ℕ) :
    ExecLe (.seq fvv_bud .brk) (fvv_st R y Q K T Y I D (List.replicate c true))
      (if 0 < c then .brk (fvv_st R y Q K T Y I D (List.replicate (c - 1) true))
        else .halt false) 4 := by
  rcases c with _ | c
  · exact (ExecLe.seq_halt (ExecLe.pop_nil rfl (ExecLe.halt false _))).cast (by simp)
      (by omega)
  · have hb : ExecLe fvv_bud (fvv_st R y Q K T Y I D (List.replicate (c + 1) true))
        (.norm (fvv_st R y Q K T Y I D (List.replicate c true))) 2 :=
      ExecLe.pop_cons (b := true) (s := List.replicate c true) (by simp [List.replicate_succ])
        (by rw [fvv_u6]; exact ExecLe.skip _)
    exact (hb.seq_norm (ExecLe.brk _)).cast (by simp) (by omega)

theorem fav_ex_cL (R y Q I D : Str) : ∀ (Y : Str) (a b c : ℕ),
    ExecLe fav_cL
      (fvv_st R y Q (List.replicate a true) (List.replicate b true) Y I D (List.replicate c true))
      (if a < (fvv_units Y).1 then
        .norm (fvv_st R y Q [] (List.replicate (a + b) true) (fvv_units Y).2 I D
          (List.replicate c true))
      else if 0 < c then
        .norm (fvv_st R y Q (List.replicate (a - (fvv_units Y).1) true)
          (List.replicate (b + (fvv_units Y).1) true) (fvv_units Y).2 I D
          (List.replicate (c - 1) true))
      else .halt false)
      (3 * Y.length + 5)
  | [], a, b, c => by
    have h := fav_ex_bb R y Q (List.replicate a true) (List.replicate b true) [] I D c
    have h2 : ExecLe fav_cB (fvv_st R y Q (List.replicate a true) (List.replicate b true) [] I D
        (List.replicate c true)) _ _ := ExecLe.pop_nil rfl h
    rcases c with _ | c
    · exact (ExecLe.loop_halt h2).cast (by simp [fvv_units]) (by simp)
    · simp only [Nat.lt_add_one_iff, zero_le, if_true] at h2
      exact (ExecLe.loop_brk h2).cast (by simp [fvv_units]) (by simp)
  | false :: s, a, b, c => by
    have h := fav_ex_bb R y Q (List.replicate a true) (List.replicate b true) s I D c
    have h2 : ExecLe fav_cB (fvv_st R y Q (List.replicate a true) (List.replicate b true)
        (false :: s) I D (List.replicate c true)) _ _ :=
      ExecLe.pop_cons (b := false) (s := s) rfl (by rw [fvv_u7]; exact h)
    rcases c with _ | c
    · exact (ExecLe.loop_halt h2).cast (by simp [fvv_units]) (by simp)
    · simp only [Nat.lt_add_one_iff, zero_le, if_true] at h2
      exact (ExecLe.loop_brk h2).cast (by simp [fvv_units]) (by simp)
  | true :: s, 0, b, c => by
    have h1 := fvv_ex_su R y Q [] (List.replicate b true) I D (List.replicate c true) s
    have hb : ExecLe fav_cB (fvv_st R y Q [] (List.replicate b true) (true :: s) I D
          (List.replicate c true))
        (.brk (fvv_st R y Q [] (List.replicate b true) (fvv_units s).2 I D
          (List.replicate c true)))
        (2 * s.length + 5) :=
      ExecLe.pop_cons (b := true) (s := s) rfl (by
        rw [fvv_u7]
        exact (ExecLe.pop_nil rfl (h1.seq_norm (ExecLe.brk _))).cast rfl (by omega))
    exact (ExecLe.loop_brk hb).cast (by simp [fvv_units]) (by simp; omega)
  | true :: s, a + 1, b, c => by
    have ih := fav_ex_cL R y Q I D s a (b + 1) c
    have hb : ExecLe fav_cB
        (fvv_st R y Q (List.replicate (a + 1) true) (List.replicate b true) (true :: s) I D
          (List.replicate c true))
        (.norm (fvv_st R y Q (List.replicate a true) (List.replicate (b + 1) true) s I D
          (List.replicate c true)))
        3 := by
      refine ExecLe.pop_cons (b := true) (s := s) rfl ?_
      rw [fvv_u7]
      refine ExecLe.pop_cons (b := true) (s := List.replicate a true)
        (by simp [List.replicate_succ]) ?_
      rw [fvv_u4]
      exact (ExecLe.push 5 true _).cast (by simp [List.replicate_succ]) le_rfl
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp only [fvv_units]
    by_cases h : a < (fvv_units s).1
    · rw [if_pos h, if_pos (by omega), show a + (b + 1) = a + 1 + b by omega]
    · rw [if_neg h, if_neg (show ¬ a + 1 < (fvv_units s).1 + 1 by omega), show a + 1 - ((fvv_units s).1 + 1) = a - (fvv_units s).1
        by omega, show b + ((fvv_units s).1 + 1) = b + 1 + (fvv_units s).1 by omega]

/-- Check a `pos` non-diagonal column (the block on stack `7`) against the row rank. -/
def fav_chk : Cmd := .pop 7 .skip fvv_bud (.seq (.push 7 true) (.seq fav_cL (move 5 4)))

theorem fav_ex_chk (R y Q I D Y : Str) (a c : ℕ) :
    ExecLe fav_chk (fvv_st R y Q (List.replicate a true) [] Y I D (List.replicate c true))
      (if (if Y ≠ [] ∧ ¬ a < fav_rk Y then 1 else 0) ≤ c then
        .norm (fvv_st R y Q (List.replicate a true) [] (fav_nx Y) I D
          (List.replicate (c - if Y ≠ [] ∧ ¬ a < fav_rk Y then 1 else 0) true))
      else .halt false)
      (3 * Y.length + 2 * a + 12) := by
  rcases Y with _ | ⟨_ | _, s⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [fav_nx, fvv_units]) (by omega)
  · rcases c with _ | c
    · exact (ExecLe.pop_cons (b := false) (s := s) rfl (by
        rw [fvv_u7]; exact ExecLe.pop_nil rfl (ExecLe.halt false _))).cast
        (by simp [fav_rk, fvv_units]) (by omega)
    · exact (ExecLe.pop_cons (b := false) (s := s) rfl (by
        rw [fvv_u7]
        exact ExecLe.pop_cons (b := true) (s := List.replicate c true)
          (by simp [List.replicate_succ]) (by rw [fvv_u6]; exact ExecLe.skip _))).cast
        (by simp [fav_rk, fav_nx, fvv_units]) (by omega)
  · have hP := ExecLe.push 7 true
      (fvv_st R y Q (List.replicate a true) [] s I D (List.replicate c true))
    rw [fvv_st_7, fvv_u7] at hP
    have h1 := fav_ex_cL R y Q I D (true :: s) a 0 c
    set u := (fvv_units (true :: s)).1 with hu
    set Yr := (fvv_units (true :: s)).2 with hYr
    have hrk : fav_rk (true :: s) = u := rfl
    have hnx : fav_nx (true :: s) = Yr := rfl
    have hul : u ≤ s.length + 1 := by
      have := fvv_units_length (true :: s); simp only [List.length_cons] at this; omega
    rw [hrk, hnx]
    by_cases ha : a < u
    · rw [if_pos ha, Nat.add_zero] at h1
      have hM := exec_move (a := 5) (b := 4) (by decide) (List.replicate a true)
        (fvv_st R y Q [] (List.replicate a true) Yr I D (List.replicate c true)) rfl
      rw [fvv_u5, fvv_u4, fvv_st_4, List.reverse_replicate, List.append_nil] at hM
      refine (ExecLe.pop_cons (b := true) (s := s) rfl (by
        rw [fvv_u7]; exact hP.seq_norm (h1.seq_norm (ExecLe.of hM)))).cast ?_ ?_
      · simp [ha]
      · simp only [List.length_replicate, List.length_cons]; omega
    · rw [if_neg ha] at h1
      rcases c with _ | c
      · rw [if_neg (by omega)] at h1
        refine (ExecLe.pop_cons (b := true) (s := s) rfl (by
          rw [fvv_u7]; exact hP.seq_norm (ExecLe.seq_halt h1))).cast ?_ ?_
        · simp [ha]
        · simp only [List.length_cons]; omega
      · rw [if_pos (by omega), Nat.zero_add] at h1
        have hM := exec_move (a := 5) (b := 4) (by decide) (List.replicate u true)
          (fvv_st R y Q (List.replicate (a - u) true) (List.replicate u true) Yr I D
            (List.replicate (c + 1 - 1) true)) rfl
        rw [fvv_u5, fvv_u4, fvv_st_4, List.reverse_replicate, List.replicate_append_replicate,
          show u + (a - u) = a by omega] at hM
        refine (ExecLe.pop_cons (b := true) (s := s) rfl (by
          rw [fvv_u7]; exact hP.seq_norm (h1.seq_norm (ExecLe.of hM)))).cast ?_ ?_
        · simp [ha]
        · simp only [List.length_replicate, List.length_cons]; omega

/-! ## One column -/

def fav_colS : Cmd := .seq (.pop 10 .skip .skip .skip) fvv_su

def fav_colP : Cmd := .pop 10 fav_chk fvv_su fav_chk

theorem fav_ex_col (R y Q I Y D : Str) (a c : ℕ) {s : SatSym} (hs : s ≠ sep) :
    ExecLe (hsv_sel s .brk fav_colS fav_colP fav_colS)
      (fvv_st R y Q (List.replicate a true) [] Y I D (List.replicate c true))
      (if (if fav_bad a s Y D then 1 else 0) ≤ c then
        .norm (fvv_st R y Q (List.replicate a true) [] (fav_nx Y) I D.tail
          (List.replicate (c - if fav_bad a s Y D then 1 else 0) true))
      else .halt false)
      (3 * Y.length + 2 * a + 14) := by
  have hS : ExecLe fav_colS
      (fvv_st R y Q (List.replicate a true) [] Y I D (List.replicate c true))
      (.norm (fvv_st R y Q (List.replicate a true) [] (fav_nx Y) I D.tail
        (List.replicate c true)))
      (3 * Y.length + 2 * a + 14) := by
    have h1 : ExecLe (.pop 10 .skip .skip .skip)
        (fvv_st R y Q (List.replicate a true) [] Y I D (List.replicate c true))
        (.norm (fvv_st R y Q (List.replicate a true) [] Y I D.tail (List.replicate c true))) 2 :=
      fvv_pop3 (by rw [fvv_st_10, fvv_u10]; exact ExecLe.skip _)
    exact (h1.seq_norm (fvv_ex_su _ _ _ _ _ _ _ _ _)).cast rfl (by omega)
  cases s with
  | sep => exact absurd rfl hs
  | zero => exact hS.cast (by simp [fav_bad]) le_rfl
  | neg => exact hS.cast (by simp [fav_bad]) le_rfl
  | pos =>
    show ExecLe fav_colP _ _ _
    rcases D with _ | ⟨_ | _, d⟩
    · exact (ExecLe.pop_nil rfl (fav_ex_chk R y Q I [] Y a c)).cast
        (by simp [fav_bad]) (by omega)
    · exact (ExecLe.pop_cons (b := false) (s := d) rfl (by
        rw [fvv_u10]; exact fvv_ex_su _ _ _ _ _ _ _ _ _)).cast
        (by simp [fav_bad, fav_nx]) (by omega)
    · exact (ExecLe.pop_cons (b := true) (s := d) rfl (by
        rw [fvv_u10]; exact fav_ex_chk R y Q I d Y a c)).cast (by simp [fav_bad]) (by omega)

/-! ## The row loop -/

def fav_kB : Cmd :=
  .pop 3 (.halt true) (.pop 3 (.halt true) .brk fav_colS) (.pop 3 (.halt true) fav_colP fav_colS)

def fav_kL : Cmd := .loop fav_kB

theorem fav_ex_kL (R y Q' I : Str) (a N : ℕ) (ha : a ≤ N) :
    ∀ (r : List SatSym) (Y D : Str) (c : ℕ), sep ∉ r → Y.length ≤ N →
    ExecLe fav_kL
      (fvv_st R y (r.flatMap ic ++ false :: false :: Q') (List.replicate a true) [] Y I D
        (List.replicate c true))
      (if fav_cnt a r Y D ≤ c then
        .norm (fvv_st R y Q' (List.replicate a true) [] (fav_nx^[r.length] Y) I
          (D.drop r.length) (List.replicate (c - fav_cnt a r Y D) true))
      else .halt false)
      (r.length * (5 * N + 16) + 3)
  | [], Y, D, c, _, _ => by
    have hb := dsv_pop2 (cE := .halt true) (cX := .halt true) (cS := .brk) (cZ := fav_colS)
      (cP := fav_colP) (cN := fav_colS) (Q := Q') sep
      (σ := fvv_st R y (false :: false :: Q') (List.replicate a true) [] Y I D
        (List.replicate c true)) rfl (ExecLe.brk _)
    exact (ExecLe.loop_brk hb).cast (by simp [fav_cnt]) (by simp)
  | s :: r, Y, D, c, hr, hY => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hc := fav_ex_col R y (r.flatMap ic ++ false :: false :: Q') I Y D a c hs
    have hb := dsv_pop2 (cE := .halt true) (cX := .halt true) s
      (Q := r.flatMap ic ++ false :: false :: Q')
      (σ := fvv_st R y ((s :: r).flatMap ic ++ false :: false :: Q') (List.replicate a true) []
        Y I D (List.replicate c true)) (by simp) (by rw [fvv_u3]; exact hc)
    simp only [List.flatMap_cons, List.append_assoc] at hb ⊢
    set k := (if fav_bad a s Y D then 1 else 0) with hk
    have hcnt : fav_cnt a (s :: r) Y D = k + fav_cnt a r (fav_nx Y) D.tail := rfl
    rw [hcnt]
    by_cases hkc : k ≤ c
    · rw [if_pos hkc] at hb
      have ih := fav_ex_kL R y Q' I a N ha r (fav_nx Y) D.tail (c - k)
        (fun e => hr (List.mem_cons_of_mem _ e)) ((fav_nx_length Y).trans hY)
      refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; nlinarith)
      simp only [List.length_cons, iterate_succ_apply]
      by_cases h2 : fav_cnt a r (fav_nx Y) D.tail ≤ c - k
      · rw [if_pos h2, if_pos (by omega), Nat.sub_sub]
        cases D <;> simp
      · rw [if_neg h2, if_neg (by omega)]
    · rw [if_neg hkc] at hb
      exact (ExecLe.loop_halt hb).cast (by rw [if_neg (by omega)]) (by simp; nlinarith)

/-! ## One row -/

def fav_mode : Cmd :=
  .pop 0 (.halt false) (.seq fav_kL fvv_end)
    (.seq (.push 4 true) (.seq fvv_rdK (.seq fav_kL fvv_end)))

def fav_row : Cmd :=
  .seq (copyVia 1 7 8) (.seq (.push 10 false) (.seq (copyVia 9 10 8) fav_mode))

theorem fav_ex_row (y Q' R : Str) (r : List SatSym) (c i N : ℕ) (hr : sep ∉ r)
    (hy : y.length ≤ N) (hR : R.length ≤ N) (hi : i + 1 ≤ N) :
    ExecLe fav_row
      (fvv_st R y (r.flatMap ic ++ false :: false :: Q') [] [] [] (List.replicate i true) []
        (List.replicate c true))
      (if R ≠ [] ∧ fav_cnt (fav_rk R) r y (List.replicate i true ++ [false]) ≤ c then
        .norm (fvv_st (fav_nx R) y Q' [] [] [] (List.replicate (i + 1) true) []
          (List.replicate (c - fav_cnt (fav_rk R) r y (List.replicate i true ++ [false])) true))
      else .halt false)
      (r.length * (5 * N + 16) + 20 * N + 30) := by
  set Q := r.flatMap ic ++ false :: false :: Q'
  set dg := List.replicate i true ++ [false]
  have hC1 := exec_copyVia (a := 1) (b := 7) (t := 8) (by decide) (by decide) (by decide)
    (fvv_st R y Q [] [] [] (List.replicate i true) [] (List.replicate c true)) rfl
  rw [fvv_st_1, fvv_st_7, List.append_nil, fvv_u7] at hC1
  have hP := ExecLe.push 10 false (fvv_st R y Q [] [] y (List.replicate i true) []
    (List.replicate c true))
  rw [fvv_st_10, fvv_u10] at hP
  have hC2 := exec_copyVia (a := 9) (b := 10) (t := 8) (by decide) (by decide) (by decide)
    (fvv_st R y Q [] [] y (List.replicate i true) [false] (List.replicate c true)) rfl
  rw [fvv_st_9, fvv_st_10, fvv_u10] at hC2
  have hpre : ∀ (res : Res) (T : ℕ),
      ExecLe fav_mode
        (fvv_st R y Q [] [] y (List.replicate i true) dg (List.replicate c true)) res T →
      ExecLe fav_row
        (fvv_st R y Q [] [] [] (List.replicate i true) [] (List.replicate c true)) res
        (5 * y.length + 4 + (1 + (5 * i + 4 + T))) := by
    intro res T h
    have hl : (List.replicate i true).length = i := List.length_replicate
    have := (ExecLe.of hC1).seq_norm (hP.seq_norm ((ExecLe.of hC2).seq_norm h))
    rw [hl] at this
    exact this
  have hdg : dg.length = i + 1 := by simp [dg]
  have hpost : ∀ (K Y' D' : Str) (C' : Str), K.length ≤ N → Y'.length ≤ N → D'.length ≤ N →
      ExecLe fvv_end (fvv_st (fav_nx R) y Q' K [] Y' (List.replicate i true) D' C')
        (.norm (fvv_st (fav_nx R) y Q' [] [] [] (List.replicate (i + 1) true) [] C'))
        (6 * N + 7) := by
    intro K Y' D' C' hK hY hD
    exact (fvv_ex_end _ _ _ _ _ _ _ _).cast (by simp [List.replicate_succ]) (by omega)
  refine (hpre _ (r.length * (5 * N + 16) + 10 * N + 21) ?_).mono (by omega)
  -- the scan of the row, with the rank `a` on stack `4`
  have hscan : ∀ a : ℕ, a ≤ N → a = fav_rk R →
      ExecLe (.seq fav_kL fvv_end)
        (fvv_st (fav_nx R) y Q (List.replicate a true) [] y (List.replicate i true) dg
          (List.replicate c true))
        (if fav_cnt (fav_rk R) r y dg ≤ c then
          .norm (fvv_st (fav_nx R) y Q' [] [] [] (List.replicate (i + 1) true) []
            (List.replicate (c - fav_cnt (fav_rk R) r y dg) true))
        else .halt false)
        (r.length * (5 * N + 16) + 6 * N + 10) := by
    intro a haN hae
    subst hae
    have hkl := fav_ex_kL (fav_nx R) y Q' (List.replicate i true) (fav_rk R) N haN r y dg c hr hy
    by_cases hok : fav_cnt (fav_rk R) r y dg ≤ c
    · rw [if_pos hok] at hkl
      rw [if_pos hok]
      refine (hkl.seq_norm (hpost _ _ _ _ ?_ ?_ ?_)).cast rfl (by omega)
      · simp only [List.length_replicate]; exact haN
      · exact (fav_nx_iter_length _ _).trans hy
      · simp only [List.length_drop, hdg]; omega
    · rw [if_neg hok] at hkl
      rw [if_neg hok]
      exact (ExecLe.seq_halt hkl).cast rfl (by omega)
  unfold fav_mode
  rcases R with _ | ⟨_ | _, s⟩
  · exact ((ExecLe.pop_nil rfl (ExecLe.halt false _))).cast (by simp)
      (by omega)
  · -- rank `0`
    have h := hscan 0 (by omega) (by simp [fav_rk, fvv_units])
    have e : fav_nx (false :: s) = s := by simp [fav_nx, fvv_units]
    rw [e] at h
    refine (ExecLe.pop_cons (b := false) (s := s) rfl (by rw [fvv_u0]; exact h)).cast
      ?_ (by omega)
    rw [e]; simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and]
  · -- rank `≥ 1`
    have hrs : (fvv_units s).1 + 1 ≤ N := by
      have := fvv_units_length s; simp at hR; omega
    have h := hscan ((fvv_units s).1 + 1) hrs (by simp [fav_rk, fvv_units])
    have e : fav_nx (true :: s) = (fvv_units s).2 := by simp [fav_nx, fvv_units]
    rw [e] at h
    have hk := fvv_ex_rdK y Q [] y (List.replicate i true) dg (List.replicate c true) s 1
    have hp := ExecLe.push 4 true
      (fvv_st s y Q [] [] y (List.replicate i true) dg (List.replicate c true))
    rw [fvv_st_4, fvv_u4] at hp
    refine (ExecLe.pop_cons (b := true) (s := s) rfl (by
      rw [fvv_u0]; exact hp.seq_norm (hk.seq_norm h))).cast ?_ ?_
    · rw [e]; simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    · simp only [List.length_cons] at hR; omega

/-! ## The outer loop -/

def fav_oB : Cmd :=
  .pop 3 (.halt true) (.seq (.push 3 false) fav_row) (.seq (.push 3 true) fav_row)

def fav_oL : Cmd := .loop fav_oB

theorem fav_ex_oL (y : Str) (N : ℕ) (hy : y.length ≤ N) : ∀ (rows : List (List SatSym))
    (R : Str) (c i : ℕ), (∀ r ∈ rows, sep ∉ r) → R.length ≤ N → i + rows.length ≤ N →
    ExecLe fav_oL (fvv_st R y (enc rows) [] [] [] (List.replicate i true) []
      (List.replicate c true)) (.halt (fav_go y rows R c i)) (fvv_To N rows)
  | [], R, c, i, _, _, _ => (ExecLe.loop_halt (ExecLe.pop_nil rfl (ExecLe.halt true _))).cast
      (by simp [fav_go]) (by simp [fvv_To])
  | r :: rows, R, c, i, hrows, hR, hi => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.length_cons] at hi
    rw [enc_cons]
    obtain ⟨b, t, hbt⟩ := List.exists_cons_of_ne_nil
      (show r.flatMap ic ++ false :: false :: enc rows ≠ [] by simp)
    have hrow := fav_ex_row y (enc rows) R r c i N hr hy hR (by omega)
    have hnx := (fav_nx_length R).trans hR
    have hpk := fun res T (h : ExecLe fav_row (fvv_st R y (r.flatMap ic ++ false :: false ::
        enc rows) [] [] [] (List.replicate i true) [] (List.replicate c true)) res T) =>
      fvv_peek (cn := .halt true) (b := b) (s := t) (by rw [fvv_st_3, hbt]) h
    by_cases hok : R ≠ [] ∧ fav_cnt (fav_rk R) r y (List.replicate i true ++ [false]) ≤ c
    · rw [if_pos hok] at hrow
      have ih := fav_ex_oL y N hy rows (fav_nx R)
        (c - fav_cnt (fav_rk R) r y (List.replicate i true ++ [false])) (i + 1) hrs hnx
        (by omega)
      exact (ExecLe.loop_norm (hpk _ _ hrow) ih).cast (by simp [fav_go, hok])
        (by simp [fvv_To])
    · rw [if_neg hok] at hrow
      refine (ExecLe.loop_halt (hpk _ _ hrow)).cast ?_ (by simp [fvv_To])
      simp only [fav_go]
      rw [show decide (R ≠ [] ∧ fav_cnt (fav_rk R) r y (List.replicate i true ++ [false]) ≤ c)
        = false from decide_eq_false hok, Bool.false_and]

/-! ## The whole verifier -/

def fav_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq (copyVia 0 1 8) (.seq dsv_bL fav_oL))))

theorem fav_exec_ver (z : Str) :
    ExecLe fav_ver (init [z]).stk (.halt (fav_vres (dec z).1 (dec z).2)) (fvv_Tver z.length) := by
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
      fvv_st y [] (enc (clauses w)) [] [] [] [] [] [] := by
    funext j
    simp only [σ₂, σ₁, fvv_st, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hC := exec_copyVia (a := 0) (b := 1) (t := 8) (by decide) (by decide) (by decide)
    (fvv_st y [] (enc (clauses w)) [] [] [] [] [] []) rfl
  rw [fvv_st_0, fvv_st_1, List.append_nil, fvv_u1] at hC
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ),
      ExecLe c (fvv_st y y (enc (clauses w)) [] [] [] [] [] []) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq (copyVia 0 1 8) c))))
        (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 +
          (5 * y.length + 4 + T)))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm ((ExecLe.of hC).seq_norm h)))
  have hsep := sep_not_mem_clauses w
  have hz2 : z.length * z.length ≤ (z.length + 2) ^ 2 := by nlinarith
  unfold fav_vres fav_ver
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · rw [hcw] at hpre
    refine (hpre _ _ _ (ExecLe.seq_halt (ExecLe.loop_halt
      (ExecLe.pop_nil (σ := fvv_st y y [] [] [] [] [] [] []) rfl (ExecLe.halt false _))))).cast
      rfl ?_
    simp only [htl, fvv_Tver]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    have hB := fvv_ex_bd y y (enc rows) kr 0 (hsep kr (by simp))
    rw [List.replicate_zero, Nat.add_zero] at hB
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hO := fav_ex_oL y z.length (by omega) rows y kr.length 0
      (fun r hr => hsep r (by simp [hr])) (by omega) (by omega)
    refine (hpre _ _ _ (hB.seq_norm hO)).cast rfl ?_
    rw [fvv_To_eq]
    simp only [htl, fvv_Tver]
    have h1 : (rows.map List.length).sum * (5 * z.length + 16) ≤
        z.length * (5 * z.length + 16) := Nat.mul_le_mul_right _ (by omega)
    have h2 : rows.length * (20 * z.length + 32) ≤ z.length * (20 * z.length + 32) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

end Pnp.Karp.FeedbackArc
