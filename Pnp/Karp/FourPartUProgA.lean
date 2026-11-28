import Pnp.Karp.FourPartU
import Pnp.Karp.ThreePartUProg

/-!
# Unary 4-PARTITION reduction program, part A: generic loops

Commands used by the program `fpup_redCmd` (`Pnp/Karp/FourPartUProg.lean`):

* `fpup_half a d`: pop two bits of stack `a` at a time, pushing one `false` onto `d`;
* `fpup_unL a d`: for each bit of `a`, push the code `rv [pos]` onto `d`;
* `fpup_cpN a d n`: append `n` copies of stack `a` onto `d` (temporary `3`);
* `fpup_rdRow`: read one row from stack `1`, pushing `rv [pos]` onto stack `2` per symbol.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.FourPartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.ThreePartU

/-! ## Unary rows as codes -/

theorem fpup_rv_pos : rv [pos] = [false, true] := rfl

theorem fpup_rv_uRow_succ (n : ℕ) : rv (uRow (n + 1)) = rv [pos] ++ rv (uRow n) := by
  unfold uRow; rw [List.replicate_succ', rv_append]

theorem fpup_rv_uRow_add (a b : ℕ) : rv (uRow (a + b)) = rv (uRow a) ++ rv (uRow b) := by
  rw [Nat.add_comm]; unfold uRow; rw [List.replicate_add, rv_append]

theorem fpup_rv_comm (n : ℕ) (l : Str) :
    rv (uRow n) ++ (rv [pos] ++ l) = rv [pos] ++ (rv (uRow n) ++ l) := by
  have e : uRow (n + 1) = [pos] ++ uRow n := rfl
  rw [← List.append_assoc, ← List.append_assoc, ← fpup_rv_uRow_succ, e, rv_append]

theorem fpup_rv_uRow_mul (k n : ℕ) :
    (List.replicate k (rv (uRow n))).flatten = rv (uRow (k * n)) := by
  induction k with
  | zero => simp [uRow]
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm,
      fpup_rv_uRow_add]

theorem fpup_len_rv_uRow (n : ℕ) : (rv (uRow n)).length = 2 * n := by
  simp [rv, uRow, ic]; ring

/-! ## Halving -/

def fpup_half (a d : ℕ) : Cmd :=
  .loop (.pop a .brk (.pop a (.push d false) (.push d false) (.push d false))
    (.pop a (.push d false) (.push d false) (.push d false)))

theorem fpup_ex_half {a d : ℕ} (had : a ≠ d) (b : Bool) : ∀ (n : ℕ) (σ : ℕ → Str),
    σ a = List.replicate (2 * n) b →
    ExecLe (fpup_half a d) σ (.norm (update (update σ a []) d (List.replicate n false ++ σ d)))
      (3 * n + 2)
  | 0, σ, h => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk _))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all) (by simp)
  | n + 1, σ, h => by
    have h' : σ a = b :: b :: List.replicate (2 * n) b := by
      rw [h, show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rfl
    have h1 : ExecLe (.pop a .brk (.pop a (.push d false) (.push d false) (.push d false))
        (.pop a (.push d false) (.push d false) (.push d false))) σ
        (.norm (update (update σ a (List.replicate (2 * n) b)) d (false :: σ d))) 3 := by
      refine ExecLe.pop_same h' ?_
      have h2 : update σ a (b :: List.replicate (2 * n) b) a = b :: List.replicate (2 * n) b := by
        simp
      refine ExecLe.pop_cons h2 ?_
      cases b <;> exact (ExecLe.push d false _).cast
        (by congr 1; rw [update_idem, update_of_ne had.symm]) le_rfl
    have ih := fpup_ex_half had b n (update (update σ a (List.replicate (2 * n) b)) d (false :: σ d)) (by rw [update_of_ne had, update_self])
    refine (ExecLe.loop_norm h1 ih).cast ?_ (by omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [List.replicate_succ']

/-! ## Unary printing of a count -/

def fpup_unL (a d : ℕ) : Cmd := .loop (.pop a .brk (pushList d (rv [pos])) (pushList d (rv [pos])))

theorem fpup_ex_unL {a d : ℕ} (had : a ≠ d) : ∀ (l : Str) (σ : ℕ → Str), σ a = l →
    ExecLe (fpup_unL a d) σ (.norm (update (update σ a []) d (rv (uRow l.length) ++ σ d)))
      (5 * l.length + 2)
  | [], σ, h => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk _))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [uRow]) (by simp)
  | x :: l, σ, h => by
    have h1 : ExecLe (.pop a .brk (pushList d (rv [pos])) (pushList d (rv [pos]))) σ
        (.norm (update (update σ a l) d (rv [pos] ++ σ d))) 4 :=
      ExecLe.pop_same h ((ExecLe.of (exec_pushList d _ _)).cast
        (by rw [update_of_ne had.symm]) (by simp [fpup_rv_pos]))
    have ih := fpup_ex_unL had l (update (update σ a l) d (rv [pos] ++ σ d)) (by rw [update_of_ne had, update_self])
    refine (ExecLe.loop_norm h1 ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all [fpup_rv_uRow_succ, fpup_rv_comm]

/-! ## Repeated copies -/

def fpup_cpN (a d : ℕ) : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (copyVia a d 3) (fpup_cpN a d n)

theorem fpup_ex_cpN {a d : ℕ} (had : a ≠ d) (ha3 : a ≠ 3) (hd3 : d ≠ 3) :
    ∀ (n : ℕ) (σ : ℕ → Str), σ 3 = [] →
    ExecLe (fpup_cpN a d n) σ (.norm (update σ d ((List.replicate n (σ a)).flatten ++ σ d)))
      (n * (5 * (σ a).length + 4) + 1)
  | 0, σ, _ => (ExecLe.skip σ).cast (by simp) (by simp)
  | n + 1, σ, h3 => by
    have h1 := ExecLe.of (exec_copyVia had ha3 hd3 σ h3)
    have ih := fpup_ex_cpN had ha3 hd3 n (update σ d (σ a ++ σ d)) (by rw [update_of_ne hd3.symm, h3])
    refine (h1.seq_norm ih).cast ?_ (by simp [update_of_ne had]; ring_nf; omega)
    congr 1; funext j; simp only [update_apply]
    split_ifs with hj
    · subst hj; simp [List.replicate_succ']
    · rfl

/-! ## Reading one row -/

def fpup_rdP : Cmd := pushList 2 (rv [pos])

def fpup_rdRow : Cmd :=
  .loop (.pop 1 .brk (.pop 1 .brk .brk fpup_rdP) (.pop 1 .brk fpup_rdP fpup_rdP))

theorem fpup_ex_rdP (σ : ℕ → Str) :
    ExecLe fpup_rdP σ (.norm (update σ 2 (rv [pos] ++ σ 2))) 3 :=
  (ExecLe.of (exec_pushList 2 _ _)).cast rfl (by simp [fpup_rv_pos])

theorem fpup_ex_rdRow : ∀ (r : List SatSym) (rest : Str) (σ : ℕ → Str), sep ∉ r →
    σ 1 = (r ++ [sep]).flatMap ic ++ rest →
    ExecLe fpup_rdRow σ (.norm (update (update σ 1 rest) 2 (rv (uRow r.length) ++ σ 2)))
      (6 * r.length + 4)
  | [], rest, σ, _, h => by
    have h' : σ 1 = false :: false :: rest := by simpa [ic] using h
    have hb : ExecLe (.pop 1 .brk (.pop 1 .brk .brk fpup_rdP) (.pop 1 .brk fpup_rdP fpup_rdP)) σ
        (.brk (update σ 1 rest)) 3 := by
      refine ExecLe.pop_cons (b := false) (s := false :: rest) h' ?_
      simp only [Bool.false_eq_true, ite_false]
      refine ExecLe.pop_cons (b := false) (s := rest) (by simp) ?_
      simp only [Bool.false_eq_true, ite_false, update_idem]
      exact ExecLe.brk _
    refine (ExecLe.loop_brk hb).cast ?_ (by simp)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [uRow]
  | s :: r, rest, σ, hs, h => by
    have hs' : s ≠ sep := fun e => hs (e ▸ List.mem_cons_self)
    have hr : sep ∉ r := fun e => hs (List.mem_cons_of_mem _ e)
    have hR : (r ++ [sep]).flatMap ic ++ rest = List.flatMap ic (r ++ [sep]) ++ rest := rfl
    have h1 : ExecLe (.pop 1 .brk (.pop 1 .brk .brk fpup_rdP) (.pop 1 .brk fpup_rdP fpup_rdP)) σ
        (.norm (update (update σ 1 ((r ++ [sep]).flatMap ic ++ rest)) 2 (rv [pos] ++ σ 2))) 5 := by
      cases s with
      | sep => exact absurd rfl hs'
      | zero =>
        have h' : σ 1 = false :: true :: ((r ++ [sep]).flatMap ic ++ rest) := by
          rw [h]; simp [ic]
        refine ExecLe.pop_cons h' ?_
        refine ExecLe.pop_cons (b := true) (s := (r ++ [sep]).flatMap ic ++ rest) (by simp) ?_
        simp only [Bool.false_eq_true, ite_false, ite_true]
        exact (fpup_ex_rdP _).cast (by congr 1; simp [update_idem]) (by omega)
      | pos =>
        have h' : σ 1 = true :: false :: ((r ++ [sep]).flatMap ic ++ rest) := by
          rw [h]; simp [ic]
        refine ExecLe.pop_cons h' ?_
        refine ExecLe.pop_cons (b := false) (s := (r ++ [sep]).flatMap ic ++ rest) (by simp) ?_
        simp only [Bool.false_eq_true, ite_false, ite_true]
        exact (fpup_ex_rdP _).cast (by congr 1; simp [update_idem]) (by omega)
      | neg =>
        have h' : σ 1 = true :: true :: ((r ++ [sep]).flatMap ic ++ rest) := by
          rw [h]; simp [ic]
        refine ExecLe.pop_cons h' ?_
        refine ExecLe.pop_cons (b := true) (s := (r ++ [sep]).flatMap ic ++ rest) (by simp) ?_
        simp only [Bool.false_eq_true, ite_false, ite_true]
        exact (fpup_ex_rdP _).cast (by congr 1; simp [update_idem]) (by omega)
    have ih := fpup_ex_rdRow r rest
      (update (update σ 1 ((r ++ [sep]).flatMap ic ++ rest)) 2 (rv [pos] ++ σ 2)) hr (by simp)
    refine (ExecLe.loop_norm h1 ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all [fpup_rv_uRow_succ, fpup_rv_comm]

theorem fpup_ex_rdRow_nil (σ : ℕ → Str) (h : σ 1 = []) :
    ExecLe fpup_rdRow σ (.norm σ) 2 :=
  (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk _))).cast rfl (by simp)

end Pnp.Karp.FourPartU
