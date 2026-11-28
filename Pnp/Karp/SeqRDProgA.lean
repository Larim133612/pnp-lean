import Pnp.Karp.SeqRD
import Pnp.Karp.FourPartUProgB

/-!
# The unary scheduling reduction program, part A: the state and the small loops

Stacks of the program `srp_redCmd` (`Pnp/Karp/SeqRDProg.lean`), state `srp_st`:
`0` the output `rv E`; `1` the code of the input rows; `2` the row buffer; `3` temporary;
`4` a counter; `5` `rv (uRow P)` (`P = B + 1`); `6` `rv (uRow D)` (`D = m P - 1`);
`7` the accumulator `rv (uRow (j P))`; `8` the counter of separators; `9` a copy of the input.

* `srp_cntL`: read all rows, keep the last one in the buffer, count the others on stack `4`;
* `srp_div`: divide the counter on stack `4` by three onto stack `8`;
* `srp_mul`: append one copy of stack `5` to stack `6` per bit of stack `4`;
* `srp_p2 j`: pop two bits of stack `j` (if any): `rv (uRow n) ↦ rv (uRow (n - 1))`.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.SeqRD

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.ThreePartU Pnp.Karp.ThreePart Pnp.Karp.FourPartU

/-! ## The state -/

def srp_st (o i rb c p d ac k x : Str) : ℕ → Str := fun j =>
  if j = 0 then o else if j = 1 then i else if j = 2 then rb else if j = 4 then c
  else if j = 5 then p else if j = 6 then d else if j = 7 then ac else if j = 8 then k
  else if j = 9 then x else []

section
variable (o i rb c p d ac k x v : Str)

@[simp] theorem srp_st0 : srp_st o i rb c p d ac k x 0 = o := rfl
@[simp] theorem srp_st1 : srp_st o i rb c p d ac k x 1 = i := rfl
@[simp] theorem srp_st2 : srp_st o i rb c p d ac k x 2 = rb := rfl
@[simp] theorem srp_st3 : srp_st o i rb c p d ac k x 3 = [] := rfl
@[simp] theorem srp_st4 : srp_st o i rb c p d ac k x 4 = c := rfl
@[simp] theorem srp_st5 : srp_st o i rb c p d ac k x 5 = p := rfl
@[simp] theorem srp_st6 : srp_st o i rb c p d ac k x 6 = d := rfl
@[simp] theorem srp_st7 : srp_st o i rb c p d ac k x 7 = ac := rfl
@[simp] theorem srp_st8 : srp_st o i rb c p d ac k x 8 = k := rfl
@[simp] theorem srp_st9 : srp_st o i rb c p d ac k x 9 = x := rfl

@[simp] theorem srp_u0 : update (srp_st o i rb c p d ac k x) 0 v = srp_st v i rb c p d ac k x := by
  funext j; simp only [srp_st, update_apply]; split_ifs <;> simp_all
@[simp] theorem srp_u1 : update (srp_st o i rb c p d ac k x) 1 v = srp_st o v rb c p d ac k x := by
  funext j; simp only [srp_st, update_apply]; split_ifs <;> simp_all
@[simp] theorem srp_u2 : update (srp_st o i rb c p d ac k x) 2 v = srp_st o i v c p d ac k x := by
  funext j; simp only [srp_st, update_apply]; split_ifs <;> simp_all
@[simp] theorem srp_u4 : update (srp_st o i rb c p d ac k x) 4 v = srp_st o i rb v p d ac k x := by
  funext j; simp only [srp_st, update_apply]; split_ifs <;> simp_all
@[simp] theorem srp_u5 : update (srp_st o i rb c p d ac k x) 5 v = srp_st o i rb c v d ac k x := by
  funext j; simp only [srp_st, update_apply]; split_ifs <;> simp_all
@[simp] theorem srp_u6 : update (srp_st o i rb c p d ac k x) 6 v = srp_st o i rb c p v ac k x := by
  funext j; simp only [srp_st, update_apply]; split_ifs <;> simp_all
@[simp] theorem srp_u7 : update (srp_st o i rb c p d ac k x) 7 v = srp_st o i rb c p d v k x := by
  funext j; simp only [srp_st, update_apply]; split_ifs <;> simp_all
@[simp] theorem srp_u8 : update (srp_st o i rb c p d ac k x) 8 v = srp_st o i rb c p d ac v x := by
  funext j; simp only [srp_st, update_apply]; split_ifs <;> simp_all
@[simp] theorem srp_u9 : update (srp_st o i rb c p d ac k x) 9 v = srp_st o i rb c p d ac k v := by
  funext j; simp only [srp_st, update_apply]; split_ifs <;> simp_all

/-- Copying stack `a` onto stack `b` (temporary `3`). -/
theorem srp_ex_cp {a b : ℕ} (hab : a ≠ b) (ha : a ≠ 3) (hb : b ≠ 3) :
    ExecLe (copyVia a b 3) (srp_st o i rb c p d ac k x)
      (.norm (update (srp_st o i rb c p d ac k x) b
        (srp_st o i rb c p d ac k x a ++ srp_st o i rb c p d ac k x b)))
      (5 * (srp_st o i rb c p d ac k x a).length + 4) :=
  ExecLe.of (exec_copyVia hab ha hb _ rfl)

theorem srp_ex_em (E L : List SatSym) :
    ExecLe (pushList 0 (rv L)) (srp_st (rv E) i rb c p d ac k x)
      (.norm (srp_st (rv (E ++ L)) i rb c p d ac k x)) (2 * L.length + 1) :=
  (ExecLe.of (exec_pushList 0 (rv L) _)).cast (by rw [srp_u0, srp_st0, rv_append])
    (by simp only [rv, List.length_reverse, length_flatMap_ic]; omega)

theorem srp_ex_dr2 :
    ExecLe (drain 2) (srp_st o i rb c p d ac k x) (.norm (srp_st o i [] c p d ac k x))
      (2 * rb.length + 2) :=
  (ExecLe.of (exec_drain 2 rb _ rfl)).cast (by rw [srp_u2]) le_rfl

end

/-! ## Popping two bits -/

def srp_p2 (j : ℕ) : Cmd := .pop j .skip (.pop j .skip .skip .skip) (.pop j .skip .skip .skip)

theorem srp_ex_p2 (j : ℕ) (σ : ℕ → Str) (l : Str) (h : σ j = rv [pos] ++ l) :
    ExecLe (srp_p2 j) σ (.norm (update σ j l)) 3 := by
  have h' : σ j = false :: true :: l := by rw [h]; rfl
  refine ExecLe.pop_cons h' ?_
  simp only [Bool.false_eq_true, ite_false]
  refine ExecLe.pop_cons (b := true) (s := l) (by simp) ?_
  simp only [ite_true, update_idem]
  exact ExecLe.skip _

theorem srp_ex_p2_nil (j : ℕ) (σ : ℕ → Str) (h : σ j = []) :
    ExecLe (srp_p2 j) σ (.norm σ) 2 :=
  (ExecLe.pop_nil h (ExecLe.skip _)).cast rfl le_rfl

theorem srp_ex_p2_uRow (j : ℕ) (σ : ℕ → Str) (n : ℕ) (h : σ j = rv (uRow n)) :
    ExecLe (srp_p2 j) σ (.norm (update σ j (rv (uRow (n - 1))))) 3 := by
  rcases n with _ | n
  · exact (srp_ex_p2_nil j σ (by simpa [uRow] using h)).cast
      (by congr 1; funext t; simp only [update_apply]; split_ifs with ht
          · subst ht; simpa [uRow] using h
          · rfl) (by omega)
  · exact srp_ex_p2 j σ _ (by rw [h, fpup_rv_uRow_succ]; rfl)

/-! ## Counting the rows -/

def srp_cntL : Cmd := .loop (.seq fpup_rdRow (tpp_pk 1 (.seq (drain 2) (.push 4 false))))

theorem srp_ex_cntL (Z : ℕ) (o p d ac k x : Str) : ∀ (rows : List (List SatSym)) (c : Str),
    (∀ r ∈ rows, sep ∉ r ∧ r.length ≤ Z) →
    ExecLe srp_cntL (srp_st o (fpup_code rows) [] c p d ac k x)
      (.norm (srp_st o [] (rv (uRow (rows.getLastD []).length))
        (List.replicate rows.dropLast.length false ++ c) p d ac k x))
      ((rows.length + 1) * (10 * Z + 20))
  | [], c, _ => by
    have h1 := fpup_ex_rdRow_nil (srp_st o (fpup_code []) [] c p d ac k x) rfl
    have h2 : ExecLe (tpp_pk 1 (.seq (drain 2) (.push 4 false)))
        (srp_st o (fpup_code []) [] c p d ac k x)
        (.brk (srp_st o (fpup_code []) [] c p d ac k x)) 2 :=
      ExecLe.pop_nil rfl (ExecLe.brk _)
    refine (ExecLe.loop_brk (h1.seq_norm h2)).cast ?_ (by simp)
    simp [fpup_code, uRow]
  | [r], c, hr => by
    have hr1 := hr r List.mem_cons_self
    have h1 := fpup_ex_rdRow r [] (srp_st o (fpup_code [r]) [] c p d ac k x) hr1.1
      (by simp [fpup_code])
    rw [srp_u1, srp_u2] at h1
    have h2 : ExecLe (tpp_pk 1 (.seq (drain 2) (.push 4 false)))
        (srp_st o [] (rv (uRow r.length) ++ srp_st o (fpup_code [r]) [] c p d ac k x 2) c p d ac k x)
        (.brk (srp_st o [] (rv (uRow r.length) ++ srp_st o (fpup_code [r]) [] c p d ac k x 2)
          c p d ac k x)) 2 :=
      ExecLe.pop_nil rfl (ExecLe.brk _)
    refine (ExecLe.loop_brk (h1.seq_norm h2)).cast ?_ ?_
    · simp
    · simp only [List.length_cons, List.length_nil]; nlinarith
  | r :: r' :: rs, c, hr => by
    have hr1 := hr r List.mem_cons_self
    have h1 := fpup_ex_rdRow r (fpup_code (r' :: rs))
      (srp_st o (fpup_code (r :: r' :: rs)) [] c p d ac k x) hr1.1 (by rw [fpup_code_cons]; rfl)
    rw [srp_u1, srp_u2] at h1
    simp only [srp_st2, List.append_nil] at h1
    obtain ⟨b, M', hbm⟩ : ∃ b M', fpup_code (r' :: rs) = b :: M' := by
      rw [fpup_code_cons]
      rcases r' with _ | ⟨s, r'⟩
      · exact ⟨_, _, rfl⟩
      · cases s <;> exact ⟨_, _, rfl⟩
    have hd := srp_ex_dr2 o (fpup_code (r' :: rs)) (rv (uRow r.length)) c p d ac k x
    have hp := (ExecLe.push 4 false (srp_st o (fpup_code (r' :: rs)) [] c p d ac k x)).cast
      (by rw [srp_u4, srp_st4]) le_rfl
    have h2 := tpp_ex_pk (srp_st o (fpup_code (r' :: rs)) (rv (uRow r.length)) c p d ac k x)
      (k := 1) hbm (hd.seq_norm hp)
    have ih := srp_ex_cntL Z o p d ac k x (r' :: rs) (false :: c)
      (fun y hy => hr y (List.mem_cons_of_mem _ hy))
    refine (ExecLe.loop_norm (h1.seq_norm h2) ih).cast ?_ ?_
    · congr 1
      simp only [List.dropLast_cons_cons, List.getLastD_cons, List.length_cons,
        List.replicate_succ', List.append_assoc]
      rfl
    · have := hr1.2
      simp only [fpup_len_rv_uRow, List.length_cons] at this ⊢
      nlinarith

/-! ## Division by three -/

def srp_D2 : Cmd := .pop 4 .brk (.push 8 false) (.push 8 false)
def srp_D1 : Cmd := .pop 4 .brk srp_D2 srp_D2
def srp_div : Cmd := .loop (.pop 4 .brk srp_D1 srp_D1)

theorem srp_ex_div (o i rb p d ac x : Str) : ∀ (n : ℕ) (k : Str),
    ExecLe srp_div (srp_st o i rb (List.replicate n false) p d ac k x)
      (.norm (srp_st o i rb [] p d ac (List.replicate (n / 3) false ++ k) x)) (2 * n + 4)
  | 0, k => (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast (by simp) (by omega)
  | 1, k => (ExecLe.loop_brk (ExecLe.pop_same (s := []) rfl
      (ExecLe.pop_nil (by rw [srp_u4]; rfl) (ExecLe.brk _)))).cast
      (by rw [srp_u4]; simp) (by omega)
  | 2, k => (ExecLe.loop_brk (ExecLe.pop_same (s := [false]) rfl
      (ExecLe.pop_same (s := []) (by rw [srp_u4]; rfl)
      (ExecLe.pop_nil (by rw [srp_u4, srp_u4]; rfl) (ExecLe.brk _))))).cast
      (by rw [srp_u4, srp_u4]; simp) (by omega)
  | n + 3, k => by
    have hb : ExecLe (.pop 4 .brk srp_D1 srp_D1)
        (srp_st o i rb (List.replicate (n + 3) false) p d ac k x)
        (.norm (srp_st o i rb (List.replicate n false) p d ac (false :: k) x)) 4 := by
      refine ExecLe.pop_same (s := List.replicate (n + 2) false) rfl ?_
      rw [srp_u4]
      refine ExecLe.pop_same (s := List.replicate (n + 1) false) rfl ?_
      rw [srp_u4]
      refine ExecLe.pop_same (s := List.replicate n false) rfl ?_
      rw [srp_u4]
      exact (ExecLe.push 8 false _).cast (by rw [srp_u8, srp_st8]) le_rfl
    have ih := srp_ex_div o i rb p d ac x n (false :: k)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    congr 1
    rw [show (n + 3) / 3 = n / 3 + 1 by omega, List.replicate_succ', List.append_assoc]
    rfl

/-! ## Multiplication -/

def srp_mul : Cmd := .loop (.pop 4 .brk (copyVia 5 6 3) (copyVia 5 6 3))

theorem srp_ex_mul (o i rb p ac k x : Str) : ∀ (n : ℕ) (d : Str),
    ExecLe srp_mul (srp_st o i rb (List.replicate n false) p d ac k x)
      (.norm (srp_st o i rb [] p ((List.replicate n p).flatten ++ d) ac k x))
      (n * (5 * p.length + 5) + 2)
  | 0, d => (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast (by simp) (by omega)
  | n + 1, d => by
    have hb : ExecLe (.pop 4 .brk (copyVia 5 6 3) (copyVia 5 6 3))
        (srp_st o i rb (List.replicate (n + 1) false) p d ac k x)
        (.norm (srp_st o i rb (List.replicate n false) p (p ++ d) ac k x))
        (5 * p.length + 5) := by
      refine ExecLe.pop_same (s := List.replicate n false) rfl ?_
      rw [srp_u4]
      exact (srp_ex_cp o i rb _ p d ac k x (a := 5) (b := 6) (by decide) (by decide)
        (by decide)).cast (by rw [srp_u6, srp_st5, srp_st6]) (by simp)
    have ih := srp_ex_mul o i rb p ac k x n (p ++ d)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by nlinarith)
    congr 1
    rw [List.replicate_succ', List.flatten_append]; simp

/-! ## Popping one bit -/

def srp_p1 : Cmd := .pop 8 .skip .skip .skip

theorem srp_ex_p1 (o i rb c p d ac x : Str) (n : ℕ) :
    ExecLe srp_p1 (srp_st o i rb c p d ac (List.replicate n false) x)
      (.norm (srp_st o i rb c p d ac (List.replicate (n - 1) false) x)) 2 := by
  rcases n with _ | n
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast rfl le_rfl
  · exact (ExecLe.pop_same (s := List.replicate n false) rfl (ExecLe.skip _)).cast
      (by rw [srp_u8]; rfl) le_rfl

end Pnp.Karp.SeqRD
