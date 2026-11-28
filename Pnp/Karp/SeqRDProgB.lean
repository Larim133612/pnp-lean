import Pnp.Karp.SeqRDProgA

/-!
# The unary scheduling reduction program, part B: the item loop and the separator loop

* `srp_itL`: for every row `r` but the last one, print the task `(|r|, 0, D)`
  (`D` from stack `6`);
* `srp_sL`: for `t` bits on stack `8`, print the separators `(1, A - 1, A)` with the
  accumulator `A = (j + 1) P` on stack `7`, adding `P` (stack `5`) each time.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.SeqRD

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.ThreePartU Pnp.Karp.ThreePart Pnp.Karp.FourPartU

/-! ## Printing an item task -/

def srp_pr : Cmd :=
  .seq (copyVia 2 0 3) (.seq (drain 2) (.seq (pushList 0 (rv [sep, sep]))
    (.seq (copyVia 6 0 3) (pushList 0 (rv [sep])))))

theorem srp_ex_pr (D n : ℕ) (E : List SatSym) (i c p ac k x : Str) :
    ExecLe srp_pr (srp_st (rv E) i (rv (uRow n)) c p (rv (uRow D)) ac k x)
      (.norm (srp_st (rv (E ++ (task n 0 D).flatMap (· ++ [sep]))) i [] c p (rv (uRow D)) ac k x))
      (20 * n + 10 * D + 30) := by
  have h1 := srp_ex_cp (rv E) i (rv (uRow n)) c p (rv (uRow D)) ac k x (a := 2) (b := 0)
    (by decide) (by decide) (by decide)
  simp only [srp_u0, srp_st2, srp_st0, ← rv_append] at h1
  have h2 := srp_ex_dr2 (rv (E ++ uRow n)) i (rv (uRow n)) c p (rv (uRow D)) ac k x
  have h3 := srp_ex_em i [] c p (rv (uRow D)) ac k x (E ++ uRow n) [sep, sep]
  have h4 := srp_ex_cp (rv (E ++ uRow n ++ [sep, sep])) i [] c p (rv (uRow D)) ac k x
    (a := 6) (b := 0) (by decide) (by decide) (by decide)
  simp only [srp_u0, srp_st6, srp_st0, ← rv_append] at h4
  have h5 := srp_ex_em i [] c p (rv (uRow D)) ac k x (E ++ uRow n ++ [sep, sep] ++ uRow D) [sep]
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm h5)))).cast ?_ ?_
  · congr 2; simp [task, uRow]
  · simp only [fpup_len_rv_uRow, List.length_cons, List.length_nil]; omega

/-! ## The item loop -/

def srp_itL : Cmd := .loop (.seq fpup_rdRow (tpp_pk 1 srp_pr))

/-- The printed item tasks. -/
def srp_itO (D : ℕ) (rows : List (List SatSym)) : List SatSym :=
  (rows.dropLast.flatMap (fun r => task r.length 0 D)).flatMap (· ++ [sep])

theorem srp_ex_itL (D Z : ℕ) (c p ac k x : Str) : ∀ (rows : List (List SatSym)) (E : List SatSym),
    (∀ r ∈ rows, sep ∉ r ∧ r.length ≤ Z) →
    ExecLe srp_itL (srp_st (rv E) (fpup_code rows) [] c p (rv (uRow D)) ac k x)
      (.norm (srp_st (rv (E ++ srp_itO D rows)) [] (rv (uRow (rows.getLastD []).length)) c p
        (rv (uRow D)) ac k x))
      ((rows.length + 1) * (30 * Z + 10 * D + 40))
  | [], E, _ => by
    have h1 := fpup_ex_rdRow_nil (srp_st (rv E) (fpup_code []) [] c p (rv (uRow D)) ac k x) rfl
    have h2 : ExecLe (tpp_pk 1 srp_pr) (srp_st (rv E) (fpup_code []) [] c p (rv (uRow D)) ac k x)
        (.brk (srp_st (rv E) (fpup_code []) [] c p (rv (uRow D)) ac k x)) 2 :=
      ExecLe.pop_nil rfl (ExecLe.brk _)
    refine (ExecLe.loop_brk (h1.seq_norm h2)).cast ?_ (by simp)
    simp [srp_itO, fpup_code, uRow]
  | [r], E, hr => by
    have hr1 := hr r List.mem_cons_self
    have h1 := fpup_ex_rdRow r [] (srp_st (rv E) (fpup_code [r]) [] c p (rv (uRow D)) ac k x)
      hr1.1 (by simp [fpup_code])
    rw [srp_u1, srp_u2] at h1
    simp only [srp_st2, List.append_nil] at h1
    have h2 : ExecLe (tpp_pk 1 srp_pr)
        (srp_st (rv E) [] (rv (uRow r.length)) c p (rv (uRow D)) ac k x)
        (.brk (srp_st (rv E) [] (rv (uRow r.length)) c p (rv (uRow D)) ac k x)) 2 :=
      ExecLe.pop_nil rfl (ExecLe.brk _)
    refine (ExecLe.loop_brk (h1.seq_norm h2)).cast ?_ ?_
    · simp [srp_itO]
    · simp only [List.length_cons, List.length_nil]; nlinarith
  | r :: r' :: rs, E, hr => by
    have hr1 := hr r List.mem_cons_self
    have h1 := fpup_ex_rdRow r (fpup_code (r' :: rs))
      (srp_st (rv E) (fpup_code (r :: r' :: rs)) [] c p (rv (uRow D)) ac k x) hr1.1
      (by rw [fpup_code_cons]; rfl)
    rw [srp_u1, srp_u2] at h1
    simp only [srp_st2, List.append_nil] at h1
    obtain ⟨b, M', hbm⟩ : ∃ b M', fpup_code (r' :: rs) = b :: M' := by
      rw [fpup_code_cons]
      rcases r' with _ | ⟨s, r'⟩
      · exact ⟨_, _, rfl⟩
      · cases s <;> exact ⟨_, _, rfl⟩
    have h2 := tpp_ex_pk (srp_st (rv E) (fpup_code (r' :: rs)) (rv (uRow r.length)) c p
      (rv (uRow D)) ac k x) (k := 1) hbm (srp_ex_pr D r.length E _ c p ac k x)
    have ih := srp_ex_itL D Z c p ac k x (r' :: rs)
      (E ++ (task r.length 0 D).flatMap (· ++ [sep]))
      (fun y hy => hr y (List.mem_cons_of_mem _ hy))
    refine (ExecLe.loop_norm (h1.seq_norm h2) ih).cast ?_ ?_
    · congr 2
      · simp [srp_itO, List.flatMap_append]
    · have := hr1.2
      simp only [List.length_cons] at this ⊢
      nlinarith

/-! ## Printing a separator task -/

def srp_sb : Cmd :=
  .seq (pushList 0 (rv [pos, sep])) (.seq (copyVia 7 0 3) (.seq (srp_p2 0)
    (.seq (pushList 0 (rv [sep])) (.seq (copyVia 7 0 3) (.seq (pushList 0 (rv [sep]))
    (copyVia 5 7 3))))))

theorem srp_ex_sb (P A : ℕ) (hA : 1 ≤ A) (E : List SatSym) (i rb c d k x : Str) :
    ExecLe srp_sb (srp_st (rv E) i rb c (rv (uRow P)) d (rv (uRow A)) k x)
      (.norm (srp_st (rv (E ++ (task 1 (A - 1) A).flatMap (· ++ [sep]))) i rb c (rv (uRow P)) d
        (rv (uRow (P + A))) k x))
      (20 * A + 10 * P + 40) := by
  obtain ⟨A, rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
  have h1 := srp_ex_em i rb c (rv (uRow P)) d (rv (uRow (A + 1))) k x E [pos, sep]
  have h2 := srp_ex_cp (rv (E ++ [pos, sep])) i rb c (rv (uRow P)) d (rv (uRow (A + 1))) k x
    (a := 7) (b := 0) (by decide) (by decide) (by decide)
  simp only [srp_u0, srp_st7, srp_st0, ← rv_append] at h2
  have h3 := srp_ex_p2 0 (srp_st (rv (E ++ [pos, sep] ++ uRow (A + 1))) i rb c (rv (uRow P)) d
    (rv (uRow (A + 1))) k x) (rv (E ++ [pos, sep] ++ uRow A)) (by
      rw [srp_st0, ← rv_append]; congr 1
      simp [uRow, List.replicate_succ'])
  rw [srp_u0] at h3
  have h4 := srp_ex_em i rb c (rv (uRow P)) d (rv (uRow (A + 1))) k x
    (E ++ [pos, sep] ++ uRow A) [sep]
  have h5 := srp_ex_cp (rv (E ++ [pos, sep] ++ uRow A ++ [sep])) i rb c (rv (uRow P)) d
    (rv (uRow (A + 1))) k x (a := 7) (b := 0) (by decide) (by decide) (by decide)
  simp only [srp_u0, srp_st7, srp_st0, ← rv_append] at h5
  have h6 := srp_ex_em i rb c (rv (uRow P)) d (rv (uRow (A + 1))) k x
    (E ++ [pos, sep] ++ uRow A ++ [sep] ++ uRow (A + 1)) [sep]
  have h7 := srp_ex_cp (rv (E ++ [pos, sep] ++ uRow A ++ [sep] ++ uRow (A + 1) ++ [sep])) i rb c
    (rv (uRow P)) d (rv (uRow (A + 1))) k x (a := 5) (b := 7) (by decide) (by decide)
    (by decide)
  simp only [srp_u7, srp_st7, srp_st5, ← fpup_rv_uRow_add] at h7
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm
    (h6.seq_norm h7)))))).cast ?_ ?_
  · congr 2; simp [task, uRow]
  · simp only [fpup_len_rv_uRow, List.length_cons, List.length_nil]; omega

/-! ## The separator loop -/

def srp_sL : Cmd := .loop (.pop 8 .brk srp_sb srp_sb)

/-- The printed separator tasks `j + 1, …, j + t`. -/
def srp_sO (P : ℕ) : ℕ → ℕ → List SatSym
  | _, 0 => []
  | j, t + 1 => (task 1 ((j + 1) * P - 1) ((j + 1) * P)).flatMap (· ++ [sep]) ++ srp_sO P (j + 1) t

theorem srp_sO_eq (P : ℕ) : ∀ (t j : ℕ), srp_sO P j t =
    ((List.range t).flatMap (fun i => task 1 ((j + i + 1) * P - 1) ((j + i + 1) * P))).flatMap
      (· ++ [sep])
  | 0, j => by simp [srp_sO]
  | t + 1, j => by
    rw [srp_sO, srp_sO_eq P t (j + 1), List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map, List.flatMap_append]
    simp only [show ∀ i, j + 1 + i + 1 = j + (i + 1) + 1 from fun i => by omega, Nat.add_zero]

theorem srp_ex_sL (P Z : ℕ) (hP : 1 ≤ P) (i rb c d x : Str) : ∀ (t j : ℕ) (E : List SatSym),
    (j + t + 1) * P ≤ Z →
    ExecLe srp_sL (srp_st (rv E) i rb c (rv (uRow P)) d (rv (uRow ((j + 1) * P)))
        (List.replicate t false) x)
      (.norm (srp_st (rv (E ++ srp_sO P j t)) i rb c (rv (uRow P)) d
        (rv (uRow ((j + t + 1) * P))) [] x))
      (t * (30 * Z + 50) + 2)
  | 0, j, E, _ => (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [srp_sO]) (by omega)
  | t + 1, j, E, hZ => by
    have hA : 1 ≤ (j + 1) * P := by nlinarith
    have hb : ExecLe (.pop 8 .brk srp_sb srp_sb)
        (srp_st (rv E) i rb c (rv (uRow P)) d (rv (uRow ((j + 1) * P)))
          (List.replicate (t + 1) false) x)
        (.norm (srp_st (rv (E ++ (task 1 ((j + 1) * P - 1) ((j + 1) * P)).flatMap (· ++ [sep])))
          i rb c (rv (uRow P)) d (rv (uRow ((j + 1 + 1) * P))) (List.replicate t false) x))
        (20 * ((j + 1) * P) + 10 * P + 41) := by
      refine ExecLe.pop_same (s := List.replicate t false) rfl ?_
      rw [srp_u8]
      exact (srp_ex_sb P ((j + 1) * P) hA E i rb c d _ x).cast
        (by rw [show P + (j + 1) * P = (j + 1 + 1) * P by ring]) le_rfl
    have ih := srp_ex_sL P Z hP i rb c d x t (j + 1)
      (E ++ (task 1 ((j + 1) * P - 1) ((j + 1) * P)).flatMap (· ++ [sep]))
      (by rw [show j + 1 + t + 1 = j + (t + 1) + 1 by omega]; exact hZ)
    refine (ExecLe.loop_norm hb ih).cast ?_ ?_
    · congr 1
      rw [srp_sO, show j + 1 + t + 1 = j + (t + 1) + 1 by omega, List.append_assoc]
    · have e1 : (j + 1) * P ≤ Z := le_trans (Nat.mul_le_mul_right _ (by omega)) hZ
      have e2 : P ≤ Z := le_trans (by nlinarith) e1
      nlinarith

end Pnp.Karp.SeqRD
