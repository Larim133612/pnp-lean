import Pnp.Karp.FourPartUProgA

/-!
# Unary 4-PARTITION reduction program, part B: the row loop and the filler loop

Stacks of the main phase (`fpup_st`): `0` the output `rv E`; `1` the code of the input rows;
`2` the row buffer (`rv (uRow |r|)`); `3` temporary; `4` the counter `false ^ c` of printed
rows; `5`, `6`, `7` the constants `rv (uRow (5 N))`, `rv (uRow (6 N))`, `rv (uRow (21 N))`.

* `fpup_rowL`: read each row; if more input follows, print `uRow (5 N + |r|) ++ [sep]`, count
  it, and continue; the last row stays in the buffer.
* `fpup_filL`: print `⌊c / 3⌋` fillers `uRow (6 N) ++ [sep]`.
* `fpup_fin`: print the last row `uRow (21 N + |last|) ++ [sep]`.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.FourPartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.ThreePartU Pnp.Karp.ThreePart

/-! ## The state -/

def fpup_st (o i rb c p5 p6 p21 : Str) : ℕ → Str := fun j =>
  if j = 0 then o else if j = 1 then i else if j = 2 then rb else if j = 4 then c
  else if j = 5 then p5 else if j = 6 then p6 else if j = 7 then p21 else []

/-- The state of the main phase for `N`. -/
abbrev fpup_ss (N : ℕ) (o i rb c : Str) : ℕ → Str :=
  fpup_st o i rb c (rv (uRow (5 * N))) (rv (uRow (6 * N))) (rv (uRow (21 * N)))

section
variable (o i rb c p5 p6 p21 v : Str)

@[simp] theorem fpup_st0 : fpup_st o i rb c p5 p6 p21 0 = o := rfl
@[simp] theorem fpup_st1 : fpup_st o i rb c p5 p6 p21 1 = i := rfl
@[simp] theorem fpup_st2 : fpup_st o i rb c p5 p6 p21 2 = rb := rfl
@[simp] theorem fpup_st3 : fpup_st o i rb c p5 p6 p21 3 = [] := rfl
@[simp] theorem fpup_st4 : fpup_st o i rb c p5 p6 p21 4 = c := rfl
@[simp] theorem fpup_st5 : fpup_st o i rb c p5 p6 p21 5 = p5 := rfl
@[simp] theorem fpup_st6 : fpup_st o i rb c p5 p6 p21 6 = p6 := rfl
@[simp] theorem fpup_st7 : fpup_st o i rb c p5 p6 p21 7 = p21 := rfl

theorem fpup_u0 : update (fpup_st o i rb c p5 p6 p21) 0 v = fpup_st v i rb c p5 p6 p21 := by
  funext j; simp only [fpup_st, update_apply]; split_ifs <;> simp_all
theorem fpup_u1 : update (fpup_st o i rb c p5 p6 p21) 1 v = fpup_st o v rb c p5 p6 p21 := by
  funext j; simp only [fpup_st, update_apply]; split_ifs <;> simp_all
theorem fpup_u2 : update (fpup_st o i rb c p5 p6 p21) 2 v = fpup_st o i v c p5 p6 p21 := by
  funext j; simp only [fpup_st, update_apply]; split_ifs <;> simp_all
theorem fpup_u4 : update (fpup_st o i rb c p5 p6 p21) 4 v = fpup_st o i rb v p5 p6 p21 := by
  funext j; simp only [fpup_st, update_apply]; split_ifs <;> simp_all

end

/-- The code of a list of rows. -/
def fpup_code (rows : List (List SatSym)) : Str := (rows.flatMap (· ++ [sep])).flatMap ic

@[simp] theorem fpup_ss2 (N : ℕ) (o i rb c : Str) : fpup_ss N o i rb c 2 = rb := rfl

/-! ## Step lemmas on the state -/

section
variable (o i rb c p5 p6 p21 : Str)

theorem fpup_ex_cp0 (k : ℕ) (hk0 : k ≠ 0) (hk3 : k ≠ 3) :
    ExecLe (copyVia k 0 3) (fpup_st o i rb c p5 p6 p21)
      (.norm (fpup_st (fpup_st o i rb c p5 p6 p21 k ++ o) i rb c p5 p6 p21))
      (5 * (fpup_st o i rb c p5 p6 p21 k).length + 4) :=
  (ExecLe.of (exec_copyVia hk0 hk3 (by decide) _ rfl)).cast (by rw [fpup_u0]; rfl) le_rfl

theorem fpup_ex_em (E L : List SatSym) :
    ExecLe (pushList 0 (rv L)) (fpup_st (rv E) i rb c p5 p6 p21)
      (.norm (fpup_st (rv (E ++ L)) i rb c p5 p6 p21)) (2 * L.length + 1) :=
  (ExecLe.of (exec_pushList 0 (rv L) _)).cast (by rw [fpup_u0, fpup_st0, rv_append])
    (by simp only [rv, List.length_reverse, length_flatMap_ic]; omega)

theorem fpup_ex_dr2 :
    ExecLe (drain 2) (fpup_st o i rb c p5 p6 p21) (.norm (fpup_st o i [] c p5 p6 p21))
      (2 * rb.length + 2) :=
  (ExecLe.of (exec_drain 2 rb _ rfl)).cast (by rw [fpup_u2]) le_rfl

theorem fpup_ex_p4 :
    ExecLe (.push 4 false) (fpup_st o i rb c p5 p6 p21) (.norm (fpup_st o i rb (false :: c) p5 p6 p21))
      1 :=
  (ExecLe.push 4 false _).cast (by rw [fpup_u4]; rfl) le_rfl

end

/-! ## Printing a non-last row -/

def fpup_pr : Cmd :=
  .seq (copyVia 5 0 3) (.seq (copyVia 2 0 3) (.seq (drain 2) (.seq (pushList 0 (rv [sep]))
    (.push 4 false))))

theorem fpup_ex_pr (N a : ℕ) (E : List SatSym) (i c : Str) :
    ExecLe fpup_pr (fpup_ss N (rv E) i (rv (uRow a)) c)
      (.norm (fpup_ss N (rv (E ++ (uRow (5 * N + a) ++ [sep]))) i [] (false :: c)))
      (50 * N + 14 * a + 14) := by
  have h1 := fpup_ex_cp0 (rv E) i (rv (uRow a)) c (rv (uRow (5 * N))) (rv (uRow (6 * N)))
    (rv (uRow (21 * N))) 5 (by decide) (by decide)
  have h2 := fpup_ex_cp0 (rv (E ++ uRow (5 * N))) i (rv (uRow a)) c (rv (uRow (5 * N)))
    (rv (uRow (6 * N))) (rv (uRow (21 * N))) 2 (by decide) (by decide)
  have h3 := fpup_ex_dr2 (rv (E ++ uRow (5 * N) ++ uRow a)) i (rv (uRow a)) c (rv (uRow (5 * N)))
    (rv (uRow (6 * N))) (rv (uRow (21 * N)))
  have h4 := fpup_ex_em i [] c (rv (uRow (5 * N))) (rv (uRow (6 * N))) (rv (uRow (21 * N)))
    (E ++ uRow (5 * N) ++ uRow a) [sep]
  have h5 := fpup_ex_p4 (rv (E ++ uRow (5 * N) ++ uRow a ++ [sep])) i [] c (rv (uRow (5 * N)))
    (rv (uRow (6 * N))) (rv (uRow (21 * N)))
  simp only [fpup_st5, fpup_st2, ← rv_append] at h1 h2
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm h5)))).cast ?_ ?_
  · congr 2
    unfold uRow; rw [List.replicate_add]; simp
  · simp only [fpup_len_rv_uRow, List.length_cons, List.length_nil]; omega

/-! ## The row loop -/

def fpup_rowL : Cmd := .loop (.seq fpup_rdRow (tpp_pk 1 fpup_pr))

/-- The printed non-last rows. -/
def fpup_rowsO (N : ℕ) (rows : List (List SatSym)) : List SatSym :=
  (rows.dropLast.map (fun r => uRow (5 * N + r.length))).flatMap (· ++ [sep])

theorem fpup_code_cons (r : List SatSym) (rows : List (List SatSym)) :
    fpup_code (r :: rows) = (r ++ [sep]).flatMap ic ++ fpup_code rows := by
  simp [fpup_code]

theorem fpup_ex_rowL (N Z : ℕ) (hN : N ≤ Z) : ∀ (rows : List (List SatSym)) (E : List SatSym)
    (c : Str), (∀ r ∈ rows, sep ∉ r ∧ r.length ≤ Z) →
    ExecLe fpup_rowL (fpup_ss N (rv E) (fpup_code rows) [] c)
      (.norm (fpup_ss N (rv (E ++ fpup_rowsO N rows)) [] (rv (uRow (rows.getLastD []).length))
        (List.replicate rows.dropLast.length false ++ c)))
      ((rows.length + 1) * (100 * Z + 100))
  | [], E, c, _ => by
    have h1 := fpup_ex_rdRow_nil (fpup_ss N (rv E) (fpup_code []) [] c) rfl
    have h2 : ExecLe (tpp_pk 1 fpup_pr) (fpup_ss N (rv E) (fpup_code []) [] c)
        (.brk (fpup_ss N (rv E) (fpup_code []) [] c)) 2 :=
      ExecLe.pop_nil rfl (ExecLe.brk _)
    refine (ExecLe.loop_brk (h1.seq_norm h2)).cast ?_ (by simp)
    simp [fpup_rowsO, fpup_code, uRow]
  | [r], E, c, hr => by
    have hr1 := hr r List.mem_cons_self
    have h1 := fpup_ex_rdRow r [] (fpup_ss N (rv E) (fpup_code [r]) [] c) hr1.1
      (by simp [fpup_code])
    rw [fpup_u1, fpup_u2] at h1
    have h2 : ExecLe (tpp_pk 1 fpup_pr) (fpup_ss N (rv E) [] (rv (uRow r.length) ++ []) c)
        (.brk (fpup_ss N (rv E) [] (rv (uRow r.length) ++ []) c)) 2 :=
      ExecLe.pop_nil rfl (ExecLe.brk _)
    refine (ExecLe.loop_brk (h1.seq_norm h2)).cast ?_ ?_
    · simp [fpup_rowsO]
    · simp only [List.length_cons, List.length_nil]; nlinarith
  | r :: r' :: rs, E, c, hr => by
    have hr1 := hr r List.mem_cons_self
    have h1 := fpup_ex_rdRow r (fpup_code (r' :: rs))
      (fpup_ss N (rv E) (fpup_code (r :: r' :: rs)) [] c) hr1.1 (by rw [fpup_code_cons]; rfl)
    rw [fpup_u1, fpup_u2] at h1
    simp only [fpup_ss2, List.append_nil] at h1
    obtain ⟨b, M', hbm⟩ : ∃ b M', fpup_code (r' :: rs) = b :: M' := by
      rw [fpup_code_cons]
      rcases r' with _ | ⟨s, r'⟩
      · exact ⟨_, _, rfl⟩
      · cases s <;> exact ⟨_, _, rfl⟩
    have h2 := tpp_ex_pk (fpup_ss N (rv E) (fpup_code (r' :: rs)) (rv (uRow r.length)) c)
      (k := 1) hbm (fpup_ex_pr N r.length E _ c)
    have ih := fpup_ex_rowL N Z hN (r' :: rs) (E ++ (uRow (5 * N + r.length) ++ [sep]))
      (false :: c) (fun x hx => hr x (List.mem_cons_of_mem _ hx))
    refine (ExecLe.loop_norm (h1.seq_norm h2) ih).cast ?_ ?_
    · congr 1
      simp only [fpup_rowsO, List.dropLast_cons_cons, List.map_cons, List.flatMap_cons,
        List.append_assoc, List.getLastD_cons, List.length_cons, List.replicate_succ',
        List.length_cons]
      rfl
    · have := hr1.2
      simp only [List.length_cons] at this ⊢
      nlinarith

/-! ## The filler loop -/

def fpup_fl : Cmd := .seq (copyVia 6 0 3) (pushList 0 (rv [sep]))
def fpup_F3 : Cmd := .pop 4 .brk fpup_fl fpup_fl
def fpup_F2 : Cmd := .pop 4 .brk fpup_F3 fpup_F3
def fpup_filL : Cmd := .loop (.pop 4 .brk fpup_F2 fpup_F2)

/-- The printed fillers. -/
def fpup_filO (N k : ℕ) : List SatSym := (List.replicate k (uRow (6 * N))).flatMap (· ++ [sep])

theorem fpup_ex_fl (N : ℕ) (E : List SatSym) (i rb c : Str) :
    ExecLe fpup_fl (fpup_ss N (rv E) i rb c)
      (.norm (fpup_ss N (rv (E ++ (uRow (6 * N) ++ [sep]))) i rb c)) (60 * N + 7) := by
  have h1 := fpup_ex_cp0 (rv E) i rb c (rv (uRow (5 * N))) (rv (uRow (6 * N)))
    (rv (uRow (21 * N))) 6 (by decide) (by decide)
  have h4 := fpup_ex_em i rb c (rv (uRow (5 * N))) (rv (uRow (6 * N))) (rv (uRow (21 * N)))
    (E ++ uRow (6 * N)) [sep]
  simp only [fpup_st6, ← rv_append] at h1
  refine (h1.seq_norm h4).cast ?_ ?_
  · simp
  · simp only [fpup_len_rv_uRow, List.length_cons, List.length_nil]; omega

theorem fpup_ex_filL (N : ℕ) (i rb : Str) : ∀ (c : ℕ) (E : List SatSym),
    ExecLe fpup_filL (fpup_ss N (rv E) i rb (List.replicate c false))
      (.norm (fpup_ss N (rv (E ++ fpup_filO N (c / 3))) i rb [])) ((c / 3 + 1) * (60 * N + 20))
  | 0, E => (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [fpup_filO]) (by omega)
  | 1, E => (ExecLe.loop_brk (ExecLe.pop_same (s := []) rfl
      (ExecLe.pop_nil (by rw [fpup_u4]; rfl) (ExecLe.brk _)))).cast
      (by rw [fpup_u4]; simp [fpup_filO]) (by omega)
  | 2, E => (ExecLe.loop_brk (ExecLe.pop_same (s := [false]) rfl
      (ExecLe.pop_same (s := []) (by rw [fpup_u4]; rfl)
      (ExecLe.pop_nil (by rw [fpup_u4, fpup_u4]; rfl) (ExecLe.brk _))))).cast
      (by rw [fpup_u4, fpup_u4]; simp [fpup_filO]) (by omega)
  | c + 3, E => by
    have hb : ExecLe (.pop 4 .brk fpup_F2 fpup_F2) (fpup_ss N (rv E) i rb
        (List.replicate (c + 3) false))
        (.norm (fpup_ss N (rv (E ++ (uRow (6 * N) ++ [sep]))) i rb (List.replicate c false)))
        (60 * N + 10) := by
      refine ExecLe.pop_same (s := List.replicate (c + 2) false) rfl ?_
      rw [fpup_u4]
      refine ExecLe.pop_same (s := List.replicate (c + 1) false) rfl ?_
      rw [fpup_u4]
      refine ExecLe.pop_same (s := List.replicate c false) rfl ?_
      rw [fpup_u4]
      exact fpup_ex_fl N E i rb _
    have ih := fpup_ex_filL N i rb c (E ++ (uRow (6 * N) ++ [sep]))
    refine (ExecLe.loop_norm hb ih).cast ?_ ?_
    · congr 1
      rw [show (c + 3) / 3 = c / 3 + 1 by omega]
      simp [fpup_filO, List.replicate_succ]
    · rw [show (c + 3) / 3 = c / 3 + 1 by omega]; nlinarith

/-! ## The last row -/

def fpup_fin : Cmd := .seq (copyVia 7 0 3) (.seq (copyVia 2 0 3) (pushList 0 (rv [sep])))

theorem fpup_ex_fin (N a : ℕ) (E : List SatSym) (i c : Str) :
    ∃ σ', ExecLe fpup_fin (fpup_ss N (rv E) i (rv (uRow a)) c) (.norm σ')
      (210 * N + 10 * a + 20) ∧ σ' 0 = rv (E ++ (uRow (21 * N + a) ++ [sep])) := by
  have h1 := fpup_ex_cp0 (rv E) i (rv (uRow a)) c (rv (uRow (5 * N))) (rv (uRow (6 * N)))
    (rv (uRow (21 * N))) 7 (by decide) (by decide)
  have h2 := fpup_ex_cp0 (rv (E ++ uRow (21 * N))) i (rv (uRow a)) c (rv (uRow (5 * N)))
    (rv (uRow (6 * N))) (rv (uRow (21 * N))) 2 (by decide) (by decide)
  have h4 := fpup_ex_em i (rv (uRow a)) c (rv (uRow (5 * N))) (rv (uRow (6 * N)))
    (rv (uRow (21 * N))) (E ++ uRow (21 * N) ++ uRow a) [sep]
  simp only [fpup_st7, fpup_st2, ← rv_append] at h1 h2
  refine ⟨_, (h1.seq_norm (h2.seq_norm h4)).mono ?_, ?_⟩
  · simp only [fpup_len_rv_uRow, List.length_cons, List.length_nil]; omega
  · rw [fpup_st0]; congr 1
    unfold uRow; rw [List.replicate_add]; simp

end Pnp.Karp.FourPartU
