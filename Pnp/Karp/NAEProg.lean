import Pnp.Karp.NAE
import Pnp.Karp.ThreeSATProg
import Pnp.CookLevin.FunBridge

/-!
# A polynomial-time program for the NAE-3SAT instance `naeI`

`nap_cmd`: a stack program computing `naeI` (stacks as in `Pnp/Karp/ThreeSATProg.lean`:
`0` input, `1` output, `2` unary `j`, `3` unary `d`, `4` temporary; `nap_E3` emits three
`zero`s per counter mark), in time `O(n²)`.  `sat_le_nae_of` turns it into the official
reduction SAT ≤ₚ NAE-3SAT, given the correctness of `naeI`.
-/

namespace Pnp.Karp.NAE

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.ThreeSAT

/-- The output block of a list of NAE clauses. -/
abbrev nap_blk (L : List NC) : List SatSym := (L.map NC.dense).flatMap (· ++ [sep])

theorem nap_c1z (j d : ℕ) : (c1 zero j d).dense =
    [pos] ++ List.replicate (3 * j) zero ++ List.replicate (3 * d) zero ++ [zero, pos, pos] := by
  simp [c1, NC.dense, mul_add, List.replicate_add, List.replicate_succ',
    -List.replicate_append_replicate]

theorem nap_c1 {s : SatSym} (hs : s ≠ zero) (j d : ℕ) : (c1 s j d).dense =
    List.replicate (3 * j) zero ++ [zero, s] ++ List.replicate (3 * d) zero ++ [pos, pos] := by
  simp [c1, hs, NC.dense, List.replicate_succ']

theorem nap_c2 (j d : ℕ) : (c2 j d).dense =
    [pos] ++ List.replicate (3 * j) zero ++ List.replicate (3 * d) zero ++
      [zero, zero, neg, zero, neg] := by
  simp [c2, NC.dense, mul_add, List.replicate_add, List.replicate_succ',
    -List.replicate_append_replicate]

theorem nap_sA (j d : ℕ) : (sA j d).dense =
    [pos] ++ List.replicate (3 * j) zero ++ List.replicate (3 * d) zero ++ [zero, pos] := by
  simp [sA, NC.dense, two, mul_add, List.replicate_add, List.replicate_succ',
    -List.replicate_append_replicate]

theorem nap_sB (j d : ℕ) : (sB j d).dense =
    [pos] ++ List.replicate (3 * j) zero ++ List.replicate (3 * d) zero ++
      [zero, zero, zero, zero, neg] := by
  simp [sB, NC.dense, two, mul_add, List.replicate_add, List.replicate_succ',
    -List.replicate_append_replicate]

theorem nap_naeI (w : List SatSym) : naeI w = [pos, zero, neg, sep] ++ nap_blk (goN w 0 0) := by
  simp [naeI, NCs, NC.dense, two]

/-! ## Emitting `3·|stack|` zeros -/

/-- Loop of `nap_E3`: three `zero`s per mark of stack `a`, marks moved to stack `4`. -/
def nap_E3Loop (a : ℕ) : Cmd :=
  .loop (.pop a .brk (.seq (.push 4 true) (emitL [zero, zero, zero]))
    (.seq (.push 4 true) (emitL [zero, zero, zero])))

/-- Emit `3·|σ a|` `zero` symbols (stack `a` holds marks, is restored). -/
def nap_E3 (a : ℕ) : Cmd := .seq (nap_E3Loop a) (move 4 a)

theorem nap_exec_E3Loop {a : ℕ} (ha1 : a ≠ 1) (ha4 : a ≠ 4) : ∀ (m k : ℕ) (O : List SatSym)
    (σ : ℕ → Str), σ a = List.replicate m true → σ 4 = List.replicate k true → σ 1 = enc O →
    ExecLe (nap_E3Loop a) σ (.norm (update (update (update σ a []) 4
      (List.replicate (m + k) true)) 1 (enc (O ++ List.replicate (3 * m) zero)))) (9 * m + 2)
  | 0, k, O, σ, h, h4, h1 => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk σ))).cast
      (by
        congr 1; funext j; simp only [update_apply]
        split_ifs <;> simp_all) (by simp)
  | m + 1, k, O, σ, h, h4, h1 => by
    have h' : σ a = true :: List.replicate m true := by rw [h, List.replicate_succ]
    let σ' := update (update (update σ a (List.replicate m true)) 4
      (List.replicate (k + 1) true)) 1 (enc (O ++ [zero, zero, zero]))
    have hb : ExecLe (.pop a .brk (.seq (.push 4 true) (emitL [zero, zero, zero]))
        (.seq (.push 4 true) (emitL [zero, zero, zero]))) σ (.norm σ') (1 + 7 + 1) :=
      ExecLe.pop_cons h' ((ExecLe.seq_norm (ExecLe.push 4 true _)
        (exec_emitL [zero, zero, zero] O _ (by
          rw [update_of_ne (by decide), update_of_ne (Ne.symm ha1), h1]))).cast
          (by
            rw [show update σ a (List.replicate m true) 4 = List.replicate k true by
              rw [update_of_ne (Ne.symm ha4), h4]]
            rfl) (by simp))
    have ih := nap_exec_E3Loop ha1 ha4 m (k + 1) (O ++ [zero, zero, zero]) σ'
      (by simp [σ', ha1, ha4]) (by simp [σ']) (by simp [σ'])
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    congr 1; funext j; simp only [σ', update_apply]
    have ez : O ++ [zero, zero, zero] ++ List.replicate (3 * m) zero =
        O ++ List.replicate (3 * (m + 1)) zero := by
      rw [show 3 * (m + 1) = 3 + 3 * m by ring, List.replicate_add, List.append_assoc]; rfl
    rw [ez, show m + (k + 1) = m + 1 + k by omega]
    split_ifs <;> rfl

theorem nap_exec_E3 {a : ℕ} (ha1 : a ≠ 1) (ha4 : a ≠ 4) (m : ℕ) (O : List SatSym)
    (σ : ℕ → Str) (h : σ a = List.replicate m true) (h4 : σ 4 = []) (h1 : σ 1 = enc O) :
    ExecLe (nap_E3 a) σ (.norm (update σ 1 (enc (O ++ List.replicate (3 * m) zero))))
      (11 * m + 4) := by
  have hl := nap_exec_E3Loop ha1 ha4 m 0 O σ h (by simp [h4]) h1
  have hm := exec_move (a := 4) (b := a) (Ne.symm ha4) (List.replicate m true)
    (update (update (update σ a []) 4 (List.replicate (m + 0) true)) 1
      (enc (O ++ List.replicate (3 * m) zero))) (by simp)
  refine (ExecLe.seq_norm hl (ExecLe.of hm)).cast ?_ (by simp; omega)
  congr 1; funext j; simp only [update_apply]
  split_ifs <;> simp_all

theorem nap_ex2 (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str) :
    ExecLe (nap_E3 2) (S r O j d τ)
      (.norm (S r (O ++ List.replicate (3 * j) zero) j d τ)) (11 * j + 4) :=
  (nap_exec_E3 (by decide) (by decide) j O _ (S_2 ..) (S_4 ..) (S_1 ..)).cast
    (by rw [S_upd1]) le_rfl

theorem nap_ex3 (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str) :
    ExecLe (nap_E3 3) (S r O j d τ)
      (.norm (S r (O ++ List.replicate (3 * d) zero) j d τ)) (11 * d + 4) :=
  (nap_exec_E3 (by decide) (by decide) d O _ (S_3 ..) (S_4 ..) (S_1 ..)).cast
    (by rw [S_upd1]) le_rfl

/-! ## One input symbol -/

/-- The symbol `zero`: emit `c1 zero j d`, `c2 j d`; `j := j + 1`. -/
def nap_nsZ : Cmd :=
  .seq (emitL [pos]) (.seq (nap_E3 2) (.seq (nap_E3 3) (.seq (emitL [zero, pos, pos, sep, pos])
    (.seq (nap_E3 2) (.seq (nap_E3 3) (.seq (emitL [zero, zero, neg, zero, neg, sep])
      (.push 2 true)))))))

/-- A literal symbol `s`: emit `c1 s j d`, `c2 j d`; `j := j + 1`. -/
def nap_nsL (s : SatSym) : Cmd :=
  .seq (nap_E3 2) (.seq (emitL [zero, s]) (.seq (nap_E3 3) (.seq (emitL [pos, pos, sep, pos])
    (.seq (nap_E3 2) (.seq (nap_E3 3) (.seq (emitL [zero, zero, neg, zero, neg, sep])
      (.push 2 true)))))))

/-- A separator: emit `sA j d`, `sB j d`; `j := 0`, `d := j + d + 1`. -/
def nap_sep : Cmd :=
  .seq (emitL [pos]) (.seq (nap_E3 2) (.seq (nap_E3 3) (.seq (emitL [zero, pos, sep, pos])
    (.seq (nap_E3 2) (.seq (nap_E3 3) (.seq (emitL [zero, zero, zero, zero, neg, sep])
      (.seq (move 2 3) (.push 3 true))))))))

theorem nap_ex_nsZ (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str) :
    ExecLe nap_nsZ (S r O j d τ)
      (.norm (S r (O ++ ((c1 zero j d).dense ++ [sep] ++ ((c2 j d).dense ++ [sep]))) (j + 1) d τ))
      (40 * (j + d) + 77) := by
  have h1 := ex_emitL [pos] r O j d τ
  have h2 := nap_ex2 r (O ++ [pos]) j d τ
  have h3 := nap_ex3 r (O ++ [pos] ++ List.replicate (3 * j) zero) j d τ
  set O1 := O ++ [pos] ++ List.replicate (3 * j) zero ++ List.replicate (3 * d) zero
  have h4 := ex_emitL [zero, pos, pos, sep, pos] r O1 j d τ
  set O2 := O1 ++ [zero, pos, pos, sep, pos]
  have h5 := nap_ex2 r O2 j d τ
  have h6 := nap_ex3 r (O2 ++ List.replicate (3 * j) zero) j d τ
  set O3 := O2 ++ List.replicate (3 * j) zero ++ List.replicate (3 * d) zero
  have h7 := ex_emitL [zero, zero, neg, zero, neg, sep] r O3 j d τ
  have h8 := ExecLe.push 2 true (S r (O3 ++ [zero, zero, neg, zero, neg, sep]) j d τ)
  rw [S_2, show true :: List.replicate j true = List.replicate (j + 1) true from rfl,
    S_upd2] at h8
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm (h6.seq_norm
    (h7.seq_norm h8))))))).cast ?_ (by simp; omega)
  rw [nap_c1z, nap_c2]
  simp only [O3, O2, O1, List.append_assoc, List.cons_append, List.nil_append]

theorem nap_ex_nsL {s : SatSym} (hs : s ≠ zero) (r : Str) (O : List SatSym) (j d : ℕ)
    (τ : ℕ → Str) :
    ExecLe (nap_nsL s) (S r O j d τ)
      (.norm (S r (O ++ ((c1 s j d).dense ++ [sep] ++ ((c2 j d).dense ++ [sep]))) (j + 1) d τ))
      (40 * (j + d) + 77) := by
  have h1 := nap_ex2 r O j d τ
  have h2 := ex_emitL [zero, s] r (O ++ List.replicate (3 * j) zero) j d τ
  have h3 := nap_ex3 r (O ++ List.replicate (3 * j) zero ++ [zero, s]) j d τ
  set O1 := O ++ List.replicate (3 * j) zero ++ [zero, s] ++ List.replicate (3 * d) zero
  have h4 := ex_emitL [pos, pos, sep, pos] r O1 j d τ
  set O2 := O1 ++ [pos, pos, sep, pos]
  have h5 := nap_ex2 r O2 j d τ
  have h6 := nap_ex3 r (O2 ++ List.replicate (3 * j) zero) j d τ
  set O3 := O2 ++ List.replicate (3 * j) zero ++ List.replicate (3 * d) zero
  have h7 := ex_emitL [zero, zero, neg, zero, neg, sep] r O3 j d τ
  have h8 := ExecLe.push 2 true (S r (O3 ++ [zero, zero, neg, zero, neg, sep]) j d τ)
  rw [S_2, show true :: List.replicate j true = List.replicate (j + 1) true from rfl,
    S_upd2] at h8
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm (h6.seq_norm
    (h7.seq_norm h8))))))).cast ?_ (by simp; omega)
  rw [nap_c1 hs, nap_c2]
  simp only [O3, O2, O1, List.append_assoc, List.cons_append, List.nil_append]

theorem nap_ex_sep (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str) :
    ExecLe nap_sep (S r O j d τ)
      (.norm (S r (O ++ ((sA j d).dense ++ [sep] ++ ((sB j d).dense ++ [sep]))) 0 (j + d + 1) τ))
      (40 * (j + d) + 77) := by
  have h1 := ex_emitL [pos] r O j d τ
  have h2 := nap_ex2 r (O ++ [pos]) j d τ
  have h3 := nap_ex3 r (O ++ [pos] ++ List.replicate (3 * j) zero) j d τ
  set O1 := O ++ [pos] ++ List.replicate (3 * j) zero ++ List.replicate (3 * d) zero
  have h4 := ex_emitL [zero, pos, sep, pos] r O1 j d τ
  set O2 := O1 ++ [zero, pos, sep, pos]
  have h5 := nap_ex2 r O2 j d τ
  have h6 := nap_ex3 r (O2 ++ List.replicate (3 * j) zero) j d τ
  set O3 := O2 ++ List.replicate (3 * j) zero ++ List.replicate (3 * d) zero
  have h7 := ex_emitL [zero, zero, zero, zero, neg, sep] r O3 j d τ
  set O4 := O3 ++ [zero, zero, zero, zero, neg, sep]
  have h8 := exec_move (a := 2) (b := 3) (by decide) _ (S r O4 j d τ) (S_2 ..)
  rw [S_3, List.reverse_replicate, List.replicate_append_replicate,
    show ([] : Str) = List.replicate 0 true from rfl, S_upd2, S_upd3] at h8
  have h9 := ExecLe.push 3 true (S r O4 0 (j + d) τ)
  rw [S_3, show true :: List.replicate (j + d) true = List.replicate (j + d + 1) true from rfl,
    S_upd3] at h9
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm (h6.seq_norm
    (h7.seq_norm ((ExecLe.of h8).seq_norm h9)))))))).cast ?_ (by simp; omega)
  rw [nap_sA, nap_sB]
  simp only [O4, O3, O2, O1, List.append_assoc, List.cons_append, List.nil_append]

/-! ## The main loop -/

/-- Loop body: read one bit pair of the input. -/
def nap_body : Cmd :=
  .pop 0 .brk (.pop 0 .brk nap_sep nap_nsZ) (.pop 0 .brk (nap_nsL pos) (nap_nsL neg))

/-- The main loop. -/
def nap_main : Cmd := .loop nap_body

/-- The reduction program. -/
def nap_cmd : Cmd := .seq (emitL [pos, zero, neg, sep]) nap_main

theorem nap_step {a b : Bool} {r : Str} {O O' : List SatSym} {j d j' d' : ℕ} {τ : ℕ → Str}
    {T₁ : ℕ} (hb : ExecLe nap_body (S (a :: b :: r) O j d τ) (.norm (S r O' j' d' τ)) T₁)
    (hT : T₁ ≤ 40 * (j + d) + 79) (hjd : j' + d' = j + d + 1)
    (hO : O' ++ nap_blk (goN (FunBridge.dec2 r) j' d') =
      O ++ nap_blk (goN (FunBridge.dec2 (a :: b :: r)) j d))
    (ih : ∃ σ', ExecLe nap_main (S r O' j' d' τ) (.norm σ')
      (r.length * (40 * (j' + d' + r.length) + 80) + 3) ∧
      σ' 1 = enc (O' ++ nap_blk (goN (FunBridge.dec2 r) j' d'))) :
    ∃ σ', ExecLe nap_main (S (a :: b :: r) O j d τ) (.norm σ')
      ((a :: b :: r).length * (40 * (j + d + (a :: b :: r).length) + 80) + 3) ∧
      σ' 1 = enc (O ++ nap_blk (goN (FunBridge.dec2 (a :: b :: r)) j d)) := by
  obtain ⟨σ', h, h1⟩ := ih
  refine ⟨σ', (ExecLe.loop_norm hb h).cast rfl ?_, by rw [h1, hO]⟩
  rw [hjd]
  simp only [List.length_cons]
  nlinarith

theorem nap_exec_main : ∀ (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str),
    ∃ σ', ExecLe nap_main (S r O j d τ) (.norm σ')
      (r.length * (40 * (j + d + r.length) + 80) + 3) ∧
      σ' 1 = enc (O ++ nap_blk (goN (FunBridge.dec2 r) j d))
  | [], O, j, d, τ => ⟨_, (ExecLe.loop_brk (ExecLe.pop_nil (S_0 ..) (ExecLe.brk _))).cast rfl
      (by simp), by simp [FunBridge.dec2, goN, nap_blk]⟩
  | [false], O, j, d, τ => ⟨_, (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := []) (S_0 ..)
      (ExecLe.pop_nil (by simp) (ExecLe.brk _)))).cast rfl (by simp),
      by simp [FunBridge.dec2, goN, nap_blk]⟩
  | [true], O, j, d, τ => ⟨_, (ExecLe.loop_brk (ExecLe.pop_cons (b := true) (s := []) (S_0 ..)
      (ExecLe.pop_nil (by simp) (ExecLe.brk _)))).cast rfl (by simp),
      by simp [FunBridge.dec2, goN, nap_blk]⟩
  | false :: false :: r, O, j, d, τ =>
    nap_step (pop2 (by simpa using nap_ex_sep r O j d τ)) (by omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goN, nap_blk, List.append_assoc])
      (nap_exec_main r _ 0 (j + d + 1) τ)
  | false :: true :: r, O, j, d, τ =>
    nap_step (pop2 (by simpa using nap_ex_nsZ r O j d τ)) (by omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goN, nap_blk, List.append_assoc])
      (nap_exec_main r _ (j + 1) d τ)
  | true :: false :: r, O, j, d, τ =>
    nap_step (pop2 (by simpa using nap_ex_nsL (by decide) r O j d τ)) (by omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goN, nap_blk, List.append_assoc])
      (nap_exec_main r _ (j + 1) d τ)
  | true :: true :: r, O, j, d, τ =>
    nap_step (pop2 (by simpa using nap_ex_nsL (by decide) r O j d τ)) (by omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goN, nap_blk, List.append_assoc])
      (nap_exec_main r _ (j + 1) d τ)

theorem nap_exec_cmd (x : Str) : ∃ σ', ExecLe nap_cmd (init [x]).stk (.norm σ') (tb 5 x.length) ∧
    σ' 1 = ((naeI (FunBridge.dec2 x)).flatMap ic).reverse := by
  obtain ⟨σ', h, h1⟩ := nap_exec_main x [pos, zero, neg, sep] 0 0 (init [x]).stk
  have h0 := ex_emitL [pos, zero, neg, sep] x [] 0 0 (init [x]).stk
  rw [← init_eq_S] at h0
  refine ⟨σ', (h0.seq_norm h).cast rfl ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil, tb]
    set n := x.length
    have e : (n + 2) ^ 5 = n ^ 5 + 10 * n ^ 4 + 40 * n ^ 3 + 80 * n ^ 2 + 80 * n + 32 := by ring
    have h3 : n * (40 * (0 + 0 + n) + 80) = 40 * n ^ 2 + 80 * n := by ring
    omega
  · rw [h1, nap_naeI]; rfl

/-- **SAT ≤ₚ NAE-3SAT**, given the correctness of the instance `naeI`. -/
theorem sat_le_nae_of (h : ∀ w, SATLang w ↔ NAE3Lang (naeI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang NAE3Lang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    nap_cmd 1 5 (fun x => naeI (FunBridge.dec2 x)) nap_exec_cmd naeI
    (fun w => by
      show naeI w = naeI (FunBridge.dec2 (w.flatMap ic))
      rw [FunBridge.dec2_flatMap_ic])
  exact ⟨naeI, hc, fun w => h w⟩

end Pnp.Karp.NAE
