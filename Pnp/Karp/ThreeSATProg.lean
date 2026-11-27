import Pnp.Karp.ThreeSATNP
import Pnp.CookLevin.FunBridge

/-!
# SAT ≤ₚ 3-SAT, and 3-SAT is NP-complete

`redCmd`: a stack program (`Pnp/Oracle/Struct.lean`) computing the reduction `red` of
`Pnp/Karp/ThreeSAT.lean` on the 2-bit internal code (`ic`) of its input.  Stacks: `0` input,
`1` output (internal codes, pushed in order), `2` unary `j` (position inside the current clause),
`3` unary `d = p - j`, `4` temporary.  Per input symbol it emits the clauses of `goC` by copying
the counters (`emitZ`: `2·|stack|` `zero` symbols) and pushing constant pieces (`emitL`); the
time is `O(n²)`.  `computable_of_cmd_code` turns it into an official polynomial-time
computation, giving `sat_le_sat3`; with `sat3_in_np` and
`Pnp.Karp.np_complete_of_sat_reduces` this proves `threeSat_np_complete`.
-/

namespace Pnp.Karp.ThreeSAT

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

/-! ## Output primitives -/

/-- The output stack holding (the internal code of) `O`. -/
def enc (O : List SatSym) : Str := (O.flatMap ic).reverse

theorem enc_append (O c : List SatSym) : enc (O ++ c) = (c.flatMap ic).reverse ++ enc O := by
  simp [enc]

/-- Push the code of the symbols `c` onto the output stack `1`. -/
def emitL (c : List SatSym) : Cmd := pushList 1 (c.flatMap ic).reverse

theorem exec_emitL (c O : List SatSym) (σ : ℕ → Str) (h : σ 1 = enc O) :
    ExecLe (emitL c) σ (.norm (update σ 1 (enc (O ++ c)))) (2 * c.length + 1) :=
  (ExecLe.of (exec_pushList 1 _ σ)).cast (by rw [h, enc_append])
    (by rw [List.length_reverse, length_flatMap_ic])

/-- Loop of `emitZ`: two `zero`s per mark of stack `a`, marks moved to stack `4`. -/
def emitZLoop (a : ℕ) : Cmd :=
  .loop (.pop a .brk (.seq (.push 4 true) (pushList 1 [true, false, true, false]))
    (.seq (.push 4 true) (pushList 1 [true, false, true, false])))

/-- Emit `2·|σ a|` `zero` symbols (stack `a` holds marks, is restored). -/
def emitZ (a : ℕ) : Cmd := .seq (emitZLoop a) (move 4 a)

theorem exec_emitZLoop {a : ℕ} (ha1 : a ≠ 1) (ha4 : a ≠ 4) : ∀ (m k : ℕ) (O : List SatSym)
    (σ : ℕ → Str), σ a = List.replicate m true → σ 4 = List.replicate k true → σ 1 = enc O →
    ExecLe (emitZLoop a) σ (.norm (update (update (update σ a []) 4
      (List.replicate (m + k) true)) 1 (enc (O ++ zs (2 * m))))) (7 * m + 2)
  | 0, k, O, σ, h, h4, h1 => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk σ))).cast
      (by
        congr 1; funext j; simp only [update_apply]
        split_ifs <;> simp_all) (by simp)
  | m + 1, k, O, σ, h, h4, h1 => by
    have h' : σ a = true :: List.replicate m true := by rw [h, List.replicate_succ]
    let σ' := update (update (update σ a (List.replicate m true)) 4
      (List.replicate (k + 1) true)) 1 (enc (O ++ [zero, zero]))
    have hb : ExecLe (.pop a .brk (.seq (.push 4 true) (pushList 1 [true, false, true, false]))
        (.seq (.push 4 true) (pushList 1 [true, false, true, false]))) σ (.norm σ') (1 + 5 + 1) :=
      ExecLe.pop_cons h' ((ExecLe.seq_norm (ExecLe.push 4 true _)
        (ExecLe.of (exec_pushList 1 _ _))).cast
          (by
            rw [show update σ a (List.replicate m true) 4 = List.replicate k true by
              rw [update_of_ne (Ne.symm ha4), h4]]
            rw [show update (update σ a (List.replicate m true)) 4
                (true :: List.replicate k true) 1 = enc O by
              rw [update_of_ne (by decide), update_of_ne (Ne.symm ha1), h1]]
            simp only [σ']
            rw [show enc (O ++ [zero, zero]) = [true, false, true, false] ++ enc O by
              simp [enc, ic]]
            rfl) (by simp))
    have ih := exec_emitZLoop ha1 ha4 m (k + 1) (O ++ [zero, zero]) σ'
      (by simp [σ', ha1, ha4]) (by simp [σ']) (by simp [σ'])
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    congr 1; funext j; simp only [σ', update_apply]
    have ez : O ++ [zero, zero] ++ zs (2 * m) = O ++ zs (2 * (m + 1)) := by
      show O ++ [zero, zero] ++ List.replicate (2 * m) zero = O ++ List.replicate (2 * (m + 1)) zero
      rw [show 2 * (m + 1) = 2 + 2 * m by ring, List.replicate_add, List.append_assoc]; rfl
    rw [ez, show m + (k + 1) = m + 1 + k by omega]
    split_ifs <;> rfl

theorem exec_emitZ {a : ℕ} (ha1 : a ≠ 1) (ha4 : a ≠ 4) (m : ℕ) (O : List SatSym) (σ : ℕ → Str)
    (h : σ a = List.replicate m true) (h4 : σ 4 = []) (h1 : σ 1 = enc O) :
    ExecLe (emitZ a) σ (.norm (update σ 1 (enc (O ++ zs (2 * m))))) (9 * m + 4) := by
  have hl := exec_emitZLoop ha1 ha4 m 0 O σ h (by simp [h4]) h1
  have hm := exec_move (a := 4) (b := a) (Ne.symm ha4) (List.replicate m true)
    (update (update (update σ a []) 4 (List.replicate (m + 0) true)) 1 (enc (O ++ zs (2 * m))))
    (by simp)
  refine (ExecLe.seq_norm hl (ExecLe.of hm)).cast ?_ (by simp; omega)
  congr 1; funext j; simp only [update_apply]
  split_ifs <;> simp_all

/-! ## The program state -/

/-- Program state: input rest `r`, output `O`, counters `j`, `d`, other stacks from `τ`. -/
def S (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str) : ℕ → Str :=
  update (update (update (update (update τ 0 r) 1 (enc O)) 2 (List.replicate j true)) 3
    (List.replicate d true)) 4 []

section S
variable (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str)

@[simp] theorem S_0 : S r O j d τ 0 = r := by simp [S]
@[simp] theorem S_1 : S r O j d τ 1 = enc O := by simp [S]
@[simp] theorem S_2 : S r O j d τ 2 = List.replicate j true := by simp [S]
@[simp] theorem S_3 : S r O j d τ 3 = List.replicate d true := by simp [S]
@[simp] theorem S_4 : S r O j d τ 4 = [] := by simp [S]

theorem S_upd0 (r' : Str) : update (S r O j d τ) 0 r' = S r' O j d τ := by
  funext k; simp only [S, update_apply]; split_ifs <;> simp_all

theorem S_upd1 (O' : List SatSym) : update (S r O j d τ) 1 (enc O') = S r O' j d τ := by
  funext k; simp only [S, update_apply]; split_ifs <;> simp_all

theorem S_upd2 (j' : ℕ) : update (S r O j d τ) 2 (List.replicate j' true) = S r O j' d τ := by
  funext k; simp only [S, update_apply]; split_ifs <;> simp_all

theorem S_upd3 (d' : ℕ) : update (S r O j d τ) 3 (List.replicate d' true) = S r O j d' τ := by
  funext k; simp only [S, update_apply]; split_ifs <;> simp_all

end S

theorem ex_emitZ2 (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str) :
    ExecLe (emitZ 2) (S r O j d τ) (.norm (S r (O ++ zs (2 * j)) j d τ)) (9 * j + 4) :=
  (exec_emitZ (by decide) (by decide) j O _ (S_2 ..) (S_4 ..) (S_1 ..)).cast
    (by rw [S_upd1]) le_rfl

theorem ex_emitZ3 (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str) :
    ExecLe (emitZ 3) (S r O j d τ) (.norm (S r (O ++ zs (2 * d)) j d τ)) (9 * d + 4) :=
  (exec_emitZ (by decide) (by decide) d O _ (S_3 ..) (S_4 ..) (S_1 ..)).cast
    (by rw [S_upd1]) le_rfl

theorem ex_emitL (c : List SatSym) (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str) :
    ExecLe (emitL c) (S r O j d τ) (.norm (S r (O ++ c) j d τ)) (2 * c.length + 1) :=
  (exec_emitL c O _ (S_1 ..)).cast (by rw [S_upd1]) le_rfl

/-! ## One input symbol -/

/-- A non-separator symbol `s`: emit the step clause, `j := j + 1`. -/
def nsCmd (s : SatSym) : Cmd :=
  .seq (emitZ 2) (.seq (emitL [s]) (.seq (emitZ 3) (.seq (emitL [pos, zero, neg, sep])
    (.push 2 true))))

/-- A separator: emit the clauses `y_p` and `¬y_{p+1}`, `j := 0`, `d := p + 1`. -/
def sepCmd : Cmd :=
  .seq (emitZ 2) (.seq (emitZ 3) (.seq (emitL [zero, pos, sep]) (.seq (emitZ 2) (.seq (emitZ 3)
    (.seq (emitL [zero, zero, zero, neg, sep]) (.seq (move 2 3) (.push 3 true)))))))

theorem ex_ns (s : SatSym) (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str) :
    ExecLe (nsCmd s) (S r O j d τ) (.norm (S r (O ++ (stp s j d ++ [sep])) (j + 1) d τ))
      (9 * j + 9 * d + 21) := by
  have h1 := ex_emitZ2 r O j d τ
  have h2 := ex_emitL [s] r (O ++ zs (2 * j)) j d τ
  have h3 := ex_emitZ3 r (O ++ zs (2 * j) ++ [s]) j d τ
  have h4 := ex_emitL [pos, zero, neg, sep] r (O ++ zs (2 * j) ++ [s] ++ zs (2 * d)) j d τ
  have h5 := ExecLe.push 2 true (S r (O ++ zs (2 * j) ++ [s] ++ zs (2 * d) ++
    [pos, zero, neg, sep]) j d τ)
  rw [S_2, show true :: List.replicate j true = List.replicate (j + 1) true from rfl,
    S_upd2] at h5
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm h5)))).cast ?_ (by simp; omega)
  simp [stp, List.append_assoc]

theorem ex_sep (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str) :
    ExecLe sepCmd (S r O j d τ)
      (.norm (S r (O ++ (uPos j d ++ [sep]) ++ (uNeg j d ++ [sep])) 0 (j + d + 1) τ))
      (20 * j + 18 * d + 37) := by
  have h1 := ex_emitZ2 r O j d τ
  have h2 := ex_emitZ3 r (O ++ zs (2 * j)) j d τ
  have h3 := ex_emitL [zero, pos, sep] r (O ++ zs (2 * j) ++ zs (2 * d)) j d τ
  set O1 := O ++ zs (2 * j) ++ zs (2 * d) ++ [zero, pos, sep]
  have h4 := ex_emitZ2 r O1 j d τ
  have h5 := ex_emitZ3 r (O1 ++ zs (2 * j)) j d τ
  have h6 := ex_emitL [zero, zero, zero, neg, sep] r (O1 ++ zs (2 * j) ++ zs (2 * d)) j d τ
  set O2 := O1 ++ zs (2 * j) ++ zs (2 * d) ++ [zero, zero, zero, neg, sep]
  have h7 := exec_move (a := 2) (b := 3) (by decide) _ (S r O2 j d τ) (S_2 ..)
  rw [S_3, List.reverse_replicate, List.replicate_append_replicate,
    show ([] : Str) = List.replicate 0 true from rfl, S_upd2, S_upd3] at h7
  have h8 := ExecLe.push 3 true (S r O2 0 (j + d) τ)
  rw [S_3, show true :: List.replicate (j + d) true = List.replicate (j + d + 1) true from rfl,
    S_upd3] at h8
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm (h6.seq_norm
    ((ExecLe.of h7).seq_norm h8))))))).cast ?_ (by simp; omega)
  simp only [O2, O1, uPos, uNeg, List.append_assoc, List.cons_append, List.nil_append]

/-! ## The main loop -/

/-- Loop body: read one bit pair of the input (`sym`). -/
def bodyR : Cmd :=
  .pop 0 .brk (.pop 0 .brk sepCmd (nsCmd zero)) (.pop 0 .brk (nsCmd pos) (nsCmd neg))

/-- The main loop. -/
def mainR : Cmd := .loop bodyR

/-- The reduction program. -/
def redCmd : Cmd := .seq (emitL [zero, neg, sep]) mainR

/-- Output block of `goC`. -/
abbrev blk (L : List (List SatSym)) : List SatSym := L.flatMap (· ++ [sep])

theorem stepR {a b : Bool} {r : Str} {O O' : List SatSym} {j d j' d' : ℕ} {τ : ℕ → Str}
    {T₁ : ℕ} (hb : ExecLe bodyR (S (a :: b :: r) O j d τ) (.norm (S r O' j' d' τ)) T₁)
    (hT : T₁ ≤ 20 * (j + d) + 39) (hjd : j' + d' = j + d + 1)
    (hO : O' ++ blk (goC (FunBridge.dec2 r) j' d') =
      O ++ blk (goC (FunBridge.dec2 (a :: b :: r)) j d))
    (ih : ∃ σ', ExecLe mainR (S r O' j' d' τ) (.norm σ')
      (r.length * (20 * (j' + d' + r.length) + 40) + 3) ∧
      σ' 1 = enc (O' ++ blk (goC (FunBridge.dec2 r) j' d'))) :
    ∃ σ', ExecLe mainR (S (a :: b :: r) O j d τ) (.norm σ')
      ((a :: b :: r).length * (20 * (j + d + (a :: b :: r).length) + 40) + 3) ∧
      σ' 1 = enc (O ++ blk (goC (FunBridge.dec2 (a :: b :: r)) j d)) := by
  obtain ⟨σ', h, h1⟩ := ih
  refine ⟨σ', (ExecLe.loop_norm hb h).cast rfl ?_, by rw [h1, hO]⟩
  rw [hjd]
  simp only [List.length_cons]
  nlinarith

theorem pop2 {c00 c01 c10 c11 : Cmd} {a b : Bool} {r : Str} {O : List SatSym} {j d : ℕ}
    {τ : ℕ → Str} {res : Res} {T : ℕ}
    (h : ExecLe (if a then (if b then c11 else c10) else (if b then c01 else c00))
      (S r O j d τ) res T) :
    ExecLe (.pop 0 .brk (.pop 0 .brk c00 c01) (.pop 0 .brk c10 c11)) (S (a :: b :: r) O j d τ)
      res (T + 1 + 1) := by
  refine ExecLe.pop_cons (b := a) (s := b :: r) (S_0 ..) ?_
  rw [S_upd0]
  cases a
  · exact ExecLe.pop_cons (b := b) (s := r) (S_0 ..) (by rw [S_upd0]; simpa using h)
  · exact ExecLe.pop_cons (b := b) (s := r) (S_0 ..) (by rw [S_upd0]; simpa using h)

theorem exec_mainR : ∀ (r : Str) (O : List SatSym) (j d : ℕ) (τ : ℕ → Str),
    ∃ σ', ExecLe mainR (S r O j d τ) (.norm σ') (r.length * (20 * (j + d + r.length) + 40) + 3) ∧
      σ' 1 = enc (O ++ blk (goC (FunBridge.dec2 r) j d))
  | [], O, j, d, τ => ⟨_, (ExecLe.loop_brk (ExecLe.pop_nil (S_0 ..) (ExecLe.brk _))).cast rfl
      (by simp), by simp [FunBridge.dec2, goC]⟩
  | [false], O, j, d, τ => ⟨_, (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := []) (S_0 ..)
      (ExecLe.pop_nil (by simp) (ExecLe.brk _)))).cast rfl (by simp),
      by simp [FunBridge.dec2, goC]⟩
  | [true], O, j, d, τ => ⟨_, (ExecLe.loop_brk (ExecLe.pop_cons (b := true) (s := []) (S_0 ..)
      (ExecLe.pop_nil (by simp) (ExecLe.brk _)))).cast rfl (by simp),
      by simp [FunBridge.dec2, goC]⟩
  | false :: false :: r, O, j, d, τ =>
    stepR (pop2 (by simpa using ex_sep r O j d τ)) (by omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goC, List.append_assoc])
      (exec_mainR r _ 0 (j + d + 1) τ)
  | false :: true :: r, O, j, d, τ =>
    stepR (pop2 (by simpa using ex_ns zero r O j d τ)) (by omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goC, List.append_assoc])
      (exec_mainR r _ (j + 1) d τ)
  | true :: false :: r, O, j, d, τ =>
    stepR (pop2 (by simpa using ex_ns pos r O j d τ)) (by omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goC, List.append_assoc])
      (exec_mainR r _ (j + 1) d τ)
  | true :: true :: r, O, j, d, τ =>
    stepR (pop2 (by simpa using ex_ns neg r O j d τ)) (by omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goC, List.append_assoc])
      (exec_mainR r _ (j + 1) d τ)

theorem init_eq_S (x : Str) : (init [x]).stk = S x [] 0 0 (init [x]).stk := by
  funext k
  simp only [S, update_apply]
  split_ifs <;> subst_vars <;> simp [init, enc]

theorem exec_redCmd (x : Str) : ∃ σ', ExecLe redCmd (init [x]).stk (.norm σ') (tb 4 x.length) ∧
    σ' 1 = ((red (FunBridge.dec2 x)).flatMap ic).reverse := by
  obtain ⟨σ', h, h1⟩ := exec_mainR x [zero, neg, sep] 0 0 (init [x]).stk
  have h0 := ex_emitL [zero, neg, sep] x [] 0 0 (init [x]).stk
  rw [← init_eq_S] at h0
  refine ⟨σ', (h0.seq_norm h).cast rfl ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil, tb]
    set n := x.length
    have e : (n + 2) ^ 4 = n ^ 4 + 8 * n ^ 3 + 24 * n ^ 2 + 32 * n + 16 := by ring
    have h1 : n ≤ n ^ 2 := by nlinarith
    have h2 : n ^ 2 ≤ n ^ 3 := by nlinarith
    have h3 : n * (20 * (0 + 0 + n) + 40) = 20 * n ^ 2 + 40 * n := by ring
    omega
  · rw [h1]; simp [enc, red, TC]

/-! ## The reduction and NP-completeness -/

/-- **SAT ≤ₚ 3-SAT** (official polynomial-time many-one reducibility). -/
theorem sat_le_sat3 :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang SAT3Lang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    redCmd 1 4 (fun x => red (FunBridge.dec2 x)) exec_redCmd red
    (fun w => by
      show red w = red (FunBridge.dec2 (w.flatMap ic))
      rw [FunBridge.dec2_flatMap_ic])
  exact ⟨red, hc, fun w => (red_iff w).symm⟩

/-- **3-SAT is NP-complete** (official definitions): `SAT3Lang` (satisfiable dense CNF
formulas with at most three literals per clause) is in `NP` and every `NP` language reduces
to it. -/
theorem threeSat_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete (Millennium.fin_encoding_string SatSym)
      SAT3Lang :=
  Pnp.Karp.np_complete_of_sat_reduces sat3_in_np sat_le_sat3

end Pnp.Karp.ThreeSAT
