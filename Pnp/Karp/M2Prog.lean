import Pnp.Karp.NAE
import Pnp.Karp.ThreeSATProg
import Pnp.CookLevin.FunBridge

/-!
# SAT ≤ₚ MAX 2-SAT: the polynomial-time stack program for `m2I`

`m2p_redCmd`: a stack program computing `m2I` (`Pnp/Karp/NAE.lean`) on the 2-bit internal code
of its input, modelled on `Pnp/Karp/ThreeSATProg.lean`.  Stacks: `0` input, `1` output, `2`
unary `j`, `3` unary `d`, `4` temporary, `5` unary counter of the threshold `K = thr w`.  Each
gadget row is emitted from pieces (`m2p_P`): `3j` zeros, `3d` zeros, or a constant list.
-/

namespace Pnp.Karp.NAE

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.ThreeSAT

/-! ## Emitting `3·m` zeros -/

/-- Loop: three `zero`s per mark of stack `a`, marks moved to stack `4`. -/
def m2p_zLoop (a : ℕ) : Cmd :=
  .loop (.pop a .brk (.seq (.push 4 true) (pushList 1 [true, false, true, false, true, false]))
    (.seq (.push 4 true) (pushList 1 [true, false, true, false, true, false])))

/-- Emit `3·|σ a|` `zero` symbols (stack `a` holds marks, is restored). -/
def m2p_emitZ (a : ℕ) : Cmd := .seq (m2p_zLoop a) (move 4 a)

theorem m2p_exec_zLoop {a : ℕ} (ha1 : a ≠ 1) (ha4 : a ≠ 4) : ∀ (m k : ℕ) (O : List SatSym)
    (σ : ℕ → Str), σ a = List.replicate m true → σ 4 = List.replicate k true → σ 1 = enc O →
    ExecLe (m2p_zLoop a) σ (.norm (update (update (update σ a []) 4
      (List.replicate (m + k) true)) 1 (enc (O ++ zs (3 * m))))) (9 * m + 2)
  | 0, k, O, σ, h, h4, h1 => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk σ))).cast
      (by
        congr 1; funext j; simp only [update_apply]
        split_ifs <;> simp_all) (by simp)
  | m + 1, k, O, σ, h, h4, h1 => by
    have h' : σ a = true :: List.replicate m true := by rw [h, List.replicate_succ]
    let σ' := update (update (update σ a (List.replicate m true)) 4
      (List.replicate (k + 1) true)) 1 (enc (O ++ [zero, zero, zero]))
    have hb : ExecLe (.pop a .brk
        (.seq (.push 4 true) (pushList 1 [true, false, true, false, true, false]))
        (.seq (.push 4 true) (pushList 1 [true, false, true, false, true, false]))) σ
        (.norm σ') (1 + 7 + 1) :=
      ExecLe.pop_cons h' ((ExecLe.seq_norm (ExecLe.push 4 true _)
        (ExecLe.of (exec_pushList 1 _ _))).cast
          (by
            rw [show update σ a (List.replicate m true) 4 = List.replicate k true by
              rw [update_of_ne (Ne.symm ha4), h4]]
            rw [show update (update σ a (List.replicate m true)) 4
                (true :: List.replicate k true) 1 = enc O by
              rw [update_of_ne (by decide), update_of_ne (Ne.symm ha1), h1]]
            simp only [σ']
            rw [show enc (O ++ [zero, zero, zero]) = [true, false, true, false, true, false] ++
                enc O by simp [enc, ic]]
            rfl) (by simp))
    have ih := m2p_exec_zLoop ha1 ha4 m (k + 1) (O ++ [zero, zero, zero]) σ'
      (by simp [σ', ha1, ha4]) (by simp [σ']) (by simp [σ'])
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    congr 1; funext j; simp only [σ', update_apply]
    have ez : O ++ [zero, zero, zero] ++ zs (3 * m) = O ++ zs (3 * (m + 1)) := by
      show O ++ [zero, zero, zero] ++ List.replicate (3 * m) zero =
        O ++ List.replicate (3 * (m + 1)) zero
      rw [show 3 * (m + 1) = 3 + 3 * m by ring, List.replicate_add, List.append_assoc]; rfl
    rw [ez, show m + (k + 1) = m + 1 + k by omega]
    split_ifs <;> rfl

theorem m2p_exec_emitZ {a : ℕ} (ha1 : a ≠ 1) (ha4 : a ≠ 4) (m : ℕ) (O : List SatSym)
    (σ : ℕ → Str) (h : σ a = List.replicate m true) (h4 : σ 4 = []) (h1 : σ 1 = enc O) :
    ExecLe (m2p_emitZ a) σ (.norm (update σ 1 (enc (O ++ zs (3 * m))))) (11 * m + 4) := by
  have hl := m2p_exec_zLoop ha1 ha4 m 0 O σ h (by simp [h4]) h1
  have hm := exec_move (a := 4) (b := a) (Ne.symm ha4) (List.replicate m true)
    (update (update (update σ a []) 4 (List.replicate (m + 0) true)) 1 (enc (O ++ zs (3 * m))))
    (by simp)
  refine (ExecLe.seq_norm hl (ExecLe.of hm)).cast ?_ (by simp; omega)
  congr 1; funext j; simp only [update_apply]
  split_ifs <;> simp_all

/-! ## The program state -/

/-- Program state: input rest `r`, output `O`, counters `j`, `d`, threshold marks `k`. -/
def m2p_S (r : Str) (O : List SatSym) (j d k : ℕ) (τ : ℕ → Str) : ℕ → Str :=
  update (update (update (update (update (update τ 0 r) 1 (enc O)) 2 (List.replicate j true)) 3
    (List.replicate d true)) 4 []) 5 (List.replicate k true)

section S
variable (r : Str) (O : List SatSym) (j d k : ℕ) (τ : ℕ → Str)

@[simp] theorem m2p_S_0 : m2p_S r O j d k τ 0 = r := by simp [m2p_S]
@[simp] theorem m2p_S_1 : m2p_S r O j d k τ 1 = enc O := by simp [m2p_S]
@[simp] theorem m2p_S_2 : m2p_S r O j d k τ 2 = List.replicate j true := by simp [m2p_S]
@[simp] theorem m2p_S_3 : m2p_S r O j d k τ 3 = List.replicate d true := by simp [m2p_S]
@[simp] theorem m2p_S_4 : m2p_S r O j d k τ 4 = [] := by simp [m2p_S]
@[simp] theorem m2p_S_5 : m2p_S r O j d k τ 5 = List.replicate k true := by simp [m2p_S]

theorem m2p_S_upd0 (r' : Str) : update (m2p_S r O j d k τ) 0 r' = m2p_S r' O j d k τ := by
  funext i; simp only [m2p_S, update_apply]; split_ifs <;> simp_all

theorem m2p_S_upd1 (O' : List SatSym) :
    update (m2p_S r O j d k τ) 1 (enc O') = m2p_S r O' j d k τ := by
  funext i; simp only [m2p_S, update_apply]; split_ifs <;> simp_all

theorem m2p_S_upd2 (j' : ℕ) :
    update (m2p_S r O j d k τ) 2 (List.replicate j' true) = m2p_S r O j' d k τ := by
  funext i; simp only [m2p_S, update_apply]; split_ifs <;> simp_all

theorem m2p_S_upd3 (d' : ℕ) :
    update (m2p_S r O j d k τ) 3 (List.replicate d' true) = m2p_S r O j d' k τ := by
  funext i; simp only [m2p_S, update_apply]; split_ifs <;> simp_all

theorem m2p_S_upd5 (k' : ℕ) :
    update (m2p_S r O j d k τ) 5 (List.replicate k' true) = m2p_S r O j d k' τ := by
  funext i; simp only [m2p_S, update_apply]; split_ifs <;> simp_all

end S

theorem m2p_ex_emitL (c : List SatSym) (r : Str) (O : List SatSym) (j d k : ℕ) (τ : ℕ → Str) :
    ExecLe (emitL c) (m2p_S r O j d k τ) (.norm (m2p_S r (O ++ c) j d k τ))
      (2 * c.length + 1) :=
  (exec_emitL c O _ (m2p_S_1 ..)).cast (by rw [m2p_S_upd1]) le_rfl

theorem m2p_ex_marks (n : ℕ) (r : Str) (O : List SatSym) (j d k : ℕ) (τ : ℕ → Str) :
    ExecLe (pushList 5 (List.replicate n true)) (m2p_S r O j d k τ)
      (.norm (m2p_S r O j d (n + k) τ)) (n + 1) :=
  (ExecLe.of (exec_pushList 5 _ _)).cast
    (by rw [m2p_S_5, List.replicate_append_replicate, m2p_S_upd5]) (by simp)

/-! ## Pieces of gadget rows -/

/-- A piece of output: `3j` zeros, `3d` zeros, or a constant list. -/
inductive m2p_P
  | J
  | D
  | L (c : List SatSym)

/-- The output of a piece. -/
def m2p_pd (j d : ℕ) : m2p_P → List SatSym
  | .J => zs (3 * j)
  | .D => zs (3 * d)
  | .L c => c

/-- The command of a piece. -/
def m2p_pc : m2p_P → Cmd
  | .J => m2p_emitZ 2
  | .D => m2p_emitZ 3
  | .L c => emitL c

/-- The time of a piece. -/
def m2p_pt (j d : ℕ) : m2p_P → ℕ
  | .J => 11 * j + 4
  | .D => 11 * d + 4
  | .L c => 2 * c.length + 1

/-- The command of a list of pieces. -/
def m2p_seqs : List m2p_P → Cmd
  | [] => .skip
  | p :: ps => .seq (m2p_pc p) (m2p_seqs ps)

/-- The time of a list of pieces. -/
def m2p_tt (j d : ℕ) : List m2p_P → ℕ
  | [] => 1
  | p :: ps => m2p_pt j d p + m2p_tt j d ps

theorem m2p_ex_pc (p : m2p_P) (r : Str) (O : List SatSym) (j d k : ℕ) (τ : ℕ → Str) :
    ExecLe (m2p_pc p) (m2p_S r O j d k τ) (.norm (m2p_S r (O ++ m2p_pd j d p) j d k τ))
      (m2p_pt j d p) := by
  cases p with
  | J => exact (m2p_exec_emitZ (by decide) (by decide) j O _ (m2p_S_2 ..) (m2p_S_4 ..)
      (m2p_S_1 ..)).cast (by rw [m2p_S_upd1]; rfl) le_rfl
  | D => exact (m2p_exec_emitZ (by decide) (by decide) d O _ (m2p_S_3 ..) (m2p_S_4 ..)
      (m2p_S_1 ..)).cast (by rw [m2p_S_upd1]; rfl) le_rfl
  | L c => exact m2p_ex_emitL c r O j d k τ

theorem m2p_ex_seqs (r : Str) (j d k : ℕ) (τ : ℕ → Str) : ∀ (ps : List m2p_P) (O : List SatSym),
    ExecLe (m2p_seqs ps) (m2p_S r O j d k τ)
      (.norm (m2p_S r (O ++ ps.flatMap (m2p_pd j d)) j d k τ)) (m2p_tt j d ps)
  | [], O => (ExecLe.skip _).cast (by simp) (by simp [m2p_tt])
  | p :: ps, O => ((m2p_ex_pc p r O j d k τ).seq_norm (m2p_ex_seqs r j d k τ ps _)).cast
      (by simp [List.append_assoc]) (by simp [m2p_tt])

open m2p_P in
/-- Rows of `c1 s j d`, `s ∈ {pos, neg}`. -/
def m2p_ps1 (s : SatSym) : List m2p_P :=
  [J, L [zero, s], D, L [pos, sep], J, L [zero, s], D, L [zero, pos, sep],
   J, L [zero], D, L [zero, pos, pos, sep], J, L [zero, swp s], D, L [neg, sep],
   J, L [zero, swp s], D, L [zero, neg, sep], J, L [zero], D, L [zero, neg, neg, sep]]

open m2p_P in
/-- Rows of `c1 zero j d`. -/
def m2p_ps1z : List m2p_P :=
  [L [pos], J, D, L [zero, pos, sep], L [pos], J, D, L [zero, zero, pos, sep],
   J, D, L [zero, zero, pos, pos, sep], L [neg], J, D, L [zero, neg, sep],
   L [neg], J, D, L [zero, zero, neg, sep], J, D, L [zero, zero, neg, neg, sep]]

open m2p_P in
/-- Rows of `c2 j d`. -/
def m2p_c2ps : List m2p_P :=
  [L [pos], J, D, L [zero, zero, neg, sep], L [pos], J, D, L [zero, zero, zero, zero, neg, sep],
   J, D, L [zero, zero, zero, neg, zero, neg, sep], L [neg], J, D, L [zero, zero, pos, sep],
   L [neg], J, D, L [zero, zero, zero, zero, pos, sep],
   J, D, L [zero, zero, zero, pos, zero, pos, sep]]

open m2p_P in
/-- Rows of `sA j d` and `sB j d`. -/
def m2p_sps : List m2p_P :=
  [L [pos], J, D, L [zero, pos, sep], L [neg], J, D, L [zero, neg, sep],
   L [pos], J, D, L [zero, zero, zero, zero, neg, sep],
   L [neg], J, D, L [zero, zero, zero, zero, pos, sep]]

theorem m2p_ps1_eq (s : SatSym) (hs : s ≠ zero) (j d : ℕ) :
    (m2p_ps1 s).flatMap (m2p_pd j d) = blk (c1 s j d).gad := by
  simp [m2p_ps1, m2p_pd, c1, hs, NC.gad, two, swp, List.replicate_add, -List.replicate_append_replicate, List.replicate_succ']

theorem m2p_ps1z_eq (j d : ℕ) :
    m2p_ps1z.flatMap (m2p_pd j d) = blk (c1 zero j d).gad := by
  simp [m2p_ps1z, m2p_pd, c1, NC.gad, two, swp, Nat.mul_add,
    List.replicate_add, -List.replicate_append_replicate, List.replicate_succ']

theorem m2p_c2ps_eq (j d : ℕ) :
    m2p_c2ps.flatMap (m2p_pd j d) = blk (c2 j d).gad := by
  simp [m2p_c2ps, m2p_pd, c2, NC.gad, two, swp, Nat.mul_add,
    List.replicate_add, -List.replicate_append_replicate, List.replicate_succ']

theorem m2p_sps_eq (j d : ℕ) :
    m2p_sps.flatMap (m2p_pd j d) = blk ((sA j d).gad ++ (sB j d).gad) := by
  simp [m2p_sps, m2p_pd, sA, sB, NC.gad, two, swp, Nat.mul_add,
    List.replicate_add, -List.replicate_append_replicate, List.replicate_succ']

/-! ## One input symbol -/

/-- A non-separator symbol: emit the rows `ps`, `j := j + 1`, ten threshold marks. -/
def m2p_nsCmd (ps : List m2p_P) : Cmd :=
  .seq (m2p_seqs ps) (.seq (.push 2 true) (pushList 5 (List.replicate 10 true)))

/-- A separator: emit the rows, `j := 0`, `d := j + d + 1`, four threshold marks. -/
def m2p_sepCmd : Cmd :=
  .seq (m2p_seqs m2p_sps) (.seq (move 2 3) (.seq (.push 3 true)
    (pushList 5 (List.replicate 4 true))))

theorem m2p_ex_ns (ps : List m2p_P) (r : Str) (O : List SatSym) (j d k : ℕ) (τ : ℕ → Str) :
    ExecLe (m2p_nsCmd ps) (m2p_S r O j d k τ)
      (.norm (m2p_S r (O ++ ps.flatMap (m2p_pd j d)) (j + 1) d (10 + k) τ))
      (m2p_tt j d ps + 12) := by
  have h1 := m2p_ex_seqs r j d k τ ps O
  have h2 := ExecLe.push 2 true (m2p_S r (O ++ ps.flatMap (m2p_pd j d)) j d k τ)
  rw [m2p_S_2, show true :: List.replicate j true = List.replicate (j + 1) true from rfl,
    m2p_S_upd2] at h2
  have h3 := m2p_ex_marks 10 r (O ++ ps.flatMap (m2p_pd j d)) (j + 1) d k τ
  exact (h1.seq_norm (h2.seq_norm h3)).cast rfl (by omega)

theorem m2p_ex_sep (r : Str) (O : List SatSym) (j d k : ℕ) (τ : ℕ → Str) :
    ExecLe m2p_sepCmd (m2p_S r O j d k τ)
      (.norm (m2p_S r (O ++ m2p_sps.flatMap (m2p_pd j d)) 0 (j + d + 1) (4 + k) τ))
      (m2p_tt j d m2p_sps + 2 * j + 8) := by
  have h1 := m2p_ex_seqs r j d k τ m2p_sps O
  set O2 := O ++ m2p_sps.flatMap (m2p_pd j d)
  have h7 := exec_move (a := 2) (b := 3) (by decide) _ (m2p_S r O2 j d k τ) (m2p_S_2 ..)
  rw [m2p_S_3, List.reverse_replicate, List.replicate_append_replicate,
    show ([] : Str) = List.replicate 0 true from rfl, m2p_S_upd2, m2p_S_upd3] at h7
  have h8 := ExecLe.push 3 true (m2p_S r O2 0 (j + d) k τ)
  rw [m2p_S_3, show true :: List.replicate (j + d) true = List.replicate (j + d + 1) true
    from rfl, m2p_S_upd3] at h8
  have h9 := m2p_ex_marks 4 r O2 0 (j + d + 1) k τ
  refine (h1.seq_norm ((ExecLe.of h7).seq_norm (h8.seq_norm h9))).cast rfl ?_
  simp; omega

/-! ## The main loop -/

/-- Loop body: read one bit pair of the input. -/
def m2p_bodyR : Cmd :=
  .pop 0 .brk (.pop 0 .brk m2p_sepCmd (m2p_nsCmd (m2p_ps1z ++ m2p_c2ps)))
    (.pop 0 .brk (m2p_nsCmd (m2p_ps1 pos ++ m2p_c2ps)) (m2p_nsCmd (m2p_ps1 neg ++ m2p_c2ps)))

/-- The main loop. -/
def m2p_mainR : Cmd := .loop m2p_bodyR

/-- Threshold contribution of the input symbols. -/
def m2p_cnt : List SatSym → ℕ
  | [] => 0
  | s :: w => (if s = sep then 4 else 10) + m2p_cnt w

theorem m2p_cnt_le : ∀ w : List SatSym, m2p_cnt w ≤ 10 * w.length
  | [] => le_rfl
  | s :: w => by
    have := m2p_cnt_le w
    simp only [m2p_cnt, List.length_cons]; split_ifs <;> omega

theorem m2p_tgt_c1 (s : SatSym) (j d : ℕ) : (c1 s j d).tgt = 5 := by
  unfold c1; split <;> rfl

theorem m2p_tgt_goN : ∀ (w : List SatSym) (j d : ℕ), ((goN w j d).map NC.tgt).sum = m2p_cnt w
  | [], _, _ => rfl
  | s :: w, j, d => by
    by_cases hs : s = sep
    · simp only [goN, hs, if_true, m2p_cnt, List.map_cons, List.sum_cons, m2p_tgt_goN w]
      simp [sA, sB, NC.tgt]; omega
    · simp only [goN, hs, if_false, m2p_cnt, List.map_cons, List.sum_cons, m2p_tgt_goN w,
        m2p_tgt_c1]
      simp [c2, NC.tgt]; omega

theorem m2p_stepR {a b : Bool} {r : Str} {O O' : List SatSym} {j d j' d' k k' : ℕ}
    {τ : ℕ → Str} {T₁ : ℕ}
    (hb : ExecLe m2p_bodyR (m2p_S (a :: b :: r) O j d k τ) (.norm (m2p_S r O' j' d' k' τ)) T₁)
    (hT : T₁ ≤ 140 * (j + d) + 499) (hjd : j' + d' = j + d + 1)
    (hO : O' ++ blk ((goN (FunBridge.dec2 r) j' d').flatMap NC.gad) =
      O ++ blk ((goN (FunBridge.dec2 (a :: b :: r)) j d).flatMap NC.gad))
    (hk : k' + m2p_cnt (FunBridge.dec2 r) = k + m2p_cnt (FunBridge.dec2 (a :: b :: r)))
    (ih : ∃ σ', ExecLe m2p_mainR (m2p_S r O' j' d' k' τ) (.norm σ')
      (r.length * (140 * (j' + d' + r.length) + 500) + 3) ∧
      σ' 1 = enc (O' ++ blk ((goN (FunBridge.dec2 r) j' d').flatMap NC.gad)) ∧
      σ' 5 = List.replicate (k' + m2p_cnt (FunBridge.dec2 r)) true) :
    ∃ σ', ExecLe m2p_mainR (m2p_S (a :: b :: r) O j d k τ) (.norm σ')
      ((a :: b :: r).length * (140 * (j + d + (a :: b :: r).length) + 500) + 3) ∧
      σ' 1 = enc (O ++ blk ((goN (FunBridge.dec2 (a :: b :: r)) j d).flatMap NC.gad)) ∧
      σ' 5 = List.replicate (k + m2p_cnt (FunBridge.dec2 (a :: b :: r))) true := by
  obtain ⟨σ', h, h1, h5⟩ := ih
  refine ⟨σ', (ExecLe.loop_norm hb h).cast rfl ?_, by rw [h1, hO], by rw [h5, hk]⟩
  rw [hjd]
  simp only [List.length_cons]
  nlinarith

theorem m2p_pop2 {c00 c01 c10 c11 : Cmd} {a b : Bool} {r : Str} {O : List SatSym}
    {j d k : ℕ} {τ : ℕ → Str} {res : Res} {T : ℕ}
    (h : ExecLe (if a then (if b then c11 else c10) else (if b then c01 else c00))
      (m2p_S r O j d k τ) res T) :
    ExecLe (.pop 0 .brk (.pop 0 .brk c00 c01) (.pop 0 .brk c10 c11))
      (m2p_S (a :: b :: r) O j d k τ) res (T + 1 + 1) := by
  refine ExecLe.pop_cons (b := a) (s := b :: r) (m2p_S_0 ..) ?_
  rw [m2p_S_upd0]
  cases a
  · exact ExecLe.pop_cons (b := b) (s := r) (m2p_S_0 ..) (by rw [m2p_S_upd0]; simpa using h)
  · exact ExecLe.pop_cons (b := b) (s := r) (m2p_S_0 ..) (by rw [m2p_S_upd0]; simpa using h)

theorem m2p_exec_mainR : ∀ (r : Str) (O : List SatSym) (j d k : ℕ) (τ : ℕ → Str),
    ∃ σ', ExecLe m2p_mainR (m2p_S r O j d k τ) (.norm σ')
      (r.length * (140 * (j + d + r.length) + 500) + 3) ∧
      σ' 1 = enc (O ++ blk ((goN (FunBridge.dec2 r) j d).flatMap NC.gad)) ∧
      σ' 5 = List.replicate (k + m2p_cnt (FunBridge.dec2 r)) true
  | [], O, j, d, k, τ => ⟨_, (ExecLe.loop_brk (ExecLe.pop_nil (m2p_S_0 ..) (ExecLe.brk _))).cast
      rfl (by simp), by simp [FunBridge.dec2, goN], by simp [FunBridge.dec2, m2p_cnt]⟩
  | [false], O, j, d, k, τ => ⟨_, (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := [])
      (m2p_S_0 ..) (ExecLe.pop_nil (by simp) (ExecLe.brk _)))).cast rfl (by simp),
      by simp [FunBridge.dec2, goN], by simp [FunBridge.dec2, m2p_cnt]⟩
  | [true], O, j, d, k, τ => ⟨_, (ExecLe.loop_brk (ExecLe.pop_cons (b := true) (s := [])
      (m2p_S_0 ..) (ExecLe.pop_nil (by simp) (ExecLe.brk _)))).cast rfl (by simp),
      by simp [FunBridge.dec2, goN], by simp [FunBridge.dec2, m2p_cnt]⟩
  | false :: false :: r, O, j, d, k, τ =>
    m2p_stepR (m2p_pop2 (by simpa using m2p_ex_sep r O j d k τ))
      (by simp [m2p_tt, m2p_sps, m2p_pt]; omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goN, List.append_assoc, m2p_sps_eq])
      (by simp [FunBridge.dec2, FunBridge.sym, m2p_cnt]; omega)
      (m2p_exec_mainR r _ 0 (j + d + 1) _ τ)
  | false :: true :: r, O, j, d, k, τ =>
    m2p_stepR (m2p_pop2 (by simpa using m2p_ex_ns (m2p_ps1z ++ m2p_c2ps) r O j d k τ))
      (by simp [m2p_tt, m2p_ps1z, m2p_c2ps, m2p_pt]; omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goN, List.append_assoc, m2p_ps1z_eq, m2p_c2ps_eq])
      (by simp [FunBridge.dec2, FunBridge.sym, m2p_cnt]; omega)
      (m2p_exec_mainR r _ (j + 1) d _ τ)
  | true :: false :: r, O, j, d, k, τ =>
    m2p_stepR (m2p_pop2 (by simpa using m2p_ex_ns (m2p_ps1 pos ++ m2p_c2ps) r O j d k τ))
      (by simp [m2p_tt, m2p_ps1, m2p_c2ps, m2p_pt]; omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goN, List.append_assoc,
        m2p_ps1_eq pos (by decide), m2p_c2ps_eq])
      (by simp [FunBridge.dec2, FunBridge.sym, m2p_cnt]; omega)
      (m2p_exec_mainR r _ (j + 1) d _ τ)
  | true :: true :: r, O, j, d, k, τ =>
    m2p_stepR (m2p_pop2 (by simpa using m2p_ex_ns (m2p_ps1 neg ++ m2p_c2ps) r O j d k τ))
      (by simp [m2p_tt, m2p_ps1, m2p_c2ps, m2p_pt]; omega) (by omega)
      (by simp [FunBridge.dec2, FunBridge.sym, goN, List.append_assoc,
        m2p_ps1_eq neg (by decide), m2p_c2ps_eq])
      (by simp [FunBridge.dec2, FunBridge.sym, m2p_cnt]; omega)
      (m2p_exec_mainR r _ (j + 1) d _ τ)

/-! ## The whole program -/

/-- Emit one `zero` per threshold mark (stack `5`). -/
def m2p_kLoop : Cmd := .loop (.pop 5 .brk (emitL [zero]) (emitL [zero]))

theorem m2p_exec_kLoop : ∀ (k : ℕ) (O : List SatSym) (σ : ℕ → Str),
    σ 5 = List.replicate k true → σ 1 = enc O →
    ∃ σ', ExecLe m2p_kLoop σ (.norm σ') (4 * k + 2) ∧ σ' 1 = enc (O ++ zs k)
  | 0, O, σ, h, h1 => ⟨σ, (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk σ))).cast rfl
      (by simp), by simp [h1]⟩
  | k + 1, O, σ, h, h1 => by
    have h' : σ 5 = true :: List.replicate k true := by rw [h, List.replicate_succ]
    have hb := ExecLe.pop_same (cn := .brk) h' (exec_emitL [zero] O (update σ 5
      (List.replicate k true)) (by rw [update_of_ne (by decide), h1]))
    obtain ⟨σ', h2, h3⟩ := m2p_exec_kLoop k (O ++ [zero])
      (update (update σ 5 (List.replicate k true)) 1 (enc (O ++ [zero]))) (by simp) (by simp)
    refine ⟨σ', (ExecLe.loop_norm hb h2).cast rfl (by simp; omega), ?_⟩
    rw [h3, List.append_assoc]; rfl

/-- The reduction program. -/
def m2p_redCmd : Cmd :=
  .seq (emitL [pos, zero, neg, sep, neg, zero, pos, sep]) (.seq (pushList 5 [true, true])
    (.seq m2p_mainR (.seq m2p_kLoop (emitL [sep]))))

theorem m2p_init_eq_S (x : Str) : (init [x]).stk = m2p_S x [] 0 0 0 (init [x]).stk := by
  funext k
  simp only [m2p_S, update_apply]
  split_ifs <;> subst_vars <;> simp [init, enc]

theorem m2p_m2I_eq (w : List SatSym) :
    m2I w = [pos, zero, neg, sep, neg, zero, pos, sep] ++
      blk ((goN w 0 0).flatMap NC.gad) ++ zs (2 + m2p_cnt w) ++ [sep] := by
  simp [m2I, NCs, thr, NC.gad, two, swp, NC.tgt, m2p_tgt_goN]

theorem m2p_exec_redCmd (x : Str) : ∃ σ', ExecLe m2p_redCmd (init [x]).stk (.norm σ')
    (tb 12 x.length) ∧ σ' 1 = ((m2I (FunBridge.dec2 x)).flatMap ic).reverse := by
  set τ := (init [x]).stk
  have h0 := m2p_ex_emitL [pos, zero, neg, sep, neg, zero, pos, sep] x [] 0 0 0 τ
  rw [← m2p_init_eq_S] at h0
  have hm := m2p_ex_marks 2 x [pos, zero, neg, sep, neg, zero, pos, sep] 0 0 0 τ
  obtain ⟨σ', h, h1, h5⟩ := m2p_exec_mainR x [pos, zero, neg, sep, neg, zero, pos, sep] 0 0 2 τ
  obtain ⟨σ'', hk, hk1⟩ := m2p_exec_kLoop _ _ σ' h5 h1
  have he := exec_emitL [sep] _ σ'' hk1
  refine ⟨_, (h0.seq_norm (hm.seq_norm (h.seq_norm (hk.seq_norm he)))).cast rfl ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil, tb]
    set n := x.length
    have hc : m2p_cnt (FunBridge.dec2 x) ≤ 10 * n :=
      (m2p_cnt_le _).trans (by have := FunBridge.length_dec2_le x; omega)
    have e1 : 2 ^ 10 ≤ (n + 2) ^ 10 := Nat.pow_le_pow_left (by omega) 10
    have e2 : (n + 2) ^ 12 = (n + 2) ^ 2 * (n + 2) ^ 10 := by ring
    have e3 : 1024 * (n + 2) ^ 2 ≤ (n + 2) ^ 2 * (n + 2) ^ 10 := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ (by simpa using e1)
    have e4 : n * (140 * (0 + 0 + n) + 500) = 140 * n ^ 2 + 500 * n := by ring
    have e5 : (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 := by ring
    omega
  · simp only [update_self]
    rw [m2p_m2I_eq]; simp [enc, List.append_assoc]

/-! ## The reduction -/

/-- **SAT ≤ₚ MAX 2-SAT** (official polynomial-time many-one reducibility), given the
correctness of the instance `m2I`. -/
theorem sat_le_m2_of (h : ∀ w, SATLang w ↔ M2Lang (m2I w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang M2Lang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    m2p_redCmd 1 12 (fun x => m2I (FunBridge.dec2 x)) m2p_exec_redCmd m2I
    (fun w => by
      show m2I w = m2I (FunBridge.dec2 (w.flatMap ic))
      rw [FunBridge.dec2_flatMap_ic])
  exact ⟨m2I, hc, h⟩

end Pnp.Karp.NAE
