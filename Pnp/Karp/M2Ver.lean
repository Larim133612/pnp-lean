import Pnp.Karp.NAE
import Pnp.Karp.ThreeSATNP
import Pnp.Karp.Clique

/-!
# MAX 2-SAT ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w` and
a certificate `y` (the values of the variables, missing bits are `false`).

Program (`m2v_ver`):
1. `phaseA`, `trimC 2`: the reversed internal code of `trunc w` is on stack `2`;
2. `m2v_kr0`: pop the final `sep` (no finished clause: halt `false`), then `m2v_krL` reads the
   last clause `kr` (reversed), one mark on stack `10` per symbol, and stops at the next `sep`
   (pushed back) or at the bottom;
3. `move 2 3`: the code of the remaining clauses `rs` (each followed by `sep`) is on stack `3`;
4. `m2v_main`: a variant of `phaseC` of `Pnp/CookLevin/SAT.lean`; stack `8` counts the literals
   of the current clause (at `sep`: halt `false` if `≥ 3`), and at the `sep` of a satisfied
   clause a mark of stack `10` is removed; at the end, accept iff stack `10` is empty.
-/

namespace Pnp.Karp.NAE

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.ThreeSAT
  Pnp.Karp.Clique

/-! ## Semantics of the main loop -/

/-- The used-bits stack after reading one symbol. -/
def m2v_sU : Str → Str → Str
  | [], U => U
  | b :: _, U => b :: U

/-- What the main loop computes (`l`: literals of the current clause, `k`: remaining marks). -/
def m2v_run : List SatSym → Str → Str → Bool → ℕ → ℕ → Bool
  | [], _, _, _, _, k => decide (k = 0)
  | sep :: w, Y, U, F, l, k =>
      decide (l ≤ 2) && m2v_run w (U.reverse ++ Y) [] false 0 (if F then k - 1 else k)
  | zero :: w, Y, U, F, l, k => m2v_run w Y.tail (m2v_sU Y U) F l k
  | pos :: w, Y, U, F, l, k => m2v_run w Y.tail (m2v_sU Y U) (F || Y.headD false) (l + 1) k
  | neg :: w, Y, U, F, l, k => m2v_run w Y.tail (m2v_sU Y U) (F || !Y.headD false) (l + 1) k

theorem m2v_len (Y U : Str) : (m2v_sU Y U).length + Y.tail.length ≤ U.length + Y.length := by
  cases Y <;> simp [m2v_sU]; omega

/-! ## Stack layout -/

/-- The stacks of the main phase. -/
def m2v_st (Q Y U : Str) (F : Bool) (l k : ℕ) : ℕ → Str := fun j =>
  if j = 0 then Y else if j = 3 then Q else if j = 4 then CookLevin.fl F else
  if j = 5 then U else if j = 8 then List.replicate l true else
  if j = 10 then List.replicate k true else []

macro "m2v_stx" : tactic =>
  `(tactic| (funext j; simp only [m2v_st, update_apply]; split_ifs <;> simp_all))

section St
variable {Q Y U : Str} {F : Bool} {l k : ℕ}
@[simp] theorem m2v_st0 : m2v_st Q Y U F l k 0 = Y := rfl
@[simp] theorem m2v_st3 : m2v_st Q Y U F l k 3 = Q := rfl
@[simp] theorem m2v_st4 : m2v_st Q Y U F l k 4 = CookLevin.fl F := rfl
@[simp] theorem m2v_st5 : m2v_st Q Y U F l k 5 = U := rfl
@[simp] theorem m2v_st8 : m2v_st Q Y U F l k 8 = List.replicate l true := rfl
@[simp] theorem m2v_st10 : m2v_st Q Y U F l k 10 = List.replicate k true := rfl

theorem m2v_u0 (Y' : Str) : update (m2v_st Q Y U F l k) 0 Y' = m2v_st Q Y' U F l k := by m2v_stx
theorem m2v_u3 (Q' : Str) : update (m2v_st Q Y U F l k) 3 Q' = m2v_st Q' Y U F l k := by m2v_stx
theorem m2v_u4 (F' : Bool) : update (m2v_st Q Y U F l k) 4 (CookLevin.fl F') =
    m2v_st Q Y U F' l k := by m2v_stx
theorem m2v_u5 (U' : Str) : update (m2v_st Q Y U F l k) 5 U' = m2v_st Q Y U' F l k := by m2v_stx
theorem m2v_u8 (l' : ℕ) : update (m2v_st Q Y U F l k) 8 (List.replicate l' true) =
    m2v_st Q Y U F l' k := by m2v_stx
theorem m2v_u10 (k' : ℕ) : update (m2v_st Q Y U F l k) 10 (List.replicate k' true) =
    m2v_st Q Y U F l k' := by m2v_stx
end St

/-! ## Commands of the main loop -/

/-- End of input: accept iff stack `10` is empty. -/
def m2v_fin : Cmd := .pop 10 (.halt true) (.halt false) (.halt false)

/-- At a separator: halt `false` if stack `8` holds at least three marks, otherwise empty it. -/
def m2v_ge3 : Cmd := p8 (p8 (p8 (.halt false)))

/-- At a separator: if the clause is satisfied, remove a mark of stack `10`; clear the flag. -/
def m2v_dk : Cmd := .pop 4 .skip .skip (.pop 10 .skip .skip .skip)

def m2v_sepA : Cmd := .seq m2v_ge3 (.seq m2v_dk (move 5 0))
def m2v_zA : Cmd := .pop 0 .skip (.push 5 false) (.push 5 true)
def m2v_pA : Cmd := .seq (.pop 0 .skip (.push 5 false) (.seq (.push 5 true) setF)) (.push 8 true)
def m2v_nA : Cmd := .seq (.pop 0 setF (.seq (.push 5 false) setF) (.push 5 true)) (.push 8 true)

/-- Loop body of the main phase. -/
def m2v_B : Cmd :=
  .pop 3 m2v_fin (.pop 3 (.halt false) m2v_sepA m2v_zA) (.pop 3 (.halt false) m2v_pA m2v_nA)

def m2v_main : Cmd := .loop m2v_B

section Main
variable {Q Y U : Str} {F : Bool} {l k : ℕ}

theorem m2v_ex_fin : ExecLe m2v_fin (m2v_st Q Y U F l k) (.halt (decide (k = 0))) 2 := by
  rcases k with _ | k
  · exact (ExecLe.pop_nil rfl (ExecLe.halt true _)).cast (by simp) le_rfl
  · exact (ExecLe.pop_cons (b := true) (s := List.replicate k true)
      (by simp [List.replicate_succ]) (ExecLe.halt false _)).cast (by simp) le_rfl

theorem m2v_ex_ge3 (σ : ℕ → Str) (l : ℕ) (h : σ 8 = List.replicate l true) :
    ExecLe m2v_ge3 σ (if l ≤ 2 then .norm (update σ 8 []) else .halt false) 4 := by
  match l, h with
  | 0, h =>
    have h' : σ 8 = [] := h
    exact (p8_nil h').cast (by rw [if_pos (by omega), ← h', update_eq_self]) (by omega)
  | 1, h => exact (p8_cons (s := []) h (p8_nil (by simp))).cast (by simp) (by omega)
  | 2, h => exact (p8_cons (s := [true]) h (p8_cons (s := []) (by simp)
      (p8_nil (by simp)))).cast (by simp) (by omega)
  | l + 3, h =>
    have h' : σ 8 = true :: true :: true :: List.replicate l true := by
      rw [h]; simp [List.replicate_succ]
    exact (p8_cons h' (p8_cons (s := true :: List.replicate l true) (by simp)
      (p8_cons (s := List.replicate l true) (by simp)
      (ExecLe.halt false _)))).cast (by rw [if_neg (by omega)]) le_rfl

theorem m2v_ex_dk : ExecLe m2v_dk (m2v_st Q Y U F 0 k)
    (.norm (m2v_st Q Y U false 0 (if F then k - 1 else k))) 3 := by
  cases F
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp) (by omega)
  · refine ExecLe.pop_cons (b := true) (s := []) rfl ?_
    rw [if_pos rfl, show ([] : Str) = CookLevin.fl false from rfl, m2v_u4]
    rcases k with _ | k
    · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast rfl (by omega)
    · refine (ExecLe.pop_same (b := true) (s := List.replicate k true)
        (by simp [List.replicate_succ]) (ExecLe.skip _)).cast ?_ (by omega)
      rw [m2v_u10]; simp

theorem m2v_ex_sepA (hl : l ≤ 2) : ExecLe m2v_sepA (m2v_st Q Y U F l k)
    (.norm (m2v_st Q (U.reverse ++ Y) [] false 0 (if F then k - 1 else k)))
    (2 * U.length + 9) := by
  have hg := m2v_ex_ge3 (m2v_st Q Y U F l k) l rfl
  rw [if_pos hl, show ([] : Str) = List.replicate 0 true from rfl, m2v_u8] at hg
  have hm := exec_move (a := 5) (b := 0) (by decide) U
    (m2v_st Q Y U false 0 (if F then k - 1 else k)) rfl
  rw [m2v_u5, m2v_st0, m2v_u0] at hm
  exact (hg.seq_norm (m2v_ex_dk.seq_norm (ExecLe.of hm))).cast rfl (by omega)

theorem m2v_ex_sepA_halt (hl : ¬ l ≤ 2) : ExecLe m2v_sepA (m2v_st Q Y U F l k) (.halt false) 4 := by
  have hg := m2v_ex_ge3 (m2v_st Q Y U F l k) l rfl
  rw [if_neg hl] at hg
  exact hg.seq_halt

theorem m2v_ex_push5 (b : Bool) : ExecLe (.push 5 b) (m2v_st Q Y U F l k)
    (.norm (m2v_st Q Y (b :: U) F l k)) 1 :=
  (ExecLe.push 5 b _).cast (by rw [m2v_st5, m2v_u5]) le_rfl

theorem m2v_ex_setF : ExecLe setF (m2v_st Q Y U F l k) (.norm (m2v_st Q Y U true l k)) 2 :=
  (exec_setF F _ rfl).cast (by rw [show [true] = CookLevin.fl true from rfl, m2v_u4]) le_rfl

theorem m2v_ex_push8 : ExecLe (.push 8 true) (m2v_st Q Y U F l k)
    (.norm (m2v_st Q Y U F (l + 1) k)) 1 :=
  (ExecLe.push 8 true _).cast (by rw [m2v_st8, ← List.replicate_succ, m2v_u8]) le_rfl

theorem m2v_ex_zA : ExecLe m2v_zA (m2v_st Q Y U F l k)
    (.norm (m2v_st Q Y.tail (m2v_sU Y U) F l k)) 2 := by
  rcases Y with _ | ⟨b, Y⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp [m2v_sU]) le_rfl
  · refine ExecLe.pop_cons (b := b) (s := Y) rfl ?_
    rw [m2v_u0]
    cases b <;> exact m2v_ex_push5 _

theorem m2v_ex_pA : ExecLe m2v_pA (m2v_st Q Y U F l k)
    (.norm (m2v_st Q Y.tail (m2v_sU Y U) (F || Y.headD false) (l + 1) k)) 5 := by
  rcases Y with _ | ⟨b, Y⟩
  · exact ((ExecLe.pop_nil rfl (ExecLe.skip _)).seq_norm m2v_ex_push8).cast
      (by simp [m2v_sU]) (by omega)
  · refine (ExecLe.seq_norm (ExecLe.pop_cons (T := 3) (b := b) (s := Y) rfl ?_) m2v_ex_push8).cast rfl
      (by omega)
    rw [m2v_u0]
    cases b
    · exact (m2v_ex_push5 false).cast (by simp [m2v_sU]) (by omega)
    · exact ((m2v_ex_push5 true).seq_norm m2v_ex_setF).cast (by simp [m2v_sU]) le_rfl

theorem m2v_ex_nA : ExecLe m2v_nA (m2v_st Q Y U F l k)
    (.norm (m2v_st Q Y.tail (m2v_sU Y U) (F || !Y.headD false) (l + 1) k)) 5 := by
  rcases Y with _ | ⟨b, Y⟩
  · exact ((ExecLe.pop_nil rfl m2v_ex_setF).seq_norm m2v_ex_push8).cast
      (by simp [m2v_sU]) (by omega)
  · refine (ExecLe.seq_norm (ExecLe.pop_cons (T := 3) (b := b) (s := Y) rfl ?_) m2v_ex_push8).cast rfl
      (by omega)
    rw [m2v_u0]
    cases b
    · exact ((m2v_ex_push5 false).seq_norm m2v_ex_setF).cast (by simp [m2v_sU]) le_rfl
    · exact (m2v_ex_push5 true).cast (by simp [m2v_sU]) (by omega)

theorem m2v_ex_main (N : ℕ) : ∀ (w : List SatSym) (Y U : Str) (F : Bool) (l k : ℕ),
    U.length + Y.length ≤ N →
    ExecLe m2v_main (m2v_st (w.flatMap ic) Y U F l k) (.halt (m2v_run w Y U F l k))
      (w.length * (2 * N + 12) + 3)
  | [], Y, U, F, l, k, _ => (ExecLe.loop_halt (ExecLe.pop_nil rfl m2v_ex_fin)).cast
      (by simp [m2v_run]) (by simp)
  | sep :: w, Y, U, F, l, k, hN => by
    have hc : ∀ {r : Res} {T : ℕ}, ExecLe m2v_sepA (m2v_st (w.flatMap ic) Y U F l k) r T →
        ExecLe m2v_B (m2v_st ((sep :: w).flatMap ic) Y U F l k) r (T + 2) := fun h =>
      ExecLe.pop_cons (b := false) (s := false :: w.flatMap ic) (by simp [ic])
        (by rw [m2v_u3]; exact ExecLe.pop_cons (b := false) (s := w.flatMap ic) rfl
                  (by rw [m2v_u3]; exact h))
    by_cases hl : l ≤ 2
    · have ih := m2v_ex_main N w (U.reverse ++ Y) [] false 0 (if F then k - 1 else k)
        (by simp; omega)
      exact (ExecLe.loop_norm (hc (m2v_ex_sepA hl)) ih).cast (by simp [m2v_run, hl])
        (by simp; nlinarith)
    · exact (ExecLe.loop_halt (hc (m2v_ex_sepA_halt hl))).cast (by simp [m2v_run, hl])
        (by simp; nlinarith)
  | zero :: w, Y, U, F, l, k, hN => by
    have hb : ExecLe m2v_B (m2v_st ((zero :: w).flatMap ic) Y U F l k)
        (.norm (m2v_st (w.flatMap ic) Y.tail (m2v_sU Y U) F l k)) (2 + 2) :=
      ExecLe.pop_cons (b := false) (s := true :: w.flatMap ic) (by simp [ic])
        (by rw [m2v_u3]; exact ExecLe.pop_cons (b := true) (s := w.flatMap ic) rfl
                  (by rw [m2v_u3]; exact m2v_ex_zA))
    have ih := m2v_ex_main N w Y.tail (m2v_sU Y U) F l k (by have := m2v_len Y U; omega)
    exact (ExecLe.loop_norm hb ih).cast (by simp [m2v_run]) (by simp; nlinarith)
  | pos :: w, Y, U, F, l, k, hN => by
    have hb : ExecLe m2v_B (m2v_st ((pos :: w).flatMap ic) Y U F l k)
        (.norm (m2v_st (w.flatMap ic) Y.tail (m2v_sU Y U) (F || Y.headD false) (l + 1) k))
        (5 + 2) :=
      ExecLe.pop_cons (b := true) (s := false :: w.flatMap ic) (by simp [ic])
        (by rw [m2v_u3]; exact ExecLe.pop_cons (b := false) (s := w.flatMap ic) rfl
                  (by rw [m2v_u3]; exact m2v_ex_pA))
    have ih := m2v_ex_main N w Y.tail (m2v_sU Y U) (F || Y.headD false) (l + 1) k
      (by have := m2v_len Y U; omega)
    exact (ExecLe.loop_norm hb ih).cast (by simp [m2v_run]) (by simp; nlinarith)
  | neg :: w, Y, U, F, l, k, hN => by
    have hb : ExecLe m2v_B (m2v_st ((neg :: w).flatMap ic) Y U F l k)
        (.norm (m2v_st (w.flatMap ic) Y.tail (m2v_sU Y U) (F || !Y.headD false) (l + 1) k))
        (5 + 2) :=
      ExecLe.pop_cons (b := true) (s := true :: w.flatMap ic) (by simp [ic])
        (by rw [m2v_u3]; exact ExecLe.pop_cons (b := true) (s := w.flatMap ic) rfl
                  (by rw [m2v_u3]; exact m2v_ex_nA))
    have ih := m2v_ex_main N w Y.tail (m2v_sU Y U) (F || !Y.headD false) (l + 1) k
      (by have := m2v_len Y U; omega)
    exact (ExecLe.loop_norm hb ih).cast (by simp [m2v_run]) (by simp; nlinarith)

end Main

/-! ## Reading the threshold clause -/

/-- Loop body of `m2v_krL`: pop one (reversed) symbol code; at a `sep` push it back and stop,
otherwise push a mark onto stack `10`. -/
def m2v_krB : Cmd :=
  .pop 2 .brk (.pop 2 .brk (.seq (.push 2 false) (.seq (.push 2 false) .brk)) (.push 10 true))
    (.pop 2 .brk (.push 10 true) (.push 10 true))

def m2v_krL : Cmd := .loop m2v_krB

theorem m2v_ex_krL (u : List SatSym) (hu : u = [] ∨ ∃ u', u = u' ++ [sep]) :
    ∀ (t : List SatSym) (σ : ℕ → Str) (m : ℕ), sep ∉ t → σ 2 = rc t ++ (u.flatMap ic).reverse →
    σ 10 = List.replicate m true →
    ExecLe m2v_krL σ (.norm (update (update σ 2 ((u.flatMap ic).reverse)) 10
      (List.replicate (t.length + m) true))) (4 * t.length + 6)
  | [], σ, m, _, h, h10 => by
    rcases hu with rfl | ⟨u', rfl⟩
    · refine (ExecLe.loop_brk (ExecLe.pop_nil (by simpa [rc] using h) (ExecLe.brk _))).cast ?_
        (by simp)
      congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [rc]
    · have h' : σ 2 = false :: false :: (u'.flatMap ic).reverse := by
        simpa [rc, List.flatMap_append, ic] using h
      refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := false)
        (s := (u'.flatMap ic).reverse)
        (by simp) ((ExecLe.push 2 false _).seq_norm ((ExecLe.push 2 false _).seq_norm
          (ExecLe.brk _)))))).cast ?_ (by simp)
      congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [List.flatMap_append, ic]
  | s :: t, σ, m, hs, h, h10 => by
    have hs' : s ≠ sep := fun e => hs (e ▸ List.mem_cons_self ..)
    have ht : sep ∉ t := fun e => hs (List.mem_cons_of_mem _ e)
    set rest := rc t ++ (u.flatMap ic).reverse
    have ih := m2v_ex_krL u hu t (update (update σ 2 rest) 10 (true :: σ 10)) (m + 1) ht
      (by simp [rest]) (by simp [h10, List.replicate_succ])
    have hb : ExecLe m2v_krB σ (.norm (update (update σ 2 rest) 10 (true :: σ 10))) 3 := by
      cases s with
      | sep => exact absurd rfl hs'
      | zero =>
        have h' : σ 2 = true :: false :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := false) (s := rest) (by simp)
          (ExecLe.push 10 true _))).cast (by simp) le_rfl
      | neg =>
        have h' : σ 2 = true :: true :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := true) (s := rest) (by simp)
          (ExecLe.push 10 true _))).cast (by simp) le_rfl
      | pos =>
        have h' : σ 2 = false :: true :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := true) (s := rest) (by simp)
          (ExecLe.push 10 true _))).cast (by simp) le_rfl
    have e : t.length + (m + 1) = (s :: t).length + m := by simp; omega
    rw [e] at ih
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all

/-- Pop the final `sep` (halt `false` if there is no finished clause), then read `kr`. -/
def m2v_kr0 : Cmd := .pop 2 (.halt false) (.pop 2 (.halt false) m2v_krL (.halt false)) (.halt false)

/-! ## The whole verifier -/

def m2v_ver : Cmd := .seq phaseA (.seq (trimC 2) (.seq m2v_kr0 (.seq (move 2 3) m2v_main)))

/-- The answer of the verifier on `(w, y)`. -/
def m2v_vres (w : List SatSym) (y : Str) : Bool :=
  match (clauses w).reverse with
  | [] => false
  | kr :: rr => m2v_run (rr.reverse.flatMap (· ++ [sep])) y [] false 0 kr.length

/-- Time bound of the verifier. -/
def m2v_T (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 8) + (4 * n + 2) +
  (n * (2 * n + 12) + 3)

theorem m2v_exec_ver (z : Str) :
    ExecLe m2v_ver (init [z]).stk (.halt (m2v_vres (dec z).1 (dec z).2)) (m2v_T z.length) := by
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
  unfold m2v_vres m2v_ver
  rcases hcw : (clauses w).reverse with _ | ⟨kr, rr⟩
  · have h2 : σ₂ 2 = [] := by
      simp only [σ₂, update_self, trunc]
      rw [List.reverse_eq_nil_iff.1 hcw]; rfl
    refine (hpre _ _ _ (ExecLe.seq_halt (ExecLe.pop_nil h2 (ExecLe.halt false _)))).cast rfl ?_
    unfold m2v_T; nlinarith
  · have hcl : clauses w = rr.reverse ++ [kr] := by
      rw [← List.reverse_reverse (clauses w), hcw]; simp
    set u := rr.reverse.flatMap (· ++ [sep])
    have htr : trunc w = u ++ (kr ++ [sep]) := by simp [trunc, hcl, u]
    have hsep : sep ∉ kr := sep_not_mem_clauses w kr (by simp [hcl])
    have hu : u = [] ∨ ∃ u', u = u' ++ [sep] := by
      rcases rr.reverse.eq_nil_or_concat with h | ⟨L, c, h⟩
      · left; simp only [u, h]; rfl
      · right; exact ⟨L.flatMap (· ++ [sep]) ++ c, by simp only [u, h]; simp⟩
    have h2 : σ₂ 2 = false :: false :: (rc kr.reverse ++ (u.flatMap ic).reverse) := by
      simp only [σ₂, update_self, htr, rc_eq]
      simp [List.flatMap_append, ic]
    set σ' := update σ₂ 2 (rc kr.reverse ++ (u.flatMap ic).reverse)
    have hK := m2v_ex_krL u hu kr.reverse σ' 0 (by simpa using hsep) (by simp [σ'])
      (by simp [σ', σ₂, σ₁, he 10 (by decide)])
    have hK0 : ExecLe m2v_kr0 σ₂ (.norm (update (update σ' 2 ((u.flatMap ic).reverse)) 10
        (List.replicate (kr.reverse.length + 0) true))) (4 * kr.reverse.length + 6 + 1 + 1) :=
      ExecLe.pop_cons (b := false) h2 (ExecLe.pop_cons (b := false)
        (s := rc kr.reverse ++ (u.flatMap ic).reverse) (by simp)
        (by simpa [σ', update_idem] using hK))
    set σ₃ := update (update σ' 2 ((u.flatMap ic).reverse)) 10
        (List.replicate (kr.reverse.length + 0) true)
    have hM := exec_move (a := 2) (b := 3) (by decide) _ σ₃ rfl
    have hσ : update (update σ₃ 2 []) 3 ((σ₃ 2).reverse ++ σ₃ 3) =
        m2v_st (u.flatMap ic) y [] false 0 kr.length := by
      funext j
      simp only [σ₃, σ', σ₂, σ₁, m2v_st, update_apply, CookLevin.fl]
      split_ifs <;> simp_all
    rw [hσ] at hM
    have hR := m2v_ex_main y.length u y [] false 0 kr.length (by simp)
    refine (hpre _ _ _ (hK0.seq_norm ((ExecLe.of hM).seq_norm hR))).cast rfl ?_
    have hul : u.length + kr.length + 1 = (trunc w).length := by simp [htr]; omega
    have hc : (u.flatMap ic).length = 2 * u.length := length_flatMap_ic u
    have h32 : σ₃ 2 = (u.flatMap ic).reverse := by simp [σ₃]
    simp only [h32, List.length_reverse, hc, m2v_T]
    have : u.length * (2 * y.length + 12) ≤ z.length * (2 * z.length + 12) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

theorem m2v_T_le (n : ℕ) : m2v_T n ≤ tb 5 n := by
  unfold m2v_T tb
  have h3 : 2 ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have : (n + 2) ^ 5 = (n + 2) ^ 2 * (n + 2) ^ 3 := by ring
  nlinarith

end Pnp.Karp.NAE
