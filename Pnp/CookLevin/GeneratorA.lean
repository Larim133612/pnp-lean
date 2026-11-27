import Pnp.CookLevin.Shape
import Pnp.KarpLipton.DTab
import Pnp.Oracle.Horner

/-!
# Infrastructure for the formula generator (M33d, part 1)

A stack layout for the generator program of `Pnp/CookLevin/Generator.lean`: stack `0` holds the
(rest of the) input, stack `1` a copy of it, stack `2` the output, and every stack `j ≥ 3` holds a
unary register `v j` (`st`).  On top of it:

* primitive commands on registers (pushes, `drain`, `copyVia`, `mul`, `polyCmd`, subtraction);
* `zerosR r t`: emit `v r` symbols `zero`;
* emission of *lines* (lists of fixed patterns and register-many zeros) with the predicate `Em`;
* `forLoop K body`: run `body` as many times as register `K` says.
-/

namespace Pnp.CookLevin.Uniform

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

/-! ## The stack layout -/

/-- Stacks: input `i` (`0`), input copy `X` (`1`), output `o` (`2`), unary registers `v j`. -/
def st (i X o : Str) (v : ℕ → ℕ) : ℕ → Str := fun j =>
  if j = 0 then i else if j = 1 then X else if j = 2 then o else List.replicate (v j) true

/-- Reversed internal code of a list of symbols (as pushed onto the output stack). -/
def rv (L : List SatSym) : Str := (L.flatMap ic).reverse

@[simp] theorem rv_nil : rv [] = [] := rfl

@[simp] theorem rv_append (L₁ L₂ : List SatSym) : rv (L₁ ++ L₂) = rv L₂ ++ rv L₁ := by
  simp [rv]

theorem rv_zs_succ (k : ℕ) : rv (zs (k + 1)) = rv (zs k) ++ [true, false] := by
  simp only [zs, List.replicate_succ]
  rw [show zero :: List.replicate k zero = [zero] ++ List.replicate k zero from rfl, rv_append]
  rfl

theorem length_rv (L : List SatSym) : (rv L).length = 2 * L.length := by
  rw [rv, List.length_reverse, length_flatMap_ic]

section St

variable {i X o : Str} {v : ℕ → ℕ}

@[simp] theorem st_zero : st i X o v 0 = i := rfl
@[simp] theorem st_one : st i X o v 1 = X := rfl
@[simp] theorem st_two : st i X o v 2 = o := rfl

theorem st_reg {r : ℕ} (h : 3 ≤ r) : st i X o v r = List.replicate (v r) true := by
  unfold st; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem upd_reg {r : ℕ} (h : 3 ≤ r) (k : ℕ) :
    update (st i X o v) r (List.replicate k true) = st i X o (update v r k) := by
  funext j; unfold st; simp only [update_apply]
  by_cases hj : j = r
  · subst hj; rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  · rw [if_neg hj, if_neg hj]

theorem upd_zero (i' : Str) : update (st i X o v) 0 i' = st i' X o v := by
  funext j; unfold st; simp only [update_apply]; split_ifs <;> simp_all

theorem upd_one (X' : Str) : update (st i X o v) 1 X' = st i X' o v := by
  funext j; unfold st; simp only [update_apply]; split_ifs <;> simp_all

theorem upd_two (o' : Str) : update (st i X o v) 2 o' = st i X o' v := by
  funext j; unfold st; simp only [update_apply]; split_ifs <;> simp_all

theorem st_congr {v v' : ℕ → ℕ} (h : ∀ j, 3 ≤ j → v j = v' j) : st i X o v = st i X o v' := by
  funext j; unfold st; split_ifs <;> try rfl
  rw [h j (by omega)]

end St

/-- Equality of register files built by `update`. -/
macro "vext" : tactic =>
  `(tactic| (funext j; simp only [update_apply]; split_ifs <;> first | omega | simp_all | skip))

/-! ## Primitive commands -/

section Prim

variable {i X o : Str}

theorem ex_push_reg {r : ℕ} (hr : 3 ≤ r) (v : ℕ → ℕ) :
    ExecLe (.push r true) (st i X o v) (.norm (st i X o (update v r (v r + 1)))) 1 := by
  refine (ExecLe.push r true _).cast ?_ le_rfl
  rw [st_reg hr, ← List.replicate_succ, upd_reg hr]

theorem ex_push_out (b : Bool) (v : ℕ → ℕ) :
    ExecLe (.push 2 b) (st i X o v) (.norm (st i X (b :: o) v)) 1 := by
  refine (ExecLe.push 2 b _).cast ?_ le_rfl
  rw [st_two, upd_two]

theorem ex_pushList_reg {r : ℕ} (hr : 3 ≤ r) (k : ℕ) (v : ℕ → ℕ) :
    ExecLe (pushList r (List.replicate k true)) (st i X o v)
      (.norm (st i X o (update v r (v r + k)))) (k + 1) := by
  refine (ExecLe.of (exec_pushList r _ _)).cast ?_ (by simp)
  rw [st_reg hr, ← List.replicate_add, Nat.add_comm, upd_reg hr]

theorem ex_pushList_out (s : Str) (v : ℕ → ℕ) :
    ExecLe (pushList 2 s) (st i X o v) (.norm (st i X (s ++ o) v)) (s.length + 1) := by
  refine (ExecLe.of (exec_pushList 2 _ _)).cast ?_ le_rfl
  rw [st_two, upd_two]

theorem ex_drain {r : ℕ} (hr : 3 ≤ r) (v : ℕ → ℕ) :
    ExecLe (drain r) (st i X o v) (.norm (st i X o (update v r 0))) (2 * v r + 2) := by
  refine (ExecLe.of (exec_drain r _ _ (st_reg hr))).cast ?_ (by simp)
  rw [show ([] : Str) = List.replicate 0 true from rfl, upd_reg hr]

theorem ex_copy {a b t : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (ht : 3 ≤ t) (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (v : ℕ → ℕ) (hv : v t = 0) :
    ExecLe (copyVia a b t) (st i X o v) (.norm (st i X o (update v b (v b + v a))))
      (5 * v a + 4) := by
  refine (ExecLe.of (exec_copyVia hab hat hbt _ (by rw [st_reg ht, hv]; rfl))).cast ?_
    (by rw [st_reg ha]; simp)
  rw [st_reg ha, st_reg hb, ← List.replicate_add, Nat.add_comm, upd_reg hb]

theorem ex_mul {a b c ta tm : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hta : 3 ≤ ta)
    (htm : 3 ≤ tm) (hab : a ≠ b) (hac : a ≠ c) (hata : a ≠ ta) (hatm : a ≠ tm)
    (hbc : b ≠ c) (hbta : b ≠ ta) (hbtm : b ≠ tm) (hcta : c ≠ ta) (hctm : c ≠ tm)
    (htatm : ta ≠ tm) (v : ℕ → ℕ) (h1 : v ta = 0) (h2 : v tm = 0) :
    ExecLe (mul a b c ta tm) (st i X o v)
      (.norm (st i X o (update v c (v c + v a * v b)))) (v a * (5 * v b + 8) + 4) := by
  refine (ExecLe.of (exec_mul hab hac hata hatm hbc hbta hbtm hcta hctm htatm (v a) (v b) _
    (st_reg ha) (st_reg hb) (by rw [st_reg hta, h1]; rfl) (by rw [st_reg htm, h2]; rfl))).cast
    ?_ le_rfl
  rw [st_reg hc, ← List.replicate_add, Nat.add_comm (v a * v b), upd_reg hc]

theorem ex_poly {xs acc nxt ta tm : ℕ} (h0 : 3 ≤ xs) (h0' : 3 ≤ acc) (h0'' : 3 ≤ nxt)
    (h0''' : 3 ≤ ta) (h0'''' : 3 ≤ tm) (h1 : acc ≠ xs) (h2 : acc ≠ nxt) (h3 : acc ≠ ta)
    (h4 : acc ≠ tm) (h5 : xs ≠ nxt) (h6 : xs ≠ ta) (h7 : xs ≠ tm) (h8 : nxt ≠ ta)
    (h9 : nxt ≠ tm) (h10 : ta ≠ tm) (q : Polynomial ℕ) (v : ℕ → ℕ) (ha : v acc = 0)
    (hn : v nxt = 0) (hta : v ta = 0) (htm : v tm = 0) :
    ExecLe (polyCmd xs acc nxt ta tm q) (st i X o v)
      (.norm (st i X o (update v acc (q.eval (v xs))))) (polyT q (v xs)) := by
  refine (ExecLe.of (exec_polyCmd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 q (v xs) _ (st_reg h0)
    (by rw [st_reg h0', ha]; rfl) (by rw [st_reg h0'', hn]; rfl) (by rw [st_reg h0''', hta]; rfl)
    (by rw [st_reg h0'''', htm]; rfl))).cast ?_ le_rfl
  rw [upd_reg h0']

/-- Decrement register `K` (if positive). -/
def decK (K : ℕ) : Cmd := .pop K .skip .skip .skip

theorem ex_decK {K : ℕ} (hK : 3 ≤ K) (v : ℕ → ℕ) :
    ExecLe (decK K) (st i X o v) (.norm (st i X o (update v K (v K - 1)))) 2 := by
  cases h : v K with
  | zero =>
    refine (ExecLe.pop_nil (by rw [st_reg hK, h]; rfl) (ExecLe.skip _)).cast ?_ le_rfl
    congr 1; apply st_congr; intro j _; simp only [update_apply]; split_ifs <;> simp_all
  | succ k =>
    refine (ExecLe.pop_cons (b := true) (s := List.replicate k true)
      (by rw [st_reg hK, h]; rfl) (ExecLe.skip _)).cast ?_ le_rfl
    rw [upd_reg hK]; simp

/-- Subtract register `N` from register `K` (truncated), using the empty temporary `t`. -/
def subLoop (K N t : ℕ) : Cmd :=
  .loop (.pop N .brk (.seq (.push t true) (decK K)) (.seq (.push t true) (decK K)))

def subCmd (K N t : ℕ) : Cmd := .seq (subLoop K N t) (move t N)

theorem ex_subLoop {K N t : ℕ} (hK : 3 ≤ K) (hN : 3 ≤ N) (ht : 3 ≤ t) (hKN : K ≠ N)
    (hKt : K ≠ t) (hNt : N ≠ t) : ∀ (k : ℕ) (v : ℕ → ℕ), v N = k →
    ExecLe (subLoop K N t) (st i X o v)
      (.norm (st i X o (update (update (update v N 0) t (v t + k)) K (v K - k)))) (4 * k + 2)
  | 0, v, h => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil (by rw [st_reg hN, h]; rfl) (ExecLe.brk _))).cast
      ?_ (by omega)
    congr 1; apply st_congr; intro j _; simp only [update_apply]; split_ifs <;> simp_all
  | k + 1, v, h => by
    have h1 := ex_push_reg (i := i) (X := X) (o := o) ht (update v N k)
    have h2 := ex_decK (i := i) (X := X) (o := o) hK
      (update (update v N k) t (update v N k t + 1))
    have hb := ExecLe.pop_same (k := N) (σ := st i X o v) (cn := .brk) (b := true)
      (s := List.replicate k true)
      (by rw [st_reg hN, h]; rfl) (by rw [upd_reg hN]; exact h1.seq_norm h2)
    have ih := ex_subLoop hK hN ht hKN hKt hNt k
      (update (update (update v N k) t (update v N k t + 1)) K
        (update (update v N k) t (update v N k t + 1) K - 1)) (by simp [hKN.symm, hNt])
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    congr 1; apply st_congr; intro j _
    simp only [update_apply]; split_ifs <;> simp_all <;> omega

theorem ex_sub {K N t : ℕ} (hK : 3 ≤ K) (hN : 3 ≤ N) (ht : 3 ≤ t) (hKN : K ≠ N)
    (hKt : K ≠ t) (hNt : N ≠ t) (v : ℕ → ℕ) (hv : v t = 0) :
    ExecLe (subCmd K N t) (st i X o v) (.norm (st i X o (update v K (v K - v N))))
      (6 * v N + 4) := by
  have h1 := ex_subLoop (i := i) (X := X) (o := o) hK hN ht hKN hKt hNt (v N) v rfl
  set v1 := update (update (update v N 0) t (v t + v N)) K (v K - v N)
  have h2 := exec_move (Ne.symm hNt) _ (st i X o v1) rfl
  refine (h1.seq_norm (ExecLe.of h2)).cast ?_ (by rw [st_reg ht]; simp [v1, hKt.symm]; omega)
  have e1 : v1 t = v N := by simp [v1, hKt.symm, hv]
  have e2 : v1 N = 0 := by simp [v1, hKN.symm, hNt]
  rw [st_reg ht, st_reg hN, List.reverse_replicate, e1, e2, List.replicate_zero, List.append_nil]
  rw [show ([] : Str) = List.replicate 0 true from rfl, upd_reg ht, upd_reg hN]
  congr 1; apply st_congr; intro j _
  simp only [v1, update_apply]; split_ifs <;> simp_all

end Prim

/-! ## Emitting zeros -/

section Zeros

variable {i X o : Str}

/-- Body of `zLoop`: count the popped mark on `t`, emit `zero`. -/
def zB (t : ℕ) : Cmd := .seq (.push t true) (.seq (.push 2 false) (.push 2 true))

def zLoop (r t : ℕ) : Cmd := .loop (.pop r .brk (zB t) (zB t))

/-- Emit `v r` symbols `zero` (register `r` is restored, `t` is an empty temporary). -/
def zerosR (r t : ℕ) : Cmd := .seq (zLoop r t) (move t r)

theorem ex_zLoop {r t : ℕ} (hr : 3 ≤ r) (ht : 3 ≤ t) (hrt : r ≠ t) : ∀ (k : ℕ) (v : ℕ → ℕ)
    (o : Str), v r = k →
    ExecLe (zLoop r t) (st i X o v)
      (.norm (st i X (rv (zs k) ++ o) (update (update v r 0) t (v t + k)))) (4 * k + 2)
  | 0, v, o, h => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil (by rw [st_reg hr, h]; rfl) (ExecLe.brk _))).cast
      ?_ (by omega)
    congr 1; simp only [zs, List.replicate_zero, rv_nil, List.nil_append]
    apply st_congr; intro j _; simp only [update_apply]; split_ifs <;> simp_all
  | k + 1, v, o, h => by
    have h1 := ex_push_reg (i := i) (X := X) (o := o) ht (update v r k)
    have h2 := ex_push_out (i := i) (X := X) (o := o) false (update (update v r k) t
      (update v r k t + 1))
    have h3 := ex_push_out (i := i) (X := X) (o := false :: o) true (update (update v r k) t
      (update v r k t + 1))
    have hb := ExecLe.pop_same (k := r) (σ := st i X o v) (cn := .brk) (b := true)
      (s := List.replicate k true) (by rw [st_reg hr, h]; rfl)
      (by rw [upd_reg hr]; exact h1.seq_norm (h2.seq_norm h3))
    have ih := ex_zLoop hr ht hrt k (update (update v r k) t (update v r k t + 1))
      (true :: false :: o) (by simp [hrt])
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    rw [rv_zs_succ, List.append_assoc]
    congr 1; apply st_congr; intro j _
    simp only [update_apply]; split_ifs <;> simp_all <;> omega

theorem ex_zerosR {r t : ℕ} (hr : 3 ≤ r) (ht : 3 ≤ t) (hrt : r ≠ t) (v : ℕ → ℕ) (hv : v t = 0)
    (o : Str) :
    ExecLe (zerosR r t) (st i X o v) (.norm (st i X (rv (zs (v r)) ++ o) v)) (6 * v r + 4) := by
  have h1 := ex_zLoop (i := i) (X := X) hr ht hrt (v r) v o rfl
  set v1 := update (update v r 0) t (v t + v r)
  have h2 := exec_move (Ne.symm hrt) _ (st i X (rv (zs (v r)) ++ o) v1) rfl
  have e1 : v1 t = v r := by simp [v1, hv]
  have e2 : v1 r = 0 := by simp [v1, hrt]
  refine (h1.seq_norm (ExecLe.of h2)).cast ?_ (by rw [st_reg ht, e1]; simp; omega)
  rw [st_reg ht, st_reg hr, List.reverse_replicate, e1, e2, List.replicate_zero, List.append_nil]
  rw [show ([] : Str) = List.replicate 0 true from rfl, upd_reg ht, upd_reg hr]
  congr 1; apply st_congr; intro j _
  simp only [v1, update_apply]; split_ifs <;> simp_all

end Zeros

/-! ## Emission -/

/-- `c` appends the code of `L` to the output within `T` steps, keeping everything else. -/
def Em (c : Cmd) (v : ℕ → ℕ) (L : List SatSym) (T : ℕ) : Prop :=
  ∀ i X o, ExecLe c (st i X o v) (.norm (st i X (rv L ++ o) v)) T

theorem Em.mono {c : Cmd} {v : ℕ → ℕ} {L : List SatSym} {T T' : ℕ} (h : Em c v L T)
    (hT : T ≤ T') : Em c v L T' := fun i X o => (h i X o).mono hT

theorem Em.seq {c d : Cmd} {v : ℕ → ℕ} {L₁ L₂ : List SatSym} {T₁ T₂ : ℕ} (h1 : Em c v L₁ T₁)
    (h2 : Em d v L₂ T₂) : Em (.seq c d) v (L₁ ++ L₂) (T₁ + T₂) := fun i X o =>
  ((h1 i X o).seq_norm (h2 i X _)).cast (by rw [rv_append, List.append_assoc]) le_rfl

theorem Em.cmdSeq {α : Type} {v : ℕ → ℕ} (f : α → Cmd) (g : α → List SatSym) (T : ℕ) :
    ∀ (cs : List α), (∀ a ∈ cs, Em (f a) v (g a) T) →
      Em (cmdSeq (cs.map f)) v (cs.flatMap g) (cs.length * T + 1)
  | [], _ => fun i X o => (ExecLe.skip _).cast (by simp) (by simp)
  | a :: cs, h => by
    have := (h a (by simp)).seq (Em.cmdSeq f g T cs (fun b hb => h b (by simp [hb])))
    refine (this.mono ?_)
    simp only [List.length_cons]; rw [Nat.succ_mul]; omega

/-- Items of a line: a fixed list of symbols, or as many `zero`s as a register says. -/
inductive It
  | lit (l : List SatSym)
  | reg (r : ℕ)

def It.cmd : It → Cmd
  | .lit l => pushList 2 (rv l)
  | .reg r => zerosR r 7

def It.sem (v : ℕ → ℕ) : It → List SatSym
  | .lit l => l
  | .reg r => zs (v r)

/-- Cost factor of an item. -/
def It.cost : It → ℕ
  | .lit l => 2 * l.length + 1
  | .reg _ => 10

/-- Registers allowed in lines (`v r ≤ Λ`). -/
def It.Ok (v : ℕ → ℕ) (Λ : ℕ) : It → Prop
  | .lit _ => True
  | .reg r => 3 ≤ r ∧ r ≠ 7 ∧ v r ≤ Λ

theorem It.em {v : ℕ → ℕ} {Λ : ℕ} (h7 : v 7 = 0) : ∀ it : It, it.Ok v Λ →
    Em it.cmd v (it.sem v) (it.cost * (Λ + 1))
  | .lit l, _ => fun i X o => (ex_pushList_out (rv l) v).cast rfl (by
      simp only [length_rv, It.cost]; nlinarith)
  | .reg r, ⟨h1, h2, h3⟩ => fun i X o => (ex_zerosR h1 (by norm_num) h2 v h7 o).cast rfl (by
      simp only [It.cost]; nlinarith)

/-- A line: items in order. -/
def lineCmd (its : List It) : Cmd := cmdSeq (its.map It.cmd)

def lineSem (v : ℕ → ℕ) (its : List It) : List SatSym := its.flatMap (It.sem v)

/-- Cost factor of a line. -/
def lineCost (its : List It) : ℕ := (its.map It.cost).sum + 1

theorem lineCmd_em {v : ℕ → ℕ} {Λ : ℕ} (h7 : v 7 = 0) : ∀ (its : List It),
    (∀ it ∈ its, it.Ok v Λ) → Em (lineCmd its) v (lineSem v its) (lineCost its * (Λ + 1))
  | [], _ => fun i X o => (ExecLe.skip _).cast (by simp [lineSem]) (by simp [lineCost])
  | it :: its, h => by
    have := (It.em h7 it (h it (by simp))).seq (lineCmd_em h7 its (fun b hb => h b (by simp [hb])))
    refine (this.mono ?_)
    simp only [lineCost, List.map_cons, List.sum_cons]; nlinarith

/-- A list of lines. -/
def linesCmd (ls : List (List It)) : Cmd := cmdSeq (ls.map lineCmd)

def linesSem (v : ℕ → ℕ) (ls : List (List It)) : List SatSym := ls.flatMap (lineSem v)

def linesCost (ls : List (List It)) : ℕ := (ls.map lineCost).sum + 1

theorem linesCmd_em {v : ℕ → ℕ} {Λ : ℕ} (h7 : v 7 = 0) : ∀ (ls : List (List It)),
    (∀ l ∈ ls, ∀ it ∈ l, it.Ok v Λ) → Em (linesCmd ls) v (linesSem v ls) (linesCost ls * (Λ + 1))
  | [], _ => fun i X o => (ExecLe.skip _).cast (by simp [linesSem]) (by simp [linesCost])
  | l :: ls, h => by
    have := (lineCmd_em h7 l (h l (by simp))).seq
      (linesCmd_em h7 ls (fun b hb => h b (by simp [hb])))
    refine (this.mono ?_)
    simp only [linesCost, List.map_cons, List.sum_cons]; nlinarith

/-! ## Counting loops -/

/-- Run `body` once per mark of register `K`. -/
def forLoop (K : ℕ) (body : Cmd) : Cmd := .loop (.pop K .brk body body)

theorem ex_forLoop {K : ℕ} (hK : 3 ≤ K) {body : Cmd} {i X : Str} (m : ℕ) (f : ℕ → ℕ → ℕ)
    (E : ℕ → List SatSym) (Tb : ℕ) (hf : ∀ k ≤ m, f k K = m - k)
    (hb : ∀ k < m, ∀ o, ExecLe body (st i X o (update (f k) K (m - k - 1)))
      (.norm (st i X (rv (E k) ++ o) (f (k + 1)))) Tb) (o : Str) :
    ExecLe (forLoop K body) (st i X o (f 0))
      (.norm (st i X (rv ((List.range m).flatMap E) ++ o) (f m))) (m * (Tb + 1) + 2) := by
  have := ExecLe.loop_iter (c := .pop K .brk body body) (T := Tb + 1)
    (r := .norm (st i X (rv ((List.range m).flatMap E) ++ o) (f m))) (T' := 2) m
    (fun k => st i X (rv ((List.range k).flatMap E) ++ o) (f k)) (fun k hk => by
      have e : st i X (rv ((List.range k).flatMap E) ++ o) (f k) K =
          true :: List.replicate (m - k - 1) true := by
        rw [st_reg hK, hf k (by omega), ← List.replicate_succ]; congr 1; omega
      refine ExecLe.pop_same e ?_
      rw [upd_reg hK]
      refine (hb k hk _).cast ?_ le_rfl
      rw [List.range_succ, List.flatMap_append, rv_append, List.flatMap_singleton,
        List.append_assoc])
    (ExecLe.loop_brk (ExecLe.pop_nil (by rw [st_reg hK, hf m le_rfl]; simp) (ExecLe.brk _)))
  simpa [forLoop] using this

/-! ## Parsing the input in blocks -/

/-- Decoding of the input in blocks of `r + 1` bits: the position of the first `true` of each
block (`0` if there is none). -/
def blocks (r : ℕ) : Str → List ℕ
  | [] => []
  | b :: l => (fi (r + 1) (b :: l)).getD 0 :: blocks r (l.drop r)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

theorem blocks_nil (r : ℕ) : blocks r [] = [] := by rw [blocks]

theorem blocks_cons (r : ℕ) (b : Bool) (l : Str) :
    blocks r (b :: l) = (fi (r + 1) (b :: l)).getD 0 :: blocks r (l.drop r) := by rw [blocks]

theorem blocks_length_le (r : ℕ) : ∀ l : Str, (blocks r l).length ≤ l.length
  | [] => by simp [blocks_nil]
  | b :: l => by
    have := blocks_length_le r (l.drop r)
    rw [blocks_cons]; simp only [List.length_cons, List.length_drop] at this ⊢; omega
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- Count the blocks of stack `0` on register `3`. -/
def cntLoop (r : ℕ) : Cmd :=
  .loop (.pop 0 .brk (.seq (dropN 0 r) (.push 3 true)) (.seq (dropN 0 r) (.push 3 true)))

theorem ex_cntLoop (r : ℕ) (X o : Str) : ∀ (l : Str) (v : ℕ → ℕ),
    ExecLe (cntLoop r) (st l X o v)
      (.norm (st [] X o (update v 3 (v 3 + (blocks r l).length)))) (l.length * (r + 4) + 2)
  | [], v => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil (by rfl) (ExecLe.brk _))).cast ?_ (by simp)
    rw [blocks_nil, List.length_nil, Nat.add_zero, update_eq_self]
  | b :: l, v => by
    have h1 := exec_dropN 0 r (st l X o v)
    rw [st_zero, upd_zero] at h1
    have h2 := ex_push_reg (i := l.drop r) (X := X) (o := o) (le_refl 3) v
    have hb := ExecLe.pop_same (k := 0) (σ := st (b :: l) X o v) (cn := .brk) (b := b) (s := l)
      rfl (by rw [upd_zero]; exact h1.seq_norm h2)
    have ih := ex_cntLoop r X o (l.drop r) (update v 3 (v 3 + 1))
    refine (ExecLe.loop_norm hb ih).cast ?_ ?_
    · rw [blocks_cons]; congr 1; apply st_congr; intro j _
      simp only [update_apply, List.length_cons]; split_ifs <;> simp_all <;> omega
    · simp only [List.length_cons, List.length_drop]
      have : (l.length - r) * (r + 4) ≤ l.length * (r + 4) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- Table look-up of one block on stack `1` with arbitrary actions (cf. `tabK`). -/
def tabC (acts : ℕ → Cmd) (d : ℕ) : ℕ → ℕ → Cmd
  | _, 0 => acts d
  | i, r + 1 => .pop 1 (acts d) (tabC acts d (i + 1) r) (.seq (dropN 1 r) (acts i))

theorem ex_tabC (acts : ℕ → Cmd) (d : ℕ) (E : ℕ → List SatSym) {i : Str} {v v' : ℕ → ℕ}
    {A : ℕ} (ha : ∀ j X o, ExecLe (acts j) (st i X o v) (.norm (st i X (rv (E j) ++ o) v')) A) :
    ∀ (r idx : ℕ) (l o : Str), ExecLe (tabC acts d idx r) (st i l o v)
      (.norm (st i (l.drop r) (rv (E ((fi r l).elim d (idx + ·))) ++ o) v')) (2 * r + A + 1)
  | 0, idx, l, o => (ha d l o).cast (by simp [fi]) (by omega)
  | r + 1, idx, [], o => (ExecLe.pop_nil rfl (ha d [] o)).cast (by simp) (by omega)
  | r + 1, idx, false :: l, o => by
    have ih := ex_tabC acts d E ha r (idx + 1) l o
    refine (ExecLe.pop_cons (b := false) (s := l) rfl (by rw [upd_one]; exact ih)).cast ?_
      (by omega)
    rw [fi_false, List.drop_succ_cons]
    cases fi r l with
    | none => rfl
    | some x =>
      simp only [Option.map_some, Option.elim_some]
      rw [show idx + 1 + x = idx + (x + 1) by omega]
  | r + 1, idx, true :: l, o => by
    have h1 := exec_dropN 1 r (st i l o v)
    rw [st_one, upd_one] at h1
    refine (ExecLe.pop_cons (b := true) (s := l) rfl (by
      rw [upd_one]; exact h1.seq_norm (ha idx _ o))).cast ?_ (by omega)
    rw [fi_true]; simp

/-- Output of the parsing loop: `E c j` for the `j`-th block at column `c`, columns `w` apart. -/
def pN (E : ℕ → ℕ → List SatSym) (w : ℕ) : ℕ → List ℕ → List SatSym
  | _, [] => []
  | c, j :: js => E c j ++ pN E w (c + w) js

/-- The parsing loop: one table look-up per block of `r + 1` bits of stack `1`. -/
def parseLoop (r : ℕ) (acts : ℕ → Cmd) : Cmd :=
  .loop (.pop 1 .brk (tabC acts 0 1 r) (.seq (dropN 1 r) (acts 0)))

theorem ex_parseLoop (r : ℕ) (acts : ℕ → Cmd) (E : ℕ → ℕ → List SatSym) (w Λ A : ℕ) {i : Str}
    (V : ℕ → ℕ → ℕ)
    (ha : ∀ c ≤ Λ, ∀ j X o, ExecLe (acts j) (st i X o (V c))
      (.norm (st i X (rv (E c j) ++ o) (V (c + w)))) A) :
    ∀ (l : Str) (c : ℕ) (o : Str), c + l.length * w ≤ Λ →
      ExecLe (parseLoop r acts) (st i l o (V c))
        (.norm (st i [] (rv (pN E w c (blocks r l)) ++ o) (V (c + (blocks r l).length * w))))
        (l.length * (2 * r + A + 3) + 2)
  | [], c, o, _ => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil (by rfl) (ExecLe.brk _))).cast ?_ (by simp)
    simp [blocks_nil, pN]
  | b :: l, c, o, hc => by
    have hc' : c ≤ Λ := by simp at hc; nlinarith
    have ih := ex_parseLoop r acts E w Λ A V ha (l.drop r) (c + w)
      (rv (E c ((fi (r + 1) (b :: l)).getD 0)) ++ o) (by
        simp only [List.length_drop, List.length_cons] at hc ⊢
        have : (l.length - r) * w ≤ l.length * w := Nat.mul_le_mul_right _ (by omega)
        nlinarith)
    have hb : ExecLe (.pop 1 .brk (tabC acts 0 1 r) (.seq (dropN 1 r) (acts 0))) (st i (b :: l) o (V c))
        (.norm (st i (l.drop r) (rv (E c ((fi (r + 1) (b :: l)).getD 0)) ++ o) (V (c + w))))
        (2 * r + A + 2) := by
      cases b
      · have h := ex_tabC acts 0 (E c) (ha c hc') r 1 l o
        refine (ExecLe.pop_cons (b := false) (s := l) rfl (by rw [upd_one]; exact h)).cast ?_
          (by omega)
        rw [fi_false]; congr 4
        cases fi r l <;> simp [Nat.add_comm 1]
      · have h1 := exec_dropN 1 r (st i l o (V c))
        rw [st_one, upd_one] at h1
        refine (ExecLe.pop_cons (b := true) (s := l) rfl (by
          rw [upd_one]; exact h1.seq_norm (ha c hc' 0 _ o))).cast ?_ (by omega)
        rw [fi_true]; simp
    refine (ExecLe.loop_norm hb ih).cast ?_ ?_
    · rw [blocks_cons]
      simp only [pN, rv_append, List.append_assoc, List.length_cons]
      congr 3; ring
    · simp only [List.length_cons, List.length_drop]
      have : (l.length - r) * (2 * r + A + 3) ≤ l.length * (2 * r + A + 3) :=
        Nat.mul_le_mul_right _ (by omega)
      nlinarith
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

end Pnp.CookLevin.Uniform
