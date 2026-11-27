import Pnp.Karp.ThreeDM
import Pnp.Karp.CliqueVer

/-!
# 3-DIMENSIONAL MATCHING ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/ThreeDM.lean`) and a certificate `y : List Bool` (bit `i` says whether row `i` of
the set rows is selected; missing bits are `false`).  Let `u :: rs = clauses w` and `q = |u|`.

Stacks (fields of `mv_S`): `0` the unread certificate `R`; `3` the code `Q` of the remaining
rows; `4` the unary `A = false^(q-1)`; `5` the block-end markers `E` (`mv_E (q-1)`: `true`
exactly at the positions `q-1`, `2q-1`, `3q-1`); `6` the consumed markers `E2` (reversed);
`7` the coverage bits `C` (position `p` covered by a selected row so far); `8` the new coverage
bits `C2` (reversed); `9` the flag `F` ("a `pos` was seen in the current block"); `10` a
temporary.

Program (`mv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3` (as for SUBSET SUM); `mv_hdL`: read the header into `A`
   (halt `false` if there is no row);
2. `mv_start`: if `q = 0`, accept iff there are no further rows; otherwise drop one mark of
   `A` and build `E` and `C = false^(3q)` (`mv_bld`);
3. `mv_mainL`: per row, pop a certificate bit `sel`, and walk the row together with `E` and `C`
   (`mv_rowL sel`): a second `pos` in a block, a block without `pos`, a wrong length, or a
   selected `pos` at an already covered position rejects; the coverage bits are updated; at the
   end of the input all coverage bits must be set (`mv_finL`).

`mv_exec_ver`: the program halts with `mv_vres (dec z).1 (dec z).2` on every input `z`,
within `mv_Tver |z| ≤ tb 6 |z|` steps.
-/

namespace Pnp.Karp.ThreeDM

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics -/

/-- The rejection condition of one step (`p`: the symbol is `pos`, `e`: block end, `c`: the
coverage bit, `f`: a `pos` was seen in the current block). -/
def mv_bad (sel p e c f : Bool) : Bool := (p && f) || (e && !(f || p)) || (sel && p && c)

/-- The new flag. -/
def mv_nf (p e f : Bool) : Bool := !e && (f || p)

/-- What the row loop computes: `none` (reject) or the new coverage bits. -/
def mv_row (sel : Bool) : List SatSym → Str → Str → Bool → Option Str
  | [], [], C, _ => some C
  | [], _ :: _, _, _ => none
  | _ :: _, [], _, _ => none
  | s :: r, e :: E, C, f =>
    if mv_bad sel (isPos s) e (C.headD false) f then none
    else (mv_row sel r E C.tail (mv_nf (isPos s) e f)).map ((C.headD false || sel && isPos s) :: ·)

/-- What the main loop computes. -/
def mv_go (E : Str) : List (List SatSym) → Str → Str → Bool
  | [], _, C => C.all id
  | r :: rows, R, C => match mv_row (R.headD false) r E C false with
    | none => false
    | some C' => mv_go E rows R.tail C'

/-- The block-end markers for `q = k + 1`. -/
def mv_E (k : ℕ) : Str :=
  List.replicate k false ++ true :: (List.replicate k false ++ true :: (List.replicate k false ++
    [true]))

/-- The initial coverage bits for `q = k + 1`. -/
def mv_C (k : ℕ) : Str :=
  List.replicate k false ++ false :: (List.replicate k false ++ false ::
    (List.replicate k false ++ [false]))

/-- The answer of the verifier on `(w, y)`. -/
def mv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | [] :: rs => rs.isEmpty
  | (_ :: u) :: rs => mv_go (mv_E u.length) rs y (mv_C u.length)

theorem mv_row_len (sel : Bool) : ∀ (r : List SatSym) (E C : Str) (f : Bool) (C' : Str),
    mv_row sel r E C f = some C' → C'.length ≤ C.length + r.length
  | [], [], C, f, C', h => by simp [mv_row] at h; subst h; simp
  | [], _ :: _, _, _, _, h => by simp [mv_row] at h
  | _ :: _, [], _, _, _, h => by simp [mv_row] at h
  | s :: r, e :: E, C, f, C', h => by
    simp only [mv_row] at h
    split_ifs at h
    obtain ⟨C'', h1, rfl⟩ := Option.map_eq_some_iff.1 h
    have := mv_row_len sel r E C.tail _ C'' h1
    have : C.tail.length ≤ C.length := by simp
    simp only [List.length_cons]; omega

/-! ## Stack layout -/

/-- The stacks of the verifier. -/
structure mv_S where
  R : Str
  Q : Str
  A : Str
  E : Str
  E2 : Str
  C : Str
  C2 : Str
  F : Str
  T : Str

/-- The stack assignment of a record. -/
def mv_S.st (s : mv_S) : ℕ → Str := fun j =>
  if j = 0 then s.R else if j = 3 then s.Q else if j = 4 then s.A else if j = 5 then s.E else
  if j = 6 then s.E2 else if j = 7 then s.C else if j = 8 then s.C2 else if j = 9 then s.F else
  if j = 10 then s.T else []

theorem mv_st_big (s : mv_S) (j : ℕ) (h : 11 ≤ j) : s.st j = [] := by
  unfold mv_S.st; repeat rw [if_neg (by omega)]

local macro "mvx" : tactic =>
  `(tactic| (funext j; by_cases h : j < 11
             · interval_cases j <;> rfl
             · rw [update_of_ne (by omega), mv_st_big _ _ (by omega), mv_st_big _ _ (by omega)]))

section St
variable (s : mv_S) (v : Str)
@[simp] theorem mv_st0 : s.st 0 = s.R := rfl
@[simp] theorem mv_st3 : s.st 3 = s.Q := rfl
@[simp] theorem mv_st4 : s.st 4 = s.A := rfl
@[simp] theorem mv_st5 : s.st 5 = s.E := rfl
@[simp] theorem mv_st6 : s.st 6 = s.E2 := rfl
@[simp] theorem mv_st7 : s.st 7 = s.C := rfl
@[simp] theorem mv_st8 : s.st 8 = s.C2 := rfl
@[simp] theorem mv_st9 : s.st 9 = s.F := rfl
@[simp] theorem mv_st10 : s.st 10 = s.T := rfl
@[simp] theorem mv_u0 : update s.st 0 v = {s with R := v}.st := by mvx
@[simp] theorem mv_u3 : update s.st 3 v = {s with Q := v}.st := by mvx
@[simp] theorem mv_u4 : update s.st 4 v = {s with A := v}.st := by mvx
@[simp] theorem mv_u5 : update s.st 5 v = {s with E := v}.st := by mvx
@[simp] theorem mv_u6 : update s.st 6 v = {s with E2 := v}.st := by mvx
@[simp] theorem mv_u7 : update s.st 7 v = {s with C := v}.st := by mvx
@[simp] theorem mv_u8 : update s.st 8 v = {s with C2 := v}.st := by mvx
@[simp] theorem mv_u9 : update s.st 9 v = {s with F := v}.st := by mvx
@[simp] theorem mv_u10 : update s.st 10 v = {s with T := v}.st := by mvx
end St

/-! ## Generic commands -/

/-- Pop with default `false` on an empty stack. -/
theorem mv_popD {k : ℕ} {C : Bool → Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ}
    (h : ExecLe (C ((σ k).headD false)) (update σ k (σ k).tail) r T) :
    ExecLe (.pop k (C false) (C false) (C true)) σ r (T + 1) := by
  cases hk : σ k with
  | nil =>
    rw [hk] at h
    simp only [List.headD_nil, List.tail_nil] at h
    rw [← hk, update_eq_self] at h
    exact ExecLe.pop_nil hk h
  | cons b l =>
    rw [hk] at h
    exact ExecLe.pop_cons hk (by cases b <;> simpa using h)

/-- Select a branch by a symbol. -/
def mv_sel (s : SatSym) (cS cZ cP cN : Cmd) : Cmd :=
  match s with
  | sep => cS
  | zero => cZ
  | pos => cP
  | neg => cN

theorem mv_pop2 {s : mv_S} {cE cX cS cZ cP cN : Cmd} (x : SatSym) (Q' : Str) {r : Res}
    {T : ℕ} (hQ : s.Q = ic x ++ Q') (h : ExecLe (mv_sel x cS cZ cP cN) {s with Q := Q'}.st r T) :
    ExecLe (.pop 3 cE (.pop 3 cX cS cZ) (.pop 3 cX cP cN)) s.st r (T + 2) := by
  cases x with
  | sep =>
    exact ExecLe.pop_cons (b := false) (s := false :: Q') (by simp [hQ, ic])
      (ExecLe.pop_cons (b := false) (s := Q') (by simp) (by simpa [mv_sel] using h))
  | zero =>
    exact ExecLe.pop_cons (b := false) (s := true :: Q') (by simp [hQ, ic])
      (ExecLe.pop_cons (b := true) (s := Q') (by simp) (by simpa [mv_sel] using h))
  | pos =>
    exact ExecLe.pop_cons (b := true) (s := false :: Q') (by simp [hQ, ic])
      (ExecLe.pop_cons (b := false) (s := Q') (by simp) (by simpa [mv_sel] using h))
  | neg =>
    exact ExecLe.pop_cons (b := true) (s := true :: Q') (by simp [hQ, ic])
      (ExecLe.pop_cons (b := true) (s := Q') (by simp) (by simpa [mv_sel] using h))

/-! ## Reading the header -/

def mv_hdB : Cmd := .pop 3 (.halt false) (.pop 3 (.halt false) .brk (.push 4 false))
    (.pop 3 (.halt false) (.push 4 false) (.push 4 false))

def mv_hdL : Cmd := .loop mv_hdB

theorem mv_ex_hd (Q' : Str) : ∀ (t : List SatSym) (s : mv_S), sep ∉ t →
    s.Q = t.flatMap ic ++ false :: false :: Q' →
    ExecLe mv_hdL s.st
      (.norm {s with Q := Q', A := List.replicate t.length false ++ s.A}.st) (3 * t.length + 3)
  | [], s, _, hQ => (ExecLe.loop_brk (mv_pop2 (cS := .brk) sep Q' (by simpa [ic] using hQ)
      (ExecLe.brk _))).cast (by simp) (by simp)
  | x :: t, s, ht, hQ => by
    have hx : x ≠ sep := fun e => ht (e ▸ List.mem_cons_self ..)
    set s' : mv_S := {s with Q := t.flatMap ic ++ false :: false :: Q', A := false :: s.A}
    have ih := mv_ex_hd Q' t s' (fun e => ht (List.mem_cons_of_mem _ e)) rfl
    have hb : ExecLe mv_hdB s.st (.norm s'.st) 3 := by
      refine mv_pop2 (cS := .brk) (cZ := .push 4 false) (cP := .push 4 false)
        (cN := .push 4 false) x (t.flatMap ic ++ false :: false :: Q') (by simp [hQ]) ?_
      have e : mv_sel x .brk (.push 4 false) (.push 4 false) (.push 4 false) = .push 4 false := by
        cases x <;> simp_all [mv_sel]
      rw [e]
      exact (ExecLe.push 4 false _).cast (by simp [s']) le_rfl
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp [s', List.replicate_succ']

theorem mv_ex_hd_nil (s : mv_S) (hQ : s.Q = []) : ExecLe mv_hdL s.st (.halt false) 2 :=
  ExecLe.loop_halt (ExecLe.pop_nil (by simpa using hQ) (ExecLe.halt false _))

/-! ## Initialization -/

/-- Push `b` on stack `k`, then a copy of `A`. -/
def mv_pc (k : ℕ) (b : Bool) : Cmd := .seq (.push k b) (copyVia 4 k 10)

theorem mv_ex_pc5 (b : Bool) (s : mv_S) (hT : s.T = []) :
    ExecLe (mv_pc 5 b) s.st (.norm {s with E := s.A ++ b :: s.E}.st) (5 * s.A.length + 5) := by
  have h1 := ExecLe.push 5 b s.st
  simp only [mv_st5, mv_u5] at h1
  have h2 := ExecLe.of (exec_copyVia (a := 4) (b := 5) (t := 10) (by decide) (by decide)
    (by decide) {s with E := b :: s.E}.st (by simpa using hT))
  simp only [mv_st4, mv_st5, mv_u5] at h2
  exact (h1.seq_norm h2).cast (by simp) (by omega)

theorem mv_ex_pc7 (b : Bool) (s : mv_S) (hT : s.T = []) :
    ExecLe (mv_pc 7 b) s.st (.norm {s with C := s.A ++ b :: s.C}.st) (5 * s.A.length + 5) := by
  have h1 := ExecLe.push 7 b s.st
  simp only [mv_st7, mv_u7] at h1
  have h2 := ExecLe.of (exec_copyVia (a := 4) (b := 7) (t := 10) (by decide) (by decide)
    (by decide) {s with C := b :: s.C}.st (by simpa using hT))
  simp only [mv_st4, mv_st7, mv_u7] at h2
  exact (h1.seq_norm h2).cast (by simp) (by omega)

def mv_bld : Cmd :=
  .seq (mv_pc 5 true) (.seq (mv_pc 5 true) (.seq (mv_pc 5 true)
    (.seq (mv_pc 7 false) (.seq (mv_pc 7 false) (mv_pc 7 false)))))

theorem mv_ex_bld (k : ℕ) (s : mv_S) (hA : s.A = List.replicate k false) (hT : s.T = [])
    (hE : s.E = []) (hC : s.C = []) :
    ExecLe mv_bld s.st (.norm {s with E := mv_E k, C := mv_C k}.st) (30 * k + 30) := by
  have h1 := mv_ex_pc5 true s hT
  have h2 := mv_ex_pc5 true {s with E := s.A ++ true :: s.E} hT
  have h3 := mv_ex_pc5 true {s with E := s.A ++ true :: (s.A ++ true :: s.E)} hT
  set s3 : mv_S := {s with E := s.A ++ true :: (s.A ++ true :: (s.A ++ true :: s.E))}
  have h4 := mv_ex_pc7 false s3 hT
  have h5 := mv_ex_pc7 false {s3 with C := s3.A ++ false :: s3.C} hT
  have h6 := mv_ex_pc7 false {s3 with C := s3.A ++ false :: (s3.A ++ false :: s3.C)} hT
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm h6))))).cast ?_ ?_
  · simp [s3, hA, hE, hC, mv_E, mv_C]
  · simp [s3, hA]; omega

/-- If `q = 0`: accept iff there are no further rows. -/
def mv_q0 : Cmd := .pop 3 (.halt true) (.halt false) (.halt false)

def mv_start : Cmd := .pop 4 mv_q0 mv_bld mv_bld

theorem mv_ex_q0 (rs : List (List SatSym)) (s : mv_S) (hQ : s.Q = enc rs) :
    ExecLe mv_q0 s.st (.halt rs.isEmpty) 2 := by
  rcases rs with _ | ⟨r, rs⟩
  · exact (ExecLe.pop_nil (by simp [hQ, enc]) (ExecLe.halt true _)).cast (by simp) le_rfl
  · rw [enc_cons] at hQ
    obtain ⟨b, l, hbl⟩ : ∃ b l, r.flatMap ic ++ false :: false :: enc rs = b :: l := by
      rcases r with _ | ⟨x, r⟩
      · exact ⟨_, _, rfl⟩
      · cases x <;> exact ⟨_, _, rfl⟩
    exact (ExecLe.pop_cons (b := b) (s := l) (by simp [hQ, hbl])
      (by cases b <;> exact ExecLe.halt false _)).cast (by simp) le_rfl

/-! ## One step of the row loop -/

theorem mv_pop3 {k : ℕ} {c : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ}
    (h : ExecLe c (update σ k (σ k).tail) r T) : ExecLe (.pop k c c c) σ r (T + 1) := by
  cases hk : σ k with
  | nil =>
    rw [hk, List.tail_nil, ← hk, update_eq_self] at h
    exact ExecLe.pop_nil hk h
  | cons b s =>
    rw [hk, List.tail_cons] at h
    exact ExecLe.pop_same hk h

/-- The leaf of a step: reject, or record the marker, the new coverage bit and the flag. -/
def mv_leaf (sel p e c f : Bool) : Cmd :=
  if mv_bad sel p e c f then .halt false else
  .seq (.push 6 e) (.seq (.push 8 (c || sel && p)) (if mv_nf p e f then .push 9 true else .skip))

theorem mv_ex_leaf (sel p e c f : Bool) (s : mv_S) (hF : s.F = []) :
    ExecLe (mv_leaf sel p e c f) s.st
      (if mv_bad sel p e c f then .halt false else
        .norm {s with E2 := e :: s.E2, C2 := (c || sel && p) :: s.C2,
                      F := CookLevin.fl (mv_nf p e f)}.st) 3 := by
  unfold mv_leaf
  cases hb : mv_bad sel p e c f
  · simp only [Bool.false_eq_true, if_false]
    have h1 := ExecLe.push 6 e s.st
    simp only [mv_st6, mv_u6] at h1
    have h2 := ExecLe.push 8 (c || sel && p) {s with E2 := e :: s.E2}.st
    simp only [mv_st8, mv_u8] at h2
    cases hn : mv_nf p e f
    · simp only [Bool.false_eq_true, if_false]
      exact (h1.seq_norm (h2.seq_norm (ExecLe.skip _))).cast
        (by simp [hF, CookLevin.fl]) le_rfl
    · simp only [if_true]
      exact (h1.seq_norm (h2.seq_norm (ExecLe.push 9 true _))).cast
        (by simp [hF, CookLevin.fl]) le_rfl
  · simp only [if_true]; exact (ExecLe.halt false _).cast rfl (by omega)

def mv_stC (sel p e c : Bool) : Cmd :=
  .pop 9 (mv_leaf sel p e c false) (mv_leaf sel p e c false) (mv_leaf sel p e c true)

def mv_stE (sel p e : Bool) : Cmd :=
  .pop 7 (mv_stC sel p e false) (mv_stC sel p e false) (mv_stC sel p e true)

/-- One step: pop the marker, the coverage bit and the flag. -/
def mv_step (sel p : Bool) : Cmd := .pop 5 (.halt false) (mv_stE sel p false) (mv_stE sel p true)

theorem mv_ex_step (sel p e : Bool) (E' : Str) (f : Bool) (s : mv_S) (hE : s.E = e :: E')
    (hF : s.F = CookLevin.fl f) :
    ExecLe (mv_step sel p) s.st
      (if mv_bad sel p e (s.C.headD false) f then .halt false else
        .norm {s with E := E', C := s.C.tail, E2 := e :: s.E2,
                      C2 := (s.C.headD false || sel && p) :: s.C2,
                      F := CookLevin.fl (mv_nf p e f)}.st) 6 := by
  refine ExecLe.pop_cons (b := e) (s := E') (by simp [hE]) ?_
  have e1 : (if e then mv_stE sel p true else mv_stE sel p false) = mv_stE sel p e := by
    cases e <;> rfl
  rw [e1, mv_u5]
  refine mv_popD (C := mv_stC sel p e) ?_
  simp only [mv_st7, mv_u7]
  refine mv_popD (C := mv_leaf sel p e _) ?_
  simp only [mv_st9, mv_u9, hF]
  have hf : (CookLevin.fl f).headD false = f := by cases f <;> rfl
  have ht : (CookLevin.fl f).tail = [] := by cases f <;> rfl
  rw [hf, ht]
  refine (mv_ex_leaf sel p e _ f _ rfl).cast ?_ le_rfl
  split_ifs <;> simp

/-! ## The row loop -/

def mv_endR : Cmd :=
  .pop 5 (.seq (.pop 9 .skip .skip .skip) (.seq (move 6 5) (.seq (move 8 7) .brk)))
    (.halt false) (.halt false)

/-- The final check: all coverage bits set. -/
def mv_finL : Cmd := .loop (.pop 7 (.halt true) (.halt false) .skip)

def mv_rowB (sel : Bool) : Cmd :=
  .pop 3 mv_finL (.pop 3 (.halt false) mv_endR (mv_step sel false))
    (.pop 3 (.halt false) (mv_step sel true) (mv_step sel false))

def mv_rowL (sel : Bool) : Cmd := .loop (mv_rowB sel)

/-- The result of the row loop. -/
def mv_rres (s : mv_S) (Q' : Str) : Option Str → Res
  | none => .halt false
  | some C' => .norm {s with Q := Q', E := s.E2.reverse ++ s.E, E2 := [],
                             C := s.C2.reverse ++ C', C2 := [], F := []}.st

theorem mv_ex_finL : ∀ (C : Str) (s : mv_S), s.C = C →
    ExecLe mv_finL s.st (.halt (C.all id)) (2 * C.length + 2)
  | [], s, h => (ExecLe.loop_halt (ExecLe.pop_nil (by simpa using h) (ExecLe.halt true _))).cast
      (by simp) (by simp)
  | false :: C, s, h => (ExecLe.loop_halt (ExecLe.pop_cons (b := false) (s := C)
      (by simpa using h) (ExecLe.halt false _))).cast (by simp) (by simp)
  | true :: C, s, h => by
    have ih := mv_ex_finL C {s with C := C} rfl
    exact (ExecLe.loop_norm (ExecLe.pop_cons (b := true) (s := C) (by simpa using h)
      ((ExecLe.skip _).cast (by simp) le_rfl)) ih).cast (by simp) (by simp; omega)

theorem mv_ex_rowEnd (sel : Bool) (s : mv_S) (hQ : s.Q = []) :
    ExecLe (mv_rowL sel) s.st (.halt (s.C.all id)) (2 * s.C.length + 3) :=
  ExecLe.loop_halt (ExecLe.pop_nil (by simpa using hQ) (mv_ex_finL s.C s rfl))

theorem mv_sel_step (sel : Bool) (x : SatSym) (hx : x ≠ sep) :
    mv_sel x mv_endR (mv_step sel false) (mv_step sel true) (mv_step sel false) =
      mv_step sel (isPos x) := by
  cases x <;> simp_all [mv_sel, isPos]

theorem mv_ex_row (sel : Bool) (Q' : Str) : ∀ (r : List SatSym) (s : mv_S) (f : Bool),
    sep ∉ r → s.Q = r.flatMap ic ++ false :: false :: Q' → s.F = CookLevin.fl f →
    ExecLe (mv_rowL sel) s.st (mv_rres s Q' (mv_row sel r s.E s.C f))
      (12 * r.length + 2 * (s.E2.length + s.E.length) + 2 * (s.C2.length + r.length) + 12)
  | [], s, f, _, hQ, hF => by
    have hQ' : s.Q = ic sep ++ Q' := by simpa [ic] using hQ
    cases hE : s.E with
    | nil =>
      set s1 : mv_S := {s with Q := Q', F := []}
      have h9 : ExecLe (.pop 9 .skip .skip .skip) {s with Q := Q'}.st (.norm s1.st) 2 := by
        refine mv_pop3 ((ExecLe.skip _).cast ?_ le_rfl)
        simp [s1, hF]; cases f <;> rfl
      have h65 := ExecLe.of (exec_move (a := 6) (b := 5) (by decide) s1.E2 s1.st rfl)
      simp only [mv_u6, mv_st5, mv_u5] at h65
      set s2 : mv_S := {s1 with E2 := [], E := s1.E2.reverse ++ s1.E}
      have h87 := ExecLe.of (exec_move (a := 8) (b := 7) (by decide) s2.C2 s2.st rfl)
      simp only [mv_u8, mv_st7, mv_u7] at h87
      have hin : ExecLe (mv_sel sep mv_endR (mv_step sel false) (mv_step sel true)
          (mv_step sel false)) {s with Q := Q'}.st
          (.brk {s2 with C2 := [], C := s2.C2.reverse ++ s2.C}.st)
          (2 * s1.E2.length + 2 * s2.C2.length + 8) := by
        simp only [mv_sel, mv_endR]
        exact (ExecLe.pop_nil (k := 5) (by simp [hE])
          (h9.seq_norm (h65.seq_norm (h87.seq_norm (ExecLe.brk _))))).cast rfl (by omega)
      have hb := mv_pop2 (cE := mv_finL) (cX := .halt false) sep Q' hQ' hin
      refine (ExecLe.loop_brk hb).cast ?_ (by simp [s2, s1])
      simp [mv_rres, mv_row, s2, s1, hE]
    | cons e E' =>
      have hin : ExecLe (mv_sel sep mv_endR (mv_step sel false) (mv_step sel true)
          (mv_step sel false)) {s with Q := Q'}.st (.halt false) 2 := by
        simp only [mv_sel, mv_endR]
        exact ExecLe.pop_cons (k := 5) (b := e) (s := E') (by simp [hE])
          (by cases e <;> exact ExecLe.halt false _)
      refine (ExecLe.loop_halt (mv_pop2 (cE := mv_finL) (cX := .halt false) sep Q' hQ' hin)).cast
        (by simp [mv_row, mv_rres]) (by omega)
  | x :: r, s, f, hr, hQ, hF => by
    have hx : x ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    set Q1 := r.flatMap ic ++ false :: false :: Q'
    have hQ1 : s.Q = ic x ++ Q1 := by simp [hQ, Q1]
    cases hE : s.E with
    | nil =>
      have hin : ExecLe (mv_sel x mv_endR (mv_step sel false) (mv_step sel true)
          (mv_step sel false)) {s with Q := Q1}.st (.halt false) 2 := by
        rw [mv_sel_step sel x hx]
        exact ExecLe.pop_nil (k := 5) (by simp [hE]) (ExecLe.halt false _)
      refine (ExecLe.loop_halt (mv_pop2 (cE := mv_finL) (cX := .halt false) x Q1 hQ1 hin)).cast
        (by simp [mv_row, mv_rres]) (by omega)
    | cons e E' =>
      have hst := mv_ex_step sel (isPos x) e E' f {s with Q := Q1} (by simp [hE]) (by simp [hF])
      cases hb : mv_bad sel (isPos x) e (s.C.headD false) f
      · simp only [hb, Bool.false_eq_true, if_false] at hst
        set s' : mv_S := {s with Q := Q1, E := E', C := s.C.tail, E2 := e :: s.E2,
                                 C2 := (s.C.headD false || sel && isPos x) :: s.C2,
                                 F := CookLevin.fl (mv_nf (isPos x) e f)}
        have ih := mv_ex_row sel Q' r s' (mv_nf (isPos x) e f) hr' rfl rfl
        have h1 := mv_pop2 (cS := mv_endR) (cZ := mv_step sel false)
          (cP := mv_step sel true) (cN := mv_step sel false) (cE := mv_finL)
          (cX := .halt false) x Q1 hQ1 (by rw [mv_sel_step sel x hx]; exact hst)
        refine (ExecLe.loop_norm (c := mv_rowB sel) h1 ih).cast ?_ ?_
        · simp only [mv_row, hb, Bool.false_eq_true, if_false]
          cases hm : mv_row sel r E' s.C.tail (mv_nf (isPos x) e f) <;>
            simp [mv_rres, s', hE]
        · simp [s']; omega
      · simp only [hb, if_true] at hst
        refine (ExecLe.loop_halt (mv_pop2 (cS := mv_endR) (cZ := mv_step sel false)
          (cP := mv_step sel true) (cN := mv_step sel false) (cE := mv_finL)
          (cX := .halt false) x Q1 hQ1 (by rw [mv_sel_step sel x hx]; exact hst))).cast
          (by simp only [mv_row, hb, if_true, mv_rres]) (by omega)

/-! ## The main loop -/

def mv_mainL : Cmd := .loop (.pop 0 (mv_rowL false) (mv_rowL false) (mv_rowL true))

/-- Cost of the main loop. -/
def mv_Tm (L N : ℕ) : List (List SatSym) → ℕ
  | [] => 2 * N + 4
  | r :: rows => 14 * r.length + 2 * L + 14 + mv_Tm L N rows

theorem mv_Tm_eq (L N : ℕ) : ∀ rows : List (List SatSym),
    mv_Tm L N rows = 14 * (rows.map List.length).sum + rows.length * (2 * L + 14) + 2 * N + 4
  | [] => by simp [mv_Tm]
  | r :: rows => by simp only [mv_Tm, mv_Tm_eq L N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem mv_ex_main (E : Str) (N : ℕ) : ∀ (rows : List (List SatSym)) (R A C T : Str),
    (∀ r ∈ rows, sep ∉ r) → C.length + (rows.map List.length).sum ≤ N →
    ExecLe mv_mainL (mv_S.mk R (enc rows) A E [] C [] [] T).st (.halt (mv_go E rows R C))
      (mv_Tm E.length N rows)
  | [], R, A, C, T, _, hN => by
    have h := mv_ex_rowEnd (R.headD false) ⟨R.tail, enc [], A, E, [], C, [], [], T⟩ (by simp [enc])
    have h' : ExecLe (mv_rowL (((mv_S.mk R (enc []) A E [] C [] [] T).st 0).headD false))
        (update (mv_S.mk R (enc []) A E [] C [] [] T).st 0
          ((mv_S.mk R (enc []) A E [] C [] [] T).st 0).tail) (.halt (C.all id))
        (2 * C.length + 3) := by simpa using h
    refine (ExecLe.loop_halt (mv_popD (k := 0) (C := mv_rowL) h')).cast (by simp [mv_go])
      (by simp [mv_Tm] at hN ⊢; omega)
  | r :: rows, R, A, C, T, hsep, hN => by
    have hr : sep ∉ r := hsep r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hsep r' (by simp [h])
    have hrow := mv_ex_row (R.headD false) (enc rows) r ⟨R.tail, enc (r :: rows), A, E, [], C, [],
      [], T⟩ false hr (by simp [enc_cons]) (by simp [CookLevin.fl])
    have hb : ExecLe (.pop 0 (mv_rowL false) (mv_rowL false) (mv_rowL true))
        (mv_S.mk R (enc (r :: rows)) A E [] C [] [] T).st
        (mv_rres ⟨R.tail, enc (r :: rows), A, E, [], C, [], [], T⟩ (enc rows)
          (mv_row (R.headD false) r E C false))
        (14 * r.length + 2 * E.length + 13) := by
      refine (mv_popD (k := 0) (C := mv_rowL) (T := 12 * r.length +
        2 * E.length + 2 * r.length + 12) ?_).cast rfl (by omega)
      simpa using hrow
    simp only [List.map_cons, List.sum_cons] at hN
    cases hm : mv_row (R.headD false) r E C false with
    | none =>
      rw [hm] at hb
      exact (ExecLe.loop_halt hb).cast (by simp only [mv_go, hm]) (by simp [mv_Tm]; omega)
    | some C' =>
      rw [hm] at hb
      have hl := mv_row_len _ r E C false C' hm
      have ih := mv_ex_main E N rows R.tail A C' T hrs (by omega)
      refine (ExecLe.loop_norm hb ih).cast ?_ (by simp [mv_Tm])
      simp only [mv_go, hm]

/-! ## The whole verifier -/

def mv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq mv_hdL (.seq mv_start mv_mainL))))

/-- Time bound of the verifier. -/
def mv_Tver (n : ℕ) : ℕ := 7 * n * n + 100 * n + 100

theorem mv_exec_ver (z : Str) :
    ExecLe mv_ver (init [z]).stk (.halt (mv_vres (dec z).1 (dec z).2)) (mv_Tver z.length) := by
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
  set s0 : mv_S := ⟨y, enc (clauses w), [], [], [], [], [], [], []⟩
  have hσ : update (update σ₂ 2 []) 3 ((σ₂ 2).reverse ++ σ₂ 3) = s0.st := by
    funext j
    simp only [σ₂, σ₁, s0, mv_S.st, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ), ExecLe c s0.st r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold mv_vres mv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨u, rs⟩
  · have hf : ExecLe (.seq mv_hdL (.seq mv_start mv_mainL)) s0.st (.halt false) 2 :=
      ExecLe.seq_halt (mv_ex_hd_nil s0 (by simp [s0, hcw, enc]))
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, mv_Tver]; nlinarith
  · rw [hcw] at hsum hsep
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hH := mv_ex_hd (enc rs) u s0 (hsep u (by simp)) (by simp [s0, hcw, enc_cons])
    rcases u with _ | ⟨x, u⟩
    · have hS : ExecLe (.seq mv_start mv_mainL)
          {s0 with Q := enc rs, A := List.replicate 0 false ++ s0.A}.st (.halt rs.isEmpty) 3 :=
        ExecLe.seq_halt (ExecLe.pop_nil (by simp [s0]) (mv_ex_q0 rs _ rfl))
      refine (hpre _ _ _ (hH.seq_norm hS)).cast rfl ?_
      simp only [htl, mv_Tver, List.length_nil] at hsum ⊢; nlinarith
    · set k := u.length
      set s1 : mv_S := {s0 with Q := enc rs, A := List.replicate k false}
      have hB := mv_ex_bld k s1 rfl rfl rfl rfl
      have hSt : ExecLe mv_start
          {s0 with Q := enc rs, A := List.replicate (x :: u).length false ++ s0.A}.st
          (.norm {s1 with E := mv_E k, C := mv_C k}.st) (30 * k + 31) := by
        refine (ExecLe.pop_cons (k := 4) (b := false) (s := List.replicate k false) (T := 30 * k + 30)
          (by simp [s0, k, List.replicate_succ]) ?_).cast rfl (by omega)
        simpa [s1, s0] using hB
      have hCl : (mv_C k).length = 3 * k + 3 := by simp [mv_C]; omega
      have hEl : (mv_E k).length = 3 * k + 3 := by simp [mv_E]; omega
      have hMn := mv_ex_main (mv_E k) (3 * k + 3 + (rs.map List.length).sum) rs
        y (List.replicate k false) (mv_C k) [] (fun r hr => hsep r (by simp [hr])) (by rw [hCl])
      refine (hpre _ _ _ (hH.seq_norm (hSt.seq_norm hMn))).cast rfl ?_
      rw [mv_Tm_eq, hEl]
      simp only [htl, mv_Tver, List.length_cons] at hsum ⊢
      have hk : k + (rs.map List.length).sum + rs.length + 2 ≤ (trunc w).length := by
        simp only [k]; omega
      have h1 : rs.length * (2 * (3 * k + 3) + 14) ≤ z.length * (6 * z.length + 20) :=
        Nat.mul_le_mul (by omega) (by omega)
      rw [show u.length = k from rfl]
      clear_value k w y
      generalize z.length = Z at *
      have h2 : Z * (6 * Z + 20) = 6 * (Z * Z) + 20 * Z := by ring
      have h3 : rs.length * (2 * (3 * k + 3) + 14) = 6 * (rs.length * k) + 20 * rs.length := by ring
      have h4 : 7 * Z * Z = 7 * (Z * Z) := by ring
      rw [h3, h4]; rw [h2, h3] at h1
      omega

theorem mv_Tver_le (n : ℕ) : mv_Tver n ≤ tb 8 n := by
  unfold mv_Tver tb
  have h6 : 2 ^ 6 ≤ (n + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have e : (n + 2) ^ 8 = (n + 2) ^ 2 * (n + 2) ^ 6 := by ring
  rw [e]
  nlinarith

end Pnp.Karp.ThreeDM
