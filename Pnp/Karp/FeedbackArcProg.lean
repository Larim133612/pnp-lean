import Pnp.Karp.FeedbackArc
import Pnp.Karp.DHamProg
import Pnp.Karp.FeedbackVSProg

/-!
# The FEEDBACK ARC SET reduction program

`fap_redCmd`, on the bit string `x` on stack `0`, prints `splitW w` (`w = dec2 x`,
`Pnp/Karp/FeedbackArc.lean`) on stack `0`.  Stacks (fields of `fap_S`): `0` the output `R`;
`1` the code `M` of the rows `clauses w` (first symbol on top); `2` the row index `V` (unary);
`3` a column counter `C`; `4` a temporary `T`.

1. `parseLoop`, `trimC 4`, `move 4 1` (as in `dp_redCmd`): stack `1` holds `enc (clauses w)`;
2. `fap_cpL`: copy the budget row `kr` (and its `sep`) to the output (nothing if there are no
   rows);
3. `fap_rsL`: for each further row `r` (index `v`): print `inRow v` (`2v + 1` zeros, `pos`)
   and `sep`; then, with `C = true^v false`, print each entry `e` of `r` as `e` (or `zero` when
   `C` pops `false`, i.e. at column `v`) followed by `zero`; print `sep`; `V := v + 1`.

`splitW_computable` follows from `FunBridge.computable_of_cmd_code`, and `sat_le_fas_of` by
composing with `VertexCover.GV_computable` and `IndSet.cmap_computable`.
-/

namespace Pnp.Karp.FeedbackArc

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Stack layout -/

structure fap_S where
  R : Str
  M : Str
  V : Str
  C : Str
  T : Str

def fap_S.st (s : fap_S) : ℕ → Str := fun j =>
  if j = 0 then s.R else if j = 1 then s.M else if j = 2 then s.V else if j = 3 then s.C else
  if j = 4 then s.T else []

theorem fap_st_big (s : fap_S) (j : ℕ) (h : 5 ≤ j) : s.st j = [] := by
  unfold fap_S.st; repeat rw [if_neg (by omega)]

local macro "fapx" : tactic =>
  `(tactic| (funext j; by_cases h : j < 5
             · interval_cases j <;> rfl
             · rw [update_of_ne (by omega), fap_st_big _ _ (by omega), fap_st_big _ _ (by omega)]))

section St
variable (s : fap_S) (v : Str)
@[simp] theorem fap_st0 : s.st 0 = s.R := rfl
@[simp] theorem fap_st1 : s.st 1 = s.M := rfl
@[simp] theorem fap_st2 : s.st 2 = s.V := rfl
@[simp] theorem fap_st3 : s.st 3 = s.C := rfl
@[simp] theorem fap_st4 : s.st 4 = s.T := rfl
@[simp] theorem fap_u0 : update s.st 0 v = {s with R := v}.st := by fapx
@[simp] theorem fap_u1 : update s.st 1 v = {s with M := v}.st := by fapx
@[simp] theorem fap_u2 : update s.st 2 v = {s with V := v}.st := by fapx
@[simp] theorem fap_u3 : update s.st 3 v = {s with C := v}.st := by fapx
end St

/-! ## Printing and reading symbols -/

/-- Print the symbols `L` on stack `0`. -/
def fap_em (L : List SatSym) : Cmd := pushList 0 (rv L)

theorem fap_ex_em (L E : List SatSym) (s : fap_S) (hR : s.R = rv E) :
    ExecLe (fap_em L) s.st (.norm {s with R := rv (E ++ L)}.st) (2 * L.length + 1) := by
  refine (ExecLe.of (exec_pushList 0 (rv L) s.st)).cast ?_
    (by simp only [rv, List.length_reverse, length_flatMap_ic]; omega)
  rw [fap_u0, fap_st0, hR, rv_append]

/-- Read one symbol from stack `1` and branch on it. -/
def fap_rd (cs c0 cp cn : Cmd) : Cmd :=
  .pop 1 .brk (.pop 1 .brk cs c0) (.pop 1 .brk cp cn)

/-- The branch taken for a symbol. -/
def fap_sel (cs c0 cp cn : Cmd) : SatSym → Cmd
  | sep => cs
  | zero => c0
  | pos => cp
  | neg => cn

theorem fap_ex_rd {cs c0 cp cn : Cmd} (e : SatSym) (s : fap_S) (M' : Str)
    (hM : s.M = ic e ++ M') {r : Res} {T : ℕ}
    (h : ExecLe (fap_sel cs c0 cp cn e) {s with M := M'}.st r T) :
    ExecLe (fap_rd cs c0 cp cn) s.st r (T + 2) := by
  cases e <;> simp only [ic, List.cons_append, List.nil_append] at hM
  · refine ExecLe.pop_cons (b := true) (s := false :: M') (by simpa using hM) ?_
    rw [fap_u1]; simp only [↓reduceIte]
    exact ExecLe.pop_cons (b := false) (s := M') rfl (by rw [fap_u1]; exact h)
  · refine ExecLe.pop_cons (b := true) (s := true :: M') (by simpa using hM) ?_
    rw [fap_u1]; simp only [↓reduceIte]
    exact ExecLe.pop_cons (b := true) (s := M') rfl (by rw [fap_u1]; exact h)
  · refine ExecLe.pop_cons (b := false) (s := true :: M') (by simpa using hM) ?_
    rw [fap_u1]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact ExecLe.pop_cons (b := true) (s := M') rfl (by rw [fap_u1]; exact h)
  · refine ExecLe.pop_cons (b := false) (s := false :: M') (by simpa using hM) ?_
    rw [fap_u1]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact ExecLe.pop_cons (b := false) (s := M') rfl (by rw [fap_u1]; exact h)

theorem fap_sel_f (cs : Cmd) (f : SatSym → Cmd) (e : SatSym) (he : e ≠ sep) :
    fap_sel cs (f zero) (f pos) (f neg) e = f e := by
  cases e <;> simp_all [fap_sel]

/-! ## Copying the budget row -/

def fap_cpL : Cmd :=
  .loop (fap_rd (.seq (fap_em [sep]) .brk) (fap_em [zero]) (fap_em [pos]) (fap_em [neg]))

theorem fap_ex_cpL : ∀ (r : List SatSym) (rest : Str) (s : fap_S) (E : List SatSym), sep ∉ r →
    s.M = (r ++ [sep]).flatMap ic ++ rest → s.R = rv E →
    ExecLe fap_cpL s.st (.norm {s with M := rest, R := rv (E ++ r ++ [sep])}.st)
      (6 * r.length + 6)
  | [], rest, s, E, _, hM, hR => by
    have h := fap_ex_rd (cs := .seq (fap_em [sep]) .brk) (c0 := fap_em [zero])
      (cp := fap_em [pos]) (cn := fap_em [neg]) sep s rest (by simpa using hM)
      ((fap_ex_em [sep] E {s with M := rest} hR).seq_norm (ExecLe.brk _))
    exact (ExecLe.loop_brk h).cast (by simp) (by simp)
  | e :: r, rest, s, E, hs, hM, hR => by
    have he : e ≠ sep := fun h => hs (h ▸ List.mem_cons_self ..)
    have hs' : sep ∉ r := fun h => hs (List.mem_cons_of_mem _ h)
    have h1 := fap_ex_rd (cs := .seq (fap_em [sep]) .brk) (c0 := fap_em [zero])
      (cp := fap_em [pos]) (cn := fap_em [neg]) e s ((r ++ [sep]).flatMap ic ++ rest)
      (by simp [hM])
      (by rw [fap_sel_f _ (fun e => fap_em [e]) e he]
          exact fap_ex_em [e] E {s with M := (r ++ [sep]).flatMap ic ++ rest} hR)
    have ih := fap_ex_cpL r rest
      {s with M := (r ++ [sep]).flatMap ic ++ rest, R := rv (E ++ [e])} (E ++ [e]) hs' rfl rfl
    exact (ExecLe.loop_norm h1 ih).cast (by simp) (by simp; omega)

/-! ## One output row -/

/-- The column-counter template `true^v false`. -/
def fap_D (v : ℕ) : Str := List.replicate v true ++ [false]

theorem fap_D_lt {v j : ℕ} (h : j < v) : (fap_D v).drop j = true :: (fap_D v).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simp [fap_D]; omega)]
  congr 1
  simp [fap_D, List.getElem_append_left (show j < (List.replicate v true).length by simp; omega)]

theorem fap_D_eq (v : ℕ) : (fap_D v).drop v = false :: (fap_D v).drop (v + 1) := by
  simp [fap_D, List.drop_append]

theorem fap_D_gt {v j : ℕ} (h : v < j) : (fap_D v).drop j = [] := by
  apply List.drop_eq_nil_of_le; simp [fap_D]; omega

theorem fap_length_D_drop (v j : ℕ) : ((fap_D v).drop j).length ≤ v + 1 := by
  simp [fap_D]

/-- Print an entry `e`: `e` (or `zero` at the diagonal), then `zero`. -/
def fap_ent (e : SatSym) : Cmd :=
  .seq (.pop 3 (fap_em [e]) (fap_em [zero]) (fap_em [e])) (fap_em [zero])

theorem fap_ex_ent (e : SatSym) (v j : ℕ) (s : fap_S) (E : List SatSym)
    (hC : s.C = (fap_D v).drop j) (hR : s.R = rv E) :
    ExecLe (fap_ent e) s.st
      (.norm {s with C := (fap_D v).drop (j + 1), R := rv (E ++ [if j = v then zero else e, zero])}.st) 7 := by
  rcases lt_trichotomy j v with h | rfl | h
  · have h1 : ExecLe (.pop 3 (fap_em [e]) (fap_em [zero]) (fap_em [e])) s.st
        (.norm {s with C := (fap_D v).drop (j + 1), R := rv (E ++ [e])}.st) 4 :=
      ExecLe.pop_cons (b := true) (s := (fap_D v).drop (j + 1)) (by rw [fap_st3, hC, fap_D_lt h])
        (by rw [fap_u3]; exact fap_ex_em [e] E _ hR)
    refine (h1.seq_norm (fap_ex_em [zero] (E ++ [e]) _ rfl)).cast ?_ (by simp)
    simp [h.ne]
  · have h1 : ExecLe (.pop 3 (fap_em [e]) (fap_em [zero]) (fap_em [e])) s.st
        (.norm {s with C := (fap_D j).drop (j + 1), R := rv (E ++ [zero])}.st) 4 :=
      ExecLe.pop_cons (b := false) (s := (fap_D j).drop (j + 1)) (by rw [fap_st3, hC, fap_D_eq])
        (by rw [fap_u3]; exact fap_ex_em [zero] E _ hR)
    refine (h1.seq_norm (fap_ex_em [zero] (E ++ [zero]) _ rfl)).cast ?_ (by simp)
    simp
  · have h1 : ExecLe (.pop 3 (fap_em [e]) (fap_em [zero]) (fap_em [e])) s.st
        (.norm {s with C := (fap_D v).drop (j + 1), R := rv (E ++ [e])}.st) 4 := by
      refine ExecLe.pop_nil (by rw [fap_st3, hC, fap_D_gt h]) ?_
      refine (fap_ex_em [e] E _ hR).cast ?_ le_rfl
      congr 2
      cases s; simp_all [fap_D_gt h, fap_D_gt (show v < j + 1 by omega)]
    refine (h1.seq_norm (fap_ex_em [zero] (E ++ [e]) _ rfl)).cast ?_ (by simp)
    simp [h.ne']

/-- The printed out-row: entry `e` at column `j` becomes `e` (or `zero` if `j = v`), `zero`. -/
def fap_orow : List SatSym → ℕ → ℕ → List SatSym
  | [], _, _ => []
  | e :: r, v, j => (if j = v then zero else e) :: zero :: fap_orow r v (j + 1)

theorem fap_orow_succ : ∀ (r : List SatSym) (v j : ℕ),
    fap_orow r (v + 1) (j + 1) = fap_orow r v j
  | [], _, _ => rfl
  | e :: r, v, j => by simp [fap_orow, fap_orow_succ r v (j + 1)]

theorem fap_orow_gt : ∀ (r : List SatSym) (v j : ℕ), v < j →
    fap_orow r v j = r.flatMap fun e => [e, zero]
  | [], _, _, _ => rfl
  | e :: r, v, j, h => by
    simp [fap_orow, h.ne', fap_orow_gt r v (j + 1) (by omega)]

theorem fap_orow_eq : ∀ (r : List SatSym) (v : ℕ), fap_orow r v 0 = outRow r v
  | [], v => by simp [fap_orow, outRow]
  | e :: r, 0 => by simp [fap_orow, outRow, fap_orow_gt r 0 1 (by omega)]
  | e :: r, v + 1 => by
    simp only [fap_orow, fap_orow_succ, fap_orow_eq r v]
    simp [outRow]

def fap_oL : Cmd :=
  .loop (fap_rd (.seq (fap_em [sep]) .brk) (fap_ent zero) (fap_ent pos) (fap_ent neg))

theorem fap_ex_oL (v : ℕ) : ∀ (r : List SatSym) (j : ℕ) (rest : Str) (s : fap_S)
    (E : List SatSym), sep ∉ r → s.M = (r ++ [sep]).flatMap ic ++ rest →
    s.C = (fap_D v).drop j → s.R = rv E →
    ExecLe fap_oL s.st (.norm {s with M := rest, C := (fap_D v).drop (j + r.length), R := rv (E ++ fap_orow r v j ++ [sep])}.st) (9 * r.length + 6)
  | [], j, rest, s, E, _, hM, hC, hR => by
    have h := fap_ex_rd (cs := .seq (fap_em [sep]) .brk) (c0 := fap_ent zero)
      (cp := fap_ent pos) (cn := fap_ent neg) sep s rest (by simpa using hM)
      ((fap_ex_em [sep] E {s with M := rest} hR).seq_norm (ExecLe.brk _))
    exact (ExecLe.loop_brk h).cast (by cases s; simp_all [fap_orow]) (by simp)
  | e :: r, j, rest, s, E, hs, hM, hC, hR => by
    have he : e ≠ sep := fun h => hs (h ▸ List.mem_cons_self ..)
    have hs' : sep ∉ r := fun h => hs (List.mem_cons_of_mem _ h)
    have h1 := fap_ex_rd (cs := .seq (fap_em [sep]) .brk) (c0 := fap_ent zero)
      (cp := fap_ent pos) (cn := fap_ent neg) e s ((r ++ [sep]).flatMap ic ++ rest)
      (by simp [hM])
      (by rw [fap_sel_f _ fap_ent e he]
          exact fap_ex_ent e v j {s with M := (r ++ [sep]).flatMap ic ++ rest} E hC hR)
    have ih := fap_ex_oL v r (j + 1) rest
      {s with M := (r ++ [sep]).flatMap ic ++ rest, C := (fap_D v).drop (j + 1), R := rv (E ++ [if j = v then zero else e, zero])}
      (E ++ [if j = v then zero else e, zero]) hs' rfl rfl rfl
    refine (ExecLe.loop_norm h1 ih).cast ?_ (by simp; omega)
    simp [fap_orow, show j + 1 + r.length = j + (r.length + 1) by omega]

/-- Print `2k` zeros, emptying the counter `C = true^k`. -/
def fap_zzL : Cmd := .loop (.pop 3 .brk (fap_em [zero, zero]) (fap_em [zero, zero]))

theorem fap_ex_zzL : ∀ (k : ℕ) (s : fap_S) (E : List SatSym), s.C = List.replicate k true →
    s.R = rv E →
    ExecLe fap_zzL s.st (.norm {s with C := [], R := rv (E ++ List.replicate (2 * k) zero)}.st)
      (6 * k + 2)
  | 0, s, E, hC, hR =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hC]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all) (by omega)
  | k + 1, s, E, hC, hR => by
    have hb : ExecLe (.pop 3 .brk (fap_em [zero, zero]) (fap_em [zero, zero])) s.st
        (.norm {s with C := List.replicate k true, R := rv (E ++ [zero, zero])}.st) 6 :=
      ExecLe.pop_same (b := true) (s := List.replicate k true)
        (by simp [hC, List.replicate_succ]) (by rw [fap_u3]; exact fap_ex_em _ E _ hR)
    have ih := fap_ex_zzL k {s with C := List.replicate k true, R := rv (E ++ [zero, zero])}
      (E ++ [zero, zero]) rfl rfl
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    simp [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.replicate_succ]

/-- One row `r` with index `v`: print `inRow v ++ [sep] ++ outRow r v ++ [sep]`. -/
def fap_row : Cmd :=
  .seq (fap_em [zero]) (.seq (copyVia 2 3 4) (.seq fap_zzL (.seq (fap_em [pos, sep])
    (.seq (.push 3 false) (.seq (copyVia 2 3 4) (.seq fap_oL (.seq (drain 3) (.push 2 true))))))))

theorem fap_ex_row (r : List SatSym) (v : ℕ) (rest : Str) (s : fap_S) (E : List SatSym)
    (hs : sep ∉ r) (hM : s.M = (r ++ [sep]).flatMap ic ++ rest)
    (hV : s.V = List.replicate v true) (hC : s.C = []) (hT : s.T = []) (hR : s.R = rv E) :
    ExecLe fap_row s.st (.norm {s with M := rest, V := List.replicate (v + 1) true, R := rv (E ++ (inRow v ++ [sep] ++ (outRow r v ++ [sep])))}.st)
      (20 * v + 9 * r.length + 40) := by
  have h1 := fap_ex_em [zero] E s hR
  have h2 := ExecLe.of (exec_copyVia (a := 2) (b := 3) (t := 4) (by decide) (by decide)
    (by decide) {s with R := rv (E ++ [zero])}.st (by simpa using hT))
  rw [fap_st2, fap_st3, fap_u3] at h2
  have h3 := fap_ex_zzL v {s with R := rv (E ++ [zero]), C := s.V ++ s.C} (E ++ [zero])
    (by simp [hV, hC]) rfl
  have h4 := fap_ex_em [pos, sep] (E ++ [zero] ++ List.replicate (2 * v) zero)
    {s with C := [], R := rv (E ++ [zero] ++ List.replicate (2 * v) zero)} rfl
  have h5 := ExecLe.push 3 false
    {s with C := [], R := rv (E ++ [zero] ++ List.replicate (2 * v) zero ++ [pos, sep])}.st
  rw [fap_st3, fap_u3] at h5
  set E1 := E ++ [zero] ++ List.replicate (2 * v) zero ++ [pos, sep] with hE1
  have h6 := ExecLe.of (exec_copyVia (a := 2) (b := 3) (t := 4) (by decide) (by decide)
    (by decide) {s with C := [false], R := rv E1}.st (by simpa using hT))
  rw [fap_st2, fap_st3, fap_u3] at h6
  have h7 := fap_ex_oL v r 0 rest {s with C := s.V ++ [false], R := rv E1} E1 hs hM
    (by simp [hV, fap_D]) rfl
  have h8 := ExecLe.of (exec_drain 3 _
    {s with M := rest, C := (fap_D v).drop (0 + r.length), R := rv (E1 ++ fap_orow r v 0 ++ [sep])}.st rfl)
  rw [fap_u3] at h8
  have h9 := ExecLe.push 2 true
    {s with M := rest, C := [], R := rv (E1 ++ fap_orow r v 0 ++ [sep])}.st
  rw [fap_st2, fap_u2] at h9
  have hall := h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm (h6.seq_norm
    (h7.seq_norm (h8.seq_norm h9)))))))
  refine hall.cast ?_ ?_
  · congr 1; cases s
    simp_all [fap_orow_eq, inRow, List.replicate_succ]
  · have hl := fap_length_D_drop v (0 + r.length)
    simp only [fap_st3, hV, List.length_replicate, List.length_cons,
      List.length_nil] at hl ⊢
    omega

/-! ## The row loop -/

def fap_rsB : Cmd := .pop 1 .brk (.seq (.push 1 false) fap_row) (.seq (.push 1 true) fap_row)

def fap_rsL : Cmd := .loop fap_rsB

theorem fap_ex_rsB (s : fap_S) {b : Bool} {M' : Str} (hM : s.M = b :: M') {r : Res} {T : ℕ}
    (h : ExecLe fap_row s.st r T) : ExecLe fap_rsB s.st r (T + 2) := by
  have e : ({s with M := b :: M'} : fap_S) = s := by cases s; simp_all
  cases b
  · refine ExecLe.pop_cons (b := false) (s := M') (by simpa using hM) ?_
    rw [fap_u1]; simp only [Bool.false_eq_true, ↓reduceIte]
    have h' : ExecLe fap_row (update ({s with M := M'} : fap_S).st 1
        (false :: ({s with M := M'} : fap_S).st 1)) r T := by
      rw [fap_u1, fap_st1]
      exact (show ({({s with M := M'} : fap_S) with M := false :: M'} : fap_S) = s from e) ▸ h
    exact ((ExecLe.push 1 false _).seq_norm h').cast rfl (by omega)
  · refine ExecLe.pop_cons (b := true) (s := M') (by simpa using hM) ?_
    rw [fap_u1]; simp only [↓reduceIte]
    have h' : ExecLe fap_row (update ({s with M := M'} : fap_S).st 1
        (true :: ({s with M := M'} : fap_S).st 1)) r T := by
      rw [fap_u1, fap_st1]
      exact (show ({({s with M := M'} : fap_S) with M := true :: M'} : fap_S) = s from e) ▸ h
    exact ((ExecLe.push 1 true _).seq_norm h').cast rfl (by omega)

/-- The rows from index `v` on, as printed. -/
def fap_out : List (List SatSym) → ℕ → List SatSym
  | [], _ => []
  | r :: rs, v => inRow v ++ [sep] ++ (outRow r v ++ [sep]) ++ fap_out rs (v + 1)

def fap_Tr : List (List SatSym) → ℕ → ℕ
  | [], _ => 2
  | r :: rs, v => 20 * v + 9 * r.length + 42 + fap_Tr rs (v + 1)

theorem fap_ex_rsL : ∀ (rs : List (List SatSym)) (v : ℕ) (s : fap_S) (E : List SatSym),
    (∀ r ∈ rs, sep ∉ r) → s.M = (rs.flatMap (· ++ [sep])).flatMap ic →
    s.V = List.replicate v true → s.C = [] → s.T = [] → s.R = rv E →
    ExecLe fap_rsL s.st (.norm {s with M := [], V := List.replicate (v + rs.length) true, R := rv (E ++ fap_out rs v)}.st) (fap_Tr rs v)
  | [], v, s, E, _, hM, hV, hC, hT, hR =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hM]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all [fap_out]) (by simp [fap_Tr])
  | r :: rs, v, s, E, hs, hM, hV, hC, hT, hR => by
    have hM1 : s.M = (r ++ [sep]).flatMap ic ++ (rs.flatMap (· ++ [sep])).flatMap ic := by
      rw [hM]; simp
    have hne : s.M ≠ [] := by rw [hM1]; simp [ic]
    obtain ⟨b, M', hbm⟩ := List.exists_cons_of_ne_nil hne
    have hrow := fap_ex_row r v _ s E (hs r List.mem_cons_self) hM1 hV hC hT hR
    have hb := fap_ex_rsB s hbm hrow
    have ih := fap_ex_rsL rs (v + 1)
      {s with M := (rs.flatMap (· ++ [sep])).flatMap ic, V := List.replicate (v + 1) true, R := rv (E ++ (inRow v ++ [sep] ++ (outRow r v ++ [sep])))}
      (E ++ (inRow v ++ [sep] ++ (outRow r v ++ [sep])))
      (fun r' hr' => hs r' (List.mem_cons_of_mem _ hr')) rfl rfl hC hT rfl
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp only [fap_Tr]; omega)
    congr 1; cases s
    simp [fap_out, show v + 1 + rs.length = v + (rs.length + 1) by omega]

theorem fap_Tr_le : ∀ (rs : List (List SatSym)) (v : ℕ),
    fap_Tr rs v ≤ rs.length * (20 * (v + rs.length) + 42) + 9 * (rs.map List.length).sum + 2
  | [], v => by simp [fap_Tr]
  | r :: rs, v => by
    have ih := fap_Tr_le rs (v + 1)
    simp only [fap_Tr, List.length_cons, List.map_cons, List.sum_cons]
    rw [show v + 1 + rs.length = v + (rs.length + 1) by omega] at ih
    have : (rs.length + 1) * (20 * (v + (rs.length + 1)) + 42) =
        rs.length * (20 * (v + (rs.length + 1)) + 42) + (20 * (v + (rs.length + 1)) + 42) := by
      ring
    omega

theorem fap_out_gen : ∀ (rs : List (List SatSym)) (v : ℕ),
    ((List.range rs.length).flatMap fun i => [inRow (v + i), outRow (rs.getD i []) (v + i)]).flatMap
      (· ++ [sep]) = fap_out rs v
  | [], v => by simp [fap_out]
  | r :: rs, v => by
    simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      fap_out, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero, List.flatMap_append]
    rw [← fap_out_gen rs (v + 1)]
    have hf : (fun a : ℕ => [inRow (v + a.succ), outRow (rs.getD a []) (v + a.succ)]) =
        (fun i => [inRow (v + 1 + i), outRow (rs.getD i []) (v + 1 + i)]) := by
      funext a; rw [show v + a.succ = v + 1 + a by omega]
    rw [hf]; simp

theorem fap_out_eq (rows : List (List SatSym)) :
    (splitRows rows).flatMap (· ++ [sep]) = fap_out rows 0 := by
  rw [← fap_out_gen]; simp [splitRows]

/-! ## The program -/

def fap_main : Cmd := .seq fap_cpL fap_rsL

def fap_s0 (M : Str) : fap_S := ⟨[], M, [], [], []⟩

theorem fap_ex_main (w : List SatSym) : ∃ s : fap_S,
    ExecLe fap_main (fap_s0 (enc (clauses w))).st (.norm s.st)
      ((clauses w).length * (20 * (clauses w).length + 42) + 15 * (trunc w).length + 10) ∧
      s.R = rv (splitW w) := by
  have hsep := sep_not_mem_clauses w
  have hsum := sum_length_le (clauses w)
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · have h1 : ExecLe fap_cpL (fap_s0 (enc [])).st (.norm (fap_s0 (enc [])).st) 2 :=
      ExecLe.loop_brk (ExecLe.pop_nil (by simp [fap_s0, enc]) (ExecLe.brk _))
    have h2 : ExecLe fap_rsL (fap_s0 (enc [])).st (.norm (fap_s0 (enc [])).st) 2 :=
      ExecLe.loop_brk (ExecLe.pop_nil (by simp [fap_s0, enc]) (ExecLe.brk _))
    refine ⟨_, (h1.seq_norm h2).cast rfl (by omega), ?_⟩
    simp [fap_s0, splitW, hcw]
  · rw [hcw] at hsep hsum
    have h1 := fap_ex_cpL kr (enc rows) (fap_s0 (enc (kr :: rows))) [] (hsep kr List.mem_cons_self)
      (by simp [fap_s0, enc]) rfl
    have h2 := fap_ex_rsL rows 0 {fap_s0 (enc (kr :: rows)) with M := enc rows, R := rv ([] ++ kr ++ [sep])} ([] ++ kr ++ [sep])
      (fun r hr => hsep r (List.mem_cons_of_mem _ hr)) rfl rfl rfl rfl rfl
    have hb := fap_Tr_le rows 0
    have ht : (trunc w).length = ((kr :: rows).flatMap (· ++ [sep])).length := by
      rw [trunc, hcw]
    refine ⟨_, (h1.seq_norm h2).cast rfl ?_, ?_⟩
    · simp only [List.length_cons, List.map_cons, List.sum_cons, zero_add] at hsum hb ⊢
      rw [ht, ← hsum]
      nlinarith
    · simp [splitW, hcw, fap_out_eq]

/-- The reduction program. -/
def fap_redCmd : Cmd := .seq parseLoop (.seq (trimC 4) (.seq (move 4 1) fap_main))

/-- The time bound. -/
def fap_Tred (L : ℕ) : ℕ := 100 * (L + 2) ^ 2

theorem fap_exec_redCmd (x : Str) : ∃ σ', ExecLe fap_redCmd (init [x]).stk (.norm σ')
    (fap_Tred x.length) ∧ σ' 0 = ((splitW (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ₁ := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := exec_trimC_word 4 w σ₁ (by simp [σ₁, he 4 (by decide)])
  set σ₂ := update σ₁ 4 (((trunc w).flatMap ic).reverse)
  have p3 := exec_move (a := 4) (b := 1) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 4 []) 1 ((σ₂ 4).reverse ++ σ₂ 1) =
      (fap_s0 (enc (clauses w))).st := by
    funext j
    by_cases hj : j < 5
    · interval_cases j <;> simp [σ₂, σ₁, he, enc, trunc, fap_S.st, fap_s0]
    · rw [fap_st_big _ _ (by omega)]
      simp [σ₂, σ₁, he j (by omega), show j ≠ 0 by omega, show j ≠ 1 by omega,
        show j ≠ 4 by omega]
  rw [hσ] at p3
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  obtain ⟨s, p4, hs⟩ := fap_ex_main w
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm p4))).cast rfl ?_, ?_⟩
  · have htl : (σ₂ 4).length = 2 * (trunc w).length := by
      simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
    rw [htl]
    unfold fap_Tred
    have h1 : (clauses w).length ≤ x.length := by omega
    have h2 : (trunc w).length ≤ x.length := by omega
    nlinarith [Nat.mul_le_mul h1 h1]
  · rw [fap_st0, hs]; rfl

theorem fap_Tred_le (n : ℕ) : fap_Tred n ≤ tb 9 n := by
  unfold fap_Tred tb
  have h7 : 2 ^ 7 ≤ (n + 2) ^ 7 := Nat.pow_le_pow_left (by omega) 7
  have e : (n + 2) ^ 9 = (n + 2) ^ 7 * (n + 2) ^ 2 := by ring
  rw [e]
  have : 100 ≤ (n + 2) ^ 7 := le_trans (by norm_num) h7
  exact Nat.mul_le_mul_right _ this

/-- `splitW` is polynomial-time computable. -/
theorem splitW_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    splitW) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    fap_redCmd 0 9 (fun x => splitW (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := fap_exec_redCmd x
      exact ⟨σ', h1.mono (fap_Tred_le _), h2⟩)
    splitW (fun t => (congrArg splitW (FunBridge.dec2_flatMap_ic t)).symm)

/-! ## The reduction -/

/-- **SAT ≤ₚ FEEDBACK ARC SET** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `FASI`. -/
theorem sat_le_fas_of (h : ∀ w, SATLang w ↔ FASLang (FASI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang FASLang := by
  obtain ⟨hG⟩ := VertexCover.GV_computable
  obtain ⟨hc⟩ := IndSet.cmap_computable
  obtain ⟨hs⟩ := splitW_computable
  exact ⟨splitW ∘ IndSet.cmap ∘ VertexCover.GV, Pnp.TM2Comp.comp (Pnp.TM2Comp.comp hG hc) hs, h⟩

end Pnp.Karp.FeedbackArc
