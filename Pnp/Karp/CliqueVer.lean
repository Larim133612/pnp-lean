import Pnp.Karp.Clique

/-!
# CLIQUE ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/Clique.lean`) and a certificate `y : List Bool` (bit `i` says whether vertex `i` is
in the clique).  Stack layout:

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the bound `k` (unary);  `5`: the number of selected rows so far (unary);
* `6`: the certificate bits read so far `Dn` (reversed);  `7`: the column bits `Y` of the
  current row;  `8`: a temporary;  `9`: the flag "the current row is selected".

Program (`verCmd`):
1. `phaseA` (from `SAT.lean`): parse the code of `w`; `trimC 2`: drop the unfinished tail;
   `move 2 3`;
2. `frLoop`: read the first row into the unary `k` (halt `false` if there is no row);
3. `srC` ("start row"): pop the next certificate bit `b` onto `Dn`; if `b`, select the row and
   set the column bits to the certificate with bit `i` cleared (`Dn.reverse ++ false :: R`);
4. `mainLoop`: one symbol per iteration; in a selected row, a set column bit requires the
   symbol `pos`; at `sep` the remaining column bits must be clear (`endRow`), the row is
   counted, and the next row is started; at the end of the input (`finalC`) the last popped
   bit and all unread certificate bits must be clear, and the count must be `≥ k`.

`exec_verCmd`: the program halts with `vres (dec z).1 (dec z).2` on every input `z`, within
`Tver |z|` steps.
-/

namespace Pnp.Karp.Clique

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

/-! ## Semantics -/

/-- All bits clear. -/
def allF : Str → Bool
  | [] => true
  | b :: Y => !b && allF Y

/-- The symbol `pos`. -/
def isPos : SatSym → Bool
  | pos => true
  | _ => false

/-- Check a selected row against its column bits. -/
def checkRow : List SatSym → Str → Bool
  | [], Y => allF Y
  | _ :: r, [] => checkRow r []
  | s :: r, c :: Y => (!c || isPos s) && checkRow r Y

/-- What the main loop computes (`K`: the bound, `R`: unread bits, `Dn`: read bits reversed,
`c`: selected rows so far). -/
def go (K : ℕ) : List (List SatSym) → Str → Str → ℕ → Bool
  | [], R, _, c => allF R && decide (K ≤ c)
  | _ :: rows, [], Dn, c => go K rows [] Dn c
  | _ :: rows, false :: R, Dn, c => go K rows R (false :: Dn) c
  | r :: rows, true :: R, Dn, c => checkRow r (Dn.reverse ++ false :: R) && go K rows R (true :: Dn) (c + 1)

/-- The answer of the verifier on `(w, y)`. -/
def vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | kr :: rows => go kr.length rows y [] 0

/-- Code of a list of rows. -/
def enc (L : List (List SatSym)) : Str := (L.flatMap (· ++ [sep])).flatMap ic

theorem enc_cons (r : List SatSym) (L : List (List SatSym)) :
    enc (r :: L) = r.flatMap ic ++ false :: false :: enc L := by
  simp [enc, List.flatMap_append, ic]

/-! ## Stack layout -/

/-- The stacks of the main phase. -/
def st1 (R Q Dn Y : Str) (K c : ℕ) (sel : Bool) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 4 then List.replicate K true else
  if j = 5 then List.replicate c true else if j = 6 then Dn else if j = 7 then Y else
  if j = 9 then CookLevin.fl sel else []

/-- Equality of stack assignments. -/
macro "stx" : tactic =>
  `(tactic| (funext j; simp only [st1, update_apply]; split_ifs <;> simp_all))

section St
variable {R Q Dn Y : Str} {K c : ℕ} {sel : Bool}
@[simp] theorem st1_0 : st1 R Q Dn Y K c sel 0 = R := rfl
@[simp] theorem st1_3 : st1 R Q Dn Y K c sel 3 = Q := rfl
@[simp] theorem st1_4 : st1 R Q Dn Y K c sel 4 = List.replicate K true := rfl
@[simp] theorem st1_5 : st1 R Q Dn Y K c sel 5 = List.replicate c true := rfl
@[simp] theorem st1_6 : st1 R Q Dn Y K c sel 6 = Dn := rfl
@[simp] theorem st1_7 : st1 R Q Dn Y K c sel 7 = Y := rfl
@[simp] theorem st1_8 : st1 R Q Dn Y K c sel 8 = [] := rfl
@[simp] theorem st1_9 : st1 R Q Dn Y K c sel 9 = CookLevin.fl sel := rfl
theorem u0 (R' : Str) : update (st1 R Q Dn Y K c sel) 0 R' = st1 R' Q Dn Y K c sel := by stx
theorem u3 (Q' : Str) : update (st1 R Q Dn Y K c sel) 3 Q' = st1 R Q' Dn Y K c sel := by stx
theorem u4 (K' : ℕ) : update (st1 R Q Dn Y K c sel) 4 (List.replicate K' true) =
    st1 R Q Dn Y K' c sel := by stx
theorem u5 (c' : ℕ) : update (st1 R Q Dn Y K c sel) 5 (List.replicate c' true) =
    st1 R Q Dn Y K c' sel := by stx
theorem u6 (D' : Str) : update (st1 R Q Dn Y K c sel) 6 D' = st1 R Q D' Y K c sel := by stx
theorem u7 (Y' : Str) : update (st1 R Q Dn Y K c sel) 7 Y' = st1 R Q Dn Y' K c sel := by stx
theorem u9 (s' : Bool) : update (st1 R Q Dn Y K c sel) 9 (CookLevin.fl s') = st1 R Q Dn Y K c s' := by stx
end St

/-! ## Commands -/

/-- Loop: halt `false` at a set bit of stack `k`, empty it otherwise. -/
def allFC (k : ℕ) : Cmd := .loop (.pop k .brk .skip (.halt false))

theorem ex_allFC (k : ℕ) : ∀ (Y : Str) (σ : ℕ → Str), σ k = Y →
    ExecLe (allFC k) σ (if allF Y then .norm (update σ k []) else .halt false) (3 * Y.length + 3)
  | [], σ, h => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk _))).cast
      (by simp [allF, ← h]) (by simp)
  | true :: Y, σ, h => (ExecLe.loop_halt (ExecLe.pop_cons (b := true) h (ExecLe.halt false _))).cast
      (by simp [allF]) (by simp)
  | false :: Y, σ, h => by
    have ih := ex_allFC k Y (update σ k Y) (by simp)
    refine (ExecLe.loop_norm (ExecLe.pop_cons (b := false) h (ExecLe.skip _)) ih).cast
      (by simp [allF]) (by simp; omega)

/-- Start a row (see the module docstring). -/
def selS : Cmd :=
  .seq (copyVia 0 7 8) (.seq (.push 7 false) (.seq (moveTwo 6 7 8) (.seq (move 8 6)
    (.seq (.push 6 true) (.push 9 true)))))

def srC : Cmd := .pop 0 .skip (.push 6 false) selS

/-- The state after `srC`. -/
def post (R Dn Q : Str) (K c : ℕ) : ℕ → Str :=
  match R with
  | [] => st1 [] Q Dn [] K c false
  | false :: R' => st1 R' Q (false :: Dn) [] K c false
  | true :: R' => st1 R' Q (true :: Dn) (Dn.reverse ++ false :: R') K c true

theorem e_move86 (R' Q Dn Y : Str) (K c : ℕ) :
    update (update (update (st1 R' Q [] Y K c false) 8 Dn.reverse) 8 []) 6
      (Dn.reverse.reverse ++ (update (st1 R' Q [] Y K c false) 8 Dn.reverse) 6) =
      st1 R' Q Dn Y K c false := by stx

theorem ex_srC (R Dn Q : Str) (K c : ℕ) :
    ExecLe srC (st1 R Q Dn [] K c false) (.norm (post R Dn Q K c))
      (5 * R.length + 5 * Dn.length + 15) := by
  rcases R with _ | ⟨_ | _, R'⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast rfl (by omega)
  · refine (ExecLe.pop_cons (b := false) (s := R') rfl (by rw [u0]; exact ExecLe.push 6 false _)).cast ?_ (by omega)
    simp only [post]; congr 1; stx
  · have h1 := exec_copyVia (a := 0) (b := 7) (t := 8) (by decide) (by decide) (by decide)
      (st1 R' Q Dn [] K c false) rfl
    have e1 : update (st1 R' Q Dn [] K c false) 7 (st1 R' Q Dn [] K c false 0 ++
        st1 R' Q Dn [] K c false 7) = st1 R' Q Dn R' K c false := by
      rw [st1_0, st1_7, List.append_nil, u7]
    rw [e1] at h1
    have h2 : ExecLe (.push 7 false) (st1 R' Q Dn R' K c false)
        (.norm (st1 R' Q Dn (false :: R') K c false)) 1 :=
      (ExecLe.push 7 false _).cast (by rw [st1_7, u7]) le_rfl
    have h3 := exec_moveTwo (s := 6) (a := 7) (b := 8) (by decide) (by decide) (by decide) Dn
      (st1 R' Q Dn (false :: R') K c false) rfl
    have e3 : update (update (update (st1 R' Q Dn (false :: R') K c false) 6 []) 7
        (Dn.reverse ++ (st1 R' Q Dn (false :: R') K c false) 7)) 8
        (Dn.reverse ++ (st1 R' Q Dn (false :: R') K c false) 8) =
        update (st1 R' Q [] (Dn.reverse ++ false :: R') K c false) 8 Dn.reverse := by
      rw [st1_7, st1_8, List.append_nil, u6, u7]
    rw [e3] at h3
    have h4 := exec_move (a := 8) (b := 6) (by decide) Dn.reverse
      (update (st1 R' Q [] (Dn.reverse ++ false :: R') K c false) 8 Dn.reverse) (by simp)
    have e4 : update (update (update (st1 R' Q [] (Dn.reverse ++ false :: R') K c false) 8
        Dn.reverse) 8 []) 6 (Dn.reverse.reverse ++ (update (st1 R' Q [] (Dn.reverse ++ false :: R')
        K c false) 8 Dn.reverse) 6) = st1 R' Q Dn (Dn.reverse ++ false :: R') K c false := by
      exact e_move86 R' Q Dn _ K c
    rw [e4] at h4
    have h5 : ExecLe (.seq (.push 6 true) (.push 9 true))
        (st1 R' Q Dn (Dn.reverse ++ false :: R') K c false)
        (.norm (st1 R' Q (true :: Dn) (Dn.reverse ++ false :: R') K c true)) 2 :=
      ((ExecLe.push 6 true _).seq_norm (ExecLe.push 9 true _)).cast
        (by rw [st1_6, u6, st1_9]; congr 1; exact u9 true) le_rfl
    refine (ExecLe.pop_cons (b := true) (s := R') rfl (by
      rw [u0]; exact (ExecLe.of h1).seq_norm (h2.seq_norm
      ((ExecLe.of h3).seq_norm ((ExecLe.of h4).seq_norm h5))))).cast rfl ?_
    simp only [List.length_cons, List.length_reverse, st1_0]; omega

/-- One column of a row (`ok`: the symbol is `pos`). -/
def colStep (ok : Bool) : Cmd :=
  .pop 9 .skip .skip (.seq (.push 9 true) (.pop 7 .skip .skip (if ok then .skip else .halt false)))

theorem ex_colStep_off (ok : Bool) (R Q Dn : Str) (K c : ℕ) :
    ExecLe (colStep ok) (st1 R Q Dn [] K c false) (.norm (st1 R Q Dn [] K c false)) 2 :=
  ExecLe.pop_nil (by simp [CookLevin.fl]) (ExecLe.skip _)

theorem ex_colStep_on (ok : Bool) (R Q Dn Y : Str) (K c : ℕ) :
    ExecLe (colStep ok) (st1 R Q Dn Y K c true)
      (if Y.head? = some true ∧ ok = false then .halt false
        else .norm (st1 R Q Dn Y.tail K c true)) 5 := by
  have e9 : st1 R Q Dn Y K c true 9 = true :: [] := rfl
  have e : update (update (st1 R Q Dn Y K c true) 9 []) 9 (true :: update (st1 R Q Dn Y K c true)
      9 [] 9) = st1 R Q Dn Y K c true := by stx
  refine (ExecLe.pop_cons (T := 4) e9 ?_).cast rfl (by omega)
  simp only [if_true]
  refine ExecLe.seq_norm (T₁ := 1) (T₂ := 3) (ExecLe.push 9 true _) ?_
  rw [e]
  rcases Y with _ | ⟨_ | _, Y'⟩
  · exact (ExecLe.pop_nil rfl (ExecLe.skip _)).cast (by simp) (by omega)
  · exact (ExecLe.pop_cons (b := false) rfl (ExecLe.skip _)).cast (by simp [u7]) (by omega)
  · cases ok
    · exact (ExecLe.pop_cons (b := true) rfl (ExecLe.halt false _)).cast (by simp) (by omega)
    · exact (ExecLe.pop_cons (b := true) rfl (ExecLe.skip _)).cast (by simp [u7]) (by omega)

/-- End of a row. -/
def endRow : Cmd := .pop 9 .skip .skip (.seq (allFC 7) (.push 5 true))

theorem ex_endRow_off (R Q Dn : Str) (K c : ℕ) :
    ExecLe endRow (st1 R Q Dn [] K c false) (.norm (st1 R Q Dn [] K c false)) 2 :=
  ExecLe.pop_nil (by simp [CookLevin.fl]) (ExecLe.skip _)

theorem ex_endRow_on (R Q Dn Y : Str) (K c : ℕ) :
    ExecLe endRow (st1 R Q Dn Y K c true)
      (if allF Y then .norm (st1 R Q Dn [] K (c + 1) false) else .halt false)
      (3 * Y.length + 5) := by
  have e9 : st1 R Q Dn Y K c true 9 = true :: [] := rfl
  refine (ExecLe.pop_cons (T := 3 * Y.length + 4) e9 ?_).cast rfl (by omega)
  simp only [if_true]
  have h := ex_allFC 7 Y _ (show update (st1 R Q Dn Y K c true) 9 [] 7 = Y by simp)
  cases hY : allF Y
  · rw [hY] at h; simp only [Bool.false_eq_true, if_false] at h ⊢
    exact (ExecLe.seq_halt h).mono (by omega)
  · rw [hY] at h; simp only [if_true] at h ⊢
    refine (h.seq_norm (ExecLe.push 5 true _)).cast ?_ le_rfl
    congr 1; funext j; simp only [st1, update_apply, CookLevin.fl]; split_ifs <;> simp_all [List.replicate_succ]

/-- Final check. -/
def finalC : Cmd :=
  .seq (.pop 9 .skip .skip (.halt false)) (.seq (allFC 0) (.seq (.push 5 true)
    (.seq (gtCmd 5 4) (.halt false))))

theorem ex_gtHalt (σ : ℕ → Str) :
    ExecLe (.seq (gtCmd 5 4) (.halt false)) σ (.halt (decide ((σ 4).length < (σ 5).length)))
      (5 * (σ 4).length + 2 * (σ 5).length + 8) := by
  have h := exec_gtCmd (yes := 5) (no := 4) (by decide) σ
  by_cases hl : (σ 4).length < (σ 5).length
  · exact (ExecLe.seq_halt (h.1 hl)).cast (by simp [hl]) (by omega)
  · exact ((h.2 hl).seq_norm (ExecLe.halt false _)).cast (by simp [hl]) (by omega)

theorem ex_finalC (R Dn : Str) (K c : ℕ) :
    ExecLe finalC (post R Dn [] K c) (.halt (go K [] R Dn c))
      (3 * R.length + 5 * K + 2 * c + 20) := by
  have hfin : ∀ R' D' : Str, ExecLe (.seq (allFC 0) (.seq (.push 5 true)
      (.seq (gtCmd 5 4) (.halt false)))) (st1 R' [] D' [] K c false)
      (.halt (allF R' && decide (K ≤ c))) (3 * R'.length + 5 * K + 2 * c + 16) := by
    intro R' D'
    have h := ex_allFC 0 R' (st1 R' [] D' [] K c false) rfl
    cases hR : allF R'
    · rw [hR] at h; simp only [Bool.false_eq_true, if_false] at h
      exact (ExecLe.seq_halt h).cast (by simp) (by omega)
    · rw [hR] at h; simp only [if_true] at h
      have hg := ex_gtHalt (update (update (st1 R' [] D' [] K c false) 0 []) 5
        (true :: update (st1 R' [] D' [] K c false) 0 [] 5))
      refine (h.seq_norm ((ExecLe.push 5 true _).seq_norm hg)).cast ?_ ?_
      · simp
      · simp; omega
  rcases R with _ | ⟨_ | _, R'⟩
  · exact ((ExecLe.pop_nil (by simp [CookLevin.fl]) (ExecLe.skip _)).seq_norm (hfin [] Dn)).cast
      (by simp [go]) (by simp; omega)
  · exact ((ExecLe.pop_nil (by simp [CookLevin.fl]) (ExecLe.skip _)).seq_norm (hfin R' (false :: Dn))).cast
      (by simp [go, allF]) (by simp; omega)
  · exact (ExecLe.seq_halt (ExecLe.pop_cons (b := true) (s := []) (by simp [post, CookLevin.fl])
      (ExecLe.halt false _))).cast (by simp [go, allF]) (by omega)

/-- Loop body of the main phase. -/
def mainB : Cmd :=
  .pop 3 finalC (.pop 3 (.halt false) (.seq endRow srC) (colStep false))
    (.pop 3 (.halt false) (colStep true) (colStep false))

def mainLoop : Cmd := .loop mainB

section Main

variable {R Dn Y Q : Str} {K c : ℕ} {sel : Bool}

theorem mainB_sym {s : SatSym} (hs : s ≠ sep) {r : Res} {T : ℕ}
    (h : ExecLe (colStep (isPos s)) (st1 R Q Dn Y K c sel) r T) :
    ExecLe mainB (st1 R (ic s ++ Q) Dn Y K c sel) r (T + 2) := by
  cases s with
  | sep => exact absurd rfl hs
  | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [u3, isPos] using h))
  | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [u3, isPos] using h))
  | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [u3, isPos] using h))

theorem mainB_sep {r : Res} {T : ℕ}
    (h : ExecLe (.seq endRow srC) (st1 R Q Dn Y K c sel) r T) :
    ExecLe mainB (st1 R (false :: false :: Q) Dn Y K c sel) r (T + 2) :=
  ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [u3, isPos] using h))

/-- An unselected row. -/
theorem ex_rowOff (N : ℕ) (hN : R.length + Dn.length ≤ N) (Q' : Str) : ∀ (r : List SatSym),
    sep ∉ r → ∀ (res : Res) (T' : ℕ), ExecLe mainLoop (post R Dn Q' K c) res T' →
    ExecLe mainLoop (st1 R (r.flatMap ic ++ false :: false :: Q') Dn [] K c false) res
      (T' + (10 * r.length + 5 * N + 20))
  | [], _, res, T', h => by
    have hb := mainB_sep (((ex_endRow_off R Q' Dn K c).seq_norm (ex_srC R Dn Q' K c)))
    exact (ExecLe.loop_norm hb h).cast rfl (by simp; omega)
  | s :: r, hr, res, T', h => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := ex_rowOff N hN Q' r (fun e => hr (List.mem_cons_of_mem _ e)) res T' h
    have hb := mainB_sym (Q := r.flatMap ic ++ false :: false :: Q') hs
      (ex_colStep_off (isPos s) R _ Dn K c)
    exact (ExecLe.loop_norm (by simpa using hb) ih).cast rfl (by simp; omega)

/-- A selected row. -/
theorem ex_rowOn (N : ℕ) (hN : R.length + Dn.length ≤ N) (Q' : Str) : ∀ (r : List SatSym) (Y : Str),
    sep ∉ r → Y.length ≤ N + 1 → ∀ (res : Res) (T' : ℕ), ExecLe mainLoop (post R Dn Q' K (c + 1)) res T' →
    ExecLe mainLoop (st1 R (r.flatMap ic ++ false :: false :: Q') Dn Y K c true)
      (if checkRow r Y then res else .halt false) (T' + (10 * r.length + 8 * N + 30))
  | [], Y, _, hY, res, T', h => by
    have he := ex_endRow_on R Q' Dn Y K c
    cases hc : allF Y
    · rw [hc] at he; simp only [Bool.false_eq_true, if_false] at he
      exact (ExecLe.loop_halt (mainB_sep (ExecLe.seq_halt he))).cast
        (by simp [checkRow, hc]) (by omega)
    · rw [hc] at he; simp only [if_true] at he
      have hb := mainB_sep (he.seq_norm (ex_srC R Dn Q' K (c + 1)))
      exact (ExecLe.loop_norm hb h).cast (by simp [checkRow, hc]) (by simp; omega)
  | s :: r, Y, hr, hY, res, T', h => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have hcs := ex_colStep_on (isPos s) R (r.flatMap ic ++ false :: false :: Q') Dn Y K c
    have hb := mainB_sym (Q := r.flatMap ic ++ false :: false :: Q') hs hcs
    simp only [List.flatMap_cons, List.append_assoc]
    rcases Y with _ | ⟨_ | _, Y'⟩
    · simp only [List.head?_nil, reduceCtorEq, false_and, if_false, List.tail_nil] at hb
      have ih := ex_rowOn N hN Q' r [] hr' (by simp) res T' h
      exact (ExecLe.loop_norm hb ih).cast (by simp [checkRow]) (by simp; omega)
    · simp only [List.head?_cons, Option.some.injEq, Bool.false_eq_true, false_and, if_false,
        List.tail_cons] at hb
      have ih := ex_rowOn N hN Q' r Y' hr' (by simp at hY; omega) res T' h
      exact (ExecLe.loop_norm hb ih).cast (by simp [checkRow]) (by simp; omega)
    · by_cases hp : s = pos
      · subst hp
        simp only [List.head?_cons, isPos, Bool.true_eq_false, and_false, if_false,
          List.tail_cons] at hb
        have ih := ex_rowOn N hN Q' r Y' hr' (by simp at hY; omega) res T' h
        exact (ExecLe.loop_norm hb ih).cast (by simp [checkRow, isPos]) (by simp; omega)
      · have hp' : isPos s = false := by cases s <;> simp_all [isPos]
        simp only [List.head?_cons, hp', and_self, if_true] at hb
        exact (ExecLe.loop_halt hb).cast (by simp [checkRow, hp']) (by omega)

/-- Cost of the main phase. -/
def Trows (N : ℕ) : List (List SatSym) → ℕ
  | [] => 10 * N + 30
  | r :: rows => 10 * r.length + 8 * N + 30 + Trows N rows

theorem ex_rows (N : ℕ) (hK : K ≤ N) : ∀ (rows : List (List SatSym)) (R Dn : Str) (c : ℕ),
    (∀ r ∈ rows, sep ∉ r) → R.length + Dn.length ≤ N → c + rows.length ≤ N →
    ExecLe mainLoop (post R Dn (enc rows) K c) (.halt (go K rows R Dn c)) (Trows N rows)
  | [], R, Dn, c, _, hN, hc => by
    have hf := ex_finalC R Dn K c
    have hb : ExecLe mainB (post R Dn [] K c) (.halt (go K [] R Dn c))
        (3 * R.length + 5 * K + 2 * c + 20 + 1) :=
      ExecLe.pop_nil (by rcases R with _ | ⟨_ | _, _⟩ <;> rfl) hf
    exact (ExecLe.loop_halt hb).cast rfl (by simp [Trows] at hc ⊢; nlinarith)
  | r :: rows, R, Dn, c, hrows, hN, hc => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.length_cons] at hc
    rw [enc_cons]
    rcases R with _ | ⟨_ | _, R'⟩
    · have ih := ex_rows N hK rows [] Dn c hrs hN (by omega)
      have := ex_rowOff (R := []) (Dn := Dn) (K := K) (c := c) N hN (enc rows) r hr _ _ ih
      exact this.cast (by simp [go]) (by simp [Trows]; omega)
    · have ih := ex_rows N hK rows R' (false :: Dn) c hrs (by simp at hN ⊢; omega) (by omega)
      have := ex_rowOff (R := R') (Dn := false :: Dn) (K := K) (c := c) N (by simp at hN ⊢; omega)
        (enc rows) r hr _ _ ih
      exact this.cast (by simp [go]) (by simp [Trows]; omega)
    · have ih := ex_rows N hK rows R' (true :: Dn) (c + 1) hrs (by simp at hN ⊢; omega) (by omega)
      have := ex_rowOn (R := R') (Dn := true :: Dn) (K := K) (c := c) N (by simp at hN ⊢; omega)
        (enc rows) r (Dn.reverse ++ false :: R') hr (by simp at hN ⊢; omega) _ _ ih
      refine this.cast ?_ (by simp [Trows]; omega)
      simp only [go]
      cases checkRow r (Dn.reverse ++ false :: R') <;> rfl

end Main

/-! ## The first row -/

def frB : Cmd :=
  .pop 3 (.halt false) (.pop 3 (.halt false) .brk (.push 4 true))
    (.pop 3 (.halt false) (.push 4 true) (.push 4 true))

def frLoop : Cmd := .loop frB

theorem ex_frLoop (R Dn Y Q' : Str) (c : ℕ) (sel : Bool) : ∀ (kr : List SatSym) (K : ℕ),
    sep ∉ kr → ExecLe frLoop (st1 R (kr.flatMap ic ++ false :: false :: Q') Dn Y K c sel)
      (.norm (st1 R Q' Dn Y (K + kr.length) c sel)) (3 * kr.length + 3)
  | [], K, _ => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) rfl
      (ExecLe.pop_cons (b := false) (s := Q') (by simp) (ExecLe.brk _)))).cast
      (by simp [u3]) (by simp)
  | s :: kr, K, hr => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := ex_frLoop R Dn Y Q' c sel kr (K + 1) (fun e => hr (List.mem_cons_of_mem _ e))
    set Q := kr.flatMap ic ++ false :: false :: Q'
    have hb : ExecLe frB (st1 R (ic s ++ Q) Dn Y K c sel) (.norm (st1 R Q Dn Y (K + 1) c sel)) 3 := by
      have hp : ExecLe (.push 4 true) (st1 R Q Dn Y K c sel) (.norm (st1 R Q Dn Y (K + 1) c sel)) 1 :=
        (ExecLe.push 4 true _).cast (by rw [st1_4, ← List.replicate_succ, u4]) le_rfl
      cases s with
      | sep => exact absurd rfl hs
      | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
          (by simp) (by simpa [u3] using hp))
      | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
          (by simp) (by simpa [u3] using hp))
      | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
          (by simp) (by simpa [u3] using hp))
    refine (ExecLe.loop_norm (by simpa [Q] using hb) ih).cast (by simp; ring_nf) (by simp; omega)

/-! ## The whole verifier -/

def verCmd : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq frLoop (.seq srC mainLoop))))

/-- Time bound of the verifier. -/
def Tver (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (3 * n + 3) + (5 * n + 15) +
  (10 * n + 8 * n * n + 30 * n + 10 * n + 30)

theorem Trows_le (N : ℕ) : ∀ rows : List (List SatSym),
    Trows N rows = 10 * (rows.map List.length).sum + rows.length * (8 * N + 30) + 10 * N + 30
  | [] => by simp [Trows]
  | r :: rows => by simp only [Trows, Trows_le N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem sum_length_le (L : List (List SatSym)) :
    (L.map List.length).sum + L.length = (L.flatMap (· ++ [sep])).length := by
  induction L with
  | nil => simp
  | cons r L ih => simp [List.flatMap_cons]; omega

theorem exec_verCmd (z : Str) :
    ExecLe verCmd (init [z]).stk (.halt (vres (dec z).1 (dec z).2)) (Tver z.length) := by
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
  have hσ : update (update σ₂ 2 []) 3 ((σ₂ 2).reverse ++ σ₂ 3) =
      st1 y (enc (clauses w)) [] [] 0 0 false := by
    funext j
    simp only [σ₂, σ₁, st1, update_apply, enc, trunc, CookLevin.fl]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ), ExecLe c (st1 y (enc (clauses w)) [] [] 0 0 false) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold vres verCmd
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq frLoop (.seq srC mainLoop)) (st1 y (enc []) [] [] 0 0 false)
        (.halt false) 2 :=
      ExecLe.seq_halt (ExecLe.loop_halt ((ExecLe.pop_nil rfl (ExecLe.halt false _)).cast rfl le_rfl))
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, Tver]; nlinarith
  · rw [hcw] at hsum hcl hsep hpre
    rw [enc_cons] at hpre
    have hF := ex_frLoop y [] [] (enc rows) 0 false kr 0 (hsep kr (by simp))
    have hS := ex_srC y [] (enc rows) (0 + kr.length) 0
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum hcl
    have hR := ex_rows (K := 0 + kr.length) z.length (by omega) rows y [] 0
      (fun r hr => hsep r (by simp [hr])) (by simp; omega) (by omega)
    refine (hpre _ _ _ (hF.seq_norm (hS.seq_norm hR))).cast (by simp) ?_
    rw [Trows_le]
    simp only [htl, Tver, List.length_nil]
    have h1 : rows.length * (8 * z.length + 30) ≤ z.length * (8 * z.length + 30) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem Tver_le (n : ℕ) : Tver n ≤ tb 6 n := by
  unfold Tver tb
  have hm : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  norm_num at hm
  have e : (n + 2) ^ 6 = (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by ring
  have : 16 * (n + 2) ^ 2 ≤ (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by nlinarith
  nlinarith

end Pnp.Karp.Clique
