import Pnp.Karp.IndSet
import Pnp.Karp.CliqueVer

/-!
# INDEPENDENT SET / VERTEX COVER ∈ NP: the verifier program

A variant of the CLIQUE verifier (`Pnp/Karp/CliqueVer.lean`; same stack layout `st1`, same
parsing, first row and row start `srC`), with a mode bit `vc`:

* the certificate `y` is the indicator list of a set `S` of vertices (an independent set);
* in a selected row, a set column bit requires the symbol to be *different from* `pos`
  (`colStep (!isPos s)`), and at the end of a row the remaining column bits are discarded
  (`endRowI`: missing entries are `zero`, i.e. no edge);
* `vc = false` (INDEPENDENT SET): stack `5` counts the selected rows, and at the end the count
  must be `≥ k`;
* `vc = true` (VERTEX COVER, `S` being the complement of the cover): stack `5` counts the
  *unselected* rows, and at the end the count must be `≤ k`.

`exec_verCmdI`: the program halts with `vresI vc (dec z).1 (dec z).2` on every input `z`, within
`TverI |z|` steps.
-/

namespace Pnp.Karp.IndSet

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Semantics -/

/-- Conditional increment. -/
def inc (b : Bool) (c : ℕ) : ℕ := if b then c + 1 else c

@[simp] theorem inc_false (c : ℕ) : inc false c = c := rfl
@[simp] theorem inc_true (c : ℕ) : inc true c = c + 1 := rfl

theorem inc_le (b : Bool) (c : ℕ) : inc b c ≤ c + 1 := by cases b <;> simp

/-- Check a selected row against its column bits: no set column holds `pos`. -/
def checkRowI : List SatSym → Str → Bool
  | [], _ => true
  | _ :: r, [] => checkRowI r []
  | s :: r, c :: Y => (!c || !isPos s) && checkRowI r Y

/-- Final count test. -/
def finB (vc : Bool) (K c : ℕ) : Bool := if vc then decide (c ≤ K) else decide (K ≤ c)

/-- What the main loop computes. -/
def goI (vc : Bool) (K : ℕ) : List (List SatSym) → Str → Str → ℕ → Bool
  | [], R, _, c => allF R && finB vc K c
  | _ :: rows, [], Dn, c => goI vc K rows [] Dn (inc vc c)
  | _ :: rows, false :: R, Dn, c => goI vc K rows R (false :: Dn) (inc vc c)
  | r :: rows, true :: R, Dn, c =>
      checkRowI r (Dn.reverse ++ false :: R) && goI vc K rows R (true :: Dn) (inc (!vc) c)

/-- The answer of the verifier on `(w, y)`. -/
def vresI (vc : Bool) (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | kr :: rows => goI vc kr.length rows y [] 0

/-! ## End of a row -/

/-- End of a row: discard the column bits; count the row. -/
def endRowI : Bool → Cmd
  | false => .pop 9 .skip .skip (.seq (drain 7) (.push 5 true))
  | true => .pop 9 (.push 5 true) (.push 5 true) (drain 7)

section Rows
variable {R Q Dn Y : Str} {K c : ℕ}

theorem ex_push5 : ExecLe (.push 5 true) (st1 R Q Dn Y K c false)
    (.norm (st1 R Q Dn Y K (c + 1) false)) 1 :=
  (ExecLe.push 5 true _).cast (by rw [st1_5, ← List.replicate_succ, u5]) le_rfl

theorem ex_endRowI_off (vc : Bool) :
    ExecLe (endRowI vc) (st1 R Q Dn [] K c false) (.norm (st1 R Q Dn [] K (inc vc c) false)) 2 := by
  cases vc
  · exact ExecLe.pop_nil (by simp [CookLevin.fl]) (ExecLe.skip _)
  · exact ExecLe.pop_nil (by simp [CookLevin.fl]) ex_push5

theorem ex_drain7 (sel : Bool) :
    ExecLe (drain 7) (st1 R Q Dn Y K c sel) (.norm (st1 R Q Dn [] K c sel)) (2 * Y.length + 2) :=
  (ExecLe.of (exec_drain 7 Y _ rfl)).cast (by rw [u7]) le_rfl

theorem ex_endRowI_on (vc : Bool) :
    ExecLe (endRowI vc) (st1 R Q Dn Y K c true)
      (.norm (st1 R Q Dn [] K (inc (!vc) c) false)) (3 * Y.length + 5) := by
  have e9 : st1 R Q Dn Y K c true 9 = true :: [] := rfl
  have e : update (st1 R Q Dn Y K c true) 9 [] = st1 R Q Dn Y K c false := by
    simpa [CookLevin.fl] using (u9 (R := R) (Q := Q) (Dn := Dn) (Y := Y) (K := K) (c := c)
      (sel := true) false)
  cases vc
  · refine (ExecLe.pop_cons e9 ?_).cast rfl (show 2 * Y.length + 2 + 1 + 1 ≤ _ by omega)
    simp only [if_true, e]
    exact (ex_drain7 false).seq_norm ex_push5
  · refine (ExecLe.pop_cons e9 ?_).cast rfl (show 2 * Y.length + 2 + 1 ≤ _ by omega)
    simp only [if_true, e]
    exact ex_drain7 false

end Rows

/-! ## Final check -/

/-- Final check (`vc = false`: `K ≤ c`, i.e. `K < c + 1`; `vc = true`: `c < K + 1`). -/
def finalCI : Bool → Cmd
  | false => finalC
  | true => .seq (.pop 9 .skip .skip (.halt false)) (.seq (allFC 0) (.seq (.push 4 true)
      (.seq (gtCmd 4 5) (.halt false))))

theorem ex_gtHalt45 (σ : ℕ → Str) :
    ExecLe (.seq (gtCmd 4 5) (.halt false)) σ (.halt (decide ((σ 5).length < (σ 4).length)))
      (5 * (σ 5).length + 2 * (σ 4).length + 8) := by
  have h := exec_gtCmd (yes := 4) (no := 5) (by decide) σ
  by_cases hl : (σ 5).length < (σ 4).length
  · exact (ExecLe.seq_halt (h.1 hl)).cast (by simp [hl]) (by omega)
  · exact ((h.2 hl).seq_norm (ExecLe.halt false _)).cast (by simp [hl]) (by omega)

theorem ex_finalCI (vc : Bool) (R Dn : Str) (K c : ℕ) :
    ExecLe (finalCI vc) (post R Dn [] K c) (.halt (goI vc K [] R Dn c))
      (3 * R.length + 5 * K + 5 * c + 22) := by
  cases vc
  · exact (ex_finalC R Dn K c).cast (by simp [goI, go, finB]) (by omega)
  have hfin : ∀ R' D' : Str, ExecLe (.seq (allFC 0) (.seq (.push 4 true)
      (.seq (gtCmd 4 5) (.halt false)))) (st1 R' [] D' [] K c false)
      (.halt (allF R' && decide (c ≤ K))) (3 * R'.length + 5 * K + 5 * c + 18) := by
    intro R' D'
    have h := ex_allFC 0 R' (st1 R' [] D' [] K c false) rfl
    cases hR : allF R'
    · rw [hR] at h; simp only [Bool.false_eq_true, if_false] at h
      exact (ExecLe.seq_halt h).cast (by simp) (by omega)
    · rw [hR] at h; simp only [if_true] at h
      have hg := ex_gtHalt45 (update (update (st1 R' [] D' [] K c false) 0 []) 4
        (true :: update (st1 R' [] D' [] K c false) 0 [] 4))
      refine (h.seq_norm ((ExecLe.push 4 true _).seq_norm hg)).cast ?_ ?_
      · simp
      · simp; omega
  rcases R with _ | ⟨_ | _, R'⟩
  · exact ((ExecLe.pop_nil (by simp [CookLevin.fl]) (ExecLe.skip _)).seq_norm (hfin [] Dn)).cast
      (by simp [goI, finB]) (by simp; omega)
  · exact ((ExecLe.pop_nil (by simp [CookLevin.fl]) (ExecLe.skip _)).seq_norm
      (hfin R' (false :: Dn))).cast (by simp [goI, allF, finB]) (by simp; omega)
  · exact (ExecLe.seq_halt (ExecLe.pop_cons (b := true) (s := []) (by simp [post, CookLevin.fl])
      (ExecLe.halt false _))).cast (by simp [goI, allF]) (by omega)

/-! ## The main loop -/

/-- Loop body of the main phase. -/
def mainBI (vc : Bool) : Cmd :=
  .pop 3 (finalCI vc) (.pop 3 (.halt false) (.seq (endRowI vc) srC) (colStep true))
    (.pop 3 (.halt false) (colStep false) (colStep true))

def mainLoopI (vc : Bool) : Cmd := .loop (mainBI vc)

section Main

variable {vc : Bool} {R Dn Y Q : Str} {K c : ℕ} {sel : Bool}

theorem mainBI_sym {s : SatSym} (hs : s ≠ sep) {r : Res} {T : ℕ}
    (h : ExecLe (colStep (!isPos s)) (st1 R Q Dn Y K c sel) r T) :
    ExecLe (mainBI vc) (st1 R (ic s ++ Q) Dn Y K c sel) r (T + 2) := by
  cases s with
  | sep => exact absurd rfl hs
  | zero => exact ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [u3, isPos] using h))
  | pos => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [u3, isPos] using h))
  | neg => exact ExecLe.pop_cons (b := true) rfl (ExecLe.pop_cons (b := true) (s := Q)
      (by simp) (by simpa [u3, isPos] using h))

theorem mainBI_sep {r : Res} {T : ℕ}
    (h : ExecLe (.seq (endRowI vc) srC) (st1 R Q Dn Y K c sel) r T) :
    ExecLe (mainBI vc) (st1 R (false :: false :: Q) Dn Y K c sel) r (T + 2) :=
  ExecLe.pop_cons (b := false) rfl (ExecLe.pop_cons (b := false) (s := Q)
      (by simp) (by simpa [u3] using h))

/-- An unselected row. -/
theorem ex_rowOffI (N : ℕ) (hN : R.length + Dn.length ≤ N) (Q' : Str) : ∀ (r : List SatSym),
    sep ∉ r → ∀ (res : Res) (T' : ℕ), ExecLe (mainLoopI vc) (post R Dn Q' K (inc vc c)) res T' →
    ExecLe (mainLoopI vc) (st1 R (r.flatMap ic ++ false :: false :: Q') Dn [] K c false) res
      (T' + (10 * r.length + 5 * N + 20))
  | [], _, res, T', h => by
    have hb := mainBI_sep (vc := vc)
      (((ex_endRowI_off vc).seq_norm (ex_srC R Dn Q' K (inc vc c))))
    exact (ExecLe.loop_norm hb h).cast rfl (by simp; omega)
  | s :: r, hr, res, T', h => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := ex_rowOffI N hN Q' r (fun e => hr (List.mem_cons_of_mem _ e)) res T' h
    have hb := mainBI_sym (vc := vc) (Q := r.flatMap ic ++ false :: false :: Q') hs
      (ex_colStep_off (!isPos s) R _ Dn K c)
    exact (ExecLe.loop_norm (by simpa using hb) ih).cast rfl (by simp; omega)

/-- A selected row. -/
theorem ex_rowOnI (N : ℕ) (hN : R.length + Dn.length ≤ N) (Q' : Str) :
    ∀ (r : List SatSym) (Y : Str),
    sep ∉ r → Y.length ≤ N + 1 → ∀ (res : Res) (T' : ℕ),
    ExecLe (mainLoopI vc) (post R Dn Q' K (inc (!vc) c)) res T' →
    ExecLe (mainLoopI vc) (st1 R (r.flatMap ic ++ false :: false :: Q') Dn Y K c true)
      (if checkRowI r Y then res else .halt false) (T' + (10 * r.length + 8 * N + 30))
  | [], Y, _, hY, res, T', h => by
    have he := ex_endRowI_on (R := R) (Q := Q') (Dn := Dn) (Y := Y) (K := K) (c := c) vc
    have hb := mainBI_sep (he.seq_norm (ex_srC R Dn Q' K (inc (!vc) c)))
    exact (ExecLe.loop_norm hb h).cast (by simp [checkRowI]) (by simp; omega)
  | s :: r, Y, hr, hY, res, T', h => by
    have hs : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    have hcs := ex_colStep_on (!isPos s) R (r.flatMap ic ++ false :: false :: Q') Dn Y K c
    have hb := mainBI_sym (vc := vc) (Q := r.flatMap ic ++ false :: false :: Q') hs hcs
    simp only [List.flatMap_cons, List.append_assoc]
    rcases Y with _ | ⟨_ | _, Y'⟩
    · simp only [List.head?_nil, reduceCtorEq, false_and, if_false, List.tail_nil] at hb
      have ih := ex_rowOnI N hN Q' r [] hr' (by simp) res T' h
      exact (ExecLe.loop_norm hb ih).cast (by simp [checkRowI]) (by simp; omega)
    · simp only [List.head?_cons, Option.some.injEq, Bool.false_eq_true, false_and, if_false,
        List.tail_cons] at hb
      have ih := ex_rowOnI N hN Q' r Y' hr' (by simp at hY; omega) res T' h
      exact (ExecLe.loop_norm hb ih).cast (by simp [checkRowI]) (by simp; omega)
    · by_cases hp : isPos s = true
      · simp only [List.head?_cons, hp, Bool.not_true, and_self, if_true] at hb
        exact (ExecLe.loop_halt hb).cast (by simp [checkRowI, hp]) (by omega)
      · have hp' : isPos s = false := by simpa using hp
        simp only [List.head?_cons, hp', Bool.not_false, Bool.true_eq_false, and_false, if_false,
          List.tail_cons] at hb
        have ih := ex_rowOnI N hN Q' r Y' hr' (by simp at hY; omega) res T' h
        exact (ExecLe.loop_norm hb ih).cast (by simp [checkRowI, hp']) (by simp; omega)

/-- Cost of the main phase. -/
def TrowsI (N : ℕ) : List (List SatSym) → ℕ
  | [] => 15 * N + 30
  | r :: rows => 10 * r.length + 8 * N + 30 + TrowsI N rows

theorem ex_rowsI (N : ℕ) (hK : K ≤ N) : ∀ (rows : List (List SatSym)) (R Dn : Str) (c : ℕ),
    (∀ r ∈ rows, sep ∉ r) → R.length + Dn.length ≤ N → c + rows.length ≤ N →
    ExecLe (mainLoopI vc) (post R Dn (enc rows) K c) (.halt (goI vc K rows R Dn c))
      (TrowsI N rows)
  | [], R, Dn, c, _, hN, hc => by
    have hf := ex_finalCI vc R Dn K c
    have hb : ExecLe (mainBI vc) (post R Dn [] K c) (.halt (goI vc K [] R Dn c))
        (3 * R.length + 5 * K + 5 * c + 22 + 1) :=
      ExecLe.pop_nil (by rcases R with _ | ⟨_ | _, _⟩ <;> rfl) hf
    exact (ExecLe.loop_halt hb).cast rfl (by simp [TrowsI] at hc ⊢; omega)
  | r :: rows, R, Dn, c, hrows, hN, hc => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.length_cons] at hc
    rw [enc_cons]
    have hi1 := inc_le vc c
    have hi2 := inc_le (!vc) c
    rcases R with _ | ⟨_ | _, R'⟩
    · have ih := ex_rowsI N hK rows [] Dn (inc vc c) hrs hN (by omega)
      have := ex_rowOffI (vc := vc) (R := []) (Dn := Dn) (K := K) (c := c) N hN (enc rows) r hr
        _ _ ih
      exact this.cast (by simp [goI]) (by simp [TrowsI]; omega)
    · have ih := ex_rowsI N hK rows R' (false :: Dn) (inc vc c) hrs (by simp at hN ⊢; omega)
        (by omega)
      have := ex_rowOffI (vc := vc) (R := R') (Dn := false :: Dn) (K := K) (c := c) N
        (by simp at hN ⊢; omega) (enc rows) r hr _ _ ih
      exact this.cast (by simp [goI]) (by simp [TrowsI]; omega)
    · have ih := ex_rowsI N hK rows R' (true :: Dn) (inc (!vc) c) hrs (by simp at hN ⊢; omega)
        (by omega)
      have := ex_rowOnI (vc := vc) (R := R') (Dn := true :: Dn) (K := K) (c := c) N
        (by simp at hN ⊢; omega) (enc rows) r (Dn.reverse ++ false :: R') hr
        (by simp at hN ⊢; omega) _ _ ih
      refine this.cast ?_ (by simp [TrowsI]; omega)
      simp only [goI]
      cases checkRowI r (Dn.reverse ++ false :: R') <;> rfl

end Main

/-! ## The whole verifier -/

def verCmdI (vc : Bool) : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq frLoop (.seq srC (mainLoopI vc)))))

/-- Time bound of the verifier. -/
def TverI (n : ℕ) : ℕ := (3 * n + 4) + (4 * n + 6) + (4 * n + 2) + (3 * n + 3) + (5 * n + 15) +
  (10 * n + 8 * n * n + 30 * n + 15 * n + 30)

theorem TrowsI_le (N : ℕ) : ∀ rows : List (List SatSym),
    TrowsI N rows = 10 * (rows.map List.length).sum + rows.length * (8 * N + 30) + 15 * N + 30
  | [] => by simp [TrowsI]
  | r :: rows => by simp only [TrowsI, TrowsI_le N rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem exec_verCmdI (vc : Bool) (z : Str) :
    ExecLe (verCmdI vc) (init [z]).stk (.halt (vresI vc (dec z).1 (dec z).2)) (TverI z.length) := by
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
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ),
      ExecLe c (st1 y (enc (clauses w)) [] [] 0 0 false) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold vresI verCmdI
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨kr, rows⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq frLoop (.seq srC (mainLoopI vc))) (st1 y (enc []) [] [] 0 0 false)
        (.halt false) 2 :=
      ExecLe.seq_halt (ExecLe.loop_halt ((ExecLe.pop_nil rfl (ExecLe.halt false _)).cast rfl
        le_rfl))
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, TverI]; nlinarith
  · rw [hcw] at hsum hcl hsep hpre
    rw [enc_cons] at hpre
    have hF := ex_frLoop y [] [] (enc rows) 0 false kr 0 (hsep kr (by simp))
    have hS := ex_srC y [] (enc rows) (0 + kr.length) 0
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum hcl
    have hR := ex_rowsI (vc := vc) (K := 0 + kr.length) z.length (by omega) rows y [] 0
      (fun r hr => hsep r (by simp [hr])) (by simp; omega) (by omega)
    refine (hpre _ _ _ (hF.seq_norm (hS.seq_norm hR))).cast (by simp) ?_
    rw [TrowsI_le]
    simp only [htl, TverI, List.length_nil]
    have h1 : rows.length * (8 * z.length + 30) ≤ z.length * (8 * z.length + 30) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem TverI_le (n : ℕ) : TverI n ≤ tb 6 n := by
  unfold TverI tb
  have hm : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  norm_num at hm
  have e : (n + 2) ^ 6 = (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by ring
  have : 16 * (n + 2) ^ 2 ≤ (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 2 := by nlinarith
  nlinarith

end Pnp.Karp.IndSet
