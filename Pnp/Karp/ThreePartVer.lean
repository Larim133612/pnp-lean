import Pnp.Karp.BinPackingVer
import Pnp.Karp.ThreePart

/-!
# 3-PARTITION ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(rows `items ++ [Bv]`, `Pnp/Karp/ThreePart.lean`) and a certificate `y : List Bool`.

## Certificate

As for BIN PACKING (`Pnp/Karp/BinPackingVer.lean`): the certificate is read in passes, one
per group; in each pass one certificate bit is popped per item that is still unassigned, a set
bit puts the item into the current group.  The sum of a group must be exactly `B`.

## Program (`tpv_ver`)

Stacks as in `bpv_st` (`0` certificate, `3` items, `4` the bound `C = B` in bits, `5` the
accumulator, `10` the unary pass counter, `12` the kept items); `13`–`16` are temporaries.

1. `phaseA`, `trimC 2`, `bpv_c0`: read the last row `Bv` (reversed) onto stack `4`;
   `move 2 3`: the code of the items is on stack `3`;
2. `copyVia 3 12 15`, then the bounds loop `tpv_bL`: per item, compute its value (`sv_addLoop`
   into the empty accumulator), check `B < 4 a` and `2 a < B` (`tpv_chk`, halt `false`
   otherwise) and push a mark onto stack `10`; then `move 12 13`, `move 13 3` restore the items;
3. `tpv_oL`: pop three marks per pass (halt `false` if fewer than three are left), run a
   BIN PACKING pass `bpv_iL` and check that the accumulator equals `B` (`tpv_fin`).  Without
   marks, accept iff all items are assigned.
-/

namespace Pnp.Karp.ThreePart

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.JobSeq Pnp.Karp.NAE Pnp.Karp.BinPacking

/-! ## Semantics -/

/-- The bound check on the value bits `A` of an item: `¬ 4 A ≤ C` and `¬ C ≤ 2 A`. -/
def tpv_okA (C A : Str) : Bool :=
  !kv_leF true (false :: false :: A) C && !kv_leF true C (false :: A)

/-- The bound check of an item. -/
def tpv_ok (C : Str) (r : List SatSym) : Bool := tpv_okA C (sv_addL false [] (sv_bits r))

/-- The bound check of all items. -/
def tpv_bnd (C : Str) : List (List SatSym) → Bool
  | [] => true
  | r :: rs => tpv_ok C r && tpv_bnd C rs

/-- What the main loop computes (`k` marks, three per pass). -/
def tpv_go (C : Str) : ℕ → List (List SatSym) → Str → Bool
  | 0, rows, _ => rows.isEmpty
  | 1, _, _ => false
  | 2, _, _ => false
  | k + 3, rows, R =>
    (kv_leF true (bpv_A rows R []) C && kv_leF true C (bpv_A rows R [])) &&
      tpv_go C k (bpv_U rows R) (bpv_rest rows R)

/-- The answer of the verifier on `(w, y)`. -/
def tpv_vres (w : List SatSym) (y : Str) : Bool :=
  match (clauses w).reverse with
  | [] => false
  | Bv :: rr => tpv_bnd (sv_bits Bv) rr.reverse &&
      tpv_go (sv_bits Bv) rr.reverse.length rr.reverse y

local macro "tpv_stx" : tactic =>
  `(tactic| (funext j; rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|j <;>
    simp [bpv_st, update_apply]))

/-! ## A comparison test -/

/-- Compare stacks `a ≤ b` (emptying both); continue with `cn` if not, with `ct` if so. -/
def tpv_test (a b : ℕ) (cn ct : Cmd) : Cmd :=
  .seq (.push 14 true) (.seq (kv_cmpLoop a b 14) (.pop 14 cn (.halt false) ct))

theorem tpv_ex_test {a b : ℕ} (hab : a ≠ b) (ha : a ≠ 14) (hb : b ≠ 14) {cn ct : Cmd}
    {σ : ℕ → Str} {X Y : Str} {r : Res} {T : ℕ} (hX : σ a = X) (hY : σ b = Y)
    (h14 : σ 14 = [])
    (h : ExecLe (if kv_leF true X Y then ct else cn) (update (update σ a []) b []) r T) :
    ExecLe (tpv_test a b cn ct) σ r (5 * (X.length + Y.length) + T + 5) := by
  have hp := ExecLe.push 14 true σ
  have hc := jsv_ex_cmp hab ha hb X Y true (update σ 14 (true :: σ 14))
    (by rw [update_of_ne ha]; exact hX) (by rw [update_of_ne hb]; exact hY)
    (by simp [h14, CookLevin.fl])
  refine (hp.seq_norm (hc.seq_norm (T₂ := T + 1) ?_)).cast rfl (by omega)
  have e : update (update (update (update σ 14 (true :: σ 14)) a []) b []) 14 [] =
      update (update σ a []) b [] := by
    funext j; simp only [update_apply]; split_ifs <;> simp_all
  cases hk : kv_leF true X Y
  · rw [hk] at h
    have e' : CookLevin.fl false = [] := rfl
    rw [e']
    refine ExecLe.pop_nil (by simp) ?_
    rw [e]; exact h
  · rw [hk] at h
    have e' : CookLevin.fl true = [true] := rfl
    rw [e']
    refine ExecLe.pop_cons (b := true) (s := []) (by simp) ?_
    rw [if_pos rfl, update_idem, e]; exact h

/-! ## The bound check of one item -/

def tpv_chk : Cmd :=
  .seq (copyVia 4 13 15) (.seq (copyVia 5 16 15) (.seq (.push 16 false) (.seq (.push 16 false)
    (tpv_test 16 13 (.seq (copyVia 4 13 15) (.seq (.push 5 false)
      (tpv_test 13 5 (.push 10 true) (.halt false)))) (.halt false)))))

theorem tpv_ex_chk (R Q C A K B : Str) :
    ExecLe tpv_chk (bpv_st R Q C A K B)
      (if tpv_okA C A then .norm (bpv_st R Q C [] (true :: K) B) else .halt false)
      (20 * (A.length + C.length) + 45) := by
  set σ0 := bpv_st R Q C A K B
  have e1 := ExecLe.of (exec_copyVia (a := 4) (b := 13) (t := 15) (by decide) (by decide)
    (by decide) σ0 rfl)
  set σ1 := update σ0 13 (σ0 4 ++ σ0 13)
  have e2 := ExecLe.of (exec_copyVia (a := 5) (b := 16) (t := 15) (by decide) (by decide)
    (by decide) σ1 (by simp [σ1, σ0, bpv_st]))
  set σ2 := update σ1 16 (σ1 5 ++ σ1 16)
  have p1 := ExecLe.push 16 false σ2
  set σ3 := update σ2 16 (false :: σ2 16)
  have p2 := ExecLe.push 16 false σ3
  set σ4 := update σ3 16 (false :: σ3 16)
  have l4 : (σ0 4).length = C.length := by simp [σ0, bpv_st]
  have l5 : (σ1 5).length = A.length := by simp [σ1, σ0, bpv_st]
  rw [l4] at e1; rw [l5] at e2
  set σ5 := update (update σ4 16 []) 13 []
  have e3 := ExecLe.of (exec_copyVia (a := 4) (b := 13) (t := 15) (by decide) (by decide)
    (by decide) σ5 (by simp [σ5, σ4, σ3, σ2, σ1, σ0, bpv_st]))
  have l4' : (σ5 4).length = C.length := by simp [σ5, σ4, σ3, σ2, σ1, σ0, bpv_st]
  rw [l4'] at e3
  set σ6 := update σ5 13 (σ5 4 ++ σ5 13)
  have p3 := ExecLe.push 5 false σ6
  set σ7 := update σ6 5 (false :: σ6 5)
  have hp10 := ExecLe.push 10 true (update (update σ7 13 []) 5 [])
  have hfin : update (update (update σ7 13 []) 5 []) 10
      (true :: update (update σ7 13 []) 5 [] 10) = bpv_st R Q C [] (true :: K) B := by
    simp only [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0]; tpv_stx
  rw [hfin] at hp10
  have t2 := tpv_ex_test (a := 13) (b := 5) (cn := .push 10 true) (ct := .halt false)
    (X := C) (Y := false :: A) (by decide) (by decide) (by decide) (σ := σ7)
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, bpv_st])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, bpv_st])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, σ0, bpv_st])
    (r := if kv_leF true C (false :: A) then .halt false else .norm (bpv_st R Q C [] (true :: K) B))
    (T := 1) (by
      cases kv_leF true C (false :: A)
      · exact hp10
      · exact ExecLe.halt false _)
  have t1 := tpv_ex_test (a := 16) (b := 13) (ct := .halt false)
    (cn := .seq (copyVia 4 13 15) (.seq (.push 5 false)
      (tpv_test 13 5 (.push 10 true) (.halt false))))
    (X := false :: false :: A) (Y := C) (by decide) (by decide) (by decide) (σ := σ4)
    (by simp [σ4, σ3, σ2, σ1, σ0, bpv_st])
    (by simp [σ4, σ3, σ2, σ1, σ0, bpv_st])
    (by simp [σ4, σ3, σ2, σ1, σ0, bpv_st])
    (r := if tpv_okA C A then .norm (bpv_st R Q C [] (true :: K) B) else .halt false)
    (T := 5 * C.length + 4 + (1 + (5 * (C.length + (false :: A).length) + 1 + 5))) (by
      cases h1 : kv_leF true (false :: false :: A) C
      · simp only [Bool.false_eq_true, if_false]
        refine (e3.seq_norm (p3.seq_norm t2)).cast ?_ le_rfl
        cases h2 : kv_leF true C (false :: A) <;> simp [tpv_okA, h1, h2]
      · simp only [if_true]
        refine (ExecLe.halt false _).cast (by simp [tpv_okA, h1]) (by omega))
  refine (e1.seq_norm (e2.seq_norm (p1.seq_norm (p2.seq_norm t1)))).cast rfl ?_
  simp only [List.length_cons]
  omega

/-! ## The bounds loop -/

def tpv_bB : Cmd := bpv_peek (.seq sv_addLoop tpv_chk)

def tpv_bL : Cmd := .loop tpv_bB

/-- Cost of the bounds loop. -/
def tpv_Tb (N : ℕ) (rows : List (List SatSym)) : ℕ := (rows.length + 1) * (60 * N + 100)

theorem tpv_ex_bL {R C : Str} (N : ℕ) (hC : C.length ≤ N) : ∀ (rows : List (List SatSym))
    (K B : Str), (∀ r ∈ rows, sep ∉ r) → (rows.map List.length).sum + rows.length ≤ N →
    ExecLe tpv_bL (bpv_st R (enc rows) C [] K B)
      (if tpv_bnd C rows then .norm (bpv_st R [] C [] (List.replicate rows.length true ++ K) B)
        else .halt false) (tpv_Tb N rows)
  | [], K, B, _, _ =>
    (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [tpv_bnd, enc]) (by simp [tpv_Tb])
  | r :: rows, K, B, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hN
    obtain ⟨x, Q', hQ⟩ := kv_enc_ne r rows
    have hT : tpv_Tb N (r :: rows) = (60 * N + 100) + tpv_Tb N rows := by
      simp [tpv_Tb]; ring
    rw [hT]
    set A' := sv_addL false [] (sv_bits r)
    have hl := sv_addL_length false [] (sv_bits r)
    simp only [sv_bits, List.length_map, List.length_nil] at hl
    rw [enc_cons] at hQ ⊢
    have ha := bpv_ex_add (R := R) (C := C) (K := K) N (enc rows) r [] B hr (by simp; omega)
    have hc := tpv_ex_chk R (enc rows) C A' K B
    have hb := bpv_ex_peek hQ (ha.seq_norm hc)
    have hl' : A'.length ≤ r.length + 1 := by simpa [A', sv_bits] using hl
    cases hok : tpv_ok C r
    · simp only [tpv_ok] at hok
      rw [hok] at hb
      exact (ExecLe.loop_halt hb).cast (by simp [tpv_bnd, tpv_ok, hok])
        (by omega)
    · simp only [tpv_ok] at hok
      rw [hok] at hb
      have ih := tpv_ex_bL (R := R) N hC rows (true :: K) B hrs (by omega)
      refine (ExecLe.loop_norm (hb.cast rfl le_rfl) ih).cast ?_ ?_
      · simp [tpv_bnd, tpv_ok, hok, List.replicate_succ']
      · omega

/-! ## The end of a pass -/

def tpv_fin : Cmd :=
  .seq (copyVia 4 13 15) (.seq (copyVia 5 16 15)
    (tpv_test 5 13 (.halt false) (.seq (copyVia 4 13 15) (tpv_test 13 16 (.halt false)
      (move 12 3)))))

theorem tpv_ex_fin (R C A K B : Str) :
    ExecLe tpv_fin (bpv_st R [] C A K B)
      (if kv_leF true A C && kv_leF true C A then .norm (bpv_st R B.reverse C [] K [])
        else .halt false)
      (20 * (A.length + C.length) + 2 * B.length + 30) := by
  set σ0 := bpv_st R [] C A K B
  have e1 := ExecLe.of (exec_copyVia (a := 4) (b := 13) (t := 15) (by decide) (by decide)
    (by decide) σ0 rfl)
  set σ1 := update σ0 13 (σ0 4 ++ σ0 13)
  have e2 := ExecLe.of (exec_copyVia (a := 5) (b := 16) (t := 15) (by decide) (by decide)
    (by decide) σ1 (by simp [σ1, σ0, bpv_st]))
  set σ2 := update σ1 16 (σ1 5 ++ σ1 16)
  have l4 : (σ0 4).length = C.length := by simp [σ0, bpv_st]
  have l5 : (σ1 5).length = A.length := by simp [σ1, σ0, bpv_st]
  rw [l4] at e1; rw [l5] at e2
  set σ3 := update (update σ2 5 []) 13 []
  have e3 := ExecLe.of (exec_copyVia (a := 4) (b := 13) (t := 15) (by decide) (by decide)
    (by decide) σ3 (by simp [σ3, σ2, σ1, σ0, bpv_st]))
  have l4' : (σ3 4).length = C.length := by simp [σ3, σ2, σ1, σ0, bpv_st]
  rw [l4'] at e3
  set σ4 := update σ3 13 (σ3 4 ++ σ3 13)
  set σ5 := update (update σ4 13 []) 16 []
  have hm := ExecLe.of (exec_move (a := 12) (b := 3) (by decide) B σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, σ0, bpv_st]))
  have hfin : update (update σ5 12 []) 3 (B.reverse ++ σ5 3) = bpv_st R B.reverse C [] K [] := by
    simp only [σ5, σ4, σ3, σ2, σ1, σ0]; tpv_stx
  rw [hfin] at hm
  have t2 := tpv_ex_test (a := 13) (b := 16) (cn := .halt false) (ct := move 12 3)
    (X := C) (Y := A) (by decide) (by decide) (by decide) (σ := σ4)
    (by simp [σ4, σ3, σ2, σ1, σ0, bpv_st])
    (by simp [σ4, σ3, σ2, σ1, σ0, bpv_st])
    (by simp [σ4, σ3, σ2, σ1, σ0, bpv_st])
    (r := if kv_leF true C A then .norm (bpv_st R B.reverse C [] K []) else .halt false)
    (T := 2 * B.length + 2) (by
      cases kv_leF true C A
      · exact (ExecLe.halt false _).cast rfl (by omega)
      · exact hm)
  have t1 := tpv_ex_test (a := 5) (b := 13) (cn := .halt false)
    (ct := .seq (copyVia 4 13 15) (tpv_test 13 16 (.halt false) (move 12 3)))
    (X := A) (Y := C) (by decide) (by decide) (by decide) (σ := σ2)
    (by simp [σ2, σ1, σ0, bpv_st])
    (by simp [σ2, σ1, σ0, bpv_st])
    (by simp [σ2, σ1, σ0, bpv_st])
    (r := if kv_leF true A C && kv_leF true C A then .norm (bpv_st R B.reverse C [] K [])
      else .halt false)
    (T := 5 * C.length + 4 + (5 * (C.length + A.length) + (2 * B.length + 2) + 5)) (by
      cases h1 : kv_leF true A C
      · simp only [Bool.false_eq_true, if_false]
        exact (ExecLe.halt false _).cast (by simp) (by omega)
      · simp only [if_true, Bool.true_and]
        exact e3.seq_norm t2)
  refine (e1.seq_norm (e2.seq_norm t1)).cast rfl ?_
  omega

/-! ## The main loop -/

def tpv_pass : Cmd := .seq bpv_iL tpv_fin

def tpv_oB : Cmd :=
  .pop 10 (.pop 3 (.halt true) (.halt false) (.halt false)) (.halt false)
    (.pop 10 (.halt false) (.halt false) (.pop 10 (.halt false) (.halt false) tpv_pass))

def tpv_oL : Cmd := .loop tpv_oB

/-- Cost of the main loop. -/
def tpv_To (N k : ℕ) : ℕ := (k + 1) * ((N + 1) * (16 * N + 30) + 50 * N + 50)

theorem tpv_ex_oL {C : Str} (N : ℕ) (hC : C.length ≤ N) : ∀ (k : ℕ)
    (rows : List (List SatSym)) (R : Str), (∀ r ∈ rows, sep ∉ r) →
    (rows.map List.length).sum + rows.length ≤ N →
    ExecLe tpv_oL (bpv_st R (enc rows) C [] (List.replicate k true) [])
      (.halt (tpv_go C k rows R)) (tpv_To N k)
  | 0, rows, R, _, _ => by
    have h : ExecLe (Cmd.pop 3 (.halt true) (.halt false) (.halt false))
        (bpv_st R (enc rows) C [] (List.replicate 0 true) []) (.halt (tpv_go C 0 rows R)) 2 := by
      rcases rows with _ | ⟨r, rows⟩
      · exact (ExecLe.pop_nil rfl (ExecLe.halt true _)).cast (by simp [tpv_go]) (by omega)
      · obtain ⟨x, Q', hQ⟩ := kv_enc_ne r rows
        refine (ExecLe.pop_cons (r := .halt false) (T := 1) (b := x) (s := Q') hQ ?_).cast
          (by simp [tpv_go]) (by omega)
        cases x <;> exact ExecLe.halt false _
    exact (ExecLe.loop_halt (ExecLe.pop_nil rfl h)).cast rfl (by unfold tpv_To; nlinarith)
  | 1, rows, R, _, _ => by
    refine (ExecLe.loop_halt (ExecLe.pop_cons (r := .halt false) (b := true) (s := []) rfl ?_)).cast
      (by simp [tpv_go]) (show 3 ≤ tpv_To N 1 by unfold tpv_To; nlinarith)
    rw [bpv_u10, if_pos rfl]
    exact (ExecLe.pop_nil rfl (ExecLe.halt false _))
  | 2, rows, R, _, _ => by
    refine (ExecLe.loop_halt (ExecLe.pop_cons (r := .halt false) (b := true) (s := [true]) rfl ?_)).cast
      (by simp [tpv_go]) (show 4 ≤ tpv_To N 2 by unfold tpv_To; nlinarith)
    rw [bpv_u10, if_pos rfl]
    refine ExecLe.pop_cons (b := true) (s := []) rfl ?_
    rw [bpv_u10, if_pos rfl]
    exact (ExecLe.pop_nil rfl (ExecLe.halt false _))
  | k + 3, rows, R, hrows, hN => by
    have hT : tpv_To N (k + 3) =
        ((N + 1) * (16 * N + 30) + 50 * N + 50) + (2 * ((N + 1) * (16 * N + 30) + 50 * N + 50)
          + tpv_To N k) := by
      simp [tpv_To]; ring
    rw [hT]
    have hA := bpv_A_length rows R []
    have hU := bpv_U_size rows R
    have hTi : bpv_Ti N rows ≤ (N + 1) * (16 * N + 30) :=
      Nat.mul_le_mul_right _ (by omega)
    have hI := bpv_ex_iL (C := C) (K := List.replicate k true) N rows R [] [] hrows
      (by simp; omega)
    have hF := tpv_ex_fin (bpv_rest rows R) C (bpv_A rows R []) (List.replicate k true)
      ((enc (bpv_U rows R)).reverse ++ [])
    have hEU := bpv_enc_length (bpv_U rows R)
    have hP : ExecLe tpv_oB (bpv_st R (enc rows) C [] (List.replicate (k + 3) true) [])
        (if kv_leF true (bpv_A rows R []) C && kv_leF true C (bpv_A rows R []) then
          .norm (bpv_st (bpv_rest rows R) (enc (bpv_U rows R)) C [] (List.replicate k true) [])
          else .halt false)
        ((N + 1) * (16 * N + 30) + 50 * N + 50) := by
      refine ExecLe.pop_cons (b := true) (s := List.replicate (k + 2) true) rfl ?_
      rw [bpv_u10, if_pos rfl]
      refine ExecLe.pop_cons (b := true) (s := List.replicate (k + 1) true) rfl ?_
      rw [bpv_u10, if_pos rfl]
      refine ExecLe.pop_cons (b := true) (s := List.replicate k true) rfl ?_
      rw [bpv_u10, if_pos rfl]
      refine ((hI.seq_norm hF).cast (by simp) ?_)
      simp only [List.append_nil, List.length_reverse, List.length_nil] at *
      omega
    cases hr : (kv_leF true (bpv_A rows R []) C && kv_leF true C (bpv_A rows R []))
    · rw [hr] at hP
      exact (ExecLe.loop_halt hP).cast (by simp [tpv_go, hr]) (by omega)
    · rw [hr] at hP
      have ih := tpv_ex_oL N hC k (bpv_U rows R) (bpv_rest rows R) (bpv_U_sep rows R hrows)
        (by omega)
      exact (ExecLe.loop_norm hP ih).cast (by simp [tpv_go, hr]) (by omega)

/-! ## The whole verifier -/

def tpv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq bpv_c0 (.seq (move 2 3) (.seq (copyVia 3 12 15)
    (.seq tpv_bL (.seq (move 12 13) (.seq (move 13 3) tpv_oL)))))))

/-- Time bound of the verifier. -/
def tpv_Tver (n : ℕ) : ℕ := 40 * n + 40 + (n + 1) * (60 * n + 100) + tpv_To n n

theorem tpv_exec_ver (z : Str) :
    ExecLe tpv_ver (init [z]).stk (.halt (tpv_vres (dec z).1 (dec z).2)) (tpv_Tver z.length) := by
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
  have hTo : tpv_To z.length 0 ≤ tpv_To z.length z.length :=
    Nat.mul_le_mul_right _ (by omega)
  unfold tpv_vres tpv_ver
  rcases hcw : (clauses w).reverse with _ | ⟨Bv, rr⟩
  · have h2 : σ₂ 2 = [] := by
      simp only [σ₂, update_self, trunc]
      rw [List.reverse_eq_nil_iff.1 hcw]; rfl
    refine (hpre _ _ _ (ExecLe.seq_halt (ExecLe.pop_nil h2 (ExecLe.halt false _)))).cast rfl ?_
    unfold tpv_Tver; omega
  · have hcl : clauses w = rr.reverse ++ [Bv] := by
      rw [← List.reverse_reverse (clauses w), hcw]; simp
    set u := rr.reverse.flatMap (· ++ [sep])
    have htr : trunc w = u ++ (Bv ++ [sep]) := by simp [trunc, hcl, u]
    have hsepC : sep ∉ Bv := sep_not_mem_clauses w Bv (by simp [hcl])
    have hu : u = [] ∨ ∃ u', u = u' ++ [sep] := by
      rcases rr.reverse.eq_nil_or_concat with h | ⟨L, c, h⟩
      · left; simp only [u, h]; rfl
      · right; exact ⟨L.flatMap (· ++ [sep]) ++ c, by simp only [u, h]; simp⟩
    have h2 : σ₂ 2 = false :: false :: (rc Bv.reverse ++ (u.flatMap ic).reverse) := by
      simp only [σ₂, update_self, htr, rc_eq]
      simp [List.flatMap_append, ic]
    set σ₄ := update σ₂ 2 (rc Bv.reverse ++ (u.flatMap ic).reverse)
    have hC := bpv_ex_cL u hu Bv.reverse σ₄ [] (by simpa using hsepC) (by simp [σ₄])
      (by simp [σ₄, σ₂, σ₁, he 4 (by decide)])
    have hC0 : ExecLe bpv_c0 σ₂ (.norm (update (update σ₄ 2 ((u.flatMap ic).reverse)) 4
        ((sv_bits Bv.reverse).reverse ++ []))) (4 * Bv.reverse.length + 6 + 1 + 1) :=
      ExecLe.pop_cons (b := false) h2 (ExecLe.pop_cons (b := false)
        (s := rc Bv.reverse ++ (u.flatMap ic).reverse) (by simp)
        (by simpa [σ₄, update_idem] using hC))
    set σ₅ := update (update σ₄ 2 ((u.flatMap ic).reverse)) 4
        ((sv_bits Bv.reverse).reverse ++ [])
    have hM := exec_move (a := 2) (b := 3) (by decide) _ σ₅ rfl
    set items := rr.reverse
    set C := sv_bits Bv
    have hσ : update (update σ₅ 2 []) 3 ((σ₅ 2).reverse ++ σ₅ 3) =
        bpv_st y (enc items) C [] [] [] := by
      have e : (sv_bits Bv.reverse).reverse = sv_bits Bv := by simp [sv_bits]
      funext j
      rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|j <;>
        simp [σ₅, σ₄, σ₂, σ₁, bpv_st, he, u, enc, e, items, C]
    rw [hσ] at hM
    have hCp := ExecLe.of (exec_copyVia (a := 3) (b := 12) (t := 15) (by decide) (by decide)
      (by decide) (bpv_st y (enc items) C [] [] []) rfl)
    have hσ2 : update (bpv_st y (enc items) C [] [] []) 12
        (bpv_st y (enc items) C [] [] [] 3 ++ bpv_st y (enc items) C [] [] [] 12) =
        bpv_st y (enc items) C [] [] (enc items) := by tpv_stx
    rw [hσ2] at hCp
    have hsum := sum_length_le items
    have l3 : (bpv_st y (enc items) C [] [] [] 3).length = (enc items).length := rfl
    have hug : (items.flatMap (· ++ [sep])).length = u.length := rfl
    have hul : u.length + Bv.length + 1 = (trunc w).length := by simp [htr]; omega
    have hCl : C.length ≤ z.length := by simp [C, sv_bits]; omega
    have hsep : ∀ r ∈ items, sep ∉ r := fun r hr =>
      sep_not_mem_clauses w r (by rw [hcl]; exact List.mem_append_left _ hr)
    have hB := tpv_ex_bL (R := y) z.length hCl items [] (enc items) hsep (by omega)
    have hc : (u.flatMap ic).length = 2 * u.length := length_flatMap_ic u
    have h52 : σ₅ 2 = (u.flatMap ic).reverse := by simp [σ₅]
    have hEl : (enc items).length = 2 * u.length := by
      rw [bpv_enc_length]; omega
    have hTb : tpv_Tb z.length items ≤ (z.length + 1) * (60 * z.length + 100) :=
      Nat.mul_le_mul_right _ (by omega)
    cases hb : tpv_bnd C items
    · rw [hb] at hB
      refine (hpre _ _ _ (hC0.seq_norm ((ExecLe.of hM).seq_norm (hCp.seq_norm
        (ExecLe.seq_halt hB))))).cast
        (by have hb' : tpv_bnd (sv_bits Bv) rr.reverse = false := hb; simp [hb']) ?_
      simp only [h52, List.length_reverse, hc, tpv_Tver, List.length_reverse] at *
      omega
    · rw [hb] at hB
      simp only [if_true] at hB
      have hM1 := exec_move (a := 12) (b := 13) (by decide) (enc items)
        (bpv_st y [] C [] (List.replicate items.length true ++ []) (enc items)) rfl
      have hM2 := exec_move (a := 13) (b := 3) (by decide) (enc items).reverse (update (update (bpv_st y [] C [] (List.replicate items.length true ++ [])
          (enc items)) 12 []) 13 ((enc items).reverse ++
            bpv_st y [] C [] (List.replicate items.length true ++ []) (enc items) 13)) (by simp [bpv_st])
      have hσ3 : update (update (update (update (bpv_st y [] C [] (List.replicate items.length
          true ++ []) (enc items)) 12 []) 13 ((enc items).reverse ++
            bpv_st y [] C [] (List.replicate items.length true ++ []) (enc items) 13)) 13 [])
          3 ((enc items).reverse.reverse ++ (update (update (bpv_st y [] C []
            (List.replicate items.length true ++ []) (enc items)) 12 []) 13
              ((enc items).reverse ++ bpv_st y [] C [] (List.replicate items.length true ++ [])
                (enc items) 13)) 3) =
          bpv_st y (enc items) C [] (List.replicate items.length true) [] := by tpv_stx
      rw [hσ3] at hM2
      have hR := tpv_ex_oL (C := C) z.length hCl items.length items y hsep (by omega)
      refine (hpre _ _ _ (hC0.seq_norm ((ExecLe.of hM).seq_norm (hCp.seq_norm
        (hB.seq_norm ((ExecLe.of hM1).seq_norm ((ExecLe.of hM2).seq_norm hR))))))).cast
        (by have hb' : tpv_bnd (sv_bits Bv) rr.reverse = true := hb; simp [hb', items, C]) ?_
      have hk : tpv_To z.length items.length ≤ tpv_To z.length z.length :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [h52, List.length_reverse, hc, tpv_Tver, List.length_reverse, hEl] at *
      omega

theorem tpv_Tver_le (n : ℕ) : tpv_Tver n ≤ tb 8 n := by
  unfold tpv_Tver tpv_To tb
  have h5 : 2 ^ 5 ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have e : (n + 2) ^ 8 = (n + 2) ^ 3 * (n + 2) ^ 5 := by ring
  have e3 : (n + 2) ^ 3 = (n + 2) * (n + 2) * (n + 2) := by ring
  have h1 : 40 * n + 40 + (n + 1) * (60 * n + 100) + (n + 1) * ((n + 1) * (16 * n + 30) +
      50 * n + 50) ≤ (n + 2) ^ 3 * 32 := by
    rw [e3]; nlinarith [Nat.zero_le (n * n * n), Nat.zero_le (n * n)]
  rw [e]
  exact h1.trans (Nat.mul_le_mul_left _ (by simpa using h5))

end Pnp.Karp.ThreePart
