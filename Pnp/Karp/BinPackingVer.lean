import Pnp.Karp.BinPacking
import Pnp.Karp.KnapVer
import Pnp.Karp.JobSeqVer
import Pnp.Karp.M2Ver

/-!
# BIN PACKING ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(rows `items ++ [C, kr]`, `Pnp/Karp/BinPacking.lean`) and a certificate `y : List Bool`.

## Certificate

The certificate is read in `|kr|` passes, one per bin.  In each pass the verifier runs over
the items that are still *unpacked*, popping one certificate bit per item: a set bit puts the
item into the current bin (its size is added to the accumulator, and the item is removed), an
unset (or missing) bit keeps it for the later passes.  At the end of a pass the accumulator
must be `≤ C`.  After the last pass every item must be packed.

## Program (`bpv_ver`)

Stacks of the main phase (`bpv_st`): `0` the unread certificate `R`; `3` the code `Q` of the
unpacked items; `4` the capacity `C` (bits, least significant on top); `5` the accumulator `A`;
`6`, `7` the adder's temporaries; `10` the unary count `K` of the remaining passes; `12` the
reversed code `B` of the items kept in the current pass; `13`, `14`, `15` a copy of `C`, the
comparison flag, a temporary.

1. `phaseA`, `trimC 2`: the reversed internal code of `trunc w` is on stack `2`;
   `m2v_kr0` (`Pnp/Karp/M2Ver.lean`): read the last row `kr` as marks on stack `10`;
   `bpv_c0`: read the row `C` (reversed) onto stack `4` (halt `false` if a row is missing);
   `move 2 3`: the code of the items is on stack `3`;
2. `bpv_oL`: per mark of stack `10`, a pass `bpv_iL` (per item: `sv_addLoop`, or the copy loop
   `bpv_cpL` to stack `12`), then `bpv_fin` (`A ≤ C` by `kv_cmpLoop` on a copy of `C`, halt
   `false` if not; `move 12 3`).  Without marks, accept iff stack `3` is empty.
-/

namespace Pnp.Karp.BinPacking

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.JobSeq Pnp.Karp.NAE

/-! ## Semantics -/

/-- The accumulator after a pass over `rows` with the certificate `R`. -/
def bpv_A : List (List SatSym) → Str → Str → Str
  | [], _, A => A
  | r :: rs, R, A => bpv_A rs R.tail (if R.headD false then sv_addL false A (sv_bits r) else A)

/-- The items kept by a pass. -/
def bpv_U : List (List SatSym) → Str → List (List SatSym)
  | [], _ => []
  | r :: rs, R => if R.headD false then bpv_U rs R.tail else r :: bpv_U rs R.tail

/-- The certificate left after a pass. -/
def bpv_rest : List (List SatSym) → Str → Str
  | [], R => R
  | _ :: rs, R => bpv_rest rs R.tail

/-- What the main loop computes (`C`: capacity, `k` passes, `rows`: unpacked items). -/
def bpv_go (C : Str) : ℕ → List (List SatSym) → Str → Bool
  | 0, rows, _ => rows.isEmpty
  | k + 1, rows, R =>
    kv_leF true (bpv_A rows R []) C && bpv_go C k (bpv_U rows R) (bpv_rest rows R)

/-- The answer of the verifier on `(w, y)`. -/
def bpv_vres (w : List SatSym) (y : Str) : Bool :=
  match (clauses w).reverse with
  | kr :: C :: rr => bpv_go (sv_bits C) kr.length rr.reverse y
  | _ => false

theorem bpv_A_length : ∀ (rows : List (List SatSym)) (R A : Str),
    (bpv_A rows R A).length ≤ A.length + (rows.map List.length).sum + rows.length
  | [], R, A => by simp [bpv_A]
  | r :: rs, R, A => by
    have ih := bpv_A_length rs R.tail
      (if R.headD false then sv_addL false A (sv_bits r) else A)
    have hl := sv_addL_length false A (sv_bits r)
    have hb : (sv_bits r).length = r.length := by simp [sv_bits]
    simp only [bpv_A, List.map_cons, List.sum_cons, List.length_cons]
    split_ifs with h <;> simp only [h, if_true, if_false, Bool.false_eq_true] at ih <;> omega

theorem bpv_U_size : ∀ (rows : List (List SatSym)) (R : Str),
    ((bpv_U rows R).map List.length).sum + (bpv_U rows R).length ≤
      (rows.map List.length).sum + rows.length
  | [], R => by simp [bpv_U]
  | r :: rs, R => by
    have ih := bpv_U_size rs R.tail
    simp only [bpv_U]
    split_ifs <;> simp <;> omega

theorem bpv_U_sep : ∀ (rows : List (List SatSym)) (R : Str), (∀ r ∈ rows, sep ∉ r) →
    ∀ r ∈ bpv_U rows R, sep ∉ r
  | [], R, _ => by simp [bpv_U]
  | r :: rs, R, h => by
    have ih := bpv_U_sep rs R.tail (fun r' hr' => h r' (by simp [hr']))
    simp only [bpv_U]
    split_ifs
    · exact ih
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact h r' (by simp)
      · exact ih r' hr'

/-! ## Stack layout -/

/-- The stacks of the main phase. -/
def bpv_st (R Q C A K B : Str) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 4 then C else if j = 5 then A else
  if j = 10 then K else if j = 12 then B else []

local macro "bpv_stx" : tactic =>
  `(tactic| (funext j; simp only [bpv_st, update_apply]; split_ifs <;> simp_all))

section St
variable {R Q C A K B : Str}
theorem bpv_u0 (R' : Str) : update (bpv_st R Q C A K B) 0 R' = bpv_st R' Q C A K B := by bpv_stx
theorem bpv_u3 (Q' : Str) : update (bpv_st R Q C A K B) 3 Q' = bpv_st R Q' C A K B := by bpv_stx
theorem bpv_u10 (K' : Str) : update (bpv_st R Q C A K B) 10 K' = bpv_st R Q C A K' B := by
  bpv_stx
theorem bpv_u12 (B' : Str) : update (bpv_st R Q C A K B) 12 B' = bpv_st R Q C A K B' := by
  bpv_stx
end St

theorem bpv_mix (R Q C A R₂ Q₂ C₂ A₂ K B : Str) :
    kv_mix kv_F (sv_st R Q C A [] false) (bpv_st R₂ Q₂ C₂ A₂ K B) = bpv_st R Q C A K B := by
  funext j; simp only [kv_mix, kv_F, sv_st, bpv_st, CookLevin.fl, decide_eq_true_eq]
  split_ifs <;> first | rfl | omega

/-! ## A pass -/

section Pass
variable {R C K : Str}

theorem bpv_ex_add (N : ℕ) (Q' : Str) (r : List SatSym) (A B : Str) (hr : sep ∉ r)
    (hN : A.length + r.length ≤ N) :
    ExecLe sv_addLoop (bpv_st R (r.flatMap ic ++ false :: false :: Q') C A K B)
      (.norm (bpv_st R Q' C (sv_addL false A (sv_bits r)) K B)) (7 * r.length + 8 * N + 20) := by
  have h := kv_mix_le (bpv_st R (r.flatMap ic ++ false :: false :: Q') C A K B)
    (sv_ex_addRow (R := R) (T := C) N Q' r A [] false hr (by simp; omega)) kv_av_add
  rw [bpv_mix] at h
  refine h.cast ?_ le_rfl
  simp only [kv_rmap, List.reverse_nil, List.nil_append]
  rw [bpv_mix]

/-- Copy one symbol code from stack `3` to stack `12` (stop after a `sep`). -/
def bpv_cpB : Cmd :=
  .pop 3 .brk
    (.pop 3 .brk (.seq (.push 12 false) (.seq (.push 12 false) .brk))
      (.seq (.push 12 false) (.push 12 true)))
    (.pop 3 .brk (.seq (.push 12 true) (.push 12 false)) (.seq (.push 12 true) (.push 12 true)))

def bpv_cpL : Cmd := .loop bpv_cpB

theorem bpv_ex_cpG : ∀ (r : List SatSym) (σ : ℕ → Str) (Q' B : Str), sep ∉ r →
    σ 3 = r.flatMap ic ++ false :: false :: Q' → σ 12 = B →
    ExecLe bpv_cpL σ
      (.norm (update (update σ 3 Q') 12 ((r.flatMap ic ++ [false, false]).reverse ++ B)))
      (4 * r.length + 6)
  | [], σ, Q', B, _, h3, h12 => by
    have h3' : σ 3 = false :: false :: Q' := by simpa using h3
    refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := false)
      (s := Q') (by simp) ((ExecLe.push 12 false _).seq_norm ((ExecLe.push 12 false _).seq_norm
        (ExecLe.brk _)))))).cast ?_ (by simp)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all
  | s :: r, σ, Q', B, hr, h3, h12 => by
    have hs' : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ht : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    set rest := r.flatMap ic ++ false :: false :: Q'
    have ih := bpv_ex_cpG r (update (update σ 3 rest) 12 ((ic s).reverse ++ B)) Q'
      ((ic s).reverse ++ B) ht (by simp [rest]) (by simp)
    have hb : ExecLe bpv_cpB σ (.norm (update (update σ 3 rest) 12 ((ic s).reverse ++ B))) 4 := by
      cases s with
      | sep => exact absurd rfl hs'
      | zero =>
        have h' : σ 3 = false :: true :: rest := by simpa [ic, rest] using h3
        refine (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := true) (s := rest)
          (by simp) ((ExecLe.push 12 false _).seq_norm (ExecLe.push 12 true _)))).cast ?_ le_rfl
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [ic]
      | pos =>
        have h' : σ 3 = true :: false :: rest := by simpa [ic, rest] using h3
        refine (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := false) (s := rest)
          (by simp) ((ExecLe.push 12 true _).seq_norm (ExecLe.push 12 false _)))).cast ?_ le_rfl
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [ic]
      | neg =>
        have h' : σ 3 = true :: true :: rest := by simpa [ic, rest] using h3
        refine (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := true) (s := rest)
          (by simp) ((ExecLe.push 12 true _).seq_norm (ExecLe.push 12 true _)))).cast ?_ le_rfl
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [ic]
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all

theorem bpv_ex_cp (Q' : Str) (r : List SatSym) (A B : Str) (hr : sep ∉ r) :
    ExecLe bpv_cpL (bpv_st R (r.flatMap ic ++ false :: false :: Q') C A K B)
      (.norm (bpv_st R Q' C A K ((r.flatMap ic ++ [false, false]).reverse ++ B)))
      (4 * r.length + 6) := by
  have h := bpv_ex_cpG r (bpv_st R (r.flatMap ic ++ false :: false :: Q') C A K B) Q' B hr rfl rfl
  rwa [bpv_u3, bpv_u12] at h

/-- Test whether stack `3` is empty (leave the loop then) and continue with `c` otherwise. -/
def bpv_peek (c : Cmd) : Cmd := .pop 3 .brk (.seq (.push 3 false) c) (.seq (.push 3 true) c)

theorem bpv_ex_peek {c : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ} {x : Bool} {Q' : Str}
    (h3 : σ 3 = x :: Q') (h : ExecLe c σ r T) : ExecLe (bpv_peek c) σ r (T + 2) := by
  have e : update (update σ 3 Q') 3 (x :: update σ 3 Q' 3) = σ := by
    rw [update_self, update_idem, ← h3, update_eq_self]
  have hp := ExecLe.push 3 x (update σ 3 Q')
  rw [e] at hp
  refine ExecLe.pop_cons (T := T + 1) h3 ?_
  cases x
  · exact (hp.seq_norm h).cast rfl (by omega)
  · exact (hp.seq_norm h).cast rfl (by omega)

def bpv_iB : Cmd := bpv_peek (.pop 0 bpv_cpL bpv_cpL sv_addLoop)

def bpv_iL : Cmd := .loop bpv_iB

/-- Cost of a pass. -/
def bpv_Ti (N : ℕ) (rows : List (List SatSym)) : ℕ := (rows.length + 1) * (16 * N + 30)

theorem bpv_ex_iL (N : ℕ) : ∀ (rows : List (List SatSym)) (R A B : Str),
    (∀ r ∈ rows, sep ∉ r) → A.length + (rows.map List.length).sum + rows.length ≤ N →
    ExecLe bpv_iL (bpv_st R (enc rows) C A K B)
      (.norm (bpv_st (bpv_rest rows R) [] C (bpv_A rows R A) K
        ((enc (bpv_U rows R)).reverse ++ B))) (bpv_Ti N rows)
  | [], R, A, B, _, _ =>
    (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast
      (by simp [bpv_rest, bpv_A, bpv_U, enc]) (by simp [bpv_Ti])
  | r :: rows, R, A, B, hrows, hN => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hN
    obtain ⟨x, Q', hQ⟩ := kv_enc_ne r rows
    have hT : bpv_Ti N (r :: rows) = (16 * N + 30) + bpv_Ti N rows := by
      simp [bpv_Ti]; ring
    rw [hT]
    have hl := sv_addL_length false A (sv_bits r)
    simp only [sv_bits, List.length_map] at hl
    rw [enc_cons] at hQ ⊢
    rcases R with _ | ⟨_ | _, R'⟩
    · have ih := bpv_ex_iL N rows [] A ((r.flatMap ic ++ [false, false]).reverse ++ B) hrs
        (by omega)
      have hb := ExecLe.pop_nil (k := 0) (cn := bpv_cpL) (cf := bpv_cpL) (ct := sv_addLoop) rfl
        (bpv_ex_cp (R := []) (C := C) (K := K) (enc rows) r A B hr)
      refine (ExecLe.loop_norm (bpv_ex_peek hQ hb) ih).cast ?_ (by omega)
      simp [bpv_rest, bpv_A, bpv_U, enc_cons]
    · have ih := bpv_ex_iL N rows R' A ((r.flatMap ic ++ [false, false]).reverse ++ B) hrs
        (by omega)
      have hb := ExecLe.pop_cons (k := 0) (cn := bpv_cpL) (cf := bpv_cpL) (ct := sv_addLoop)
        (b := false) (s := R')
        (σ := bpv_st (false :: R') (r.flatMap ic ++ false :: false :: enc rows) C A K B) rfl
        (by rw [bpv_u0]; exact bpv_ex_cp (enc rows) r A B hr)
      refine (ExecLe.loop_norm (bpv_ex_peek hQ hb) ih).cast ?_ (by omega)
      simp [bpv_rest, bpv_A, bpv_U, enc_cons]
    · have ih := bpv_ex_iL N rows R' (sv_addL false A (sv_bits r)) B hrs
        (by simp only [sv_bits] at *; omega)
      have hb := ExecLe.pop_cons (k := 0) (cn := bpv_cpL) (cf := bpv_cpL) (ct := sv_addLoop)
        (b := true) (s := R')
        (σ := bpv_st (true :: R') (r.flatMap ic ++ false :: false :: enc rows) C A K B) rfl
        (by rw [bpv_u0]; exact bpv_ex_add N (enc rows) r A B hr (by omega))
      refine (ExecLe.loop_norm (bpv_ex_peek hQ hb) ih).cast ?_ (by omega)
      simp [bpv_rest, bpv_A, bpv_U]

end Pass

/-! ## The end of a pass -/

def bpv_fin : Cmd := .seq (copyVia 4 13 15) (.seq (.push 14 true) (.seq (kv_cmpLoop 5 13 14)
  (.pop 14 (.halt false) (.halt false) (move 12 3))))

theorem bpv_ex_fin (R C A K B : Str) :
    ExecLe bpv_fin (bpv_st R [] C A K B)
      (if kv_leF true A C then .norm (bpv_st R B.reverse C [] K []) else .halt false)
      (5 * C.length + 5 * (A.length + C.length) + 2 * B.length + 14) := by
  set σ0 := bpv_st R [] C A K B
  set σ1 := update σ0 13 (σ0 4 ++ σ0 13)
  set σ2 := update σ1 14 (true :: σ1 14)
  have e1 := ExecLe.of (exec_copyVia (a := 4) (b := 13) (t := 15) (by decide) (by decide)
    (by decide) σ0 rfl)
  have hp := ExecLe.push 14 true σ1
  have e2 := jsv_ex_cmp (a := 5) (b := 13) (f := 14) (by decide) (by decide) (by decide) A C true
    σ2 (by simp [σ2, σ1, σ0, bpv_st]) (by simp [σ2, σ1, σ0, bpv_st])
    (by simp [σ2, σ1, σ0, bpv_st, CookLevin.fl])
  set σ3 := update (update (update σ2 5 []) 13 []) 14 (CookLevin.fl (kv_leF true A C))
  have e4 : (σ0 4).length = C.length := by simp [σ0, bpv_st]
  refine (e1.seq_norm (hp.seq_norm (e2.seq_norm (T₂ := 2 * B.length + 3) ?_))).cast rfl
    (by rw [e4]; omega)
  cases hr : kv_leF true A C
  · exact (ExecLe.pop_nil (by simp [σ3, hr, CookLevin.fl]) (ExecLe.halt false _)).cast (by simp)
      (by omega)
  · refine ExecLe.pop_cons (b := true) (s := []) (by simp [σ3, hr, CookLevin.fl]) ?_
    have hm := exec_move (a := 12) (b := 3) (by decide) B (update σ3 14 [])
      (by simp [σ3, σ2, σ1, σ0, bpv_st])
    refine (ExecLe.of hm).cast ?_ (by omega)
    simp only [if_true]
    congr 1; funext j; simp only [σ3, σ2, σ1, σ0, bpv_st, update_apply]; split_ifs <;> simp_all

/-! ## The main loop -/

def bpv_pass : Cmd := .seq bpv_iL bpv_fin

def bpv_oB : Cmd := .pop 10 (.pop 3 (.halt true) (.halt false) (.halt false)) bpv_pass bpv_pass

def bpv_oL : Cmd := .loop bpv_oB

/-- Cost of the main loop. -/
def bpv_To (N k : ℕ) : ℕ := (k + 1) * ((N + 1) * (16 * N + 30) + 30 * N + 30)

theorem bpv_enc_length (rows : List (List SatSym)) :
    (enc rows).length = 2 * ((rows.map List.length).sum + rows.length) := by
  rw [enc, length_flatMap_ic, sum_length_le]

theorem bpv_ex_oL {C : Str} (N : ℕ) (hC : C.length ≤ N) : ∀ (k : ℕ)
    (rows : List (List SatSym)) (R : Str), (∀ r ∈ rows, sep ∉ r) →
    (rows.map List.length).sum + rows.length ≤ N →
    ExecLe bpv_oL (bpv_st R (enc rows) C [] (List.replicate k true) [])
      (.halt (bpv_go C k rows R)) (bpv_To N k)
  | 0, rows, R, _, _ => by
    have h : ExecLe (Cmd.pop 3 (.halt true) (.halt false) (.halt false))
        (bpv_st R (enc rows) C [] (List.replicate 0 true) []) (.halt (bpv_go C 0 rows R)) 2 := by
      rcases rows with _ | ⟨r, rows⟩
      · exact (ExecLe.pop_nil rfl (ExecLe.halt true _)).cast (by simp [bpv_go]) (by omega)
      · obtain ⟨x, Q', hQ⟩ := kv_enc_ne r rows
        refine (ExecLe.pop_cons (r := .halt false) (T := 1) (b := x) (s := Q') hQ ?_).cast
          (by simp [bpv_go]) (by omega)
        cases x <;> exact ExecLe.halt false _
    exact (ExecLe.loop_halt (ExecLe.pop_nil rfl h)).cast rfl (by unfold bpv_To; nlinarith)
  | k + 1, rows, R, hrows, hN => by
    have hT : bpv_To N (k + 1) = ((N + 1) * (16 * N + 30) + 30 * N + 30) + bpv_To N k := by
      simp [bpv_To]; ring
    rw [hT]
    have hA := bpv_A_length rows R []
    have hU := bpv_U_size rows R
    have hTi : bpv_Ti N rows ≤ (N + 1) * (16 * N + 30) :=
      Nat.mul_le_mul_right _ (by omega)
    have hI := bpv_ex_iL (C := C) (K := List.replicate k true) N rows R [] [] hrows
      (by simp; omega)
    have hF := bpv_ex_fin (bpv_rest rows R) C (bpv_A rows R []) (List.replicate k true)
      ((enc (bpv_U rows R)).reverse ++ [])
    have hEU := bpv_enc_length (bpv_U rows R)
    have hP : ExecLe bpv_oB (bpv_st R (enc rows) C [] (List.replicate (k + 1) true) [])
        (if kv_leF true (bpv_A rows R []) C then
          .norm (bpv_st (bpv_rest rows R) (enc (bpv_U rows R)) C [] (List.replicate k true) [])
          else .halt false)
        ((N + 1) * (16 * N + 30) + 30 * N + 30) := by
      refine ExecLe.pop_cons (b := true) (s := List.replicate k true) rfl ?_
      rw [bpv_u10]
      refine ((hI.seq_norm hF).cast (by simp) ?_)
      simp only [List.append_nil, List.length_reverse, List.length_nil] at *
      omega
    cases hr : kv_leF true (bpv_A rows R []) C
    · rw [hr] at hP
      exact (ExecLe.loop_halt hP).cast (by simp [bpv_go, hr]) (by omega)
    · rw [hr] at hP
      have ih := bpv_ex_oL N hC k (bpv_U rows R) (bpv_rest rows R) (bpv_U_sep rows R hrows)
        (by omega)
      exact (ExecLe.loop_norm hP ih).cast (by simp [bpv_go, hr]) le_rfl

/-! ## Reading the capacity -/

/-- Loop body of `bpv_cL`: pop one (reversed) symbol code; at a `sep` push it back and stop,
otherwise push its bit onto stack `4`. -/
def bpv_cB : Cmd :=
  .pop 2 .brk (.pop 2 .brk (.seq (.push 2 false) (.seq (.push 2 false) .brk)) (.push 4 true))
    (.pop 2 .brk (.push 4 false) (.push 4 false))

def bpv_cL : Cmd := .loop bpv_cB

theorem bpv_ex_cL (u : List SatSym) (hu : u = [] ∨ ∃ u', u = u' ++ [sep]) :
    ∀ (t : List SatSym) (σ : ℕ → Str) (S : Str), sep ∉ t → σ 2 = rc t ++ (u.flatMap ic).reverse →
    σ 4 = S →
    ExecLe bpv_cL σ (.norm (update (update σ 2 ((u.flatMap ic).reverse)) 4
      ((sv_bits t).reverse ++ S))) (4 * t.length + 6)
  | [], σ, S, _, h, h4 => by
    rcases hu with rfl | ⟨u', rfl⟩
    · refine (ExecLe.loop_brk (ExecLe.pop_nil (by simpa [rc] using h) (ExecLe.brk _))).cast ?_
        (by simp)
      congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [rc, sv_bits]
    · have h' : σ 2 = false :: false :: (u'.flatMap ic).reverse := by
        simpa [rc, List.flatMap_append, ic] using h
      refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := false)
        (s := (u'.flatMap ic).reverse)
        (by simp) ((ExecLe.push 2 false _).seq_norm ((ExecLe.push 2 false _).seq_norm
          (ExecLe.brk _)))))).cast ?_ (by simp)
      congr 1; funext j; simp only [update_apply]
      split_ifs <;> simp_all [List.flatMap_append, ic, sv_bits]
  | s :: t, σ, S, hs, h, h4 => by
    have hs' : s ≠ sep := fun e => hs (e ▸ List.mem_cons_self ..)
    have ht : sep ∉ t := fun e => hs (List.mem_cons_of_mem _ e)
    set rest := rc t ++ (u.flatMap ic).reverse
    have ih := bpv_ex_cL u hu t (update (update σ 2 rest) 4 (isPos s :: S)) (isPos s :: S) ht
      (by simp [rest]) (by simp)
    have hb : ExecLe bpv_cB σ (.norm (update (update σ 2 rest) 4 (isPos s :: S))) 3 := by
      cases s with
      | sep => exact absurd rfl hs'
      | zero =>
        have h' : σ 2 = true :: false :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := false) (s := rest) (by simp)
          (ExecLe.push 4 false _))).cast (by simp [isPos, h4]) le_rfl
      | neg =>
        have h' : σ 2 = true :: true :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := true) (s := rest) (by simp)
          (ExecLe.push 4 false _))).cast (by simp [isPos, h4]) le_rfl
      | pos =>
        have h' : σ 2 = false :: true :: rest := by simpa [rc, ic, rest] using h
        exact (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := true) (s := rest) (by simp)
          (ExecLe.push 4 true _))).cast (by simp [isPos, h4]) le_rfl
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [sv_bits]

/-- Pop the `sep` of the capacity row (halt `false` if there is none), then read it. -/
def bpv_c0 : Cmd := .pop 2 (.halt false) (.pop 2 (.halt false) bpv_cL (.halt false)) (.halt false)

/-! ## The whole verifier -/

def bpv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq m2v_kr0 (.seq bpv_c0 (.seq (move 2 3) bpv_oL))))

/-- Time bound of the verifier. -/
def bpv_Tver (n : ℕ) : ℕ :=
  (3 * n + 4) + (4 * n + 6) + (4 * n + 8) + (4 * n + 8) + (4 * n + 2) + bpv_To n n

theorem bpv_exec_ver (z : Str) :
    ExecLe bpv_ver (init [z]).stk (.halt (bpv_vres (dec z).1 (dec z).2)) (bpv_Tver z.length) := by
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
  have hTo : bpv_To z.length 0 ≤ bpv_To z.length z.length :=
    Nat.mul_le_mul_right _ (by omega)
  unfold bpv_vres bpv_ver
  rcases hcw : (clauses w).reverse with _ | ⟨kr, rr⟩
  · have h2 : σ₂ 2 = [] := by
      simp only [σ₂, update_self, trunc]
      rw [List.reverse_eq_nil_iff.1 hcw]; rfl
    refine (hpre _ _ _ (ExecLe.seq_halt (ExecLe.pop_nil h2 (ExecLe.halt false _)))).cast rfl ?_
    unfold bpv_Tver; omega
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
    have hul : u.length + kr.length + 1 = (trunc w).length := by simp [htr]; omega
    rcases rr with _ | ⟨C, rr⟩
    · have h32 : σ₃ 2 = [] := by simp [σ₃, u]
      refine (hpre _ _ _ (hK0.seq_norm (ExecLe.seq_halt (ExecLe.pop_nil h32
        (ExecLe.halt false _))))).cast rfl ?_
      simp only [List.length_reverse] at *
      unfold bpv_Tver; omega
    · set u2 := rr.reverse.flatMap (· ++ [sep])
      have hu' : u = u2 ++ (C ++ [sep]) := by simp [u, u2]
      have hsepC : sep ∉ C := sep_not_mem_clauses w C (by simp [hcl])
      have hu2 : u2 = [] ∨ ∃ u', u2 = u' ++ [sep] := by
        rcases rr.reverse.eq_nil_or_concat with h | ⟨L, c, h⟩
        · left; simp only [u2, h]; rfl
        · right; exact ⟨L.flatMap (· ++ [sep]) ++ c, by simp only [u2, h]; simp⟩
      have h32 : σ₃ 2 = false :: false :: (rc C.reverse ++ (u2.flatMap ic).reverse) := by
        simp only [σ₃, update_self, update_of_ne (show (2 : ℕ) ≠ 10 by decide), hu', rc_eq]
        simp [List.flatMap_append, ic]
      set σ₄ := update σ₃ 2 (rc C.reverse ++ (u2.flatMap ic).reverse)
      have hC := bpv_ex_cL u2 hu2 C.reverse σ₄ [] (by simpa using hsepC) (by simp [σ₄])
        (by simp [σ₄, σ₃, σ', σ₂, σ₁, he 4 (by decide)])
      have hC0 : ExecLe bpv_c0 σ₃ (.norm (update (update σ₄ 2 ((u2.flatMap ic).reverse)) 4
          ((sv_bits C.reverse).reverse ++ []))) (4 * C.reverse.length + 6 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h32 (ExecLe.pop_cons (b := false)
          (s := rc C.reverse ++ (u2.flatMap ic).reverse) (by simp)
          (by simpa [σ₄, update_idem] using hC))
      set σ₅ := update (update σ₄ 2 ((u2.flatMap ic).reverse)) 4
          ((sv_bits C.reverse).reverse ++ [])
      have hM := exec_move (a := 2) (b := 3) (by decide) _ σ₅ rfl
      have hσ : update (update σ₅ 2 []) 3 ((σ₅ 2).reverse ++ σ₅ 3) =
          bpv_st y (enc rr.reverse) (sv_bits C) [] (List.replicate kr.length true) [] := by
        have e : (sv_bits C.reverse).reverse = sv_bits C := by simp [sv_bits]
        funext j
        rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|j <;>
          simp [σ₅, σ₄, σ₃, σ', σ₂, σ₁, bpv_st, he, u2, enc, e]
      rw [hσ] at hM
      have hsum := sum_length_le rr.reverse
      have hu2l : u2.length = (rr.reverse.map List.length).sum + rr.reverse.length := by
        rw [hsum]
      have hu'l : u.length = u2.length + C.length + 1 := by simp [hu']; omega
      have hR := bpv_ex_oL (C := sv_bits C) z.length (by simp [sv_bits]; omega) kr.length
        rr.reverse y (fun r hr => sep_not_mem_clauses w r (by rw [hcl]; exact List.mem_append_left _ (by simp [hr])))
        (by omega)
      refine (hpre _ _ _ (hK0.seq_norm (hC0.seq_norm ((ExecLe.of hM).seq_norm hR)))).cast
        (by simp) ?_
      have hc : (u2.flatMap ic).length = 2 * u2.length := length_flatMap_ic u2
      have h52 : σ₅ 2 = (u2.flatMap ic).reverse := by simp [σ₅]
      have hk : bpv_To z.length kr.length ≤ bpv_To z.length z.length :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [h52, List.length_reverse, hc, bpv_Tver]
      omega

theorem bpv_Tver_le (n : ℕ) : bpv_Tver n ≤ tb 8 n := by
  unfold bpv_Tver bpv_To tb
  have h2 : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h5 : 2 ^ 5 ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have e : (n + 2) ^ 8 = (n + 2) ^ 3 * (n + 2) ^ 5 := by ring
  have e3 : (n + 2) ^ 3 = (n + 2) * (n + 2) * (n + 2) := by ring
  rw [e, e3]
  norm_num at h2 h5
  nlinarith

end Pnp.Karp.BinPacking
