import Pnp.Karp.SubsetSum
import Pnp.Karp.HamProg

/-!
# The SUBSET SUM reduction program, part 1: digits, printing primitives, the rows

A stack program printing `SS w` (`Pnp/Karp/SubsetSum.lean`), on the layout `st2` of
`Pnp/Karp/CliqueGen.lean`, with the register file a plain function `v : ℕ → ℕ`.  Registers:
`5 ↦ N`, `6 ↦ k` (clause index), `8 ↦ d` (clauses after `k`), `9 ↦ m`, `13 ↦ j`, `14 ↦ j'`
(`= N - 1 - j`), `15`, `16` loop counters; `7` is the countdown of a run of `zero`s, `10` /
`12` the counters of the digit / block repetitions, `11` the copy temporary.

Rows are printed digit by digit: digit `b` is `sg_dg N b = (pos or zero) :: 0^N` (`N = b - 1`),
a list of digits `ds` is printed as `sg_pr N ds`, and `digRow (N + 1) D S = sg_pr N (S 0, …)`
(`sg_digRow`).

* `sg_Em c v out T`: `c` prints `out` within `T` steps, leaving the registers `v`;
* `sg_dig b` prints one digit, `sg_rD b r` prints `v r` digits `b`, `sg_blk r` prints `v r`
  zero clause blocks (`2N + 1` digits), `sg_rep r c body` repeats `body` `v r` times;
* the rows: target `sg_tgtC`, variable rows `sg_vRowC x` (`tP` / `fP`), clause rows
  `sg_cRowC cl x` (`wP` and fillers), zero rows `sg_zRowC`;
* the digit lemmas: `(List.range D).map S` for every item `S`.
-/

namespace Pnp.Karp.SubsetSum

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Digits -/

/-- `n` zero digits. -/
abbrev sg_F (n : ℕ) : List Bool := List.replicate n false

/-- One printed digit. -/
def sg_dg (N : ℕ) (b : Bool) : List SatSym := (if b then pos else zero) :: List.replicate N zero

/-- A printed list of digits. -/
def sg_pr (N : ℕ) (ds : List Bool) : List SatSym := ds.flatMap (sg_dg N)

theorem sg_pr_append (N : ℕ) (a b : List Bool) : sg_pr N (a ++ b) = sg_pr N a ++ sg_pr N b := by
  simp [sg_pr]

theorem sg_pr_rep (N : ℕ) (ds : List Bool) : ∀ n : ℕ,
    (List.replicate n (sg_pr N ds)).flatten = sg_pr N (List.replicate n ds).flatten
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, List.flatten_cons,
      sg_pr_append, sg_pr_rep N ds n]

theorem sg_digRow (N D : ℕ) (S : ℕ → Bool) :
    digRow (N + 1) D S = sg_pr N ((List.range D).map S) := by
  unfold digRow sg_pr
  rw [List.flatMap_map]
  refine List.flatMap_congr fun p _ => ?_
  cases S p <;> simp [sg_dg, List.replicate_succ]

theorem sg_FF (a b : ℕ) (l : List Bool) : sg_F a ++ (sg_F b ++ l) = sg_F (a + b) ++ l := by
  rw [← List.append_assoc, List.replicate_append_replicate]

/-! ## Printing -/

/-- `c` prints `out` within `T` steps, leaving everything else unchanged. -/
def sg_Em (c : Cmd) (v : ℕ → ℕ) (out : List SatSym) (T : ℕ) : Prop :=
  ∀ W O Q E, ExecLe c (st2 W O Q (rv E) v) (.norm (st2 W O Q (rv (E ++ out)) v)) T

theorem sg_Em.seq {c d : Cmd} {v : ℕ → ℕ} {o₁ o₂ : List SatSym} {T₁ T₂ : ℕ}
    (h1 : sg_Em c v o₁ T₁) (h2 : sg_Em d v o₂ T₂) :
    sg_Em (.seq c d) v (o₁ ++ o₂) (T₁ + T₂) := fun W O Q E =>
  ((h1 W O Q E).seq_norm (h2 W O Q (E ++ o₁))).cast (by rw [List.append_assoc]) le_rfl

theorem sg_Em.cast {c : Cmd} {v : ℕ → ℕ} {o o' : List SatSym} {T T' : ℕ} (h : sg_Em c v o T)
    (ho : o = o') (hT : T ≤ T') : sg_Em c v o' T' := fun W O Q E =>
  (h W O Q E).cast (by rw [ho]) hT

theorem sg_Em.seqP {c d : Cmd} {v : ℕ → ℕ} {N : ℕ} {a b : List Bool} {T₁ T₂ : ℕ}
    (h1 : sg_Em c v (sg_pr N a) T₁) (h2 : sg_Em d v (sg_pr N b) T₂) :
    sg_Em (.seq c d) v (sg_pr N (a ++ b)) (T₁ + T₂) :=
  (h1.seq h2).cast (sg_pr_append N a b).symm le_rfl

theorem sg_em_emL (L : List SatSym) (v : ℕ → ℕ) : sg_Em (emL L) v L (2 * L.length + 1) :=
  fun _ _ _ E => ex_emL L E v

/-- Print `v a` zeros. -/
def sg_zsC (a : ℕ) : Cmd := .seq (copyVia a 7 11) Color.zLoop

theorem sg_em_zsC {a : ℕ} (ha : 5 ≤ a) (ha7 : a ≠ 7) (ha11 : a ≠ 11) {v : ℕ → ℕ}
    (h7 : v 7 = 0) (h11 : v 11 = 0) :
    sg_Em (sg_zsC a) v (List.replicate (v a) zero) (9 * v a + 6) := by
  intro W O Q E
  have h1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := a) (b := 7) ha (by norm_num) ha7 ha11
    (by norm_num) (rv E) v h11
  have h2 := Color.ex_zLoop W O Q (v a) E (update v 7 (v 7 + v a)) (by simp [h7])
  refine (h1.seq_norm h2).cast ?_ (by omega)
  rw [update_idem, ← h7, update_eq_self]

/-- Print one digit (`N = v 5`). -/
def sg_dig (b : Bool) : Cmd := .seq (emL [if b then pos else zero]) (sg_zsC 5)

/-- Time of one digit. -/
def sg_tD (V : ℕ) : ℕ := 9 * V + 9

theorem sg_em_dig (b : Bool) {v : ℕ → ℕ} {N V : ℕ} (h5 : v 5 = N) (hN : N ≤ V) (h7 : v 7 = 0)
    (h11 : v 11 = 0) : sg_Em (sg_dig b) v (sg_pr N [b]) (sg_tD V) :=
  ((sg_em_emL _ v).seq (sg_em_zsC (a := 5) (by norm_num) (by norm_num) (by norm_num) h7 h11)).cast
    (by simp [sg_pr, sg_dg, h5]) (by simp [sg_tD]; omega)

/-! ## Repetition -/

/-- Repeat `body` `v r` times (counter `c`). -/
def sg_rep (r c : ℕ) (body : Cmd) : Cmd := .seq (copyVia r c 11) (.loop (.pop c .brk body body))

theorem sg_ex_loopc {c : ℕ} (hc : 5 ≤ c) {body : Cmd} {v : ℕ → ℕ} {o : List SatSym} {T : ℕ}
    (hb : ∀ n, sg_Em body (update v c n) o T) : ∀ (n : ℕ) (W O Q : Str) (E : List SatSym),
    ExecLe (.loop (.pop c .brk body body)) (st2 W O Q (rv E) (update v c n))
      (.norm (st2 W O Q (rv (E ++ (List.replicate n o).flatten)) (update v c 0))) (n * (T + 1) + 2)
  | 0, W, O, Q, E => (Ham.hg_cend (by rw [st2_reg hc]; simp)).cast (by simp) (by simp)
  | n + 1, W, O, Q, E => by
    have ih := sg_ex_loopc hc hb n W O Q (E ++ o)
    have hbody := hb n W O Q E
    refine (Ham.hg_cstep (n := n) (by rw [st2_reg hc]; simp)
      (by rw [upd2_reg hc, update_idem]; exact hbody) ih).cast ?_ ?_
    · simp [List.replicate_succ, List.append_assoc]
    · rw [Nat.succ_mul]; omega

theorem sg_em_rep {r c : ℕ} (hr : 5 ≤ r) (hc : 5 ≤ c) (hrc : r ≠ c) (hr11 : r ≠ 11)
    (hc11 : c ≠ 11) {body : Cmd} {v : ℕ → ℕ} {o : List SatSym} {T : ℕ} (hv : v c = 0)
    (h11 : v 11 = 0) (hb : ∀ n, sg_Em body (update v c n) o T) :
    sg_Em (sg_rep r c body) v (List.replicate (v r) o).flatten (v r * (T + 1) + 5 * v r + 6) := by
  intro W O Q E
  have h1 := ex_copy_reg (W := W) (O := O) (Q := Q) hr hc hrc hr11 hc11 (rv E) v h11
  rw [hv, Nat.zero_add] at h1
  have h2 := sg_ex_loopc hc hb (v r) W O Q E
  have e : update v c 0 = v := by rw [← hv]; exact update_eq_self c v
  rw [e] at h2
  exact (h1.seq_norm h2).cast rfl (by omega)

theorem sg_em_repP {r c : ℕ} (hr : 5 ≤ r) (hc : 5 ≤ c) (hrc : r ≠ c) (hr11 : r ≠ 11)
    (hc11 : c ≠ 11) {body : Cmd} {v : ℕ → ℕ} {N V : ℕ} {ds : List Bool} {T : ℕ} (hv : v c = 0)
    (h11 : v 11 = 0) (hrV : v r ≤ V) (hb : ∀ n, sg_Em body (update v c n) (sg_pr N ds) T) :
    sg_Em (sg_rep r c body) v (sg_pr N (List.replicate (v r) ds).flatten)
      (V * (T + 1) + 5 * V + 6) :=
  (sg_em_rep hr hc hrc hr11 hc11 hv h11 hb).cast (sg_pr_rep N ds _)
    (by have := Nat.mul_le_mul_right (T + 1) hrV; omega)

/-! ## Runs of digits and blocks -/

/-- Print `v r` digits `b`. -/
def sg_rD (b : Bool) (r : ℕ) : Cmd := sg_rep r 10 (sg_dig b)

/-- Time of a run of digits. -/
def sg_tZ (V : ℕ) : ℕ := V * (sg_tD V + 1) + 5 * V + 6

/-- The zero registers. -/
def sg_Z (v : ℕ → ℕ) : Prop := v 7 = 0 ∧ v 10 = 0 ∧ v 11 = 0

theorem sg_Z_upd {v : ℕ → ℕ} (h : sg_Z v) {r : ℕ} (h7 : r ≠ 7) (h10 : r ≠ 10) (h11 : r ≠ 11)
    (n : ℕ) : sg_Z (update v r n) := by
  obtain ⟨a, b, c⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp [*, Ne.symm h7, Ne.symm h10, Ne.symm h11]

theorem sg_em_rD (b : Bool) {r : ℕ} (hr : 5 ≤ r) (hr10 : r ≠ 10) (hr11 : r ≠ 11) {v : ℕ → ℕ}
    {N V : ℕ} (h5 : v 5 = N) (hN : N ≤ V) (hrV : v r ≤ V) (hz : sg_Z v) :
    sg_Em (sg_rD b r) v (sg_pr N (List.replicate (v r) b)) (sg_tZ V) := by
  obtain ⟨h7, h10, h11⟩ := hz
  refine (sg_em_repP hr (c := 10) (by norm_num) hr10 hr11 (by norm_num) h10 h11 hrV
    (fun n => sg_em_dig b (v := update v 10 n) (by simp [h5]) hN
      (by simp [h7]) (by simp [h11]))).cast ?_ le_rfl
  rw [List.flatten_replicate_singleton]

/-- Uniform time of the bodies of block repetitions, and of a block repetition. -/
def sg_tP (V : ℕ) : ℕ := 4 * sg_tZ V + 4 * sg_tD V

def sg_tB (V : ℕ) : ℕ := V * (sg_tP V + 1) + 5 * V + 6

/-- Print `v r` zero clause blocks (`2N + 1` digits each). -/
def sg_blk (r : ℕ) : Cmd := sg_rep r 12 (.seq (sg_rD false 5) (.seq (sg_rD false 5) (sg_dig false)))

theorem sg_blk_eq (N : ℕ) : sg_F N ++ (sg_F N ++ [false]) = sg_F (2 * N + 1) := by
  rw [show [false] = sg_F 1 from rfl, List.replicate_append_replicate,
    List.replicate_append_replicate]; congr 1; omega

theorem sg_em_blk {r : ℕ} (hr : 5 ≤ r) (hr12 : r ≠ 12) (hr11 : r ≠ 11) {v : ℕ → ℕ} {N V : ℕ}
    (h5 : v 5 = N) (hN : N ≤ V) (hrV : v r ≤ V) (hz : sg_Z v) (h12 : v 12 = 0) :
    sg_Em (sg_blk r) v (sg_pr N (sg_F ((2 * N + 1) * v r))) (sg_tB V) := by
  have hb : ∀ n, sg_Em (.seq (sg_rD false 5) (.seq (sg_rD false 5) (sg_dig false))) (update v 12 n)
      (sg_pr N (sg_F N ++ (sg_F N ++ [false]))) (sg_tP V) := by
    intro n
    have h5' : update v 12 n 5 = N := by simp [h5]
    have hz'' := sg_Z_upd hz (r := 12) (by norm_num) (by norm_num) (by norm_num) n
    have q1 := sg_em_rD false (r := 5) (by norm_num) (by norm_num) (by norm_num) h5' hN
      (by omega) hz''
    have q3 := sg_em_dig false (v := update v 12 n) h5' hN hz''.1 hz''.2.2
    rw [h5'] at q1
    exact (q1.seqP (q1.seqP q3)).cast rfl (by unfold sg_tP; omega)
  refine (sg_em_repP hr (c := 12) (by norm_num) hr12 hr11 (by norm_num) h12 hz.2.2 hrV
    hb).cast ?_ le_rfl
  rw [sg_blk_eq, List.flatten_replicate_replicate, Nat.mul_comm]

/-! ## The pair digits of a clause block -/

/-- The `2N` digits after the clause digit of a block: `1` at local position `2j` (`x = false`)
or `2j + 1` (`x = true`), with `j' = N - 1 - j`. -/
def sg_pDg (j j' : ℕ) : Bool → List Bool
  | false => sg_F (2 * j) ++ true :: sg_F (2 * j' + 1)
  | true => sg_F (2 * j + 1) ++ true :: sg_F (2 * j')

def sg_pC : Bool → Cmd
  | false => .seq (sg_rD false 13) (.seq (sg_rD false 13) (.seq (sg_dig true) (.seq (sg_dig false)
      (.seq (sg_rD false 14) (sg_rD false 14)))))
  | true => .seq (sg_dig false) (.seq (sg_rD false 13) (.seq (sg_rD false 13) (.seq (sg_dig true)
      (.seq (sg_rD false 14) (sg_rD false 14)))))

theorem sg_em_pC (x : Bool) {v : ℕ → ℕ} {N V j j' : ℕ} (h5 : v 5 = N) (h13 : v 13 = j)
    (h14 : v 14 = j') (hN : N ≤ V) (hj : j ≤ V) (hj' : j' ≤ V) (hz : sg_Z v) :
    sg_Em (sg_pC x) v (sg_pr N (sg_pDg j j' x)) (4 * sg_tZ V + 2 * sg_tD V) := by
  have a := sg_em_rD false (r := 13) (by norm_num) (by norm_num) (by norm_num) h5 hN
    (by omega) hz
  have b := sg_em_rD false (r := 14) (by norm_num) (by norm_num) (by norm_num) h5 hN
    (by omega) hz
  have t := sg_em_dig true h5 hN hz.1 hz.2.2
  have f := sg_em_dig false h5 hN hz.1 hz.2.2
  rw [h13] at a
  rw [h14] at b
  cases x with
  | false =>
    refine (a.seqP (a.seqP (t.seqP (f.seqP (b.seqP b))))).cast ?_ (by omega)
    congr 1
    rw [sg_FF, List.replicate_append_replicate, show j + j = 2 * j by omega]
    simp only [sg_pDg]
    rw [show 2 * j' + 1 = (j' + j') + 1 by omega]
    rfl
  | true =>
    refine (f.seqP (a.seqP (a.seqP (t.seqP (b.seqP b))))).cast ?_ (by omega)
    congr 1
    rw [sg_FF, List.replicate_append_replicate, show j' + j' = 2 * j' by omega]
    simp only [sg_pDg]
    rw [show 2 * j + 1 = (j + j) + 1 by omega]
    rfl

/-! ## The rows -/

/-- Time bound of every row. -/
def sg_rowT (V : ℕ) : ℕ := 6 * sg_tZ V + 6 * sg_tD V + 2 * sg_tB V + 3

/-- The target row. -/
def sg_tgtC : Cmd :=
  .seq (.seq (sg_rD true 5) (sg_rep 9 12 (.seq (sg_rD true 5) (.seq (sg_rD true 5) (sg_dig true)))))
    (emL [sep])

theorem sg_em_tgt {v : ℕ → ℕ} {N m V : ℕ} (h5 : v 5 = N) (h9 : v 9 = m) (hN : N ≤ V)
    (hm : m ≤ V) (hz : sg_Z v) (h12 : v 12 = 0) :
    sg_Em sg_tgtC v (sg_pr N (List.replicate (DD N m) true) ++ [sep]) (sg_rowT V) := by
  have a := sg_em_rD true (r := 5) (by norm_num) (by norm_num) (by norm_num) h5 hN
    (by omega) hz
  rw [h5] at a
  have hb : ∀ n, sg_Em (.seq (sg_rD true 5) (.seq (sg_rD true 5) (sg_dig true))) (update v 12 n)
      (sg_pr N (List.replicate N true ++ (List.replicate N true ++ [true]))) (sg_tP V) := by
    intro n
    have h5' : update v 12 n 5 = N := by simp [h5]
    have hz' := sg_Z_upd hz (r := 12) (by norm_num) (by norm_num) (by norm_num) n
    have a' := sg_em_rD true (r := 5) (by norm_num) (by norm_num) (by norm_num) h5' hN
      (by omega) hz'
    rw [h5'] at a'
    exact (a'.seqP (a'.seqP (sg_em_dig true h5' hN hz'.1 hz'.2.2))).cast rfl
      (by unfold sg_tP; omega)
  have r := sg_em_repP (r := 9) (c := 12) (V := V) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h12 hz.2.2 (by omega) hb
  rw [h9] at r
  refine ((a.seqP r).seq (sg_em_emL [sep] v)).cast ?_ (by unfold sg_rowT sg_tB; simp only [List.length_cons, List.length_nil]; omega)
  congr 2
  rw [show List.replicate N true ++ (List.replicate N true ++ [true]) = List.replicate (2 * N + 1) true
    by rw [show [true] = List.replicate 1 true from rfl, List.replicate_append_replicate,
      List.replicate_append_replicate]; congr 1; omega,
    List.flatten_replicate_replicate, List.replicate_append_replicate, DD, Nat.mul_comm m]

/-- The digits of a variable row (`x = true`: `tP`, `x = false`: `fP`). -/
def sg_vDg (m j j' : ℕ) (x : Bool) : List Bool :=
  sg_F j ++ (true :: (sg_F j' ++ (List.replicate m (false :: sg_pDg j j' x)).flatten))

def sg_vRowC (x : Bool) : Cmd :=
  .seq (.seq (sg_rD false 13) (.seq (sg_dig true) (.seq (sg_rD false 14)
    (sg_rep 9 12 (.seq (sg_dig false) (sg_pC x)))))) (emL [sep])

theorem sg_em_vRow (x : Bool) {v : ℕ → ℕ} {N m V j j' : ℕ} (h5 : v 5 = N) (h9 : v 9 = m)
    (h13 : v 13 = j) (h14 : v 14 = j') (hN : N ≤ V) (hm : m ≤ V) (hj : j ≤ V) (hj' : j' ≤ V)
    (hz : sg_Z v) (h12 : v 12 = 0) :
    sg_Em (sg_vRowC x) v (sg_pr N (sg_vDg m j j' x) ++ [sep]) (sg_rowT V) := by
  have a := sg_em_rD false (r := 13) (by norm_num) (by norm_num) (by norm_num) h5 hN
    (by omega) hz
  have b := sg_em_rD false (r := 14) (by norm_num) (by norm_num) (by norm_num) h5 hN
    (by omega) hz
  rw [h13] at a
  rw [h14] at b
  have hb : ∀ n, sg_Em (.seq (sg_dig false) (sg_pC x)) (update v 12 n)
      (sg_pr N ([false] ++ sg_pDg j j' x)) (sg_tP V) := by
    intro n
    have hz' := sg_Z_upd hz (r := 12) (by norm_num) (by norm_num) (by norm_num) n
    have h5' : update v 12 n 5 = N := by simp [h5]
    exact ((sg_em_dig false h5' hN hz'.1 hz'.2.2).seqP (sg_em_pC x h5' (by simp [h13])
      (by simp [h14]) hN hj hj' hz')).cast rfl (by unfold sg_tP; omega)
  have r := sg_em_repP (r := 9) (c := 12) (V := V) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h12 hz.2.2 (by omega) hb
  rw [h9] at r
  refine ((a.seqP ((sg_em_dig true h5 hN hz.1 hz.2.2).seqP (b.seqP r))).seq
    (sg_em_emL [sep] v)).cast rfl (by unfold sg_rowT sg_tB; simp only [List.length_cons, List.length_nil]; omega)

/-- The digits of a clause row: clause digit `cl`, pair digit `x` (`wP` / fillers). -/
def sg_cDg (N k d j j' : ℕ) (cl x : Bool) : List Bool :=
  sg_F (N + (2 * N + 1) * k) ++ (cl :: (sg_pDg j j' x ++ sg_F ((2 * N + 1) * d)))

def sg_cRowC (cl x : Bool) : Cmd :=
  .seq (.seq (sg_rD false 5) (.seq (sg_blk 6) (.seq (sg_dig cl) (.seq (sg_pC x) (sg_blk 8)))))
    (emL [sep])

theorem sg_em_cRow (cl x : Bool) {v : ℕ → ℕ} {N V k d j j' : ℕ} (h5 : v 5 = N) (h6 : v 6 = k)
    (h8 : v 8 = d) (h13 : v 13 = j) (h14 : v 14 = j') (hN : N ≤ V) (hk : k ≤ V) (hd : d ≤ V)
    (hj : j ≤ V) (hj' : j' ≤ V) (hz : sg_Z v) (h12 : v 12 = 0) :
    sg_Em (sg_cRowC cl x) v (sg_pr N (sg_cDg N k d j j' cl x) ++ [sep]) (sg_rowT V) := by
  have a := sg_em_rD false (r := 5) (by norm_num) (by norm_num) (by norm_num) h5 hN
    (by omega) hz
  rw [h5] at a
  have b1 := sg_em_blk (r := 6) (by norm_num) (by norm_num) (by norm_num) h5 hN
    (by omega) hz h12
  have b2 := sg_em_blk (r := 8) (by norm_num) (by norm_num) (by norm_num) h5 hN
    (by omega) hz h12
  rw [h6] at b1
  rw [h8] at b2
  refine ((a.seqP (b1.seqP ((sg_em_dig cl h5 hN hz.1 hz.2.2).seqP
    ((sg_em_pC x h5 h13 h14 hN hj hj' hz).seqP b2)))).seq (sg_em_emL [sep] v)).cast ?_
    (by unfold sg_rowT; simp only [List.length_cons, List.length_nil]; omega)
  congr 2
  rw [sg_FF]; rfl

/-- The zero row. -/
def sg_zRowC : Cmd := .seq (.seq (sg_rD false 5) (sg_blk 9)) (emL [sep])

theorem sg_em_zRow {v : ℕ → ℕ} {N m V : ℕ} (h5 : v 5 = N) (h9 : v 9 = m) (hN : N ≤ V)
    (hm : m ≤ V) (hz : sg_Z v) (h12 : v 12 = 0) :
    sg_Em sg_zRowC v (sg_pr N (sg_F (DD N m)) ++ [sep]) (sg_rowT V) := by
  have a := sg_em_rD false (r := 5) (by norm_num) (by norm_num) (by norm_num) h5 hN
    (by omega) hz
  rw [h5] at a
  have b := sg_em_blk (r := 9) (by norm_num) (by norm_num) (by norm_num) h5 hN
    (by omega) hz h12
  rw [h9] at b
  refine ((a.seqP b).seq (sg_em_emL [sep] v)).cast ?_ (by unfold sg_rowT; simp only [List.length_cons, List.length_nil]; omega)
  rw [List.replicate_append_replicate]; rfl

/-! ## The digits of the items -/

theorem sg_map_split (S : ℕ → Bool) (a b : ℕ) :
    (List.range (a + b)).map S = (List.range a).map S ++ (List.range b).map (fun i => S (a + i)) := by
  rw [List.range_add, List.map_append, List.map_map]; rfl

theorem sg_map_const (S : ℕ → Bool) (n : ℕ) (c : Bool) (h : ∀ i < n, S i = c) :
    (List.range n).map S = List.replicate n c := by
  rw [List.map_congr_left (fun i hi => h i (List.mem_range.1 hi)), List.map_const',
    List.length_range]

theorem sg_map_one (S : ℕ → Bool) (a d : ℕ) (h : ∀ i < a + 1 + d, S i = decide (i = a)) :
    (List.range (a + 1 + d)).map S = sg_F a ++ true :: sg_F d := by
  rw [Nat.add_assoc, sg_map_split, sg_map_split,
    sg_map_const S a false (fun i hi => by rw [h i (by omega)]; exact decide_eq_false (by omega)),
    sg_map_const _ d false (fun i hi => by
      rw [h _ (by omega)]; exact decide_eq_false (by omega))]
  simp [h a (by omega)]

theorem sg_map_blocks (T : ℕ → Bool) (P : ℕ) : ∀ m : ℕ, (List.range (P * m)).map T =
    ((List.range m).map (fun k => (List.range P).map (fun i => T (P * k + i)))).flatten
  | 0 => by simp
  | m + 1 => by
    rw [Nat.mul_succ, sg_map_split, sg_map_blocks T P m, List.range_succ, List.map_append,
      List.flatten_append]
    simp

theorem sg_block (N j j' : ℕ) (cl x : Bool) (S0 : ℕ → Bool) (hj : j < N) (hj' : j' = N - 1 - j)
    (h0 : S0 0 = cl) (h1 : ∀ i < 2 * N, S0 (i + 1) = decide (i = 2 * j + if x then 1 else 0)) :
    (List.range (2 * N + 1)).map S0 = cl :: sg_pDg j j' x := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, h0]
  congr 1
  cases x with
  | false =>
    rw [show 2 * N = 2 * j + 1 + (2 * j' + 1) by omega]
    exact sg_map_one _ _ _ (fun i hi => by simpa using h1 i (by omega))
  | true =>
    rw [show 2 * N = 2 * j + 1 + 1 + 2 * j' by omega]
    exact sg_map_one _ _ _ (fun i hi => by simpa using h1 i (by omega))

theorem sg_uniq {a k k' i i' : ℕ} (hi : i < a) (hi' : i' < a) (h : a * k + i = a * k' + i') :
    k = k' := by
  rcases Nat.lt_trichotomy k k' with h1 | h1 | h1
  · have := Nat.mul_le_mul_left a (Nat.succ_le_of_lt h1); rw [Nat.mul_succ] at this; omega
  · exact h1
  · have := Nat.mul_le_mul_left a (Nat.succ_le_of_lt h1); rw [Nat.mul_succ] at this; omega

/-- The digits of a variable-type item. -/
theorem sg_vDig (N m j : ℕ) (x : Bool) (S : ℕ → Bool) (hj : j < N)
    (hV : ∀ i < N, S i = decide (i = j))
    (hB : ∀ k < m, ∀ i < 2 * N + 1, S (N + (2 * N + 1) * k + i) =
      decide (i = 1 + 2 * j + if x then 1 else 0)) :
    (List.range (DD N m)).map S = sg_vDg m j (N - 1 - j) x := by
  unfold DD sg_vDg
  rw [sg_map_split, sg_map_blocks]
  have e1 : (List.range N).map S = sg_F j ++ true :: sg_F (N - 1 - j) := by
    conv_lhs => rw [show N = j + 1 + (N - 1 - j) by omega]
    exact sg_map_one S j _ (fun i hi => hV i (by omega))
  rw [e1, List.append_assoc, List.cons_append]
  congr 3
  rw [List.map_congr_left (g := fun _ => false :: sg_pDg j (N - 1 - j) x), List.map_const',
    List.length_range]
  intro k hk
  have hk := List.mem_range.1 hk
  refine sg_block N j _ false x _ hj rfl ?_ ?_
  · have := hB k hk 0 (by omega)
    show S (N + ((2 * N + 1) * k + 0)) = false
    rw [← Nat.add_assoc, this]
    cases x <;> exact decide_eq_false (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
  · intro i hi
    have := hB k hk (i + 1) (by omega)
    show S (N + ((2 * N + 1) * k + (i + 1))) = _
    rw [← Nat.add_assoc, this]
    cases x <;> exact decide_eq_decide.2 (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)

/-- The digits of a clause-type item. -/
theorem sg_cDig (N m k d j : ℕ) (cl x : Bool) (S : ℕ → Bool) (hj : j < N) (hm : k + 1 + d = m)
    (hS : ∀ p, S p = decide ((p = clD N k ∧ cl = true) ∨
      p = clD N k + 1 + 2 * j + if x then 1 else 0)) :
    (List.range (DD N m)).map S = sg_cDg N k d j (N - 1 - j) cl x := by
  have e : DD N m = (N + (2 * N + 1) * k) + ((2 * N + 1) + (2 * N + 1) * d) := by
    subst hm; unfold DD; ring
  unfold sg_cDg
  rw [e, sg_map_split S (N + (2 * N + 1) * k), sg_map_split _ (2 * N + 1),
    sg_map_const S _ false (fun i hi => by
      rw [hS]; simp only [clD]; exact decide_eq_false (by cases x <;> simp <;> omega)),
    sg_map_const _ ((2 * N + 1) * d) false (fun i hi => by
      rw [hS]; simp only [clD]; exact decide_eq_false (by cases x <;> simp <;> omega))]
  congr 1
  rw [sg_block N j _ cl x _ hj rfl (by rw [hS]; simp only [clD]; cases x <;> cases cl <;> simp <;> omega) (fun i hi => by
    rw [hS]; simp only [clD]
    exact decide_eq_decide.2 (by cases x <;> cases cl <;> simp <;> omega))]
  rfl

/-- The items, as digit lists. -/
theorem sg_tP_dig (N m j : ℕ) (hj : j < N) :
    (List.range (DD N m)).map (tP N m j) = sg_vDg m j (N - 1 - j) true := by
  refine sg_vDig N m j true _ hj (fun i hi => ?_) (fun k hk i hi => ?_)
  · unfold tP qD clD
    rw [decide_eq_decide]
    constructor
    · rintro (h | ⟨k, -, h⟩) <;> omega
    · exact Or.inl
  · unfold tP qD clD
    rw [decide_eq_decide]
    constructor
    · rintro (h | ⟨k', -, h⟩)
      · omega
      · have := sg_uniq (a := 2 * N + 1) (k := k) (k' := k') (i := i) (i' := 2 + 2 * j) hi
          (by omega) (by omega)
        subst this; simp; omega
    · intro h; exact Or.inr ⟨k, hk, by simp at h; omega⟩

theorem sg_fP_dig (N m j : ℕ) (hj : j < N) :
    (List.range (DD N m)).map (fP N m j) = sg_vDg m j (N - 1 - j) false := by
  refine sg_vDig N m j false _ hj (fun i hi => ?_) (fun k hk i hi => ?_)
  · unfold fP pD clD
    rw [decide_eq_decide]
    constructor
    · rintro (h | ⟨k, -, h⟩) <;> omega
    · exact Or.inl
  · unfold fP pD clD
    rw [decide_eq_decide]
    constructor
    · rintro (h | ⟨k', -, h⟩)
      · omega
      · have := sg_uniq (a := 2 * N + 1) (k := k) (k' := k') (i := i) (i' := 1 + 2 * j) hi
          (by omega) (by omega)
        subst this; simp; omega
    · intro h; exact Or.inr ⟨k, hk, by simp at h; omega⟩

theorem sg_wPpos_dig (N m k d j : ℕ) (hj : j < N) (hm : k + 1 + d = m) :
    (List.range (DD N m)).map (wP N k j pos) = sg_cDg N k d j (N - 1 - j) true false :=
  sg_cDig N m k d j true false _ hj hm (fun p => by
    simp only [wP, pD]; exact decide_eq_decide.2 (by simp))

theorem sg_wPneg_dig (N m k d j : ℕ) (hj : j < N) (hm : k + 1 + d = m) :
    (List.range (DD N m)).map (wP N k j neg) = sg_cDg N k d j (N - 1 - j) true true :=
  sg_cDig N m k d j true true _ hj hm (fun p => by
    simp only [wP, qD]; exact decide_eq_decide.2 (by simp; omega))

theorem sg_oneP_dig (N m k d j : ℕ) (hj : j < N) (hm : k + 1 + d = m) :
    (List.range (DD N m)).map (oneP (pD N k j)) = sg_cDg N k d j (N - 1 - j) false false :=
  sg_cDig N m k d j false false _ hj hm (fun p => by
    simp only [oneP, pD]; exact decide_eq_decide.2 (by simp))

theorem sg_oneQ_dig (N m k d j : ℕ) (hj : j < N) (hm : k + 1 + d = m) :
    (List.range (DD N m)).map (oneP (qD N k j)) = sg_cDg N k d j (N - 1 - j) false true :=
  sg_cDig N m k d j false true _ hj hm (fun p => by
    simp only [oneP, qD]; exact decide_eq_decide.2 (by simp; omega))

end Pnp.Karp.SubsetSum
