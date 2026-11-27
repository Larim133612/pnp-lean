import Pnp.Karp.ThreeDMGen

/-!
# The 3DM / X3C reduction program, part 2: the phases, the whole program, the reductions

`mg_redCmd hd` (rows and primitives: `Pnp/Karp/ThreeDMGen.lean`), on the bit string `x` on
stack `0`, prints `mg_out hd (dec2 x)` (`= DMI` for `hd = 1`, `= X3I` for `hd = 3`):

1. parsing and counting as for SUBSET SUM: `N` (register `5`), `m` (`9`);
2. `mg_setC`: `m - 1` (`12`), `M = N m` (`13`), `q = 2M` (`14`), `M - m` (`30`);
3. `mg_hdC hd`: the header `zero^(hd q)`;
4. `mg_ringC`: the ring rows (`L = m i + k` in `15`, `M - 1 - L` in `16`, `M - 2 - L` in `17`,
   `m i` in `18`; counters `19`, `20`);
5. `mg_clC`: the clause rows, scanning `trunc w` on stack `3` (`k` in `21`, `M - 1 - k` in
   `22`, `m j + k` in `23`, `M - 1 - k - m j` in `24`; counter `33`);
6. `mg_garC`: the garbage rows (`x` in `26`, `q - 1 - x` in `27`, `t` in `28`,
   `M - m - 1 - t` in `29`; counters `31`, `32`).

Registers `7`, `11`, `25` are temporaries (zero between steps).
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.ThreeDM

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

/-! ## The global registers -/

/-- The global registers. -/
def mg_G (v : ℕ → ℕ) (N m : ℕ) : Prop :=
  v 5 = N ∧ v 9 = m ∧ v 12 = m - 1 ∧ v 13 = N * m ∧ v 14 = 2 * (N * m) ∧ v 30 = N * m - m ∧
    v 7 = 0 ∧ v 11 = 0 ∧ v 25 = 0

theorem mg_G_congr {v v' : ℕ → ℕ} {N m : ℕ} (h : mg_G v N m)
    (h' : ∀ r, r = 5 ∨ r = 9 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 30 ∨ r = 7 ∨ r = 11 ∨ r = 25 →
      v' r = v r) : mg_G v' N m := by
  obtain ⟨a, b, c, d, e, f, g, i, j⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h'] <;> first | assumption | simp

@[simp] theorem mg_fm_nil {α : Type*} (l : List α) : l.flatMap (fun _ => ([] : List SatSym)) = [] := by
  induction l <;> simp_all

section Reg
variable {W O Q : Str}

/-- Subtract `v a` from `v b` (counter `25`). -/
def mg_subC (a b : ℕ) : Cmd :=
  .seq (copyVia a 25 11) (.loop (.pop 25 .brk (Ham.hg_dec b) (Ham.hg_dec b)))

theorem mg_ex_sub {a b : ℕ} (ha : 5 ≤ a) (hb : 5 ≤ b) (hab : a ≠ b) (ha11 : a ≠ 11)
    (ha25 : a ≠ 25) (hb25 : b ≠ 25) (E : List SatSym) (v : ℕ → ℕ) (h11 : v 11 = 0)
    (h25 : v 25 = 0) :
    ExecLe (mg_subC a b) (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv E) (update v b (v b - v a)))) (9 * v a + 6) := by
  have p1 := ex_copy_reg (W := W) (O := O) (Q := Q) ha (show 5 ≤ 25 by norm_num) ha25 ha11
    (by norm_num) (rv E) v h11
  rw [h25, Nat.zero_add] at p1
  obtain ⟨v', f1, f2, p2⟩ := mg_loop (c := 25) (B := Ham.hg_dec b) (by norm_num) W Q (fun _ => O)
    (fun j u => ∀ r, r ≠ 25 → u r = update v b (v b - j) r) (fun _ => []) 2 (v a)
    (fun j u x h r hr => by rw [update_of_ne hr]; exact h r hr)
    (fun j u E' _ h => ⟨update u b (u b - 1), fun r hr => by
        by_cases hrb : r = b
        · subst hrb; simp [h r hr]; omega
        · rw [update_of_ne hrb, h r hr, update_of_ne hrb, update_of_ne hrb],
      by simp [Ne.symm hb25], (sg_ex_dec hb (rv E') u).cast (by simp) le_rfl⟩)
    (v a) 0 E (update v 25 (v a)) (by omega)
    (fun r hr => by rw [update_of_ne hr, Nat.sub_zero, update_eq_self]) (by simp)
  have e : v' = update v b (v b - v a) := by
    funext r
    by_cases hr : r = 25
    · subst hr; rw [f2, update_of_ne (Ne.symm hb25), h25]
    · rw [f1 r hr, Nat.zero_add]
  rw [e, mg_fm_nil, List.append_nil] at p2
  refine (p1.seq_norm p2).cast rfl (by
    have : v a * (2 + 1) = 3 * v a := by ring
    omega)

end Reg

/-! ## Setup: `m - 1`, `M`, `q`, `M - m` -/

def mg_mulL : Cmd := .loop (.pop 6 .brk (copyVia 9 13 11) (copyVia 9 13 11))

def mg_setC : Cmd :=
  .seq (copyVia 9 12 11) (.seq (Ham.hg_dec 12) (.seq (copyVia 5 6 11) (.seq mg_mulL
    (.seq (copyVia 13 14 11) (.seq (copyVia 13 14 11) (.seq (copyVia 13 30 11) (mg_subC 9 30)))))))

def mg_tS (U : ℕ) : ℕ := U * (5 * U + 5) + 40 * U + 60

theorem mg_ex_set (N m U : ℕ) (hU : 2 * (N * m) + N + m ≤ U) (W O Q : Str) (E : List SatSym)
    (v : ℕ → ℕ) (h5 : v 5 = N) (h9 : v 9 = m) (h0 : ∀ r, r ≠ 5 → r ≠ 9 → v r = 0) :
    ∃ v', mg_G v' N m ∧ (∀ r, r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 30 → v' r = v r) ∧
      ExecLe mg_setC (st2 W O Q (rv E) v) (.norm (st2 W O Q (rv E) v')) (mg_tS U) := by
  have z11 : v 11 = 0 := h0 11 (by norm_num) (by norm_num)
  have p1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 9) (b := 12) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v z11
  set v1 := update v 12 (v 12 + v 9)
  have p2 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 12) (by norm_num) (rv E) v1
  set v2 := update v1 12 (v1 12 - 1)
  have p3 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 5) (b := 6) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v2 (by simp [v2, v1, z11])
  set v3 := update v2 6 (v2 6 + v2 5)
  obtain ⟨v4, ⟨f1, f2⟩, f3, p4⟩ := mg_loop (c := 6) (B := copyVia 9 13 11) (by norm_num) W Q
    (fun _ => O) (fun j u => (∀ r, r ≠ 6 → r ≠ 13 → u r = v3 r) ∧ u 13 = j * m) (fun _ => [])
    (5 * m + 4) N
    (fun j u x ⟨a, b⟩ => ⟨fun r h6 h13 => by rw [update_of_ne h6]; exact a r h6 h13,
      by rw [update_of_ne (by norm_num)]; exact b⟩)
    (fun j u E' _ ⟨a, b⟩ => by
      have u9 : u 9 = m := by rw [a 9 (by norm_num) (by norm_num)]; simp [v3, v2, v1, h9]
      have u11 : u 11 = 0 := by rw [a 11 (by norm_num) (by norm_num)]; simp [v3, v2, v1, z11]
      refine ⟨update u 13 (u 13 + u 9), ⟨fun r h6 h13 => by rw [update_of_ne h13]; exact a r h6 h13,
        by simp [b, u9, Nat.succ_mul]⟩, by simp, ?_⟩
      have := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 9) (b := 13) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E') u u11
      rw [u9] at this
      exact this.cast (by rw [List.append_nil, u9]) le_rfl)
    N 0 E v3 (by omega)
    ⟨fun _ _ _ => rfl, by simp [v3, v2, v1, h0 13]⟩ (by simp [v3, v2, v1, h5, h0 6])
  rw [mg_fm_nil, List.append_nil] at p4
  have g : ∀ r, r ≠ 6 → r ≠ 13 → v4 r = v3 r := f1
  have z4 : v4 11 = 0 := by rw [g 11 (by norm_num) (by norm_num)]; simp [v3, v2, v1, z11]
  have p5 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 13) (b := 14) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v4 z4
  set v5 := update v4 14 (v4 14 + v4 13)
  have p6 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 13) (b := 14) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v5 (by simp [v5, z4])
  set v6 := update v5 14 (v5 14 + v5 13)
  have p7 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 13) (b := 30) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v6 (by simp [v6, v5, z4])
  set v7 := update v6 30 (v6 30 + v6 13)
  have p8 := mg_ex_sub (W := W) (O := O) (Q := Q) (a := 9) (b := 30) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) E v7 (by simp [v7, v6, v5, z4])
    (by simp [v7, v6, v5, g, v3, v2, v1, h0 25])
  have k13 : v4 13 = N * m := by rw [f2, Nat.zero_add]
  have k14 : v4 14 = 0 := by rw [g 14 (by norm_num) (by norm_num)]; simp [v3, v2, v1, h0 14]
  have k30 : v4 30 = 0 := by rw [g 30 (by norm_num) (by norm_num)]; simp [v3, v2, v1, h0 30]
  have k9 : v4 9 = m := by rw [g 9 (by norm_num) (by norm_num)]; simp [v3, v2, v1, h9]
  have k5 : v4 5 = N := by rw [g 5 (by norm_num) (by norm_num)]; simp [v3, v2, v1, h5]
  have k12 : v4 12 = m - 1 := by
    rw [g 12 (by norm_num) (by norm_num)]; simp [v3, v2, v1, h9, h0 12]
  have hrest : ∀ r, r ≠ 6 → r ≠ 12 → r ≠ 13 → v4 r = v r := fun r a b c => by
    rw [g r a c]; simp [v3, v2, v1, a, b]
  refine ⟨update v7 30 (v7 30 - v7 9), ?_, ?_, (p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm
    (p5.seq_norm (p6.seq_norm (p7.seq_norm p8))))))).cast (by simp) ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [v7, v6, v5, k13, k14, k30, k9, k5, k12, hrest, h0]
    · omega
  · intro r a b c d
    by_cases h6 : r = 6
    · subst h6; simp [v7, v6, v5, f3, h0 6]
    · simp [v7, v6, v5, a, b, c, d, hrest r h6 a b]
  · simp only [v3, v2, v1, update_self, update_of_ne (show (6 : ℕ) ≠ 12 by norm_num),
      update_of_ne (show (5 : ℕ) ≠ 12 by norm_num), update_of_ne (show (5 : ℕ) ≠ 6 by norm_num),
      h5, h9, h0 6 (by norm_num) (by norm_num), h0 12 (by norm_num) (by norm_num), k13, k14,
      k30, v7, v6, v5, update_of_ne (show (13 : ℕ) ≠ 14 by norm_num),
      update_of_ne (show (13 : ℕ) ≠ 30 by norm_num), update_of_ne (show (14 : ℕ) ≠ 30 by norm_num),
      update_of_ne (show (9 : ℕ) ≠ 30 by norm_num), update_of_ne (show (9 : ℕ) ≠ 14 by norm_num),
      k9]
    have b1 : N * (5 * m + 4 + 1) ≤ U * (5 * U + 5) :=
      Nat.mul_le_mul (by omega) (by omega)
    unfold mg_tS
    omega

theorem mg_G_out {v v' : ℕ → ℕ} {N m : ℕ} (S : List ℕ) (h : mg_G v N m)
    (h' : ∀ r, r ∉ S → v' r = v r)
    (hS : ([5, 9, 12, 13, 14, 30, 7, 11, 25].all fun r => !(S.contains r)) = true) :
    mg_G v' N m := by
  refine mg_G_congr h (fun r hr => h' r ?_)
  have := List.all_eq_true.1 hS r (by rcases hr with h|h|h|h|h|h|h|h|h <;> subst h <;> simp)
  simpa using this

theorem mg_upd_out {u u0 : ℕ → ℕ} {S : List ℕ} (r0 x : ℕ) (h : ∀ r, r ∉ S → u r = u0 r)
    (hr0 : r0 ∈ S) : ∀ r, r ∉ S → update u r0 x r = u0 r := fun r hr => by
  have : r ≠ r0 := fun e => hr (e ▸ hr0)
  rw [update_of_ne this, h r hr]

/-! ## The header -/

def mg_hdC (hd : ℕ) : Cmd := .seq (mg_zsL (List.replicate hd 14)) (emL [sep])

theorem mg_sum_rep (v : ℕ → ℕ) (r : ℕ) : ∀ n, mg_sum v (List.replicate n r) = n * v r
  | 0 => by simp
  | n + 1 => by rw [List.replicate_succ, mg_sum_cons, mg_sum_rep v r n, Nat.succ_mul]; omega

theorem mg_em_hd (hd : ℕ) {v : ℕ → ℕ} {N m U : ℕ} (hG : mg_G v N m) (hU : 2 * (N * m) ≤ U) :
    sg_Em (mg_hdC hd) v (List.replicate (hd * (2 * (N * m))) zero ++ [sep])
      (hd * (9 * U + 6) + 4) := by
  obtain ⟨-, -, -, -, h14, -, h7, h11, -⟩ := hG
  have := mg_em_zsL U h7 h11 (List.replicate hd 14) (fun r hr => by
    rw [List.eq_of_mem_replicate hr]; exact ⟨by norm_num, by norm_num, by norm_num, by omega⟩)
  rw [mg_sum_rep, h14, List.length_replicate] at this
  exact (this.seq (sg_em_emL [sep] v)).cast rfl (by simp)

/-! ## The ring rows -/

/-- Row `(2L + 1, L, L)`. -/
def mg_r1C : Cmd := mg_rowC ⟨[15, 15], 1, 0, [16, 16]⟩ ⟨[15], 0, 0, [16, 13]⟩ ⟨[15], 0, 0, [16, 13]⟩
/-- Row `(2L, L + 1, L)`. -/
def mg_r2C : Cmd := mg_rowC ⟨[15, 15], 0, 1, [16, 16]⟩ ⟨[15], 1, 0, [17, 13]⟩ ⟨[15], 0, 0, [16, 13]⟩
/-- Row `(2L, B, L)` (`L = B + m - 1`). -/
def mg_r2sC : Cmd :=
  mg_rowC ⟨[15, 15], 0, 1, [16, 16]⟩ ⟨[18], 0, 0, [12, 16, 13]⟩ ⟨[15], 0, 0, [16, 13]⟩

local macro "mg_row" : tactic => `(tactic| (
  refine mg_em_row _ _ _ _ _ (by assumption) (by assumption) _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [mg_V, *] <;> omega))

theorem mg_em_r1 {v : ℕ → ℕ} {N m U L : ℕ} (hG : mg_G v N m) (hU : 2 * (N * m) + N + m ≤ U)
    (h15 : v 15 = L) (h16 : v 16 = N * m - 1 - L) (hL : L < N * m) :
    sg_Em mg_r1C v (mg_tOut (2 * (N * m)) (2 * L + 1, L, L)) (mg_rowT U) := by
  obtain ⟨-, -, -, h13, -, -, h7, h11, -⟩ := hG
  mg_row

theorem mg_em_r2 {v : ℕ → ℕ} {N m U L : ℕ} (hG : mg_G v N m) (hU : 2 * (N * m) + N + m ≤ U)
    (h15 : v 15 = L) (h16 : v 16 = N * m - 1 - L) (h17 : v 17 = N * m - 2 - L)
    (hL : L + 1 < N * m) :
    sg_Em mg_r2C v (mg_tOut (2 * (N * m)) (2 * L, L + 1, L)) (mg_rowT U) := by
  obtain ⟨-, -, -, h13, -, -, h7, h11, -⟩ := hG
  mg_row

theorem mg_em_r2s {v : ℕ → ℕ} {N m U L B : ℕ} (hG : mg_G v N m) (hU : 2 * (N * m) + N + m ≤ U)
    (h15 : v 15 = L) (h16 : v 16 = N * m - 1 - L) (h18 : v 18 = B) (hm : 1 ≤ m)
    (hL : L = B + (m - 1)) (hB : B + m ≤ N * m) :
    sg_Em mg_r2sC v (mg_tOut (2 * (N * m)) (2 * L, B, L)) (mg_rowT U) := by
  obtain ⟨-, -, h12, h13, -, -, h7, h11, -⟩ := hG
  mg_row

/-! ## The ring loops -/

def mg_stepR : Cmd := .seq (.push 15 true) (.seq (Ham.hg_dec 16) (Ham.hg_dec 17))

theorem mg_ex_stepR {W O Q : Str} (E : List SatSym) (v : ℕ → ℕ) :
    ExecLe mg_stepR (st2 W O Q (rv E) v) (.norm (st2 W O Q (rv E)
      (update (update (update v 15 (v 15 + 1)) 16 (v 16 - 1)) 17 (v 17 - 1)))) 5 := by
  have p1 := ex_push_reg (W := W) (O := O) (Q := Q) (r := 15) (by norm_num) (rv E) v
  have p2 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 16) (by norm_num) (rv E)
    (update v 15 (v 15 + 1))
  have p3 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 17) (by norm_num) (rv E)
    (update (update v 15 (v 15 + 1)) 16 (update v 15 (v 15 + 1) 16 - 1))
  exact (p1.seq_norm (p2.seq_norm p3)).cast (by simp) le_rfl

def mg_rIB : Cmd := .seq mg_r1C (.seq mg_r2C mg_stepR)

def mg_rInL : Cmd := .loop (.pop 20 .brk mg_rIB mg_rIB)

theorem mg_ex_rIn (N m U i : ℕ) (hU : 2 * (N * m) + N + m ≤ U) (hi : m * i + m ≤ N * m)
    (W O Q : Str) (u0 : ℕ → ℕ) (hG : mg_G u0 N m) (E : List SatSym) (v : ℕ → ℕ)
    (hv : ∀ r, r ∉ [15, 16, 17, 20] → v r = u0 r) (h15 : v 15 = m * i)
    (h16 : v 16 = N * m - 1 - m * i) (h17 : v 17 = N * m - 2 - m * i) (h20 : v 20 = m - 1) :
    ∃ v', (∀ r, r ∉ [15, 16, 17, 20] → v' r = u0 r) ∧ v' 20 = 0 ∧ v' 15 = m * i + (m - 1) ∧
      v' 16 = N * m - 1 - (m * i + (m - 1)) ∧ v' 17 = N * m - 2 - (m * i + (m - 1)) ∧
      ExecLe mg_rInL (st2 W O Q (rv E) v)
        (.norm (st2 W O Q (rv (E ++ (List.range' 0 (m - 1)).flatMap
          (mg_regO (2 * (N * m)) m i))) v'))
        ((m - 1) * (2 * mg_rowT U + 6) + 2) := by
  obtain ⟨v', ⟨a, b1, b2, b3⟩, z, e⟩ := mg_loop (c := 20) (B := mg_rIB) (by norm_num) W Q
    (fun _ => O) (fun k u => (∀ r, r ∉ [15, 16, 17, 20] → u r = u0 r) ∧ u 15 = m * i + k ∧
      u 16 = N * m - 1 - (m * i + k) ∧ u 17 = N * m - 2 - (m * i + k))
    (mg_regO (2 * (N * m)) m i) (2 * mg_rowT U + 5) (m - 1)
    (fun k u x ⟨a, b1, b2, b3⟩ => ⟨mg_upd_out 20 x a (by simp), by simp [b1], by simp [b2],
      by simp [b3]⟩)
    (fun k u E' hk ⟨a, b1, b2, b3⟩ => by
      have hGu : mg_G u N m := mg_G_out [15, 16, 17, 20] hG a (by decide)
      have r1 := mg_em_r1 (U := U) hGu hU b1 b2 (by omega) W O Q E'
      have r2 := mg_em_r2 (U := U) hGu hU b1 b2 b3 (by omega) W O Q
        (E' ++ mg_tOut (2 * (N * m)) (2 * (m * i + k) + 1, m * i + k, m * i + k))
      have st := mg_ex_stepR (W := W) (O := O) (Q := Q)
        (E' ++ mg_tOut (2 * (N * m)) (2 * (m * i + k) + 1, m * i + k, m * i + k) ++
          mg_tOut (2 * (N * m)) (2 * (m * i + k), m * i + k + 1, m * i + k)) u
      refine ⟨update (update (update u 15 (u 15 + 1)) 16 (u 16 - 1)) 17 (u 17 - 1),
        ⟨mg_upd_out 17 _ (mg_upd_out 16 _ (mg_upd_out 15 _ a (by simp)) (by simp)) (by simp),
        by simp [b1]; omega, by simp [b2]; omega, by simp [b3]; omega⟩, by simp,
        (r1.seq_norm (r2.seq_norm st)).cast (by simp [mg_regO]) (by omega)⟩)
    (m - 1) 0 E v (by omega) ⟨hv, by simp [h15], by simp [h16], by simp [h17]⟩ h20
  exact ⟨v', a, z, by simpa using b1, by simpa using b2, by simpa using b3, e.cast rfl le_rfl⟩

def mg_rB : Cmd :=
  .seq (drain 18) (.seq (copyVia 15 18 11) (.seq (copyVia 12 20 11) (.seq mg_rInL
    (.seq mg_r1C (.seq mg_r2sC mg_stepR)))))

def mg_rOutL : Cmd := .loop (.pop 19 .brk mg_rB mg_rB)

/-- Time of one variable's ring rows. -/
def mg_tRO (U : ℕ) : ℕ := U * (2 * mg_rowT U + 6) + 2 * mg_rowT U + 12 * U + 20

theorem mg_ex_rOut (N m U : ℕ) (hU : 2 * (N * m) + N + m ≤ U) (W O Q : Str) (u0 : ℕ → ℕ)
    (hG : mg_G u0 N m) (E : List SatSym) (v : ℕ → ℕ)
    (hv : ∀ r, r ∉ [15, 16, 17, 18, 19, 20] → v r = u0 r) (h15 : v 15 = 0)
    (h16 : v 16 = N * m - 1) (h17 : v 17 = N * m - 2) (h18 : v 18 = 0) (h20 : v 20 = 0)
    (h19 : v 19 = if m = 0 then 0 else N) :
    ∃ v', (∀ r, r ∉ [15, 16, 17, 18, 19, 20] → v' r = u0 r) ∧
      ExecLe mg_rOutL (st2 W O Q (rv E) v)
        (.norm (st2 W O Q (rv (E ++ mg_ringP (2 * (N * m)) N m)) v'))
        ((if m = 0 then 0 else N) * (mg_tRO U + 1) + 2) := by
  obtain ⟨v', ⟨a, -⟩, -, e⟩ := mg_loop (c := 19) (B := mg_rB) (by norm_num) W Q
    (fun _ => O) (fun i u => (∀ r, r ∉ [15, 16, 17, 18, 19, 20] → u r = u0 r) ∧ u 15 = m * i ∧
      u 16 = N * m - 1 - m * i ∧ u 17 = N * m - 2 - m * i ∧ u 18 ≤ N * m ∧ u 20 = 0)
    (mg_ringO (2 * (N * m)) m) (mg_tRO U) (if m = 0 then 0 else N)
    (fun k u x ⟨a, b1, b2, b3, b4, b5⟩ => ⟨mg_upd_out 19 x a (by simp), by simp [b1],
      by simp [b2], by simp [b3], by simp [b4], by simp [b5]⟩)
    (fun i u E' hi ⟨a, b1, b2, b3, b4, b5⟩ => by
      have hm : m ≠ 0 := fun h => by simp [h] at hi
      rw [if_neg hm] at hi
      have hb : m * i + m ≤ N * m := by
        have := Nat.mul_le_mul_left m (show i + 1 ≤ N by omega)
        rw [Nat.mul_succ, Nat.mul_comm m N] at this; exact this
      have hGu : mg_G u N m := mg_G_out [15, 16, 17, 18, 19, 20] hG a (by decide)
      obtain ⟨-, -, g12, -, -, -, -, g11, -⟩ := id hGu
      have p1 := ex_drain_reg (W := W) (O := O) (Q := Q) (r := 18) (by norm_num) (rv E') u
      have p2 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 15) (b := 18) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E') (update u 18 0)
        (by simp [g11])
      have p3 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 12) (b := 20) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E')
        (update (update u 18 0) 18 (update u 18 0 18 + update u 18 0 15)) (by simp [g11])
      have e2 : update (update (update u 18 0) 18 (update u 18 0 18 + update u 18 0 15)) 20
          (update (update u 18 0) 18 (update u 18 0 18 + update u 18 0 15) 20 +
            update (update u 18 0) 18 (update u 18 0 18 + update u 18 0 15) 12) =
          update (update u 18 (m * i)) 20 (m - 1) := by
        funext r
        by_cases h20 : r = 20
        · subst h20; simp [b5, g12]
        · by_cases h18 : r = 18
          · subst h18; simp [b1]
          · simp [h20, h18]
      rw [e2] at p3
      set w2 := update (update u 18 (m * i)) 20 (m - 1) with hw2
      have hw2o : ∀ r, r ∉ [18, 20] → w2 r = u r := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hw2, hr.1, hr.2]
      have hGw : mg_G w2 N m := mg_G_out [18, 20] hGu hw2o (by decide)
      obtain ⟨v', c1, c20, c15, c16, c17, p4⟩ := mg_ex_rIn N m U i hU hb W O Q w2 hGw E' w2
        (fun _ _ => rfl) (by simp [hw2, b1]) (by simp [hw2, b2]) (by simp [hw2, b3])
        (by simp [hw2])
      have hGv : mg_G v' N m := mg_G_out [15, 16, 17, 20] hGw c1 (by decide)
      have c18 : v' 18 = m * i := by rw [c1 18 (by simp)]; simp [hw2]
      set E1 := E' ++ (List.range' 0 (m - 1)).flatMap (mg_regO (2 * (N * m)) m i)
      have r1 := mg_em_r1 (U := U) hGv hU c15 c16 (by omega) W O Q E1
      have r2 := mg_em_r2s (U := U) hGv hU c15 c16 c18 (by omega) rfl hb W O Q
        (E1 ++ mg_tOut (2 * (N * m)) (2 * (m * i + (m - 1)) + 1, m * i + (m - 1),
          m * i + (m - 1)))
      have st := mg_ex_stepR (W := W) (O := O) (Q := Q)
        (E1 ++ mg_tOut (2 * (N * m)) (2 * (m * i + (m - 1)) + 1, m * i + (m - 1),
          m * i + (m - 1)) ++ mg_tOut (2 * (N * m)) (2 * (m * i + (m - 1)), m * i,
            m * i + (m - 1))) v'
      have hmi : m * (i + 1) = m * i + m := Nat.mul_succ m i
      have ho : ∀ r, r ∉ [15, 16, 17, 18, 19, 20] → v' r = u0 r := fun r hr => by
        have h1 : r ∉ [15, 16, 17, 20] := fun h => hr (by simp at h ⊢; omega)
        have h2 : r ∉ [18, 20] := fun h => hr (by simp at h ⊢; omega)
        rw [c1 r h1, hw2o r h2, a r hr]
      refine ⟨update (update (update v' 15 (v' 15 + 1)) 16 (v' 16 - 1)) 17 (v' 17 - 1),
        ⟨mg_upd_out 17 _ (mg_upd_out 16 _ (mg_upd_out 15 _ ho (by simp)) (by simp)) (by simp),
          by simp [c15]; omega, by simp [c16]; omega, by simp [c17]; omega,
          by simp [c18]; omega, by simp [c20]⟩,
        by simp [c1 19 (by simp), hw2], ?_⟩
      have hmul : (m - 1) * (2 * mg_rowT U + 6) ≤ U * (2 * mg_rowT U + 6) :=
        Nat.mul_le_mul_right _ (by omega)
      refine (p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm (r1.seq_norm
        (r2.seq_norm st)))))).cast (by simp [E1, mg_ringO, mg_spcO]) ?_
      simp only [update_self, update_of_ne (show (15 : ℕ) ≠ 18 by norm_num),
        update_of_ne (show (12 : ℕ) ≠ 18 by norm_num), b1, g12]
      unfold mg_tRO
      omega)
    (if m = 0 then 0 else N) 0 E v (by omega)
    ⟨hv, by simp [h15], by simp [h16], by simp [h17], by simp [h18], h20⟩ h19
  exact ⟨v', a, e.cast (by simp [mg_ringP]) le_rfl⟩

/-- The outer counter `N` if `m > 0`, `0` otherwise. -/
def mg_guardC : Cmd :=
  .pop 9 .skip (.seq (.push 9 true) (copyVia 5 19 11)) (.seq (.push 9 true) (copyVia 5 19 11))

theorem mg_ex_guard {W O Q : Str} {N m : ℕ} (E : List SatSym) (v : ℕ → ℕ) (h9 : v 9 = m)
    (h5 : v 5 = N) (h19 : v 19 = 0) (h11 : v 11 = 0) :
    ExecLe mg_guardC (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv E) (update v 19 (if m = 0 then 0 else N)))) (5 * N + 7) := by
  rcases m with _ | m
  · refine (ExecLe.pop_nil (by rw [st2_reg (by norm_num), h9]; rfl) (ExecLe.skip _)).cast ?_
      (by omega)
    rw [if_pos rfl, ← h19, update_eq_self]
  · have p1 := ex_push_reg (W := W) (O := O) (Q := Q) (r := 9) (by norm_num) (rv E)
      (update v 9 m)
    have e : update (update v 9 m) 9 (update v 9 m 9 + 1) = v := by
      rw [update_idem]; simp [← h9]
    rw [e] at p1
    have p2 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 5) (b := 19) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v h11
    have p3 := (p1.seq_norm p2).cast (r' := .norm (st2 W O Q (rv E)
      (update v 19 (if m + 1 = 0 then 0 else N)))) (by simp [h19, h5]) (show _ ≤ 5 * N + 6 by
        rw [h5]; omega)
    rw [← upd2_reg (by norm_num)] at p3
    exact ExecLe.pop_same (b := true) (s := List.replicate m true)
      (by rw [st2_reg (by norm_num), h9, List.replicate_succ]) p3

def mg_ringC : Cmd :=
  .seq (copyVia 13 16 11) (.seq (Ham.hg_dec 16) (.seq (copyVia 13 17 11) (.seq (Ham.hg_dec 17)
    (.seq (Ham.hg_dec 17) (.seq mg_guardC mg_rOutL)))))

def mg_tR (U : ℕ) : ℕ := U * (mg_tRO U + 1) + 20 * U + 40

theorem mg_ex_ring (N m U : ℕ) (hU : 2 * (N * m) + N + m ≤ U) (W O Q : Str) (E : List SatSym)
    (v : ℕ → ℕ) (hG : mg_G v N m) (hz : ∀ r ∈ [15, 16, 17, 18, 19, 20], v r = 0) :
    ∃ v', (∀ r, r ∉ [15, 16, 17, 18, 19, 20] → v' r = v r) ∧
      ExecLe mg_ringC (st2 W O Q (rv E) v)
        (.norm (st2 W O Q (rv (E ++ mg_ringP (2 * (N * m)) N m)) v')) (mg_tR U) := by
  obtain ⟨h5, h9, -, h13, -, -, -, h11, -⟩ := id hG
  have p1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 13) (b := 16) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v h11
  rw [h13, hz 16 (by simp), Nat.zero_add] at p1
  have p2 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 16) (by norm_num) (rv E)
    (update v 16 (N * m))
  rw [update_idem, update_self] at p2
  set x1 := update v 16 (N * m - 1) with hx1
  have p3 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 13) (b := 17) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) x1 (by simp [hx1, h11])
  rw [show x1 17 + x1 13 = N * m by simp [hx1, h13, hz 17]] at p3
  have p4 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 17) (by norm_num) (rv E)
    (update x1 17 (N * m))
  rw [update_idem, update_self] at p4
  have p5 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 17) (by norm_num) (rv E)
    (update x1 17 (N * m - 1))
  rw [update_idem, update_self, show N * m - 1 - 1 = N * m - 2 by omega] at p5
  set x2 := update x1 17 (N * m - 2) with hx2
  have p6 := mg_ex_guard (W := W) (O := O) (Q := Q) (N := N) (m := m) E x2
    (by simp [hx2, hx1, h9]) (by simp [hx2, hx1, h5]) (by simp [hx2, hx1, hz 19])
    (by simp [hx2, hx1, h11])
  set x3 := update x2 19 (if m = 0 then 0 else N) with hx3
  obtain ⟨v', f1, p7⟩ := mg_ex_rOut N m U hU W O Q v hG E x3
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hx3, hx2, hx1, hr.2.1, hr.2.2.1, hr.2.2.2.2.1])
    (by simp [hx3, hx2, hx1, hz 15]) (by simp [hx3, hx2, hx1]) (by simp [hx3, hx2, hx1])
    (by simp [hx3, hx2, hx1, hz 18]) (by simp [hx3, hx2, hx1, hz 20]) (by simp [hx3])
  refine ⟨v', f1, (p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm (p5.seq_norm
    (p6.seq_norm p7)))))).cast rfl ?_⟩
  have hn : (if m = 0 then 0 else N) * (mg_tRO U + 1) ≤ U * (mg_tRO U + 1) :=
    Nat.mul_le_mul_right _ (by split_ifs <;> omega)
  simp only [hx1, update_of_ne (show (13 : ℕ) ≠ 16 by norm_num), h13]
  unfold mg_tR
  omega

/-! ## The clause rows -/

/-- Row `(2J, M + k, M + k)` (symbol `pos`). -/
def mg_cPC : Cmd := mg_rowC ⟨[23, 23], 0, 1, [24, 24]⟩ ⟨[13, 21], 0, 0, [22]⟩ ⟨[13, 21], 0, 0, [22]⟩
/-- Row `(2J + 1, M + k, M + k)` (symbol `neg`). -/
def mg_cNC : Cmd := mg_rowC ⟨[23, 23], 1, 0, [24, 24]⟩ ⟨[13, 21], 0, 0, [22]⟩ ⟨[13, 21], 0, 0, [22]⟩

theorem mg_em_cP {v : ℕ → ℕ} {N m U J k : ℕ} (hG : mg_G v N m) (hU : 2 * (N * m) + N + m ≤ U)
    (h23 : v 23 = J) (h24 : v 24 = N * m - 1 - k - (J - k)) (h21 : v 21 = k)
    (h22 : v 22 = N * m - 1 - k) (hJ : J < N * m) (hkJ : k ≤ J) (hk : k < N * m) :
    sg_Em mg_cPC v (mg_tOut (2 * (N * m)) (2 * J, N * m + k, N * m + k)) (mg_rowT U) := by
  obtain ⟨-, -, -, h13, -, -, h7, h11, -⟩ := hG
  mg_row

theorem mg_em_cN {v : ℕ → ℕ} {N m U J k : ℕ} (hG : mg_G v N m) (hU : 2 * (N * m) + N + m ≤ U)
    (h23 : v 23 = J) (h24 : v 24 = N * m - 1 - k - (J - k)) (h21 : v 21 = k)
    (h22 : v 22 = N * m - 1 - k) (hJ : J < N * m) (hkJ : k ≤ J) (hk : k < N * m) :
    sg_Em mg_cNC v (mg_tOut (2 * (N * m)) (2 * J + 1, N * m + k, N * m + k)) (mg_rowT U) := by
  obtain ⟨-, -, -, h13, -, -, h7, h11, -⟩ := hG
  mg_row

def mg_stepC : Cmd := .seq (copyVia 9 23 11) (mg_subC 9 24)

theorem mg_ex_stepC {W O Q : Str} (E : List SatSym) (v : ℕ → ℕ) (h11 : v 11 = 0)
    (h25 : v 25 = 0) :
    ExecLe mg_stepC (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv E) (update (update v 23 (v 23 + v 9)) 24 (v 24 - v 9))))
      (14 * v 9 + 10) := by
  have p1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 9) (b := 23) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v h11
  have p2 := mg_ex_sub (W := W) (O := O) (Q := Q) (a := 9) (b := 24) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) E
    (update v 23 (v 23 + v 9)) (by simp [h11]) (by simp [h25])
  exact (p1.seq_norm p2).cast (by simp) (by simp; omega)

def mg_sBr : SatSym → Cmd
  | sep => .brk
  | pos => .seq mg_cPC mg_stepC
  | neg => .seq mg_cNC mg_stepC
  | zero => mg_stepC

def mg_scanL : Cmd := .loop (disp 3 mg_sBr)

/-- Time of one symbol of a clause scan. -/
def mg_tSy (U : ℕ) : ℕ := mg_rowT U + 14 * U + 13

theorem mg_ex_scan (N m U k : ℕ) (hU : 2 * (N * m) + N + m ≤ U) (hk : k < m) (W Q : Str)
    (u0 : ℕ → ℕ) (hG : mg_G u0 N m) (h21 : u0 21 = k) (h22 : u0 22 = N * m - 1 - k) :
    ∀ (c : List SatSym), sep ∉ c → ∀ (rest E : List SatSym) (j : ℕ) (v : ℕ → ℕ),
    (∀ r, r ∉ [23, 24] → v r = u0 r) → v 23 = m * j + k → v 24 = N * m - 1 - k - m * j →
    j + c.length ≤ N →
    ∃ v', (∀ r, r ∉ [23, 24] → v' r = u0 r) ∧ v' 23 = m * (j + c.length) + k ∧
      v' 24 = N * m - 1 - k - m * (j + c.length) ∧
      ExecLe mg_scanL (st2 W ((c ++ sep :: rest).flatMap ic) Q (rv E) v)
        (.norm (st2 W (rest.flatMap ic) Q
          (rv (E ++ mg_scanO (2 * (N * m)) (N * m) m k j c)) v'))
        (c.length * mg_tSy U + 4)
  | [], _, rest, E, j, v, hv, h23, h24, _ => by
    refine ⟨v, hv, by simpa using h23, by simpa using h24, ?_⟩
    have hb := ex_disp (k := 3) (f := mg_sBr) (s := sep) (Q' := rest.flatMap ic)
      (σ := st2 W (([] ++ sep :: rest).flatMap ic) Q (rv E) v) (by simp) (ExecLe.brk _)
    refine (ExecLe.loop_brk hb).cast ?_ (by simp)
    rw [upd2_3]; simp [mg_scanO]
  | a :: c, hc, rest, E, j, v, hv, h23, h24, hl => by
    have ha : a ≠ sep := fun e => hc (e ▸ List.mem_cons_self ..)
    have hc' : sep ∉ c := fun e => hc (List.mem_cons_of_mem _ e)
    simp only [List.length_cons] at hl
    have hGv : mg_G v N m := mg_G_out [23, 24] hG hv (by decide)
    obtain ⟨-, g9, -, -, -, -, -, g11, g25⟩ := id hGv
    have v21 : v 21 = k := by rw [hv 21 (by simp), h21]
    have v22 : v 22 = N * m - 1 - k := by rw [hv 22 (by simp), h22]
    have hb : m * j + m ≤ N * m := by
      have := Nat.mul_le_mul_left m (show j + 1 ≤ N by omega)
      rw [Nat.mul_succ, Nat.mul_comm m N] at this; exact this
    have h24' : v 24 = N * m - 1 - k - (m * j + k - k) := by rw [h24]; congr 1; omega
    set O' := (c ++ sep :: rest).flatMap ic
    set u2 := update (update v 23 (v 23 + v 9)) 24 (v 24 - v 9)
    have st : ∀ E', ExecLe mg_stepC (st2 W O' Q (rv E') v) (.norm (st2 W O' Q (rv E') u2))
        (14 * U + 10) := fun E' =>
      (mg_ex_stepC (W := W) (O := O') (Q := Q) E' v g11 g25).cast rfl (by rw [g9]; omega)
    have hbr : ExecLe (mg_sBr a) (st2 W O' Q (rv E) v)
        (.norm (st2 W O' Q (rv (E ++ mg_symO (2 * (N * m)) (N * m) m k j a)) u2))
        (mg_rowT U + 14 * U + 10) := by
      cases a with
      | sep => exact absurd rfl ha
      | zero => exact (st E).cast (by simp [mg_symO]) (by omega)
      | pos =>
        exact ((mg_em_cP (U := U) hGv hU h23 h24' v21 v22 (by omega) (by omega) (by omega) W O' Q
          E).seq_norm (st _)).cast rfl le_rfl
      | neg =>
        exact ((mg_em_cN (U := U) hGv hU h23 h24' v21 v22 (by omega) (by omega) (by omega) W O' Q
          E).seq_norm (st _)).cast rfl le_rfl
    have hd := ex_disp (k := 3) (f := mg_sBr) (s := a) (Q' := O')
      (σ := st2 W ((a :: c ++ sep :: rest).flatMap ic) Q (rv E) v) (by simp [O'])
      (by rw [upd2_3]; exact hbr)
    obtain ⟨v', f1, f2, f3, ih⟩ := mg_ex_scan N m U k hU hk W Q u0 hG h21 h22 c hc' rest
      (E ++ mg_symO (2 * (N * m)) (N * m) m k j a) (j + 1) u2
      (mg_upd_out 24 _ (mg_upd_out 23 _ hv (by simp)) (by simp))
      (by simp [u2, h23, g9, Nat.mul_succ]; omega)
      (by simp [u2, h24, g9, Nat.mul_succ]; omega) (by omega)
    have ej : j + 1 + c.length = j + (a :: c).length := by simp; omega
    refine ⟨v', f1, by rw [f2, ej], by rw [f3, ej],
      (ExecLe.loop_norm hd ih).cast ?_ ?_⟩
    · simp [mg_scanO, List.append_assoc]
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; unfold mg_tSy; omega

theorem mg_drop_eq (cs : List (List SatSym)) (k : ℕ) (hk : k < cs.length) :
    (cs.drop k).flatMap (· ++ [sep]) =
      cs.getD k [] ++ sep :: (cs.drop (k + 1)).flatMap (· ++ [sep]) := by
  conv_lhs => rw [List.drop_eq_getElem_cons hk]
  rw [List.flatMap_cons, List.getD_eq_getElem _ _ hk]; simp

def mg_cB : Cmd :=
  .seq mg_scanL (.seq (.push 21 true) (.seq (Ham.hg_dec 22) (.seq (drain 23)
    (.seq (copyVia 21 23 11) (.seq (drain 24) (copyVia 22 24 11))))))

def mg_cOutL : Cmd := .loop (.pop 33 .brk mg_cB mg_cB)

/-- Time of the rows of one clause. -/
def mg_tCO (U : ℕ) : ℕ := U * mg_tSy U + 14 * U + 30

theorem mg_ex_cOut (N m U : ℕ) (hU : 2 * (N * m) + N + m ≤ U) (W Q : Str)
    (cs : List (List SatSym)) (hcs : ∀ c ∈ cs, sep ∉ c ∧ c.length ≤ N) (hlen : cs.length = m)
    (u0 : ℕ → ℕ) (hG : mg_G u0 N m) (E : List SatSym) (v : ℕ → ℕ)
    (hv : ∀ r, r ∉ [21, 22, 23, 24, 33] → v r = u0 r) (h21 : v 21 = 0)
    (h22 : v 22 = N * m - 1) (h23 : v 23 = 0) (h24 : v 24 = N * m - 1) (h33 : v 33 = m) :
    ∃ v', (∀ r, r ∉ [21, 22, 23, 24, 33] → v' r = u0 r) ∧
      ExecLe mg_cOutL (st2 W ((cs.flatMap (· ++ [sep])).flatMap ic) Q (rv E) v)
        (.norm (st2 W [] Q (rv (E ++ mg_clP (2 * (N * m)) (N * m) m cs)) v'))
        (m * (mg_tCO U + 1) + 2) := by
  obtain ⟨v', ⟨a, -⟩, -, e⟩ := mg_loop (c := 33) (B := mg_cB) (by norm_num) W Q
    (fun j => ((cs.drop j).flatMap (· ++ [sep])).flatMap ic)
    (fun k u => (∀ r, r ∉ [21, 22, 23, 24, 33] → u r = u0 r) ∧ u 21 = k ∧
      u 22 = N * m - 1 - k ∧ u 23 = k ∧ u 24 = N * m - 1 - k)
    (fun k => mg_scanO (2 * (N * m)) (N * m) m k 0 (cs.getD k [])) (mg_tCO U) m
    (fun k u x ⟨a, b1, b2, b3, b4⟩ => ⟨mg_upd_out 33 x a (by simp), by simp [b1],
      by simp [b2], by simp [b3], by simp [b4]⟩)
    (fun k u E' hk ⟨a, b1, b2, b3, b4⟩ => by
      have hkc : k < cs.length := by omega
      have hmem : cs.getD k [] ∈ cs := by
        rw [List.getD_eq_getElem _ _ hkc]; exact List.getElem_mem hkc
      obtain ⟨hsep, hcl⟩ := hcs _ hmem
      have hGu : mg_G u N m := mg_G_out [21, 22, 23, 24, 33] hG a (by decide)
      obtain ⟨-, -, -, -, -, -, -, g11, -⟩ := id hGu
      rw [show ((cs.drop k).flatMap (· ++ [sep])).flatMap ic =
        (cs.getD k [] ++ sep :: (cs.drop (k + 1)).flatMap (· ++ [sep])).flatMap ic by
          rw [mg_drop_eq cs k hkc]]
      obtain ⟨v1, c1, c23, c24, q1⟩ := mg_ex_scan N m U k hU (by omega) W Q u hGu b1 b2
        (cs.getD k []) hsep ((cs.drop (k + 1)).flatMap (· ++ [sep])) E' 0 u (fun _ _ => rfl)
        (by simp [b3]) (by simp [b4]) (by omega)
      set E1 := E' ++ mg_scanO (2 * (N * m)) (N * m) m k 0 (cs.getD k [])
      set O1 := ((cs.drop (k + 1)).flatMap (· ++ [sep])).flatMap ic
      have q2 := ex_push_reg (W := W) (O := O1) (Q := Q) (r := 21) (by norm_num) (rv E1) v1
      set x1 := update v1 21 (v1 21 + 1) with hx1
      have q3 := sg_ex_dec (W := W) (O := O1) (Q := Q) (r := 22) (by norm_num) (rv E1) x1
      set x2 := update x1 22 (x1 22 - 1) with hx2
      have q4 := ex_drain_reg (W := W) (O := O1) (Q := Q) (r := 23) (by norm_num) (rv E1) x2
      set x3 := update x2 23 0 with hx3
      have q5 := ex_copy_reg (W := W) (O := O1) (Q := Q) (a := 21) (b := 23) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E1) x3
        (by simp [hx3, hx2, hx1, c1 11 (by simp), g11])
      set x4 := update x3 23 (x3 23 + x3 21) with hx4
      have q6 := ex_drain_reg (W := W) (O := O1) (Q := Q) (r := 24) (by norm_num) (rv E1) x4
      set x5 := update x4 24 0 with hx5
      have q7 := ex_copy_reg (W := W) (O := O1) (Q := Q) (a := 22) (b := 24) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E1) x5
        (by simp [hx5, hx4, hx3, hx2, hx1, c1 11 (by simp), g11])
      have v21 : v1 21 = k := by rw [c1 21 (by simp), b1]
      have v22 : v1 22 = N * m - 1 - k := by rw [c1 22 (by simp), b2]
      have v33 : v1 33 = u 33 := c1 33 (by simp)
      refine ⟨update x5 24 (x5 24 + x5 22), ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩, ?_,
        (q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm (q5.seq_norm (q6.seq_norm
          q7)))))).cast rfl ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hx5, hx4, hx3, hx2, hx1, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2,
          c1 r (by simp; omega), a r (by simp; omega)]
      · simp [hx5, hx4, hx3, hx2, hx1, v21]
      · simp [hx5, hx4, hx3, hx2, hx1, v22]; omega
      · simp [hx5, hx4, hx3, hx2, hx1, v21]
      · simp [hx5, hx4, hx3, hx2, hx1, v22]; omega
      · simp [hx5, hx4, hx3, hx2, hx1, v33]
      · have hmc : m * (0 + (cs.getD k []).length) ≤ m * N :=
          Nat.mul_le_mul_left m (by omega)
        have hl : (cs.getD k []).length * mg_tSy U ≤ U * mg_tSy U :=
          Nat.mul_le_mul_right _ (by omega)
        have t1 : x2 23 = m * (0 + (cs.getD k []).length) + k := by simp [hx2, hx1, c23]
        have t2 : x3 21 = k + 1 := by simp [hx3, hx2, hx1, v21]
        have t3 : x4 24 = N * m - 1 - k - m * (0 + (cs.getD k []).length) := by
          simp [hx4, hx3, hx2, hx1, c24]
        have t4 : x5 22 = N * m - 1 - k - 1 := by simp [hx5, hx4, hx3, hx2, hx1, v22]
        rw [t1, t2, t3, t4]
        rw [Nat.mul_comm m N] at hmc
        unfold mg_tCO
        omega)
    m 0 E v (by omega) ⟨hv, h21, by simp [h22], h23, by simp [h24]⟩ h33
  refine ⟨v', a, e.cast ?_ le_rfl⟩
  rw [Nat.zero_add, List.drop_eq_nil_of_le (by omega)]
  simp [mg_clP]

def mg_clC : Cmd :=
  .seq (copyVia 13 22 11) (.seq (Ham.hg_dec 22) (.seq (copyVia 13 24 11) (.seq (Ham.hg_dec 24)
    (.seq (copyVia 2 3 11) (.seq (copyVia 9 33 11) mg_cOutL)))))

def mg_tC (U : ℕ) : ℕ := U * (mg_tCO U + 1) + 30 * U + 40

theorem mg_ex_cl (N m U : ℕ) (hU : 2 * (N * m) + N + m ≤ U) (W Q : Str)
    (cs : List (List SatSym)) (hcs : ∀ c ∈ cs, sep ∉ c ∧ c.length ≤ N) (hlen : cs.length = m)
    (hW : W = (cs.flatMap (· ++ [sep])).flatMap ic) (hWl : W.length ≤ 2 * N)
    (E : List SatSym) (v : ℕ → ℕ) (hG : mg_G v N m)
    (hz : ∀ r ∈ [21, 22, 23, 24, 33], v r = 0) :
    ∃ v', (∀ r, r ∉ [21, 22, 23, 24, 33] → v' r = v r) ∧
      ExecLe mg_clC (st2 W [] Q (rv E) v)
        (.norm (st2 W [] Q (rv (E ++ mg_clP (2 * (N * m)) (N * m) m cs)) v')) (mg_tC U) := by
  obtain ⟨h5, h9, -, h13, -, -, -, h11, -⟩ := id hG
  have p1 := ex_copy_reg (W := W) (O := []) (Q := Q) (a := 13) (b := 22) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v h11
  rw [h13, hz 22 (by simp), Nat.zero_add] at p1
  have p2 := sg_ex_dec (W := W) (O := []) (Q := Q) (r := 22) (by norm_num) (rv E)
    (update v 22 (N * m))
  rw [update_idem, update_self] at p2
  set x1 := update v 22 (N * m - 1) with hx1
  have p3 := ex_copy_reg (W := W) (O := []) (Q := Q) (a := 13) (b := 24) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) x1 (by simp [hx1, h11])
  rw [show x1 24 + x1 13 = N * m by simp [hx1, h13, hz 24]] at p3
  have p4 := sg_ex_dec (W := W) (O := []) (Q := Q) (r := 24) (by norm_num) (rv E)
    (update x1 24 (N * m))
  rw [update_idem, update_self] at p4
  set x2 := update x1 24 (N * m - 1) with hx2
  have p5 := sg_ex_cpW3 (W := W) (Q := Q) (rv E) x2 (by simp [hx2, hx1, h11])
  have p6 := ex_copy_reg (W := W) (O := W) (Q := Q) (a := 9) (b := 33) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) x2 (by simp [hx2, hx1, h11])
  rw [show x2 33 + x2 9 = m by simp [hx2, hx1, h9, hz 33]] at p6
  set x3 := update x2 33 m with hx3
  have p7 := mg_ex_cOut N m U hU W Q cs hcs hlen v hG E x3
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hx3, hx2, hx1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2])
    (by simp [hx3, hx2, hx1, hz 21]) (by simp [hx3, hx2, hx1]) (by simp [hx3, hx2, hx1, hz 23])
    (by simp [hx3, hx2, hx1]) (by simp [hx3])
  obtain ⟨v', f1, p7⟩ := p7
  rw [← hW] at p7
  refine ⟨v', f1, (p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm (p5.seq_norm
    (p6.seq_norm p7)))))).cast rfl ?_⟩
  have hn : m * (mg_tCO U + 1) ≤ U * (mg_tCO U + 1) := Nat.mul_le_mul_right _ (by omega)
  simp only [hx2, hx1, update_of_ne (show (13 : ℕ) ≠ 22 by norm_num),
    update_of_ne (show (9 : ℕ) ≠ 22 by norm_num), update_of_ne (show (9 : ℕ) ≠ 24 by norm_num),
    h13, h9]
  unfold mg_tC
  omega

/-! ## The garbage rows -/

/-- Row `(x, M + m + t, M + m + t)`. -/
def mg_gRC : Cmd := mg_rowC ⟨[26], 0, 0, [27]⟩ ⟨[13, 9, 28], 0, 0, [29]⟩ ⟨[13, 9, 28], 0, 0, [29]⟩

theorem mg_em_gR {v : ℕ → ℕ} {N m U x t : ℕ} (hG : mg_G v N m) (hU : 2 * (N * m) + N + m ≤ U)
    (h26 : v 26 = x) (h27 : v 27 = 2 * (N * m) - 1 - x) (hx : x < 2 * (N * m)) (h28 : v 28 = t)
    (h29 : v 29 = N * m - m - 1 - t) (ht : t < N * m - m) :
    sg_Em mg_gRC v (mg_tOut (2 * (N * m)) (x, N * m + m + t, N * m + m + t)) (mg_rowT U) := by
  obtain ⟨-, h9, -, h13, -, -, h7, h11, -⟩ := hG
  mg_row

def mg_gIB : Cmd := .seq mg_gRC (.seq (.push 28 true) (Ham.hg_dec 29))

def mg_gInL : Cmd := .loop (.pop 32 .brk mg_gIB mg_gIB)

theorem mg_ex_gIn (N m U x : ℕ) (hU : 2 * (N * m) + N + m ≤ U) (hx : x < 2 * (N * m))
    (W O Q : Str) (u0 : ℕ → ℕ) (hG : mg_G u0 N m) (h26 : u0 26 = x)
    (h27 : u0 27 = 2 * (N * m) - 1 - x) (E : List SatSym) (v : ℕ → ℕ)
    (hv : ∀ r, r ∉ [28, 29, 32] → v r = u0 r) (h28 : v 28 = 0) (h29 : v 29 = N * m - m - 1)
    (h32 : v 32 = N * m - m) :
    ∃ v', (∀ r, r ∉ [28, 29, 32] → v' r = u0 r) ∧ v' 28 = N * m - m ∧ v' 29 ≤ U ∧
      v' 32 = 0 ∧
      ExecLe mg_gInL (st2 W O Q (rv E) v)
        (.norm (st2 W O Q (rv (E ++ (List.range' 0 (N * m - m)).flatMap
          (fun t => mg_tOut (2 * (N * m)) (x, N * m + m + t, N * m + m + t)))) v'))
        ((N * m - m) * (mg_rowT U + 4) + 2) := by
  obtain ⟨v', ⟨a, b1, b2⟩, z, e⟩ := mg_loop (c := 32) (B := mg_gIB) (by norm_num) W Q
    (fun _ => O) (fun t u => (∀ r, r ∉ [28, 29, 32] → u r = u0 r) ∧ u 28 = t ∧
      u 29 = N * m - m - 1 - t)
    (fun t => mg_tOut (2 * (N * m)) (x, N * m + m + t, N * m + m + t)) (mg_rowT U + 3)
    (N * m - m)
    (fun k u y ⟨a, b1, b2⟩ => ⟨mg_upd_out 32 y a (by simp), by simp [b1], by simp [b2]⟩)
    (fun t u E' ht ⟨a, b1, b2⟩ => by
      have hGu : mg_G u N m := mg_G_out [28, 29, 32] hG a (by decide)
      have r1 := mg_em_gR (U := U) hGu hU (by rw [a 26 (by simp), h26])
        (by rw [a 27 (by simp), h27]) hx b1 b2 ht W O Q E'
      have p1 := ex_push_reg (W := W) (O := O) (Q := Q) (r := 28) (by norm_num)
        (rv (E' ++ mg_tOut (2 * (N * m)) (x, N * m + m + t, N * m + m + t))) u
      have p2 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 29) (by norm_num)
        (rv (E' ++ mg_tOut (2 * (N * m)) (x, N * m + m + t, N * m + m + t)))
        (update u 28 (u 28 + 1))
      refine ⟨update (update u 28 (u 28 + 1)) 29 (update u 28 (u 28 + 1) 29 - 1),
        ⟨mg_upd_out 29 _ (mg_upd_out 28 _ a (by simp)) (by simp), by simp [b1],
          by simp [b2]; omega⟩, by simp, (r1.seq_norm (p1.seq_norm p2)).cast rfl (by omega)⟩)
    (N * m - m) 0 E v (by omega) ⟨hv, h28, by simp [h29]⟩ h32
  exact ⟨v', a, by simpa using b1, by rw [b2]; omega, z, e.cast rfl le_rfl⟩

def mg_gB : Cmd :=
  .seq (drain 28) (.seq (drain 29) (.seq (copyVia 30 29 11) (.seq (Ham.hg_dec 29)
    (.seq (copyVia 30 32 11) (.seq mg_gInL (.seq (.push 26 true) (Ham.hg_dec 27)))))))

def mg_gOutL : Cmd := .loop (.pop 31 .brk mg_gB mg_gB)

/-- Time of the garbage rows of one tip. -/
def mg_tGO (U : ℕ) : ℕ := U * (mg_rowT U + 4) + 14 * U + 20

theorem mg_ex_gOut (N m U : ℕ) (hU : 2 * (N * m) + N + m ≤ U) (W O Q : Str) (u0 : ℕ → ℕ)
    (hG : mg_G u0 N m) (E : List SatSym) (v : ℕ → ℕ)
    (hv : ∀ r, r ∉ [26, 27, 28, 29, 31, 32] → v r = u0 r) (h26 : v 26 = 0)
    (h27 : v 27 = 2 * (N * m) - 1) (h28 : v 28 = 0) (h29 : v 29 = 0) (h32 : v 32 = 0)
    (h31 : v 31 = 2 * (N * m)) :
    ∃ v', (∀ r, r ∉ [26, 27, 28, 29, 31, 32] → v' r = u0 r) ∧
      ExecLe mg_gOutL (st2 W O Q (rv E) v)
        (.norm (st2 W O Q (rv (E ++ mg_garP (2 * (N * m)) (N * m) m)) v'))
        (2 * (N * m) * (mg_tGO U + 1) + 2) := by
  obtain ⟨v', ⟨a, -⟩, -, e⟩ := mg_loop (c := 31) (B := mg_gB) (by norm_num) W Q
    (fun _ => O) (fun x u => (∀ r, r ∉ [26, 27, 28, 29, 31, 32] → u r = u0 r) ∧ u 26 = x ∧
      u 27 = 2 * (N * m) - 1 - x ∧ u 28 ≤ U ∧ u 29 ≤ U ∧ u 32 = 0)
    (fun x => (List.range' 0 (N * m - m)).flatMap
      (fun t => mg_tOut (2 * (N * m)) (x, N * m + m + t, N * m + m + t))) (mg_tGO U)
    (2 * (N * m))
    (fun k u y ⟨a, b1, b2, b3, b4, b5⟩ => ⟨mg_upd_out 31 y a (by simp), by simp [b1],
      by simp [b2], by simp [b3], by simp [b4], by simp [b5]⟩)
    (fun x u E' hx ⟨a, b1, b2, b3, b4, b5⟩ => by
      have hGu : mg_G u N m := mg_G_out [26, 27, 28, 29, 31, 32] hG a (by decide)
      obtain ⟨-, -, -, -, -, g30, -, g11, -⟩ := id hGu
      have p1 := ex_drain_reg (W := W) (O := O) (Q := Q) (r := 28) (by norm_num) (rv E') u
      have p2 := ex_drain_reg (W := W) (O := O) (Q := Q) (r := 29) (by norm_num) (rv E')
        (update u 28 0)
      have p3 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 30) (b := 29) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E')
        (update (update u 28 0) 29 0) (by simp [g11])
      rw [show update (update u 28 0) 29 0 29 + update (update u 28 0) 29 0 30 = N * m - m by
        simp [g30], update_idem] at p3
      have p4 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 29) (by norm_num) (rv E')
        (update (update u 28 0) 29 (N * m - m))
      rw [update_idem, update_self] at p4
      set w1 := update (update u 28 0) 29 (N * m - m - 1) with hw1
      have p5 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 30) (b := 32) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E') w1 (by simp [hw1, g11])
      rw [show w1 32 + w1 30 = N * m - m by simp [hw1, g30, b5]] at p5
      set w2 := update w1 32 (N * m - m) with hw2
      have hw2o : ∀ r, r ∉ [28, 29, 32] → w2 r = u r := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hw2, hw1, hr.1, hr.2.1, hr.2.2]
      obtain ⟨v1, c1, c28, c29, c32, p6⟩ := mg_ex_gIn N m U x hU hx W O Q u hGu b1 b2 E' w2
        hw2o (by simp [hw2, hw1]) (by simp [hw2, hw1]) (by simp [hw2])
      set E1 := E' ++ (List.range' 0 (N * m - m)).flatMap
        (fun t => mg_tOut (2 * (N * m)) (x, N * m + m + t, N * m + m + t))
      have p7 := ex_push_reg (W := W) (O := O) (Q := Q) (r := 26) (by norm_num) (rv E1) v1
      have p8 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 27) (by norm_num) (rv E1)
        (update v1 26 (v1 26 + 1))
      have v26 : v1 26 = x := by rw [c1 26 (by simp), b1]
      have v27 : v1 27 = 2 * (N * m) - 1 - x := by rw [c1 27 (by simp), b2]
      refine ⟨update (update v1 26 (v1 26 + 1)) 27 (update v1 26 (v1 26 + 1) 27 - 1),
        ⟨fun r hr => ?_, by simp [v26], by simp [v27]; omega, by simp [c28]; omega,
          by simp [c29], by simp [c32]⟩,
        by simp [c1 31 (by simp)], ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [hr.1, hr.2.1, c1 r (by simp; omega), a r (by simp; omega)]
      · have hmul : (N * m - m) * (mg_rowT U + 4) ≤ U * (mg_rowT U + 4) :=
          Nat.mul_le_mul_right _ (by omega)
        refine (p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm (p5.seq_norm (p6.seq_norm
          (p7.seq_norm p8))))))).cast (by simp [E1]) ?_
        simp only [update_self, update_of_ne (show (30 : ℕ) ≠ 29 by norm_num),
          update_of_ne (show (30 : ℕ) ≠ 28 by norm_num), g30]
        rw [show update u 28 0 29 = u 29 by simp]
        have : w1 30 = N * m - m := by simp [hw1, g30]
        unfold mg_tGO
        omega)
    (2 * (N * m)) 0 E v (by omega) ⟨hv, h26, by simp [h27], by simp [h28], by simp [h29], h32⟩
    h31
  exact ⟨v', a, e.cast (by simp [mg_garP]) le_rfl⟩

def mg_garC : Cmd :=
  .seq (copyVia 14 27 11) (.seq (Ham.hg_dec 27) (.seq (copyVia 14 31 11) mg_gOutL))

def mg_tG (U : ℕ) : ℕ := U * (mg_tGO U + 1) + 20 * U + 20

theorem mg_ex_gar (N m U : ℕ) (hU : 2 * (N * m) + N + m ≤ U) (W O Q : Str) (E : List SatSym)
    (v : ℕ → ℕ) (hG : mg_G v N m) (hz : ∀ r ∈ [26, 27, 28, 29, 31, 32], v r = 0) :
    ∃ v', ExecLe mg_garC (st2 W O Q (rv E) v)
        (.norm (st2 W O Q (rv (E ++ mg_garP (2 * (N * m)) (N * m) m)) v')) (mg_tG U) := by
  obtain ⟨-, -, -, -, h14, -, -, h11, -⟩ := id hG
  have p1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 14) (b := 27) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) v h11
  rw [h14, hz 27 (by simp), Nat.zero_add] at p1
  have p2 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 27) (by norm_num) (rv E)
    (update v 27 (2 * (N * m)))
  rw [update_idem, update_self] at p2
  set x1 := update v 27 (2 * (N * m) - 1) with hx1
  have p3 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 14) (b := 31) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) x1 (by simp [hx1, h11])
  rw [show x1 31 + x1 14 = 2 * (N * m) by simp [hx1, h14, hz 31]] at p3
  set x2 := update x1 31 (2 * (N * m)) with hx2
  obtain ⟨v', -, p4⟩ := mg_ex_gOut N m U hU W O Q v hG E x2
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [hx2, hx1, hr.2.1, hr.2.2.2.2.1])
    (by simp [hx2, hx1, hz 26]) (by simp [hx2, hx1]) (by simp [hx2, hx1, hz 28])
    (by simp [hx2, hx1, hz 29]) (by simp [hx2, hx1, hz 32]) (by simp [hx2])
  refine ⟨v', (p1.seq_norm (p2.seq_norm (p3.seq_norm p4))).cast rfl ?_⟩
  have hn : 2 * (N * m) * (mg_tGO U + 1) ≤ U * (mg_tGO U + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [hx1, update_of_ne (show (14 : ℕ) ≠ 27 by norm_num), h14]
  unfold mg_tG
  omega

/-! ## The whole program -/

/-- The reduction program (header `zero^(hd q)`). -/
def mg_redCmd (hd : ℕ) : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq (copyVia 2 4 11) (.seq (.push 5 true)
  (.seq sg_cntLoop (.seq mg_setC (.seq (mg_hdC hd) (.seq mg_ringC (.seq mg_clC mg_garC)))))))))

/-- The register bound. -/
def mg_U (n : ℕ) : ℕ := 4 * ((n + 1) * (n + 1))

/-- Time bound of the program. -/
def mg_Tred (n : ℕ) : ℕ :=
  100 * (n + 1) + 100 + mg_tS (mg_U n) + 3 * (9 * mg_U n + 6) + 4 + mg_tR (mg_U n) +
    mg_tC (mg_U n) + mg_tG (mg_U n)

set_option maxHeartbeats 1600000 in
theorem mg_exec_redCmd (hd : ℕ) (hhd : hd ≤ 3) (x : Str) : ∃ σ', ExecLe (mg_redCmd hd)
    (init [x]).stk (.norm σ') (mg_Tred x.length) ∧
    σ' 1 = ((mg_out hd (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  set L := trunc w
  set W := L.flatMap ic
  set m := mC w
  set N := NV w
  set V := x.length + 1 with hVd
  set U := mg_U x.length with hUd
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have hLw : L.length ≤ w.length := length_trunc_le w
  have hmw : m ≤ w.length := length_clauses_le w
  have hW : W.length = 2 * L.length := length_flatMap_ic L
  have hN : N = L.length + 1 := rfl
  have hNV : N ≤ V := by omega
  have hmV : m ≤ V := by omega
  have hU : 2 * (N * m) + N + m ≤ U := by
    have h1 : N * m ≤ V * V := Nat.mul_le_mul hNV hmV
    have h2 : V ≤ V * V := Nat.le_mul_of_pos_left V (by omega)
    rw [hUd, mg_U, ← hVd]; omega
  have hcnt : (L.flatMap Clique.hg).length = m := by
    simp only [L, hg_trunc, List.length_replicate]; rfl
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ1 := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := exec_trimC_word 4 w σ1 (by simp [σ1, he 4 (by decide)])
  set σ2 := update σ1 4 ((L.flatMap ic).reverse)
  have p3 := exec_move (a := 4) (b := 2) (by decide) _ σ2 rfl
  have e3 : update (update σ2 4 []) 2 ((σ2 4).reverse ++ σ2 2) =
      Clique.st2 W [] [] (rv []) fun _ => 0 := by
    funext j
    simp only [σ2, σ1, Clique.st2, update_apply, rv_nil, W, L]
    split_ifs <;> simp_all
  rw [e3] at p3
  -- counting
  have q1 := ex_copyW (W := W) (O := []) (rv []) (fun _ : ℕ => (0 : ℕ)) rfl
  have q2 := ex_push_reg (W := W) (O := []) (Q := W) (r := 5) (by norm_num) (rv [])
    (fun _ : ℕ => (0 : ℕ))
  obtain ⟨v1, c1, c2, c3, q3⟩ := sg_ex_cnt W [] L []
    (update (fun _ : ℕ => (0 : ℕ)) 5 ((fun _ : ℕ => (0 : ℕ)) 5 + 1))
  have v1_5 : v1 5 = N := by rw [c2]; simp [hN]; omega
  have v1_9 : v1 9 = m := by rw [c3, hcnt]; simp
  have v1_o : ∀ r, r ≠ 5 → r ≠ 9 → v1 r = 0 := fun r a b => by rw [c1 r a b]; simp [a]
  -- the phases
  obtain ⟨v2, hG2, f2, q4⟩ := mg_ex_set N m U hU W [] [] [] v1 v1_5 v1_9 v1_o
  have q5 := mg_em_hd hd hG2 (U := U) (by omega) W [] [] []
  set E1 := [] ++ (List.replicate (hd * (2 * (N * m))) zero ++ [sep])
  obtain ⟨v3, f3, q6⟩ := mg_ex_ring N m U hU W [] [] E1 v2 hG2 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [f2 r (by omega) (by omega) (by omega) (by omega), v1_o r (by omega) (by omega)])
  set E2 := E1 ++ mg_ringP (2 * (N * m)) N m
  have hG3 : mg_G v3 N m := mg_G_out [15, 16, 17, 18, 19, 20] hG2 f3 (by decide)
  obtain ⟨v4, f4, q7⟩ := mg_ex_cl N m U hU W [] (clauses w)
    (fun c hc => by
      refine ⟨sep_not_mem_clauses w c hc, ?_⟩
      have := Ham.hg_len_le_flatMap hc
      simp only [N, NV, trunc] at this ⊢; omega)
    rfl rfl (by rw [hW, hN]; omega) E2 v3 hG3 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [f3 r (by simp; omega), f2 r (by omega) (by omega) (by omega) (by omega),
      v1_o r (by omega) (by omega)])
  set E3 := E2 ++ mg_clP (2 * (N * m)) (N * m) m (clauses w)
  have hG4 : mg_G v4 N m := mg_G_out [21, 22, 23, 24, 33] hG3 f4 (by decide)
  obtain ⟨v5, q8⟩ := mg_ex_gar N m U hU W [] [] E3 v4 hG4 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [f4 r (by simp; omega), f3 r (by simp; omega),
      f2 r (by omega) (by omega) (by omega) (by omega), v1_o r (by omega) (by omega)])
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm (q1.seq_norm (q2.seq_norm
    (q3.seq_norm (q4.seq_norm (q5.seq_norm (q6.seq_norm (q7.seq_norm q8)))))))))).cast rfl ?_, ?_⟩
  · have tσ : (σ2 4).length = W.length := by simp [σ2, W]
    rw [tσ, hW]
    have hh : hd * (9 * U + 6) ≤ 3 * (9 * U + 6) := Nat.mul_le_mul_right _ hhd
    unfold mg_Tred
    rw [← hUd, ← hVd]
    omega
  · simp only [st2_1, rv, E3, E2, E1]
    rw [mg_out_eq hd w, show qB w = 2 * (N * m) by unfold qB; ring]
    simp only [List.append_assoc, List.nil_append]
    rfl

theorem mg_Tred_le (n : ℕ) : mg_Tred n ≤ tb 22 n := by
  unfold mg_Tred mg_U tb
  set V := n + 1
  set P := n + 2
  have e : 100 * V + 100 + mg_tS (4 * (V * V)) + 3 * (9 * (4 * (V * V)) + 6) + 4 +
      mg_tR (4 * (V * V)) + mg_tC (4 * (V * V)) + mg_tG (4 * (V * V)) =
      42368 * V ^ 6 + 14720 * V ^ 4 + 1916 * V ^ 2 + 100 * V + 282 := by
    unfold mg_tS mg_tR mg_tRO mg_tC mg_tCO mg_tSy mg_tG mg_tGO mg_rowT mg_ohT; ring
  rw [e]
  have hVP : V ≤ P := by omega
  have h1 : 1 ≤ P := by omega
  have k6 : V ^ 6 ≤ P ^ 6 := Nat.pow_le_pow_left hVP 6
  have k4 : V ^ 4 ≤ P ^ 6 :=
    le_trans (Nat.pow_le_pow_left hVP 4) (Nat.pow_le_pow_right h1 (by norm_num))
  have k2 : V ^ 2 ≤ P ^ 6 :=
    le_trans (Nat.pow_le_pow_left hVP 2) (Nat.pow_le_pow_right h1 (by norm_num))
  have k1 : V ≤ P ^ 6 := le_trans hVP (by
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ 6 := Nat.pow_le_pow_right h1 (by norm_num))
  have k0 : 1 ≤ P ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 ^ 16 ≤ P ^ 16 := Nat.pow_le_pow_left (by omega) 16
  have h3 : 2 ^ 16 * P ^ 6 ≤ P ^ 16 * P ^ 6 := Nat.mul_le_mul h2 le_rfl
  have e2 : P ^ 22 = P ^ 16 * P ^ 6 := by ring
  rw [e2]
  norm_num at h3
  generalize P ^ 16 * P ^ 6 = A at *
  generalize P ^ 6 = B at *
  generalize V ^ 6 = a6 at *
  generalize V ^ 4 = a4 at *
  generalize V ^ 2 = a2 at *
  clear_value V P
  omega

/-! ## The reductions -/

theorem mg_computable (hd : ℕ) (hhd : hd ≤ 3) (F : List SatSym → List SatSym)
    (hF : ∀ w, F w = mg_out hd w) :
    Nonempty (Turing.TM2ComputableInPolyTime (Millennium.fin_encoding_string SatSym).encode
      (Millennium.fin_encoding_string SatSym).encode F) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    (mg_redCmd hd) 1 22 (fun x => mg_out hd (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := mg_exec_redCmd hd hhd x
      exact ⟨σ', h1.mono (mg_Tred_le _), h2⟩)
    F (fun t => by rw [hF]; exact (congrArg (mg_out hd) (FunBridge.dec2_flatMap_ic t)).symm)

/-- **SAT ≤ₚ 3DM** (official polynomial-time many-one reducibility), given the correctness of
the reduction instance `DMI`. -/
theorem sat_le_dm_of (h : ∀ w, SATLang w ↔ DMLang (DMI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang DMLang := by
  obtain ⟨hc⟩ := mg_computable 1 (by norm_num) DMI mg_DMI
  exact ⟨DMI, hc, h⟩

/-- **SAT ≤ₚ X3C** (official polynomial-time many-one reducibility), given the correctness of
the reduction instance `X3I`. -/
theorem sat_le_x3c_of (h : ∀ w, SATLang w ↔ X3CLang (X3I w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang X3CLang := by
  obtain ⟨hc⟩ := mg_computable 3 (by norm_num) X3I mg_X3I
  exact ⟨X3I, hc, h⟩

end Pnp.Karp.ThreeDM
