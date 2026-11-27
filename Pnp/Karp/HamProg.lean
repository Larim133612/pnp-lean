import Pnp.Karp.Ham
import Pnp.Karp.ColorGen
import Pnp.Karp.CliqueProg

/-!
# The HAMILTONIAN CYCLE reduction program, part 1: registers, primitives, loops

A stack program printing `H w` (`Pnp/Karp/Ham.lean`), on the layout `st2` of
`Pnp/Karp/CliqueGen.lean`: stack `1` the (reversed code of the) output, `2` the code `W` of
`trunc w`, `3` / `4` the rest of `trunc w` for the in-rows / out-rows of the clause vertices.
Unary registers (`hg_rg`): `5 ↦ N`, `6 ↦ K` (`3k`), `8 ↦ D` (`3(m - k - 1)`), `9 ↦ M` (clauses
left), `10 ↦ C` (padding countdown), `12 ↦ X` (`3x`), `13 ↦ J` (rows left), `14 ↦ T` (row
positions left); `7` is the countdown of a run of `zero`s (`Color.zLoop`), `11` the copy
temporary.

* `hg_zsR a` prints `v a` zeros; `hg_blkC mid` prints a block `zs (3K) ++ mid ++ zs (3D)`;
* `hg_bLoop3`, `hg_bLoop4`: the blocks of one clause (read from stack `3` / `4` up to its `sep`),
  `hg_pad`: the padding blocks; `hg_inRow`, `hg_oneRow`, `hg_outRow`, `hg_clLoop`: the rows of
  the clause vertices;
* `hg_vSp`, `hg_vNm`, `hg_tLoop`, `hg_jLoop`, `hg_zRows`: the rows of the other vertices.
-/

namespace Pnp.Karp.Ham

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Registers and states -/

/-- The register values. -/
structure hg_R where
  N : ℕ
  K : ℕ
  D : ℕ
  M : ℕ
  C : ℕ
  X : ℕ
  J : ℕ
  T : ℕ

/-- The register function. -/
def hg_rg (s : hg_R) : ℕ → ℕ := fun r =>
  if r = 5 then s.N else if r = 6 then s.K else if r = 8 then s.D else if r = 9 then s.M else
  if r = 10 then s.C else if r = 12 then s.X else if r = 13 then s.J else if r = 14 then s.T
  else 0

local macro "rgt" : tactic =>
  `(tactic| (funext i; simp only [hg_rg, update_apply]; split_ifs <;> simp_all))

section RG
variable (s : hg_R) (n : ℕ)
@[simp] theorem hg_rg5 : hg_rg s 5 = s.N := by simp [hg_rg]
@[simp] theorem hg_rg6 : hg_rg s 6 = s.K := by simp [hg_rg]
@[simp] theorem hg_rg7 : hg_rg s 7 = 0 := by simp [hg_rg]
@[simp] theorem hg_rg8 : hg_rg s 8 = s.D := by simp [hg_rg]
@[simp] theorem hg_rg9 : hg_rg s 9 = s.M := by simp [hg_rg]
@[simp] theorem hg_rg10 : hg_rg s 10 = s.C := by simp [hg_rg]
@[simp] theorem hg_rg11 : hg_rg s 11 = 0 := by simp [hg_rg]
@[simp] theorem hg_rg12 : hg_rg s 12 = s.X := by simp [hg_rg]
@[simp] theorem hg_rg13 : hg_rg s 13 = s.J := by simp [hg_rg]
@[simp] theorem hg_rg14 : hg_rg s 14 = s.T := by simp [hg_rg]

theorem hg_upd5 : update (hg_rg s) 5 n = hg_rg {s with N := n} := by rgt
theorem hg_upd6 : update (hg_rg s) 6 n = hg_rg {s with K := n} := by rgt
theorem hg_upd8 : update (hg_rg s) 8 n = hg_rg {s with D := n} := by rgt
theorem hg_upd9 : update (hg_rg s) 9 n = hg_rg {s with M := n} := by rgt
theorem hg_upd10 : update (hg_rg s) 10 n = hg_rg {s with C := n} := by rgt
theorem hg_upd12 : update (hg_rg s) 12 n = hg_rg {s with X := n} := by rgt
theorem hg_upd13 : update (hg_rg s) 13 n = hg_rg {s with J := n} := by rgt
theorem hg_upd14 : update (hg_rg s) 14 n = hg_rg {s with T := n} := by rgt
end RG

theorem hg_rg_zero : (fun _ : ℕ => (0 : ℕ)) = hg_rg ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ := by
  funext r; simp only [hg_rg]; split_ifs <;> rfl

/-- The states. -/
def hg_S (W O Q : Str) (E : List SatSym) (s : hg_R) : ℕ → Str := st2 W O Q (rv E) (hg_rg s)

section S
variable (W O Q : Str) (E : List SatSym) (s : hg_R)
@[simp] theorem hg_S1 : hg_S W O Q E s 1 = rv E := rfl
@[simp] theorem hg_S3 : hg_S W O Q E s 3 = O := rfl
@[simp] theorem hg_S4 : hg_S W O Q E s 4 = Q := rfl

theorem hg_Sreg {r : ℕ} (hr : 5 ≤ r) : hg_S W O Q E s r = List.replicate (hg_rg s r) true :=
  st2_reg hr

theorem hg_updS3 (O' : Str) : update (hg_S W O Q E s) 3 O' = hg_S W O' Q E s := upd2_3 O'
theorem hg_updS4 (Q' : Str) : update (hg_S W O Q E s) 4 Q' = hg_S W O Q' E s := upd2_4 Q'
end S

/-! ## Register steps -/

section Reg
variable (W O Q : Str) (E : List SatSym) (s : hg_R)

theorem hg_ex_push {r : ℕ} (hr : 5 ≤ r) :
    ExecLe (.push r true) (hg_S W O Q E s)
      (.norm (st2 W O Q (rv E) (update (hg_rg s) r (hg_rg s r + 1)))) 1 :=
  ex_push_reg hr _ _

/-- Decrement a register (no effect on `0`). -/
def hg_dec (r : ℕ) : Cmd := .pop r .skip .skip .skip

theorem hg_ex_dec {r : ℕ} (hr : 5 ≤ r) :
    ExecLe (hg_dec r) (hg_S W O Q E s)
      (.norm (st2 W O Q (rv E) (update (hg_rg s) r (hg_rg s r - 1)))) 2 := by
  unfold hg_S
  rcases h : hg_rg s r with _ | n
  · refine (ExecLe.pop_nil (by rw [st2_reg hr, h]; rfl) (ExecLe.skip _)).cast ?_ le_rfl
    rw [Nat.zero_sub, ← h, update_eq_self]
  · refine ExecLe.pop_cons (b := true) (s := List.replicate n true)
      (by rw [st2_reg hr, h, List.replicate_succ]) ?_
    rw [if_pos rfl, upd2_reg hr, Nat.add_sub_cancel]
    exact ExecLe.skip _

theorem hg_pushN : ExecLe (.push 5 true) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with N := s.N + 1})) 1 :=
  (hg_ex_push W O Q E s (r := 5) (by norm_num)).cast (by rw [hg_rg5, hg_upd5]; rfl) le_rfl
theorem hg_pushK : ExecLe (.push 6 true) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with K := s.K + 1})) 1 :=
  (hg_ex_push W O Q E s (r := 6) (by norm_num)).cast (by rw [hg_rg6, hg_upd6]; rfl) le_rfl
theorem hg_pushM : ExecLe (.push 9 true) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with M := s.M + 1})) 1 :=
  (hg_ex_push W O Q E s (r := 9) (by norm_num)).cast (by rw [hg_rg9, hg_upd9]; rfl) le_rfl
theorem hg_pushX : ExecLe (.push 12 true) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with X := s.X + 1})) 1 :=
  (hg_ex_push W O Q E s (r := 12) (by norm_num)).cast (by rw [hg_rg12, hg_upd12]; rfl) le_rfl
theorem hg_pushT : ExecLe (.push 14 true) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with T := s.T + 1})) 1 :=
  (hg_ex_push W O Q E s (r := 14) (by norm_num)).cast (by rw [hg_rg14, hg_upd14]; rfl) le_rfl

theorem hg_decD : ExecLe (hg_dec 8) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with D := s.D - 1})) 2 :=
  (hg_ex_dec W O Q E s (r := 8) (by norm_num)).cast (by rw [hg_rg8, hg_upd8]; rfl) le_rfl
theorem hg_decC : ExecLe (hg_dec 10) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with C := s.C - 1})) 2 :=
  (hg_ex_dec W O Q E s (r := 10) (by norm_num)).cast (by rw [hg_rg10, hg_upd10]; rfl) le_rfl
theorem hg_decX : ExecLe (hg_dec 12) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with X := s.X - 1})) 2 :=
  (hg_ex_dec W O Q E s (r := 12) (by norm_num)).cast (by rw [hg_rg12, hg_upd12]; rfl) le_rfl

theorem hg_copy {a b : ℕ} (ha : 5 ≤ a) (hb : 5 ≤ b) (hab : a ≠ b) (ha11 : a ≠ 11)
    (hb11 : b ≠ 11) :
    ExecLe (copyVia a b 11) (hg_S W O Q E s)
      (.norm (st2 W O Q (rv E) (update (hg_rg s) b (hg_rg s b + hg_rg s a))))
      (5 * hg_rg s a + 4) :=
  ex_copy_reg ha hb hab ha11 hb11 _ _ (hg_rg11 s)

/-- Three decrements / increments. -/
def hg_dec3 (r : ℕ) : Cmd := .seq (hg_dec r) (.seq (hg_dec r) (hg_dec r))
def hg_inc3 (r : ℕ) : Cmd := .seq (.push r true) (.seq (.push r true) (.push r true))

theorem hg_dec3D : ExecLe (hg_dec3 8) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with D := s.D - 3})) 6 :=
  ((hg_decD W O Q E s).seq_norm ((hg_decD W O Q E _).seq_norm (hg_decD W O Q E _))).cast
    (by congr 2) le_rfl
theorem hg_dec3X : ExecLe (hg_dec3 12) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with X := s.X - 3})) 6 :=
  ((hg_decX W O Q E s).seq_norm ((hg_decX W O Q E _).seq_norm (hg_decX W O Q E _))).cast
    (by congr 2) le_rfl
theorem hg_inc3K : ExecLe (hg_inc3 6) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with K := s.K + 3})) 3 :=
  ((hg_pushK W O Q E s).seq_norm ((hg_pushK W O Q E _).seq_norm (hg_pushK W O Q E _))).cast
    rfl le_rfl
theorem hg_inc3X : ExecLe (hg_inc3 12) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with X := s.X + 3})) 3 :=
  ((hg_pushX W O Q E s).seq_norm ((hg_pushX W O Q E _).seq_norm (hg_pushX W O Q E _))).cast
    rfl le_rfl

end Reg

/-! ## Counter loops -/

/-- One iteration of a counter loop. -/
theorem hg_cstep {r : ℕ} {c : Cmd} {σ σ1 : ℕ → Str} {res : Res} {n B T : ℕ}
    (h : σ r = List.replicate (n + 1) true)
    (hb : ExecLe c (update σ r (List.replicate n true)) (.norm σ1) B)
    (hl : ExecLe (.loop (.pop r .brk c c)) σ1 res T) :
    ExecLe (.loop (.pop r .brk c c)) σ res (B + 1 + T) :=
  ExecLe.loop_norm (ExecLe.pop_same (by rw [h, List.replicate_succ]) hb) hl

theorem hg_cend {r : ℕ} {c : Cmd} {σ : ℕ → Str} (h : σ r = []) :
    ExecLe (.loop (.pop r .brk c c)) σ (.norm σ) 2 :=
  ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk _))

/-! ## Printing -/

/-- `c` prints `out` within `T` steps, leaving everything else unchanged. -/
def hg_Em (c : Cmd) (s : hg_R) (out : List SatSym) (T : ℕ) : Prop :=
  ∀ W O Q E, ExecLe c (hg_S W O Q E s) (.norm (hg_S W O Q (E ++ out) s)) T

theorem hg_Em.seq {c d : Cmd} {s : hg_R} {o₁ o₂ : List SatSym} {T₁ T₂ : ℕ}
    (h1 : hg_Em c s o₁ T₁) (h2 : hg_Em d s o₂ T₂) :
    hg_Em (.seq c d) s (o₁ ++ o₂) (T₁ + T₂) := fun W O Q E =>
  ((h1 W O Q E).seq_norm (h2 W O Q (E ++ o₁))).cast (by rw [List.append_assoc]) le_rfl

theorem hg_Em.cast {c : Cmd} {s : hg_R} {o o' : List SatSym} {T T' : ℕ} (h : hg_Em c s o T)
    (ho : o = o') (hT : T ≤ T') : hg_Em c s o' T' := fun W O Q E =>
  (h W O Q E).cast (by rw [ho]) hT

theorem hg_em_emL (L : List SatSym) (s : hg_R) : hg_Em (emL L) s L (2 * L.length + 1) :=
  fun _ _ _ E => ex_emL L E _

/-- Print `v a` zeros. -/
def hg_zsR (a : ℕ) : Cmd := .seq (copyVia a 7 11) Color.zLoop

theorem hg_em_zsR {a : ℕ} (ha : 5 ≤ a) (ha7 : a ≠ 7) (ha11 : a ≠ 11) (s : hg_R) :
    hg_Em (hg_zsR a) s (zs (hg_rg s a)) (9 * hg_rg s a + 6) := by
  intro W O Q E
  have h1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := a) (b := 7) ha (by norm_num) ha7 ha11
    (by norm_num) (rv E) (hg_rg s) (hg_rg11 s)
  have h2 := Color.ex_zLoop W O Q (hg_rg s a) E
    (update (hg_rg s) 7 (hg_rg s 7 + hg_rg s a)) (by simp)
  refine (h1.seq_norm h2).cast ?_ (by omega)
  rw [update_idem, update_eq_self_iff.2 (hg_rg7 s)]; rfl

theorem hg_em_zK (s : hg_R) : hg_Em (hg_zsR 6) s (zs s.K) (9 * s.K + 6) := by
  simpa using hg_em_zsR (a := 6) (by norm_num) (by norm_num) (by norm_num) s
theorem hg_em_zD (s : hg_R) : hg_Em (hg_zsR 8) s (zs s.D) (9 * s.D + 6) := by
  simpa using hg_em_zsR (a := 8) (by norm_num) (by norm_num) (by norm_num) s
theorem hg_em_zX (s : hg_R) : hg_Em (hg_zsR 12) s (zs s.X) (9 * s.X + 6) := by
  simpa using hg_em_zsR (a := 12) (by norm_num) (by norm_num) (by norm_num) s

/-! ## Blocks -/

/-- A block: `zs (3K) ++ mid ++ zs (3D)`. -/
def hg_blkP (K D : ℕ) (mid : List SatSym) : List SatSym := zs (3 * K) ++ mid ++ zs (3 * D)

def hg_blkC (mid : List SatSym) : Cmd :=
  .seq (hg_zsR 6) (.seq (hg_zsR 6) (.seq (hg_zsR 6) (.seq (emL mid)
    (.seq (hg_zsR 8) (.seq (hg_zsR 8) (hg_zsR 8))))))

theorem hg_em_blkC (mid : List SatSym) (s : hg_R) :
    hg_Em (hg_blkC mid) s (hg_blkP s.K s.D mid) (27 * s.K + 27 * s.D + 2 * mid.length + 37) := by
  refine ((hg_em_zK s).seq ((hg_em_zK s).seq ((hg_em_zK s).seq ((hg_em_emL mid s).seq
    ((hg_em_zD s).seq ((hg_em_zD s).seq (hg_em_zD s))))))).cast ?_ (by omega)
  simp only [hg_blkP, show 3 * s.K = s.K + s.K + s.K by ring,
    show 3 * s.D = s.D + s.D + s.D by ring, List.replicate_add, List.append_assoc]

/-- The middle parts of the blocks of in-rows / out-rows. -/
def hg_midIn : SatSym → List SatSym
  | pos => zs 11 ++ [pos] ++ zs 9
  | neg => zs 14 ++ [pos] ++ zs 6
  | _ => zs 21

def hg_midOut : SatSym → List SatSym
  | pos => zs 12 ++ [pos] ++ zs 8
  | neg => zs 9 ++ [pos] ++ zs 11
  | _ => zs 21

theorem hg_len_midIn (a : SatSym) : (hg_midIn a).length = 21 := by cases a <;> rfl
theorem hg_len_midOut (a : SatSym) : (hg_midOut a).length = 21 := by cases a <;> rfl

/-- Per-symbol action of a block loop. -/
def hg_bBr (mid : SatSym → List SatSym) : SatSym → Cmd
  | sep => .brk
  | a => .seq (hg_blkC (mid a)) (hg_dec 10)

def hg_bLoop3 (mid : SatSym → List SatSym) : Cmd := .loop (disp 3 (hg_bBr mid))
def hg_bLoop4 (mid : SatSym → List SatSym) : Cmd := .loop (disp 4 (hg_bBr mid))

theorem hg_ex_bBr (mid : SatSym → List SatSym) (hm : ∀ a, (mid a).length = 21) {a : SatSym}
    (ha : a ≠ sep) (W O Q : Str) (E : List SatSym) (s : hg_R) :
    ExecLe (hg_bBr mid a) (hg_S W O Q E s)
      (.norm (hg_S W O Q (E ++ hg_blkP s.K s.D (mid a)) {s with C := s.C - 1}))
      (27 * s.K + 27 * s.D + 81) := by
  have h := ((hg_em_blkC (mid a) s) W O Q E).seq_norm (hg_decC W O Q _ s)
  rw [hm a] at h
  cases a with
  | sep => exact absurd rfl ha
  | zero => exact h.cast rfl (by omega)
  | pos => exact h.cast rfl (by omega)
  | neg => exact h.cast rfl (by omega)

theorem hg_ex_bLoop3 (mid : SatSym → List SatSym) (hm : ∀ a, (mid a).length = 21)
    (W Q : Str) : ∀ (c : List SatSym), sep ∉ c → ∀ (rest E : List SatSym) (s : hg_R),
    ExecLe (hg_bLoop3 mid) (hg_S W ((c ++ sep :: rest).flatMap ic) Q E s)
      (.norm (hg_S W (rest.flatMap ic) Q (E ++ c.flatMap fun a => hg_blkP s.K s.D (mid a))
        {s with C := s.C - c.length})) (c.length * (27 * s.K + 27 * s.D + 83) + 3)
  | [], _, rest, E, s => by
    have hb := ex_disp (k := 3) (f := hg_bBr mid) (s := sep) (Q' := rest.flatMap ic)
      (σ := hg_S W (([] ++ sep :: rest).flatMap ic) Q E s) (by simp)
      (ExecLe.brk _)
    refine (ExecLe.loop_brk hb).cast ?_ (by simp)
    rw [hg_updS3]; simp
  | a :: c, hc, rest, E, s => by
    have ha : a ≠ sep := fun e => hc (e ▸ List.mem_cons_self ..)
    have hc' : sep ∉ c := fun e => hc (List.mem_cons_of_mem _ e)
    have h1 := hg_ex_bBr mid hm ha W ((c ++ sep :: rest).flatMap ic) Q E s
    have hb := ex_disp (k := 3) (f := hg_bBr mid) (s := a) (Q' := (c ++ sep :: rest).flatMap ic)
      (σ := hg_S W ((a :: c ++ sep :: rest).flatMap ic) Q E s) (by simp)
      (by rw [hg_updS3]; exact h1)
    have ih := hg_ex_bLoop3 mid hm W Q c hc' rest (E ++ hg_blkP s.K s.D (mid a))
      {s with C := s.C - 1}
    refine (ExecLe.loop_norm hb ih).cast ?_ ?_
    · simp only [List.flatMap_cons, List.append_assoc, List.length_cons, Nat.sub_sub,
        Nat.add_comm 1 c.length]
    · simp only [List.length_cons]; nlinarith

theorem hg_ex_bLoop4 (mid : SatSym → List SatSym) (hm : ∀ a, (mid a).length = 21)
    (W O : Str) : ∀ (c : List SatSym), sep ∉ c → ∀ (rest E : List SatSym) (s : hg_R),
    ExecLe (hg_bLoop4 mid) (hg_S W O ((c ++ sep :: rest).flatMap ic) E s)
      (.norm (hg_S W O (rest.flatMap ic) (E ++ c.flatMap fun a => hg_blkP s.K s.D (mid a))
        {s with C := s.C - c.length})) (c.length * (27 * s.K + 27 * s.D + 83) + 3)
  | [], _, rest, E, s => by
    have hb := ex_disp (k := 4) (f := hg_bBr mid) (s := sep) (Q' := rest.flatMap ic)
      (σ := hg_S W O (([] ++ sep :: rest).flatMap ic) E s) (by simp)
      (ExecLe.brk _)
    refine (ExecLe.loop_brk hb).cast ?_ (by simp)
    rw [hg_updS4]; simp
  | a :: c, hc, rest, E, s => by
    have ha : a ≠ sep := fun e => hc (e ▸ List.mem_cons_self ..)
    have hc' : sep ∉ c := fun e => hc (List.mem_cons_of_mem _ e)
    have h1 := hg_ex_bBr mid hm ha W O ((c ++ sep :: rest).flatMap ic) E s
    have hb := ex_disp (k := 4) (f := hg_bBr mid) (s := a) (Q' := (c ++ sep :: rest).flatMap ic)
      (σ := hg_S W O ((a :: c ++ sep :: rest).flatMap ic) E s) (by simp)
      (by rw [hg_updS4]; exact h1)
    have ih := hg_ex_bLoop4 mid hm W O c hc' rest (E ++ hg_blkP s.K s.D (mid a))
      {s with C := s.C - 1}
    refine (ExecLe.loop_norm hb ih).cast ?_ ?_
    · simp only [List.flatMap_cons, List.append_assoc, List.length_cons, Nat.sub_sub,
        Nat.add_comm 1 c.length]
    · simp only [List.length_cons]; nlinarith
/-! ## Register updates of popped counters and copies -/

section Upd
variable (W O Q : Str) (E : List SatSym) (s : hg_R) (n : ℕ)

theorem hg_updS9 : update (hg_S W O Q E s) 9 (List.replicate n true) = hg_S W O Q E {s with M := n} := by
  unfold hg_S; rw [upd2_reg (by norm_num), hg_upd9]
theorem hg_updS10 : update (hg_S W O Q E s) 10 (List.replicate n true) = hg_S W O Q E {s with C := n} := by
  unfold hg_S; rw [upd2_reg (by norm_num), hg_upd10]
theorem hg_updS13 : update (hg_S W O Q E s) 13 (List.replicate n true) = hg_S W O Q E {s with J := n} := by
  unfold hg_S; rw [upd2_reg (by norm_num), hg_upd13]
theorem hg_updS14 : update (hg_S W O Q E s) 14 (List.replicate n true) = hg_S W O Q E {s with T := n} := by
  unfold hg_S; rw [upd2_reg (by norm_num), hg_upd14]

theorem hg_cp5_10 : ExecLe (copyVia 5 10 11) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with C := s.C + s.N})) (5 * s.N + 4) :=
  (hg_copy W O Q E s (a := 5) (b := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).cast (by rw [hg_rg10, hg_rg5, hg_upd10]; rfl) (by simp)
theorem hg_cp9_8 : ExecLe (copyVia 9 8 11) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with D := s.D + s.M})) (5 * s.M + 4) :=
  (hg_copy W O Q E s (a := 9) (b := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).cast (by rw [hg_rg8, hg_rg9, hg_upd8]; rfl) (by simp)
theorem hg_cp6_12 : ExecLe (copyVia 6 12 11) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with X := s.X + s.K})) (5 * s.K + 4) :=
  (hg_copy W O Q E s (a := 6) (b := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).cast (by rw [hg_rg12, hg_rg6, hg_upd12]; rfl) (by simp)
theorem hg_cp5_13 : ExecLe (copyVia 5 13 11) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with J := s.J + s.N})) (5 * s.N + 4) :=
  (hg_copy W O Q E s (a := 5) (b := 13) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).cast (by rw [hg_rg13, hg_rg5, hg_upd13]; rfl) (by simp)
theorem hg_cp6_14 : ExecLe (copyVia 6 14 11) (hg_S W O Q E s)
    (.norm (hg_S W O Q E {s with T := s.T + s.K})) (5 * s.K + 4) :=
  (hg_copy W O Q E s (a := 6) (b := 14) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).cast (by rw [hg_rg14, hg_rg6, hg_upd14]; rfl) (by simp)

end Upd

/-! ## Padding -/

def hg_pad : Cmd := .loop (.pop 10 .brk (hg_blkC (zs 21)) (hg_blkC (zs 21)))

theorem hg_ex_pad (W O Q : Str) : ∀ (n : ℕ) (E : List SatSym) (s : hg_R), s.C = n →
    ExecLe hg_pad (hg_S W O Q E s)
      (.norm (hg_S W O Q (E ++ (List.replicate n (hg_blkP s.K s.D (zs 21))).flatten)
        {s with C := 0})) (n * (27 * s.K + 27 * s.D + 80) + 2)
  | 0, E, s, h => (hg_cend (by rw [hg_Sreg _ _ _ _ _ (by norm_num), hg_rg10, h]; rfl)).cast
      (by cases s; simp only at h; subst h; simp) (by simp)
  | n + 1, E, s, h => by
    have hb := hg_em_blkC (zs 21) {s with C := n} W O Q E
    have ih := hg_ex_pad W O Q n (E ++ hg_blkP s.K s.D (zs 21)) {s with C := n} rfl
    refine (hg_cstep (n := n) (by rw [hg_Sreg _ _ _ _ _ (by norm_num), hg_rg10, h])
      (by rw [hg_updS10]; exact hb) ih).cast ?_ ?_
    · simp [List.replicate_succ, List.append_assoc]
    · simp only [List.length_replicate]; nlinarith

/-! ## The rows of the clause vertices -/

/-- The printed in-row of a clause `c` (with `sep`). -/
def hg_inP (N K D : ℕ) (c : List SatSym) : List SatSym :=
  zs K ++ [zero, pos] ++ zs D ++ [zero] ++ c.flatMap (fun a => hg_blkP K D (hg_midIn a)) ++
    (List.replicate (N - c.length) (hg_blkP K D (zs 21))).flatten ++ [sep]

/-- The printed out-row of a clause `c` (with `sep`). -/
def hg_outP (N K D : ℕ) (c : List SatSym) : List SatSym :=
  zs K ++ zs 3 ++ zs D ++ c.flatMap (fun a => hg_blkP K D (hg_midOut a)) ++
    (List.replicate (N - c.length) (hg_blkP K D (zs 21))).flatten ++ [sep]

def hg_inRow : Cmd :=
  .seq (.seq (hg_zsR 6) (.seq (emL [zero, pos]) (.seq (hg_zsR 8) (emL [zero]))))
    (.seq (copyVia 5 10 11) (.seq (hg_bLoop3 hg_midIn) (.seq hg_pad (emL [sep]))))

def hg_outRow : Cmd :=
  .seq (.seq (hg_zsR 6) (.seq (emL (zs 3)) (hg_zsR 8)))
    (.seq (copyVia 5 10 11) (.seq (hg_bLoop4 hg_midOut) (.seq hg_pad (emL [sep]))))

def hg_oneRow : Cmd := .seq (hg_zsR 6) (emL [zero, zero, pos, sep])

theorem hg_em_oneRow (s : hg_R) :
    hg_Em hg_oneRow s (zs s.K ++ [zero, zero, pos, sep]) (9 * s.K + 15) :=
  ((hg_em_zK s).seq (hg_em_emL _ s)).cast rfl (by simp)

/-- Cost of a clause row. -/
def hg_rowT (N K D : ℕ) : ℕ := 9 * K + 9 * D + 5 * N + N * (27 * K + 27 * D + 83) + 40

theorem hg_blocksT (N K D l : ℕ) (hl : l ≤ N) :
    l * (27 * K + 27 * D + 83) + (N - l) * (27 * K + 27 * D + 80) ≤
      N * (27 * K + 27 * D + 83) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [Nat.add_sub_cancel_left]; nlinarith

theorem hg_ex_inRow (W Q : Str) (c : List SatSym) (hc : sep ∉ c) (rest E : List SatSym)
    (s : hg_R) (hC : s.C = 0) (hN : c.length ≤ s.N) :
    ExecLe hg_inRow (hg_S W ((c ++ sep :: rest).flatMap ic) Q E s)
      (.norm (hg_S W (rest.flatMap ic) Q (E ++ hg_inP s.N s.K s.D c) s))
      (hg_rowT s.N s.K s.D) := by
  have q1 := ((hg_em_zK s).seq ((hg_em_emL [zero, pos] s).seq ((hg_em_zD s).seq
    (hg_em_emL [zero] s)))) W ((c ++ sep :: rest).flatMap ic) Q E
  have q2 := hg_cp5_10 W ((c ++ sep :: rest).flatMap ic) Q
    (E ++ (zs s.K ++ ([zero, pos] ++ (zs s.D ++ [zero])))) s
  rw [hC, Nat.zero_add] at q2
  have q3 := hg_ex_bLoop3 hg_midIn hg_len_midIn W Q c hc rest
    (E ++ (zs s.K ++ ([zero, pos] ++ (zs s.D ++ [zero])))) {s with C := s.N}
  have q4 := hg_ex_pad W (rest.flatMap ic) Q (s.N - c.length)
    (E ++ (zs s.K ++ ([zero, pos] ++ (zs s.D ++ [zero]))) ++
      c.flatMap fun a => hg_blkP s.K s.D (hg_midIn a)) {s with C := s.N - c.length} rfl
  have e : ({ s with C := 0 } : hg_R) = s := by
    cases s; simp only at hC; subst hC; rfl
  refine (q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm
    (hg_em_emL [sep] {s with C := 0} _ _ _ _))))).cast ?_ ?_
  · rw [e]; simp [hg_inP, List.append_assoc]
  · have := hg_blocksT s.N s.K s.D c.length hN
    simp only [hg_rowT, List.length_cons, List.length_nil]; omega

theorem hg_ex_outRow (W O : Str) (c : List SatSym) (hc : sep ∉ c) (rest E : List SatSym)
    (s : hg_R) (hC : s.C = 0) (hN : c.length ≤ s.N) :
    ExecLe hg_outRow (hg_S W O ((c ++ sep :: rest).flatMap ic) E s)
      (.norm (hg_S W O (rest.flatMap ic) (E ++ hg_outP s.N s.K s.D c) s))
      (hg_rowT s.N s.K s.D) := by
  have q1 := ((hg_em_zK s).seq ((hg_em_emL (zs 3) s).seq (hg_em_zD s)))
    W O ((c ++ sep :: rest).flatMap ic) E
  have q2 := hg_cp5_10 W O ((c ++ sep :: rest).flatMap ic)
    (E ++ (zs s.K ++ (zs 3 ++ zs s.D))) s
  rw [hC, Nat.zero_add] at q2
  have q3 := hg_ex_bLoop4 hg_midOut hg_len_midOut W O c hc rest
    (E ++ (zs s.K ++ (zs 3 ++ zs s.D))) {s with C := s.N}
  have q4 := hg_ex_pad W O (rest.flatMap ic) (s.N - c.length)
    (E ++ (zs s.K ++ (zs 3 ++ zs s.D)) ++
      c.flatMap fun a => hg_blkP s.K s.D (hg_midOut a)) {s with C := s.N - c.length} rfl
  have e : ({ s with C := 0 } : hg_R) = s := by
    cases s; simp only at hC; subst hC; rfl
  refine (q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm
    (hg_em_emL [sep] {s with C := 0} _ _ _ _))))).cast ?_ ?_
  · rw [e]; simp [hg_outP, List.append_assoc, Nat.add_assoc]
  · have := hg_blocksT s.N s.K s.D c.length hN
    simp only [hg_rowT, List.length_cons, List.length_nil, List.length_replicate]; omega

/-- The three rows of a clause. -/
def hg_cl1 (N K D : ℕ) (c : List SatSym) : List SatSym :=
  hg_inP N K D c ++ (zs K ++ [zero, zero, pos, sep]) ++ hg_outP N K D c

/-- The printed rows of the clauses `cs`, from index `k` on. -/
def hg_clP (N : ℕ) : ℕ → List (List SatSym) → List SatSym
  | _, [] => []
  | k, c :: cs => hg_cl1 N (3 * k) (3 * cs.length) c ++ hg_clP N (k + 1) cs

def hg_clB : Cmd := .seq (hg_dec3 8) (.seq hg_inRow (.seq hg_oneRow (.seq hg_outRow (hg_inc3 6))))

def hg_clLoop : Cmd := .loop (.pop 9 .brk hg_clB hg_clB)

/-- Cost bound of one clause. -/
def hg_Bc (V : ℕ) : ℕ := 2 * (V * (54 * V + 83)) + 60 * V + 150

theorem hg_ex_clLoop (W : Str) (N V : ℕ) : ∀ (cs : List (List SatSym)) (k : ℕ)
    (E : List SatSym) (s : hg_R), (∀ c ∈ cs, sep ∉ c ∧ c.length ≤ N) → s.N = N →
    s.M = cs.length → s.K = 3 * k → s.D = 3 * cs.length → s.C = 0 → N ≤ V →
    3 * (k + cs.length) ≤ V →
    ExecLe hg_clLoop (hg_S W ((cs.flatMap (· ++ [sep])).flatMap ic)
        ((cs.flatMap (· ++ [sep])).flatMap ic) E s)
      (.norm (hg_S W [] [] (E ++ hg_clP N k cs) {s with M := 0, K := 3 * (k + cs.length), D := 0}))
      (cs.length * (hg_Bc V + 1) + 2)
  | [], k, E, s, _, _, hM, hK, hD, _, _, _ => by
    refine (hg_cend (by rw [hg_Sreg _ _ _ _ _ (by norm_num), hg_rg9, hM]; rfl)).cast ?_ (by simp)
    cases s; simp only [List.length_nil] at hM hD hK; subst hM; simp at hD; subst hD
    simp [hg_clP, hK]
  | c :: cs, k, E, s, hcs, hN, hM, hK, hD, hC, hNV, hV => by
    obtain ⟨hc, hcN⟩ := hcs c (by simp)
    have hcs' : ∀ c ∈ cs, sep ∉ c ∧ c.length ≤ N := fun c' h => hcs c' (by simp [h])
    simp only [List.length_cons] at hM hD hV
    set rest := cs.flatMap (· ++ [sep])
    have eW : ((c :: cs).flatMap (· ++ [sep])).flatMap ic = (c ++ sep :: rest).flatMap ic := by
      simp [rest]
    rw [eW]
    set s1 : hg_R := {s with M := cs.length}
    have p1 := hg_dec3D W ((c ++ sep :: rest).flatMap ic) ((c ++ sep :: rest).flatMap ic) E s1
    set s2 : hg_R := {s1 with D := s1.D - 3}
    have e2N : s2.N = N := hN
    have e2K : s2.K = 3 * k := hK
    have e2D : s2.D = 3 * cs.length := by simp only [s2, s1, hD]; omega
    have e2C : s2.C = 0 := hC
    have p2 := hg_ex_inRow W ((c ++ sep :: rest).flatMap ic) c hc rest E s2 e2C (by omega)
    have p3 := hg_em_oneRow s2 W (rest.flatMap ic) ((c ++ sep :: rest).flatMap ic)
      (E ++ hg_inP s2.N s2.K s2.D c)
    have p4 := hg_ex_outRow W (rest.flatMap ic) c hc rest
      (E ++ hg_inP s2.N s2.K s2.D c ++ (zs s2.K ++ [zero, zero, pos, sep])) s2 e2C (by omega)
    have p5 := hg_inc3K W (rest.flatMap ic) (rest.flatMap ic)
      (E ++ hg_inP s2.N s2.K s2.D c ++ (zs s2.K ++ [zero, zero, pos, sep]) ++
        hg_outP s2.N s2.K s2.D c) s2
    set s3 : hg_R := {s2 with K := s2.K + 3}
    have ih := hg_ex_clLoop W N V cs (k + 1) (E ++ hg_inP s2.N s2.K s2.D c ++
        (zs s2.K ++ [zero, zero, pos, sep]) ++ hg_outP s2.N s2.K s2.D c) s3 hcs'
      hN rfl (by simp [s3, e2K]; ring) e2D hC hNV (by omega)
    have hpop : hg_S W ((c ++ sep :: rest).flatMap ic) ((c ++ sep :: rest).flatMap ic) E s 9 =
        List.replicate (cs.length + 1) true := by
      rw [hg_Sreg _ _ _ _ _ (by norm_num), hg_rg9, hM]
    refine (hg_cstep hpop (by rw [hg_updS9]; exact p1.seq_norm (p2.seq_norm (p3.seq_norm
      (p4.seq_norm p5)))) ih).cast ?_ ?_
    · congr 2
      · simp only [hg_clP, e2N, e2K, e2D, List.append_assoc, hg_cl1]
      · simp only [s3, s2, s1, List.length_cons]; congr 1; omega
    · have hK' : s2.K ≤ V := by omega
      have hD' : s2.D ≤ V := by omega
      have hN' : s2.N ≤ V := by omega
      have m1 : s2.N * (27 * s2.K + 27 * s2.D + 83) ≤ V * (54 * V + 83) :=
        Nat.mul_le_mul hN' (by omega)
      simp only [hg_rowT, hg_Bc, List.length_cons] at *
      nlinarith

/-! ## Counting the clauses -/

def hg_cB : SatSym → Cmd
  | sep => .seq (.push 5 true) (.push 9 true)
  | _ => .push 5 true

def hg_cntLoop : Cmd := .loop (disp 4 hg_cB)

theorem hg_ex_cnt (W O : Str) : ∀ (l E : List SatSym) (s : hg_R),
    ExecLe hg_cntLoop (hg_S W O (l.flatMap ic) E s)
      (.norm (hg_S W O [] E {s with N := s.N + l.length, M := s.M + (l.flatMap hg).length}))
      (4 * l.length + 2)
  | [], E, s => (ex_disp_nil rfl).cast (by simp) (by simp)
  | a :: l, E, s => by
    have hb : ExecLe (hg_cB a) (hg_S W O (l.flatMap ic) E s)
        (.norm (hg_S W O (l.flatMap ic) E {s with N := s.N + 1, M := s.M + (hg a).length})) 2 := by
      cases a with
      | sep => exact ((hg_pushN W O _ E s).seq_norm (hg_pushM W O _ E _)).cast rfl le_rfl
      | zero => exact (hg_pushN W O _ E s).cast (by simp [hg]) (by omega)
      | pos => exact (hg_pushN W O _ E s).cast (by simp [hg]) (by omega)
      | neg => exact (hg_pushN W O _ E s).cast (by simp [hg]) (by omega)
    have hd := ex_disp (k := 4) (f := hg_cB) (s := a) (Q' := l.flatMap ic)
      (σ := hg_S W O ((a :: l).flatMap ic) E s) (by simp) (by rw [hg_updS4]; exact hb)
    have ih := hg_ex_cnt W O l E {s with N := s.N + 1, M := s.M + (hg a).length}
    refine (ExecLe.loop_norm hd ih).cast ?_ (by simp; omega)
    congr 2; simp only [List.length_cons, List.flatMap_cons, List.length_append]; congr 1 <;> omega

/-! ## The rows of the other vertices -/

/-- The rows of a vertex `x` (`X = 3x`) with `t ∈ {0, 1}` / `t ≥ 2`. -/
def hg_vtxS (K X : ℕ) : List SatSym :=
  (one (X + 1) ++ [sep]) ++ (one (X + 2) ++ [sep]) ++ (two (X + 3) (3 * K + 5) ++ [sep])

def hg_vtxN (X : ℕ) : List SatSym :=
  (one (X + 1) ++ [sep]) ++ (one (X + 2) ++ [sep]) ++ (two (X - 3) 5 ++ [sep])

def hg_vSp : Cmd :=
  .seq (hg_zsR 12) (.seq (emL [zero, pos, sep]) (.seq (hg_zsR 12) (.seq (emL [zero, zero, pos, sep])
    (.seq (hg_zsR 12) (.seq (emL [zero, zero, zero, pos]) (.seq (hg_zsR 6) (.seq (hg_zsR 6)
    (.seq (hg_zsR 6) (emL (zs 5 ++ [pos, sep]))))))))))

theorem hg_em_vSp (s : hg_R) : hg_Em hg_vSp s (hg_vtxS s.K s.X) (27 * s.X + 27 * s.K + 76) := by
  refine ((hg_em_zX s).seq ((hg_em_emL _ s).seq ((hg_em_zX s).seq ((hg_em_emL _ s).seq
    ((hg_em_zX s).seq ((hg_em_emL _ s).seq ((hg_em_zK s).seq ((hg_em_zK s).seq
    ((hg_em_zK s).seq (hg_em_emL _ s)))))))))).cast ?_ (by simp; omega)
  simp only [hg_vtxS, one, two, show 3 * s.K + 5 = s.K + s.K + s.K + 5 by ring,
    List.replicate_add, List.append_assoc]
  simp [List.replicate_succ]

def hg_vNm : Cmd :=
  .seq (.seq (hg_zsR 12) (.seq (emL [zero, pos, sep]) (.seq (hg_zsR 12)
    (emL [zero, zero, pos, sep]))))
    (.seq (.seq (hg_dec3 12) (.seq (hg_zsR 12) (hg_inc3 12))) (emL (pos :: zs 5 ++ [pos, sep])))

theorem hg_em_vNm (s : hg_R) (h : 3 ≤ s.X) : hg_Em hg_vNm s (hg_vtxN s.X) (27 * s.X + 60) := by
  intro W O Q E
  have h1 := ((hg_em_zX s).seq ((hg_em_emL [zero, pos, sep] s).seq ((hg_em_zX s).seq
    (hg_em_emL [zero, zero, pos, sep] s)))) W O Q E
  have e : ({ { s with X := s.X - 3 } with X := s.X - 3 + 3 } : hg_R) = s := by
    cases s; simp only at h ⊢; congr 1; omega
  have h2 := (hg_dec3X W O Q (E ++ (zs s.X ++ ([zero, pos, sep] ++ (zs s.X ++
    [zero, zero, pos, sep])))) s).seq_norm ((hg_em_zX {s with X := s.X - 3} W O Q _).seq_norm
    (hg_inc3X W O Q _ {s with X := s.X - 3}))
  rw [e] at h2
  refine (h1.seq_norm (h2.seq_norm (hg_em_emL (pos :: zs 5 ++ [pos, sep]) s W O Q _))).cast ?_ ?_
  · simp only [hg_vtxN, one, two, List.replicate_add, List.append_assoc]
    simp [List.replicate_succ]
  · simp; omega

def hg_tB : Cmd := .seq hg_vNm (hg_inc3 12)
def hg_tLoop : Cmd := .loop (.pop 14 .brk hg_tB hg_tB)

def hg_tP : ℕ → ℕ → List SatSym
  | _, 0 => []
  | X, n + 1 => hg_vtxN X ++ hg_tP (X + 3) n

theorem hg_ex_tLoop (V : ℕ) (W O Q : Str) : ∀ (n : ℕ) (E : List SatSym) (s : hg_R), s.T = n →
    3 ≤ s.X → s.X + 3 * n ≤ V →
    ExecLe hg_tLoop (hg_S W O Q E s)
      (.norm (hg_S W O Q (E ++ hg_tP s.X n) {s with T := 0, X := s.X + 3 * n}))
      (n * (27 * V + 64) + 2)
  | 0, E, s, hT, _, _ => (hg_cend (by rw [hg_Sreg _ _ _ _ _ (by norm_num), hg_rg14, hT]; rfl)).cast
      (by cases s; simp only at hT; subst hT; simp [hg_tP]) (by simp)
  | n + 1, E, s, hT, hX, hV => by
    have p1 := hg_em_vNm {s with T := n} hX W O Q E
    have p2 := hg_inc3X W O Q (E ++ hg_vtxN s.X) {s with T := n}
    have ih := hg_ex_tLoop V W O Q n (E ++ hg_vtxN s.X) {s with T := n, X := s.X + 3} rfl
      (by simp only; omega) (by simp only; omega)
    refine (hg_cstep (n := n) (by rw [hg_Sreg _ _ _ _ _ (by norm_num), hg_rg14, hT])
      (by rw [hg_updS14]; exact p1.seq_norm p2) ih).cast ?_ ?_
    · simp only [hg_tP, List.append_assoc]; congr 3; omega
    · simp only at *; nlinarith

def hg_jB : Cmd :=
  .seq hg_vSp (.seq (hg_inc3 12) (.seq hg_vSp (.seq (hg_inc3 12) (.seq (copyVia 6 14 11)
    (.seq (.push 14 true) (.seq (.push 14 true) hg_tLoop))))))

def hg_jLoop : Cmd := .loop (.pop 13 .brk hg_jB hg_jB)

/-- The rows of one variable row (`R = K + 4` vertices from `X = 3x`). -/
def hg_rowP (K X : ℕ) : List SatSym := hg_vtxS K X ++ hg_vtxS K (X + 3) ++ hg_tP (X + 6) (K + 2)

def hg_jP (K : ℕ) : ℕ → ℕ → List SatSym
  | _, 0 => []
  | X, n + 1 => hg_rowP K X ++ hg_jP K (X + 3 * K + 12) n

/-- Cost bound of one variable row. -/
def hg_Bj (V : ℕ) : ℕ := (V + 2) * (27 * V + 64) + 113 * V + 250

theorem hg_ex_jLoop (V : ℕ) (W O Q : Str) : ∀ (n : ℕ) (E : List SatSym) (s : hg_R), s.J = n →
    s.T = 0 → s.X + n * (3 * s.K + 12) ≤ V →
    ExecLe hg_jLoop (hg_S W O Q E s)
      (.norm (hg_S W O Q (E ++ hg_jP s.K s.X n) {s with J := 0, X := s.X + n * (3 * s.K + 12)}))
      (n * (hg_Bj V + 1) + 2)
  | 0, E, s, hJ, _, _ => (hg_cend (by rw [hg_Sreg _ _ _ _ _ (by norm_num), hg_rg13, hJ]; rfl)).cast
      (by cases s; simp only at hJ; subst hJ; simp [hg_jP]) (by simp)
  | n + 1, E, s, hJ, hT, hV => by
    set s1 : hg_R := {s with J := n}
    have p1 := hg_em_vSp s1 W O Q E
    have p2 := hg_inc3X W O Q (E ++ hg_vtxS s1.K s1.X) s1
    have p3 := hg_em_vSp {s1 with X := s1.X + 3} W O Q (E ++ hg_vtxS s1.K s1.X)
    have p4 := hg_inc3X W O Q (E ++ hg_vtxS s1.K s1.X ++ hg_vtxS s1.K (s1.X + 3))
      {s1 with X := s1.X + 3}
    set s2 : hg_R := {s1 with X := s1.X + 3 + 3}
    set E2 := E ++ hg_vtxS s1.K s1.X ++ hg_vtxS s1.K (s1.X + 3)
    have p5 := hg_cp6_14 W O Q E2 s2
    have p6 := hg_pushT W O Q E2 {s2 with T := s2.T + s2.K}
    have p7 := hg_pushT W O Q E2 {s2 with T := s2.T + s2.K + 1}
    have hV' : s.X + (3 * s.K + 12) ≤ V := le_trans (by nlinarith) hV
    have p8 := hg_ex_tLoop V W O Q (s.K + 2) E2 {s2 with T := s2.T + s2.K + 1 + 1}
      (by simp [s2, s1, hT]) (by simp [s2, s1]) (by simp [s2, s1]; omega)
    set s3 : hg_R := {s with J := n, X := s.X + 3 * s.K + 12}
    set s2' : hg_R := { s2 with T := s2.T + s2.K + 1 + 1 }
    have e3 : ({ s2' with T := 0, X := s2'.X + 3 * (s.K + 2) } : hg_R) = s3 := by
      simp only [s3, s2', s2, s1, hT]; congr 1; omega
    rw [e3] at p8
    have ih := hg_ex_jLoop V W O Q n (E2 ++ hg_tP (s.X + 6) (s.K + 2)) s3 rfl (by simp [s3, hT])
      (by simp only [s3]; nlinarith)
    have hstep := p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm (p5.seq_norm (p6.seq_norm
      (p7.seq_norm p8))))))
    refine (hg_cstep (n := n) (by rw [hg_Sreg _ _ _ _ _ (by norm_num), hg_rg13, hJ])
      (by rw [hg_updS13]; exact hstep) ih).cast ?_ ?_
    · simp only [hg_jP, hg_rowP, s3, s1, E2, List.append_assoc]
      congr 2; congr 1; ring
    · have hX : s.X + 3 ≤ V := by omega
      have hK : s.K ≤ V := by omega
      have m1 : (s.K + 2) * (27 * V + 64) ≤ (V + 2) * (27 * V + 64) :=
        Nat.mul_le_mul (by omega) le_rfl
      simp only [s2, s1, hg_Bj] at *
      nlinarith

/-- The rows of the final hub. -/
def hg_zP (K X : ℕ) : List SatSym := (one (X + 1) ++ [sep]) ++ (one (X + 2) ++ [sep]) ++ (one K ++ [sep])

def hg_zRows : Cmd :=
  .seq (hg_zsR 12) (.seq (emL [zero, pos, sep]) (.seq (hg_zsR 12)
    (.seq (emL [zero, zero, pos, sep]) (.seq (hg_zsR 6) (emL [pos, sep])))))

theorem hg_em_zRows (s : hg_R) : hg_Em hg_zRows s (hg_zP s.K s.X) (18 * s.X + 9 * s.K + 40) := by
  refine ((hg_em_zX s).seq ((hg_em_emL _ s).seq ((hg_em_zX s).seq ((hg_em_emL _ s).seq
    ((hg_em_zK s).seq (hg_em_emL _ s)))))).cast ?_ (by simp; omega)
  simp only [hg_zP, one, List.replicate_add, List.append_assoc]
  simp [List.replicate_succ]

end Pnp.Karp.Ham
