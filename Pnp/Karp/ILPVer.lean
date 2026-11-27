import Pnp.Karp.ILP
import Pnp.Karp.KnapVer

/-!
# 0-1 INTEGER PROGRAMMING ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/ILP.lean`) and a certificate `y : List Bool` (the variables `x = y`; missing bits
are `false`).  Numbers are bit stacks, least significant bit on top.  It reuses the
ripple-carry adder `sv_addLoop` of SUBSET SUM (`Pnp/Karp/SubVer.lean`, framed by `kv_mix` and
renamed by `kv_ren` as in `Pnp/Karp/KnapVer.lean`) and the comparison loop `kv_cmpLoop`.

Stacks (fields of `ilv_S`): `0` the certificate `Y` (never consumed); `1` the code `Q` of the
remaining rows; `3`–`7` the adder (`3` its input `K`, `5` the accumulator `L` of the
`P`-chunks, `6`, `7` sum bits and carry); `8` the accumulator `A` of the `N`-chunks; `9` the
current vector `Z` (a copy of `true :: Y`, consumed pair by pair); `10` a temporary; `11` the
code `B` of the current chunk (reversed); `12` the flag `G` "the current pair is selected";
`13` the flag `E` "the chunk ended the row"; `14` the flag of the comparison.

Program (`ilv_ver`):
1. parse (`phaseA`, `trimC 2`, `move 2 1`);
2. `ilv_rowL`, per row (accept at the end of the input): `Z := true :: Y` (`copyVia 0 9 10`,
   `push 9 true`); `ilv_pairL`; `drain 9`;
3. `ilv_pairL`, per pair of chunks: pop the next bit of `Z` into `G`; read the chunk `P` into
   `B` (`ilv_readL`, up to `neg` or `sep`); if `G`, add it to `L` (`ilv_addL`: terminate `B`
   by the code of `sep`, move it to `3`, `sv_addLoop`), otherwise drop it; unless the row has
   ended, the same for the chunk `N` and `A` (`ilv_addR`, the adder with `5 ↔ 8`); at the end
   of the row compare `A ≤ L` (`kv_cmpLoop 8 5 14`, which also empties both), halt `false`
   if not, and leave the loop.

`ilv_exec_ver`: the program halts with `ilv_vres (dec z).1 (dec z).2` within `ilv_Tver |z|`
steps.
-/

namespace Pnp.Karp.ILP

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack

/-! ## Semantics -/

/-- The accumulator after adding the value of the chunk `e`. -/
def ilv_acc (A : Str) (e : List SatSym) : Str := sv_addL false A (sv_bits e)

/-- What the pair loop computes on the chunks `cs` (vector `Z`, accumulators `L`, `A`). -/
def ilv_pg : List (List SatSym) → Str → Str → Str → Bool
  | [], _, L, A => kv_leF true A L
  | [a], Z, L, A => kv_leF true A (if Z.headD false then ilv_acc L a else L)
  | [a, b], Z, L, A => kv_leF true (if Z.headD false then ilv_acc A b else A)
      (if Z.headD false then ilv_acc L a else L)
  | a :: b :: c :: cs, Z, L, A => ilv_pg (c :: cs) Z.tail (if Z.headD false then ilv_acc L a else L)
      (if Z.headD false then ilv_acc A b else A)

/-- The verdict on one row. -/
def ilv_row (y : Str) (r : List SatSym) : Bool := ilv_pg (ichunks r) (true :: y) [] []

/-- The answer of the verifier on `(w, y)`. -/
def ilv_vres (w : List SatSym) (y : Str) : Bool := (clauses w).all (ilv_row y)

/-- The code of the row with chunks `cs` (chunks joined by `neg`, then `sep`), then `Q'`. -/
def ilv_cenc : List (List SatSym) → Str → Str
  | [], Q' => Q'
  | [c], Q' => c.flatMap ic ++ false :: false :: Q'
  | c :: d :: cs, Q' => c.flatMap ic ++ true :: true :: ilv_cenc (d :: cs) Q'

theorem ilv_ichunks_ne : ∀ r : List SatSym, ichunks r ≠ []
  | [] => by simp [ichunks]
  | s :: r => by
    unfold ichunks
    split_ifs
    · simp
    · cases ichunks r <;> simp

theorem ilv_cenc_ichunks (Q' : Str) : ∀ r : List SatSym, sep ∉ r →
    r.flatMap ic ++ false :: false :: Q' = ilv_cenc (ichunks r) Q'
  | [], _ => by simp [ichunks, ilv_cenc]
  | s :: r, h => by
    have hr : sep ∉ r := fun e => h (List.mem_cons_of_mem _ e)
    have ih := ilv_cenc_ichunks Q' r hr
    have hne := ilv_ichunks_ne r
    unfold ichunks
    by_cases hs : s = neg
    · subst hs
      rw [if_pos rfl]
      obtain ⟨d, cs, e⟩ := List.exists_cons_of_ne_nil hne
      rw [e] at ih ⊢
      simp [ilv_cenc, ic, ih]
    · rw [if_neg hs]
      rcases e : ichunks r with _ | ⟨c, _ | ⟨d, cs⟩⟩
      · exact absurd e hne
      · rw [e] at ih; simp [ilv_cenc] at ih ⊢; rw [ih]
      · rw [e] at ih; simp [ilv_cenc] at ih ⊢; rw [ih]

theorem ilv_ichunks_sym : ∀ r : List SatSym, sep ∉ r → ∀ c ∈ ichunks r, ∀ x ∈ c,
    x = zero ∨ x = pos
  | [], _ => by simp [ichunks]
  | s :: r, h => by
    have hr : sep ∉ r := fun e => h (List.mem_cons_of_mem _ e)
    have hs : s ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := ilv_ichunks_sym r hr
    unfold ichunks
    by_cases hn : s = neg
    · rw [if_pos hn]
      simp only [List.mem_cons]
      rintro c (rfl | hc)
      · simp
      · exact ih c hc
    · rw [if_neg hn]
      have hs' : s = zero ∨ s = pos := by cases s <;> simp_all
      rcases e : ichunks r with _ | ⟨c, cs⟩
      · simp only [List.mem_singleton]
        rintro c rfl x hx; simp at hx; rw [hx]; exact hs'
      · rw [e] at ih
        simp only [List.mem_cons]
        rintro c' (rfl | hc)
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hs'
          · exact ih c (by simp) x hx
        · exact ih c' (by simp [hc])

theorem ilv_ichunks_len : ∀ r : List SatSym,
    ((ichunks r).map List.length).sum + (ichunks r).length ≤ r.length + 1
  | [] => by simp [ichunks]
  | s :: r => by
    have ih := ilv_ichunks_len r
    unfold ichunks
    split_ifs
    · simp; omega
    · rcases e : ichunks r with _ | ⟨c, cs⟩
      · simp
      · rw [e] at ih; simp at ih ⊢; omega

/-! ## Stack layout -/

/-- The stacks of the verifier. -/
structure ilv_S where
  Y : Str
  Q : Str
  W : Str
  K : Str
  T : Str
  L : Str
  S : Str
  C : Str
  A : Str
  Z : Str
  U : Str
  B : Str
  G : Str
  E : Str
  F : Str

/-- The stack assignment of a record. -/
def ilv_S.st (s : ilv_S) : ℕ → Str := fun j =>
  if j = 0 then s.Y else if j = 1 then s.Q else if j = 2 then s.W else if j = 3 then s.K else
  if j = 4 then s.T else if j = 5 then s.L else if j = 6 then s.S else if j = 7 then s.C else
  if j = 8 then s.A else if j = 9 then s.Z else if j = 10 then s.U else if j = 11 then s.B else
  if j = 12 then s.G else if j = 13 then s.E else if j = 14 then s.F else []

theorem ilv_st_big (s : ilv_S) (j : ℕ) (h : 15 ≤ j) : s.st j = [] := by
  unfold ilv_S.st; repeat rw [if_neg (by omega)]

local macro "ilvx" : tactic =>
  `(tactic| (funext j; by_cases h : j < 15
             · interval_cases j <;> rfl
             · rw [update_of_ne (by omega), ilv_st_big _ _ (by omega), ilv_st_big _ _ (by omega)]))

section St
variable (s : ilv_S) (v : Str)
@[simp] theorem ilv_st0 : s.st 0 = s.Y := rfl
@[simp] theorem ilv_st1 : s.st 1 = s.Q := rfl
@[simp] theorem ilv_st2 : s.st 2 = s.W := rfl
@[simp] theorem ilv_st3 : s.st 3 = s.K := rfl
@[simp] theorem ilv_st4 : s.st 4 = s.T := rfl
@[simp] theorem ilv_st5 : s.st 5 = s.L := rfl
@[simp] theorem ilv_st6 : s.st 6 = s.S := rfl
@[simp] theorem ilv_st7 : s.st 7 = s.C := rfl
@[simp] theorem ilv_st8 : s.st 8 = s.A := rfl
@[simp] theorem ilv_st9 : s.st 9 = s.Z := rfl
@[simp] theorem ilv_st10 : s.st 10 = s.U := rfl
@[simp] theorem ilv_st11 : s.st 11 = s.B := rfl
@[simp] theorem ilv_st12 : s.st 12 = s.G := rfl
@[simp] theorem ilv_st13 : s.st 13 = s.E := rfl
@[simp] theorem ilv_st14 : s.st 14 = s.F := rfl
@[simp] theorem ilv_u0 : update s.st 0 v = {s with Y := v}.st := by ilvx
@[simp] theorem ilv_u1 : update s.st 1 v = {s with Q := v}.st := by ilvx
@[simp] theorem ilv_u2 : update s.st 2 v = {s with W := v}.st := by ilvx
@[simp] theorem ilv_u3 : update s.st 3 v = {s with K := v}.st := by ilvx
@[simp] theorem ilv_u4 : update s.st 4 v = {s with T := v}.st := by ilvx
@[simp] theorem ilv_u5 : update s.st 5 v = {s with L := v}.st := by ilvx
@[simp] theorem ilv_u6 : update s.st 6 v = {s with S := v}.st := by ilvx
@[simp] theorem ilv_u7 : update s.st 7 v = {s with C := v}.st := by ilvx
@[simp] theorem ilv_u8 : update s.st 8 v = {s with A := v}.st := by ilvx
@[simp] theorem ilv_u9 : update s.st 9 v = {s with Z := v}.st := by ilvx
@[simp] theorem ilv_u10 : update s.st 10 v = {s with U := v}.st := by ilvx
@[simp] theorem ilv_u11 : update s.st 11 v = {s with B := v}.st := by ilvx
@[simp] theorem ilv_u12 : update s.st 12 v = {s with G := v}.st := by ilvx
@[simp] theorem ilv_u13 : update s.st 13 v = {s with E := v}.st := by ilvx
@[simp] theorem ilv_u14 : update s.st 14 v = {s with F := v}.st := by ilvx
end St

/-! ## Reading a chunk -/

def ilv_readB : Cmd :=
  .pop 1 (.halt false) (.pop 1 (.halt false) (.seq (.push 13 true) .brk)
      (.seq (.push 11 false) (.push 11 true)))
    (.pop 1 (.halt false) (.seq (.push 11 true) (.push 11 false)) .brk)

/-- Read the chunk on `Q` (up to `neg`, or `sep`: then `E` is set) onto `B`, reversed. -/
def ilv_readL : Cmd := .loop ilv_readB

theorem ilv_ex_read (e : Bool) (Q' : Str) : ∀ (c : List SatSym) (s : ilv_S),
    (∀ x ∈ c, x = zero ∨ x = pos) → s.Q = c.flatMap ic ++ (!e) :: (!e) :: Q' → s.E = [] →
    ExecLe ilv_readL s.st
      (.norm {s with Q := Q', B := (c.flatMap ic).reverse ++ s.B, E := CookLevin.fl e}.st)
      (4 * c.length + 4)
  | [], s, _, hQ, hE => by
    cases e
    · refine (ExecLe.loop_brk (ExecLe.pop_cons (b := true) (s := true :: Q') (by simp [hQ])
        (ExecLe.pop_cons (b := true) (s := Q') (by simp) (ExecLe.brk _)))).cast ?_ (by simp)
      simp only [ilv_u1]; congr 1; cases s; simp_all [CookLevin.fl]
    · refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := false :: Q') (by simp [hQ])
        (ExecLe.pop_cons (b := false) (s := Q') (by simp)
          ((ExecLe.push 13 true _).seq_norm (ExecLe.brk _))))).cast ?_ (by simp)
      simp only [ilv_u1, ilv_st13, ilv_u13]; congr 1; cases s; simp_all [CookLevin.fl]
  | x :: c, s, hc, hQ, hE => by
    have hx := hc x (by simp)
    have hc' : ∀ x ∈ c, x = zero ∨ x = pos := fun y hy => hc y (by simp [hy])
    set Q1 := c.flatMap ic ++ (!e) :: (!e) :: Q'
    have ih := ilv_ex_read e Q' c {s with Q := Q1, B := (ic x).reverse ++ s.B} hc' rfl hE
    have hb : ExecLe ilv_readB s.st (.norm {s with Q := Q1, B := (ic x).reverse ++ s.B}.st) 4 := by
      rcases hx with rfl | rfl
      · exact (ExecLe.pop_cons (b := false) (s := true :: Q1) (by simp [hQ, ic, Q1])
          (ExecLe.pop_cons (b := true) (s := Q1) (by simp)
            ((ExecLe.push 11 false _).seq_norm (ExecLe.push 11 true _)))).cast
          (by simp [ic]) le_rfl
      · exact (ExecLe.pop_cons (b := true) (s := false :: Q1) (by simp [hQ, ic, Q1])
          (ExecLe.pop_cons (b := false) (s := Q1) (by simp)
            ((ExecLe.push 11 true _).seq_norm (ExecLe.push 11 false _)))).cast
          (by simp [ic]) le_rfl
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    simp

/-! ## Adding a chunk to an accumulator -/

/-- The stacks untouched by the adder `sv_addLoop` (all but `3`–`7`). -/
def ilv_Fa : ℕ → Bool := fun j => !(decide (3 ≤ j) && decide (j ≤ 7))

/-- The renaming for the accumulator `A` of the `N`-chunks. -/
def ilv_π : Equiv.Perm ℕ := Equiv.swap 5 8

theorem ilv_av_add : kv_av ilv_Fa sv_addLoop = true := by decide

theorem ilv_mixst (s : ilv_S) (R Q Tv A S : Str) (c : Bool) :
    kv_mix ilv_Fa (sv_st R Q Tv A S c) s.st =
      {s with K := Q, T := Tv, L := A, S := S, C := CookLevin.fl c}.st := by
  funext j
  by_cases hj : j < 15
  · interval_cases j <;> rfl
  · have hF : ilv_Fa j = true := by simp [ilv_Fa]; omega
    simp only [kv_mix, hF, if_true]
    rw [ilv_st_big _ _ (by omega), ilv_st_big _ _ (by omega)]

theorem ilv_mixstR (s : ilv_S) (R Q Tv A S : Str) (c : Bool) :
    kv_mix ilv_Fa (sv_st R Q Tv A S c) (s.st ∘ ilv_π) ∘ ilv_π.symm =
      {s with K := Q, T := Tv, A := A, S := S, C := CookLevin.fl c}.st := by
  funext j
  by_cases hj : j < 15
  · interval_cases j <;> rfl
  · have hF : ilv_Fa j = true := by simp [ilv_Fa]; omega
    have h1 : ilv_π j = j := Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
    have h2 : ilv_π.symm j = j := by
      simp only [ilv_π, Equiv.symm_swap]; exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
    simp only [comp_apply, h2, kv_mix, hF, if_true, h1]
    rw [ilv_st_big _ _ (by omega), ilv_st_big _ _ (by omega)]

/-- Add the chunk on `B` to `L`. -/
def ilv_addL : Cmd := .seq (.push 3 false) (.seq (.push 3 false) (.seq (move 11 3) sv_addLoop))

/-- Add the chunk on `B` to `A`. -/
def ilv_addR : Cmd :=
  .seq (.push 3 false) (.seq (.push 3 false) (.seq (move 11 3) (kv_ren ilv_π sv_addLoop)))

/-- The common prefix: `B` becomes the input row of the adder. -/
theorem ilv_ex_pre (s : ilv_S) (e : List SatSym) (hB : s.B = (e.flatMap ic).reverse)
    (hK : s.K = []) {c : Cmd} {r : Res} {T : ℕ}
    (h : ExecLe c {s with B := [], K := e.flatMap ic ++ [false, false]}.st r T) :
    ExecLe (.seq (.push 3 false) (.seq (.push 3 false) (.seq (move 11 3) c))) s.st r
      (4 * e.length + 4 + T) := by
  have h1 := ExecLe.push 3 false s.st
  have h2 := ExecLe.push 3 false (update s.st 3 (false :: s.st 3))
  simp only [ilv_u3, ilv_st3] at h1 h2
  have h3 := exec_move (a := 11) (b := 3) (by decide) _
    {s with K := false :: false :: s.K}.st rfl
  simp only [ilv_u11, ilv_st11, ilv_u3, ilv_st3] at h3
  have h3' : ExecLe (move 11 3) {s with K := false :: false :: s.K}.st
      (.norm {s with B := [], K := e.flatMap ic ++ [false, false]}.st) (2 * s.B.length + 2) :=
    (ExecLe.of h3).cast (by simp [hB, hK]) le_rfl
  have hl : (s.B).length = 2 * e.length := by rw [hB, List.length_reverse, length_flatMap_ic]
  refine (h1.seq_norm (h2.seq_norm (h3'.seq_norm h))).cast rfl ?_
  simp only [hl]; omega

theorem ilv_ex_addL (s : ilv_S) (Nacc : ℕ) (e : List SatSym) (hsep : sep ∉ e)
    (hB : s.B = (e.flatMap ic).reverse) (hK : s.K = []) (hS : s.S = []) (hC : s.C = [])
    (hN : s.L.length + e.length ≤ Nacc) :
    ExecLe ilv_addL s.st (.norm {s with B := [], L := ilv_acc s.L e}.st)
      (11 * e.length + 8 * Nacc + 24) := by
  set s3 : ilv_S := {s with B := [], K := e.flatMap ic ++ [false, false]}
  have h := sv_ex_addRow (R := s.Y) (T := s.T) Nacc [] e s.L [] false hsep (by simp; omega)
  have h' := kv_mix_le s3.st h ilv_av_add
  simp only [kv_rmap] at h'
  rw [ilv_mixst, ilv_mixst] at h'
  have e3 : ({s3 with K := e.flatMap ic ++ false :: false :: [], T := s.T, L := s.L, S := [], C := CookLevin.fl false} : ilv_S) = s3 := by
    simp only [s3]; cases s; simp_all [CookLevin.fl]
  rw [e3] at h'
  refine (ilv_ex_pre s e hB hK h').cast ?_ (by omega)
  simp only [s3, ilv_acc]; congr 1; cases s; simp_all [CookLevin.fl]

theorem ilv_ex_addR (s : ilv_S) (Nacc : ℕ) (e : List SatSym) (hsep : sep ∉ e)
    (hB : s.B = (e.flatMap ic).reverse) (hK : s.K = []) (hS : s.S = []) (hC : s.C = [])
    (hN : s.A.length + e.length ≤ Nacc) :
    ExecLe ilv_addR s.st (.norm {s with B := [], A := ilv_acc s.A e}.st)
      (11 * e.length + 8 * Nacc + 24) := by
  set s3 : ilv_S := {s with B := [], K := e.flatMap ic ++ [false, false]}
  have h := sv_ex_addRow (R := s.Y) (T := s.T) Nacc [] e s.A [] false hsep (by simp; omega)
  have h' := kv_ren_le ilv_π (kv_mix_le (s3.st ∘ ilv_π) h ilv_av_add) kv_nc_add
  simp only [kv_rmap] at h'
  rw [ilv_mixstR, ilv_mixstR] at h'
  have e3 : ({s3 with K := e.flatMap ic ++ false :: false :: [], T := s.T, A := s.A, S := [], C := CookLevin.fl false} : ilv_S) = s3 := by
    simp only [s3]; cases s; simp_all [CookLevin.fl]
  rw [e3] at h'
  refine (ilv_ex_pre s e hB hK h').cast ?_ (by omega)
  simp only [s3, ilv_acc]; congr 1; cases s; simp_all [CookLevin.fl]

/-! ## Selecting, flags, the comparison -/

theorem ilv_ex_drain (k : ℕ) (σ : ℕ → Str) :
    ExecLe (drain k) σ (.norm (update σ k [])) (2 * (σ k).length + 2) :=
  ExecLe.of (exec_drain k _ σ rfl)

/-- Add the chunk on `B` to `L` if `G` is set, drop it otherwise. -/
def ilv_selL : Cmd := .pop 12 (drain 11) (drain 11) (.seq (.push 12 true) ilv_addL)

/-- Add the chunk on `B` to `A` if `G` is set, drop it otherwise. -/
def ilv_selR : Cmd := .pop 12 (drain 11) (drain 11) (.seq (.push 12 true) ilv_addR)

theorem ilv_ex_selL (s : ilv_S) (g : Bool) (hG : s.G = CookLevin.fl g) (Nacc : ℕ)
    (e : List SatSym) (hsep : sep ∉ e) (hB : s.B = (e.flatMap ic).reverse) (hK : s.K = [])
    (hS : s.S = []) (hC : s.C = []) (hN : s.L.length + e.length ≤ Nacc) :
    ExecLe ilv_selL s.st (.norm {s with B := [], L := if g then ilv_acc s.L e else s.L}.st)
      (11 * e.length + 8 * Nacc + 26) := by
  have hl : (s.B).length = 2 * e.length := by rw [hB, List.length_reverse, length_flatMap_ic]
  cases g
  · refine (ExecLe.pop_nil (by simpa [CookLevin.fl] using hG) (ilv_ex_drain 11 s.st)).cast ?_
      (by rw [ilv_st11, hl]; omega)
    simp
  · have h := ilv_ex_addL s Nacc e hsep hB hK hS hC hN
    have hp := ExecLe.push 12 true (update s.st 12 [])
    simp only [ilv_u12, ilv_st12] at hp
    have e1 : ({ {s with G := []} with G := [true] } : ilv_S) = s := by
      cases s; simp_all [CookLevin.fl]
    rw [e1] at hp
    refine ExecLe.pop_cons (b := true) (s := []) (by simp [hG, CookLevin.fl]) ?_
    simp only [ilv_u12, if_true]
    exact (hp.seq_norm h).cast (by simp) (by omega)

theorem ilv_ex_selR (s : ilv_S) (g : Bool) (hG : s.G = CookLevin.fl g) (Nacc : ℕ)
    (e : List SatSym) (hsep : sep ∉ e) (hB : s.B = (e.flatMap ic).reverse) (hK : s.K = [])
    (hS : s.S = []) (hC : s.C = []) (hN : s.A.length + e.length ≤ Nacc) :
    ExecLe ilv_selR s.st (.norm {s with B := [], A := if g then ilv_acc s.A e else s.A}.st)
      (11 * e.length + 8 * Nacc + 26) := by
  have hl : (s.B).length = 2 * e.length := by rw [hB, List.length_reverse, length_flatMap_ic]
  cases g
  · refine (ExecLe.pop_nil (by simpa [CookLevin.fl] using hG) (ilv_ex_drain 11 s.st)).cast ?_
      (by rw [ilv_st11, hl]; omega)
    simp
  · have h := ilv_ex_addR s Nacc e hsep hB hK hS hC hN
    have hp := ExecLe.push 12 true (update s.st 12 [])
    simp only [ilv_u12, ilv_st12] at hp
    have e1 : ({ {s with G := []} with G := [true] } : ilv_S) = s := by
      cases s; simp_all [CookLevin.fl]
    rw [e1] at hp
    refine ExecLe.pop_cons (b := true) (s := []) (by simp [hG, CookLevin.fl]) ?_
    simp only [ilv_u12, if_true]
    exact (hp.seq_norm h).cast (by simp) (by omega)

/-- Pop the next bit of `Z` into `G`. -/
def ilv_getB : Cmd := .pop 9 .skip .skip (.push 12 true)

theorem ilv_ex_getB (s : ilv_S) (hG : s.G = []) :
    ExecLe ilv_getB s.st (.norm {s with Z := s.Z.tail, G := CookLevin.fl (s.Z.headD false)}.st)
      2 := by
  rcases hZ : s.Z with _ | ⟨_ | _, Z'⟩
  · refine (ExecLe.pop_nil (by simp [hZ]) (ExecLe.skip _)).cast ?_ (by omega)
    congr 1; cases s; simp_all [CookLevin.fl]
  · refine (ExecLe.pop_cons (b := false) (s := Z') (by simp [hZ]) (ExecLe.skip _)).cast ?_
      (by omega)
    simp only [ilv_u9]; congr 1; cases s; simp_all [CookLevin.fl]
  · refine (ExecLe.pop_cons (b := true) (s := Z') (by simp [hZ]) (ExecLe.push 12 true _)).cast ?_
      le_rfl
    simp only [ilv_u9, ilv_u12, ilv_st12]; congr 1; cases s; simp_all [CookLevin.fl]

/-- Clear `G`. -/
def ilv_clrG : Cmd := .pop 12 .skip .skip .skip

theorem ilv_ex_clrG (s : ilv_S) (g : Bool) (hG : s.G = CookLevin.fl g) :
    ExecLe ilv_clrG s.st (.norm {s with G := []}.st) 2 := by
  cases g
  · refine (ExecLe.pop_nil (by simpa [CookLevin.fl] using hG) (ExecLe.skip _)).cast ?_ le_rfl
    congr 1; cases s; simp_all [CookLevin.fl]
  · exact (ExecLe.pop_cons (b := true) (s := []) (by simp [hG, CookLevin.fl])
      (ExecLe.skip _)).cast (by simp) le_rfl

section Cmp
variable {a b f : ℕ} (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f)
include hab haf hbf

/-- `kv_ex_cmp`, also recording that the comparison empties both stacks. -/
theorem ilv_ex_cmp : ∀ (X Y : Str) (g : Bool) (σ : ℕ → Str), σ a = X → σ b = Y →
    σ f = CookLevin.fl g →
    ∃ σ', ExecLe (kv_cmpLoop a b f) σ (.norm σ') (5 * (X.length + Y.length) + 3) ∧
      σ' f = CookLevin.fl (kv_leF g X Y) ∧ σ' a = [] ∧ σ' b = [] ∧
      ∀ j, j ≠ a → j ≠ b → j ≠ f → σ' j = σ j
  | [], [], g, σ, ha, hb, hf =>
    ⟨σ, (ExecLe.loop_brk (ExecLe.pop_nil ha (ExecLe.pop_nil hb (ExecLe.brk _)))).cast rfl
      (by simp), by simp [kv_leF, hf], ha, hb, fun _ _ _ _ => rfl⟩
  | [], y :: Y, g, σ, ha, hb, hf => by
    obtain ⟨σ₁, h1, h1a, h1b, h1f, h1j⟩ := kv_ex_cmpB hab haf hbf [] (y :: Y) g σ ha hb hf
      (by simp)
    obtain ⟨σ', h2, h2f, h2a, h2b, h2j⟩ := ilv_ex_cmp [] Y _ σ₁ h1a h1b h1f
    refine ⟨σ', (ExecLe.loop_norm h1 h2).cast rfl (by simp; omega), by simpa [kv_leF] using h2f,
      h2a, h2b, fun j j1 j2 j3 => by rw [h2j j j1 j2 j3, h1j j j1 j2 j3]⟩
  | x :: X, [], g, σ, ha, hb, hf => by
    obtain ⟨σ₁, h1, h1a, h1b, h1f, h1j⟩ := kv_ex_cmpB hab haf hbf (x :: X) [] g σ ha hb hf
      (by simp)
    obtain ⟨σ', h2, h2f, h2a, h2b, h2j⟩ := ilv_ex_cmp X [] _ σ₁ h1a h1b h1f
    refine ⟨σ', (ExecLe.loop_norm h1 h2).cast rfl (by simp; omega), by simpa [kv_leF] using h2f,
      h2a, h2b, fun j j1 j2 j3 => by rw [h2j j j1 j2 j3, h1j j j1 j2 j3]⟩
  | x :: X, y :: Y, g, σ, ha, hb, hf => by
    obtain ⟨σ₁, h1, h1a, h1b, h1f, h1j⟩ := kv_ex_cmpB hab haf hbf (x :: X) (y :: Y) g σ ha hb
      hf (by simp)
    obtain ⟨σ', h2, h2f, h2a, h2b, h2j⟩ := ilv_ex_cmp X Y _ σ₁ h1a h1b h1f
    refine ⟨σ', (ExecLe.loop_norm h1 h2).cast rfl (by simp; omega), by simpa [kv_leF] using h2f,
      h2a, h2b, fun j j1 j2 j3 => by rw [h2j j j1 j2 j3, h1j j j1 j2 j3]⟩

end Cmp

/-- At the end of a row: `A ≤ L`, or halt `false`; leave the pair loop. -/
def ilv_finC : Cmd :=
  .seq (.push 14 true) (.seq (kv_cmpLoop 8 5 14) (.pop 14 (.halt false) (.halt false) .brk))

theorem ilv_ex_finC (s : ilv_S) (hF : s.F = []) :
    ExecLe ilv_finC s.st
      (if kv_leF true s.A s.L then .brk {s with A := [], L := []}.st else .halt false)
      (5 * (s.A.length + s.L.length) + 6) := by
  have hp := ExecLe.push 14 true s.st
  obtain ⟨σ', h1, h1f, h1a, h1b, h1j⟩ := ilv_ex_cmp (a := 8) (b := 5) (f := 14) (by decide)
    (by decide) (by decide) s.A s.L true (update s.st 14 (true :: s.st 14)) (by simp) (by simp)
    (by simp [hF, CookLevin.fl])
  refine (hp.seq_norm (h1.seq_norm (T₂ := 2) ?_)).cast rfl (by omega)
  cases hr : kv_leF true s.A s.L
  · rw [hr] at h1f
    exact (ExecLe.pop_nil h1f (ExecLe.halt false _)).cast (by simp) (by omega)
  · rw [hr] at h1f
    refine (ExecLe.pop_cons (b := true) (s := []) h1f (ExecLe.brk _)).cast ?_ (by omega)
    simp only [if_true]
    congr 1; funext j
    by_cases j14 : j = 14
    · subst j14; simp [hF]
    by_cases j5 : j = 5
    · subst j5; simp [h1b]
    by_cases j8 : j = 8
    · subst j8; simp [h1a]
    rw [update_of_ne j14, h1j j j8 j5 j14, update_of_ne j14]
    by_cases hj : j < 15
    · interval_cases j <;> first | rfl | omega
    · rw [ilv_st_big _ _ (by omega), ilv_st_big _ _ (by omega)]

/-! ## The pair loop -/

/-- The second chunk of a pair. -/
def ilv_nB : Cmd := .seq ilv_readL (.seq ilv_selR (.seq ilv_clrG (.pop 13 .skip .skip ilv_finC)))

def ilv_pairB : Cmd :=
  .seq ilv_getB (.seq ilv_readL (.seq ilv_selL (.pop 13 ilv_nB .skip (.seq ilv_clrG ilv_finC))))

/-- Per pair of chunks: see the module docstring. -/
def ilv_pairL : Cmd := .loop ilv_pairB

/-- The empty work stacks. -/
structure ilv_Inv (s : ilv_S) : Prop where
  hK : s.K = []
  hS : s.S = []
  hC : s.C = []
  hU : s.U = []
  hB : s.B = []
  hG : s.G = []
  hE : s.E = []
  hF : s.F = []

theorem ilv_ex_half1 (N : ℕ) (s : ilv_S) (hi : ilv_Inv s) (a : List SatSym) (e : Bool) (Q1 : Str)
    (ha : ∀ x ∈ a, x = zero ∨ x = pos) (hQ : s.Q = a.flatMap ic ++ (!e) :: (!e) :: Q1)
    (hN : s.L.length + a.length ≤ N) {k : Cmd} {r : Res} {T : ℕ}
    (h : ExecLe k
      { s with
        Q := Q1, Z := s.Z.tail, G := CookLevin.fl (s.Z.headD false), E := CookLevin.fl e,
        L := if s.Z.headD false then ilv_acc s.L a else s.L }.st r T) :
    ExecLe (.seq ilv_getB (.seq ilv_readL (.seq ilv_selL k))) s.st r
      (15 * a.length + 8 * N + 32 + T) := by
  have hsep : sep ∉ a := fun hm => by rcases ha sep hm with h | h <;> cases h
  have h1 := ilv_ex_getB s hi.hG
  have h2 := ilv_ex_read e Q1 a {s with Z := s.Z.tail, G := CookLevin.fl (s.Z.headD false)} ha
    hQ hi.hE
  have h3 := ilv_ex_selL
    { s with
      Z := s.Z.tail, G := CookLevin.fl (s.Z.headD false), Q := Q1,
      B := (a.flatMap ic).reverse ++ s.B, E := CookLevin.fl e } (s.Z.headD false) rfl N a hsep
    (by simp [hi.hB]) hi.hK hi.hS hi.hC hN
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (T₂ := T) ?_))).cast rfl (by omega)
  obtain ⟨hK, hS, hC, hU, hB, hG, hE, hF⟩ := hi
  convert h using 2
  cases s; simp_all

theorem ilv_ex_half2 (N : ℕ) (s : ilv_S) (g : Bool) (hG : s.G = CookLevin.fl g)
    (hK : s.K = []) (hS : s.S = []) (hC : s.C = []) (hB : s.B = []) (hE : s.E = [])
    (b : List SatSym) (e : Bool) (Q1 : Str)
    (hb : ∀ x ∈ b, x = zero ∨ x = pos) (hQ : s.Q = b.flatMap ic ++ (!e) :: (!e) :: Q1)
    (hN : s.A.length + b.length ≤ N) {k : Cmd} {r : Res} {T : ℕ}
    (h : ExecLe k
      {s with Q := Q1, G := [], E := CookLevin.fl e, A := if g then ilv_acc s.A b else s.A}.st
      r T) :
    ExecLe (.seq ilv_readL (.seq ilv_selR (.seq ilv_clrG k))) s.st r
      (15 * b.length + 8 * N + 32 + T) := by
  have hsep : sep ∉ b := fun hm => by rcases hb sep hm with h | h <;> cases h
  have h2 := ilv_ex_read e Q1 b s hb hQ hE
  have h3 := ilv_ex_selR
    {s with Q := Q1, B := (b.flatMap ic).reverse ++ s.B, E := CookLevin.fl e} g hG N b hsep
    (by simp [hB]) hK hS hC hN
  have h4 := ilv_ex_clrG
    {s with Q := Q1, B := [], E := CookLevin.fl e, A := if g then ilv_acc s.A b else s.A} g hG
  refine (h2.seq_norm (h3.seq_norm (h4.seq_norm (T₂ := T) ?_))).cast rfl (by omega)
  convert h using 2
  cases s; simp_all

theorem ilv_ex_end1 (c : Cmd) (s : ilv_S) (g : Bool) (hG : s.G = CookLevin.fl g)
    (hE : s.E = [true]) (hF : s.F = []) :
    ExecLe (.pop 13 c .skip (.seq ilv_clrG ilv_finC)) s.st
      (if kv_leF true s.A s.L then .brk {s with G := [], E := [], A := [], L := []}.st
        else .halt false) (5 * (s.A.length + s.L.length) + 9) := by
  have h1 := ilv_ex_clrG {s with E := []} g hG
  have h2 := ilv_ex_finC {s with E := [], G := []} hF
  refine ExecLe.pop_cons (b := true) (s := []) (by simp [hE]) ?_
  simp only [ilv_u13, if_true]
  exact (h1.seq_norm h2).cast rfl (by simp; omega)

theorem ilv_ex_end2 (s : ilv_S) (hE : s.E = [true]) (hF : s.F = []) :
    ExecLe (.pop 13 .skip .skip ilv_finC) s.st
      (if kv_leF true s.A s.L then .brk {s with E := [], A := [], L := []}.st
        else .halt false) (5 * (s.A.length + s.L.length) + 7) := by
  have h2 := ilv_ex_finC {s with E := []} hF
  refine ExecLe.pop_cons (b := true) (s := []) (by simp [hE]) ?_
  simp only [ilv_u13, if_true]
  exact h2.cast rfl (by simp)

theorem ilv_loopF {c : Cmd} {σ σ' : ℕ → Str} {p : Bool} {T : ℕ}
    (h : ExecLe c σ (if p then .brk σ' else .halt false) T) :
    ExecLe (.loop c) σ (if p then .norm σ' else .halt false) T := by
  cases p
  · exact ExecLe.loop_halt (by simpa using h)
  · exact ExecLe.loop_brk (by simpa using h)

theorem ilv_length_acc (A : Str) (e : List SatSym) :
    (ilv_acc A e).length ≤ A.length + e.length + 1 := by
  have := sv_addL_length false A (sv_bits e)
  simpa [ilv_acc, sv_bits] using this

theorem ilv_length_ite (g : Bool) (A : Str) (e : List SatSym) :
    (if g then ilv_acc A e else A).length ≤ A.length + e.length + 1 := by
  have := ilv_length_acc A e
  split_ifs <;> omega

/-- Cost of one iteration of the pair loop. -/
def ilv_Tp (N : ℕ) : ℕ := 60 * N + 100

theorem ilv_ex_pairs (N : ℕ) (Q' : Str) : ∀ (cs : List (List SatSym)) (s : ilv_S), cs ≠ [] →
    (∀ c ∈ cs, ∀ x ∈ c, x = zero ∨ x = pos) → ilv_Inv s → s.Q = ilv_cenc cs Q' →
    s.L.length + s.A.length + (cs.map List.length).sum + cs.length ≤ N →
    ∃ Z', Z'.length ≤ s.Z.length ∧
      ExecLe ilv_pairL s.st
        (if ilv_pg cs s.Z s.L s.A then .norm {s with Q := Q', Z := Z', L := [], A := []}.st
          else .halt false) (cs.length * ilv_Tp N)
  | [], _, h, _, _, _, _ => absurd rfl h
  | [a], s, _, hcs, hi, hQ, hN => by
    have ha := hcs a (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at hN
    have hl := ilv_length_ite (s.Z.headD false) s.L a
    have hb := ilv_ex_half1 N s hi a true Q' ha (by simpa [ilv_cenc] using hQ) (by omega)
      (ilv_ex_end1 ilv_nB _ (s.Z.headD false) rfl rfl hi.hF)
    refine ⟨s.Z.tail, by simp, (ilv_loopF hb).cast ?_ ?_⟩
    · obtain ⟨hK, hS, hC, hU, hB, hG, hE, hF⟩ := hi
      cases s; simp_all [ilv_pg]
    · simp only [ilv_Tp, List.length_cons, List.length_nil]; omega
  | [a, b], s, _, hcs, hi, hQ, hN => by
    have ha := hcs a (by simp)
    have hb' := hcs b (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at hN
    have hl := ilv_length_ite (s.Z.headD false) s.L a
    have hl2 := ilv_length_ite (s.Z.headD false) s.A b
    have h2 := ilv_ex_half2 N
      { s with
        Q := b.flatMap ic ++ false :: false :: Q', Z := s.Z.tail,
        G := CookLevin.fl (s.Z.headD false), E := [],
        L := if s.Z.headD false then ilv_acc s.L a else s.L }
      (s.Z.headD false) rfl hi.hK hi.hS hi.hC hi.hB rfl b true Q' hb' rfl (by simp; omega)
      (ilv_ex_end2 _ rfl hi.hF)
    have hb := ilv_ex_half1 N s hi a false _ ha (by simpa [ilv_cenc] using hQ) (by omega)
      (ExecLe.pop_nil (k := 13) (cn := ilv_nB) (cf := .skip) (ct := .seq ilv_clrG ilv_finC)
        (by simp [CookLevin.fl]) h2)
    refine ⟨s.Z.tail, by simp, (ilv_loopF hb).cast ?_ ?_⟩
    · obtain ⟨hK, hS, hC, hU, hB, hG, hE, hF⟩ := hi
      cases s; simp_all [ilv_pg]
    · simp only [ilv_Tp, List.length_cons, List.length_nil]; omega
  | a :: b :: c :: cs, s, _, hcs, hi, hQ, hN => by
    have ha := hcs a (by simp)
    have hb' := hcs b (by simp)
    have hcs' : ∀ c' ∈ c :: cs, ∀ x ∈ c', x = zero ∨ x = pos := fun c' h => hcs c' (by simp_all)
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hN
    have hl := ilv_length_ite (s.Z.headD false) s.L a
    have hl2 := ilv_length_ite (s.Z.headD false) s.A b
    have h2 := ilv_ex_half2 N
      { s with
        Q := b.flatMap ic ++ true :: true :: ilv_cenc (c :: cs) Q', Z := s.Z.tail,
        G := CookLevin.fl (s.Z.headD false), E := [],
        L := if s.Z.headD false then ilv_acc s.L a else s.L }
      (s.Z.headD false) rfl hi.hK hi.hS hi.hC hi.hB rfl b false _ hb' rfl (by simp; omega)
      (ExecLe.pop_nil (k := 13) (cn := .skip) (cf := .skip) (ct := ilv_finC) rfl (ExecLe.skip _))
    have hb := ilv_ex_half1 N s hi a false _ ha (by simpa [ilv_cenc] using hQ) (by omega)
      (ExecLe.pop_nil (k := 13) (cn := ilv_nB) (cf := .skip) (ct := .seq ilv_clrG ilv_finC)
        (by simp [CookLevin.fl]) h2)
    obtain ⟨Z'', hZ, ih⟩ := ilv_ex_pairs N Q' (c :: cs)
      { s with
        Q := ilv_cenc (c :: cs) Q', Z := s.Z.tail, G := [], E := [],
        L := if s.Z.headD false then ilv_acc s.L a else s.L,
        A := if s.Z.headD false then ilv_acc s.A b else s.A }
      (by simp) hcs' (by obtain ⟨⟩ := hi; constructor <;> simp_all) rfl
      (by simp only [List.map_cons, List.sum_cons, List.length_cons]; omega)
    have hb2 : ExecLe ilv_pairB s.st
        (.norm
          { s with
            Q := ilv_cenc (c :: cs) Q', Z := s.Z.tail, G := [], E := [],
            L := if s.Z.headD false then ilv_acc s.L a else s.L,
            A := if s.Z.headD false then ilv_acc s.A b else s.A }.st)
        (40 * N + 80) := by
      refine hb.cast ?_ (by omega)
      all_goals congr 1
    refine ⟨Z'', by simp at hZ; omega, (ExecLe.loop_norm hb2 ih).cast ?_ ?_⟩
    · simp only [ilv_pg]
      obtain ⟨hK, hS, hC, hU, hB, hG, hE, hF⟩ := hi
      cases s; simp_all
    · simp only [ilv_Tp, List.length_cons]; nlinarith

/-! ## The row loop -/

def ilv_rowW : Cmd := .seq (copyVia 0 9 10) (.seq (.push 9 true) (.seq ilv_pairL (drain 9)))

def ilv_rowB : Cmd := .pop 1 (.halt true) (.seq (.push 1 false) ilv_rowW) (.seq (.push 1 true) ilv_rowW)

/-- Per row: see the module docstring. -/
def ilv_rowL : Cmd := .loop ilv_rowB

/-- Cost of the row loop. -/
def ilv_Trows (N Ly : ℕ) : List (List SatSym) → ℕ
  | [] => 2
  | r :: rows => (r.length + 1) * ilv_Tp N + 7 * Ly + 20 + ilv_Trows N Ly rows

theorem ilv_ex_rowW (N : ℕ) (s : ilv_S) (hi : ilv_Inv s) (hZ : s.Z = []) (hL : s.L = [])
    (hA : s.A = []) (r : List SatSym) (Q' : Str) (hr : sep ∉ r) (hN : r.length + 1 ≤ N)
    (hQ : s.Q = r.flatMap ic ++ false :: false :: Q') :
    ExecLe ilv_rowW s.st (if ilv_row s.Y r then .norm {s with Q := Q'}.st else .halt false)
      ((r.length + 1) * ilv_Tp N + 7 * s.Y.length + 18) := by
  have h1 := ExecLe.of (exec_copyVia (a := 0) (b := 9) (t := 10) (by decide) (by decide)
    (by decide) s.st (by simpa using hi.hU))
  simp only [ilv_st0, ilv_st9, ilv_u9, hZ, List.append_nil] at h1
  have h2 := ExecLe.push 9 true {s with Z := s.Y}.st
  simp only [ilv_st9, ilv_u9] at h2
  have hcl := ilv_ichunks_len r
  obtain ⟨Z', hZ', h3⟩ := ilv_ex_pairs N Q' (ichunks r) {s with Z := true :: s.Y}
    (ilv_ichunks_ne r) (ilv_ichunks_sym r hr) (by obtain ⟨⟩ := hi; constructor <;> assumption)
    (by simp [hQ, ilv_cenc_ichunks Q' r hr]) (by simp [hL, hA]; omega)
  have hcl' : (ichunks r).length ≤ r.length + 1 := by omega
  have hT : (ichunks r).length * ilv_Tp N ≤ (r.length + 1) * ilv_Tp N :=
    Nat.mul_le_mul_right _ hcl'
  simp only at h3 hZ'
  unfold ilv_rowW ilv_row
  by_cases hp : ilv_pg (ichunks r) (true :: s.Y) [] [] = true
  · rw [if_pos hp]
    have hp2 : ilv_pg (ichunks r) (true :: s.Y) s.L s.A = true := by rw [hL, hA]; exact hp
    rw [if_pos hp2] at h3
    have h4 := ilv_ex_drain 9 {s with Z := Z', Q := Q', L := [], A := []}.st
    simp only [ilv_st9, ilv_u9] at h4
    refine (h1.seq_norm (h2.seq_norm (h3.seq_norm h4))).cast ?_ ?_
    · congr 1; cases s; simp_all
    · simp at hZ'; omega
  · rw [if_neg hp]
    have hp2 : ¬ ilv_pg (ichunks r) (true :: s.Y) s.L s.A = true := by rw [hL, hA]; exact hp
    rw [if_neg hp2] at h3
    exact (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3))).cast rfl (by simp only [List.length_cons] at *; omega)

theorem ilv_ex_rows (N : ℕ) : ∀ (rows : List (List SatSym)) (s : ilv_S), ilv_Inv s →
    s.Z = [] → s.L = [] → s.A = [] → (∀ r ∈ rows, sep ∉ r) → (∀ r ∈ rows, r.length + 1 ≤ N) →
    s.Q = enc rows →
    ExecLe ilv_rowL s.st (.halt (rows.all (ilv_row s.Y))) (ilv_Trows N s.Y.length rows)
  | [], s, _, _, _, _, _, _, hQ =>
    (ExecLe.loop_halt (ExecLe.pop_nil (by simpa [enc] using hQ) (ExecLe.halt true _))).cast
      (by simp) (by simp [ilv_Trows])
  | r :: rows, s, hi, hZ, hL, hA, hsep, hN, hQ => by
    have hr := hsep r (by simp)
    obtain ⟨x, Q'', hx⟩ := kv_enc_ne r rows
    have hw := ilv_ex_rowW N s hi hZ hL hA r (enc rows) hr (hN r (by simp))
      (by rw [hQ, enc_cons])
    have hp := ExecLe.push 1 x {s with Q := Q''}.st
    simp only [ilv_st1, ilv_u1] at hp
    have e1 : ({ {s with Q := Q''} with Q := x :: Q''} : ilv_S) = s := by
      cases s; simp_all
    rw [e1] at hp
    have hb : ExecLe ilv_rowB s.st
        (if ilv_row s.Y r then .norm {s with Q := enc rows}.st else .halt false)
        ((r.length + 1) * ilv_Tp N + 7 * s.Y.length + 20) := by
      refine ExecLe.pop_cons (b := x) (s := Q'') (by simp [hQ, hx]) ?_
      simp only [ilv_u1]
      cases x
      · exact (hp.seq_norm hw).cast rfl (by omega)
      · exact (hp.seq_norm hw).cast rfl (by omega)
    by_cases hp' : ilv_row s.Y r = true
    · rw [if_pos hp'] at hb
      have ih := ilv_ex_rows N rows {s with Q := enc rows}
        (by obtain ⟨⟩ := hi; constructor <;> assumption) hZ hL hA
        (fun r' h => hsep r' (by simp [h])) (fun r' h => hN r' (by simp [h])) rfl
      exact (ExecLe.loop_norm hb ih).cast (by simp [hp']) (by simp [ilv_Trows])
    · rw [if_neg hp'] at hb
      exact (ExecLe.loop_halt hb).cast (by simp [hp']) (by simp only [ilv_Trows]; omega)

/-! ## The whole verifier -/

def ilv_ver : Cmd := .seq phaseA (.seq (trimC 2) (.seq (move 2 1) ilv_rowL))

/-- The state after parsing. -/
def ilv_s0 (y Q : Str) : ilv_S := ⟨y, Q, [], [], [], [], [], [], [], [], [], [], [], [], []⟩

theorem ilv_Trows_le (N Ly : ℕ) : ∀ rows : List (List SatSym),
    ilv_Trows N Ly rows ≤ ((rows.map List.length).sum + rows.length) * (ilv_Tp N + 7 * Ly + 20) + 2
  | [] => by simp [ilv_Trows]
  | r :: rows => by
    have ih := ilv_Trows_le N Ly rows
    simp only [ilv_Trows, List.map_cons, List.sum_cons, List.length_cons]
    have e : ((r.length + (rows.map List.length).sum) + (rows.length + 1)) *
        (ilv_Tp N + 7 * Ly + 20) = (r.length + 1) * ilv_Tp N + (r.length + 1) * (7 * Ly + 20) +
        ((rows.map List.length).sum + rows.length) * (ilv_Tp N + 7 * Ly + 20) := by ring
    rw [e]
    have : 7 * Ly + 20 ≤ (r.length + 1) * (7 * Ly + 20) := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- Time bound of the verifier. -/
def ilv_Tver (n : ℕ) : ℕ := 70 * (n + 2) ^ 2

theorem ilv_exec_ver (z : Str) :
    ExecLe ilv_ver (init [z]).stk (.halt (ilv_vres (dec z).1 (dec z).2)) (ilv_Tver z.length) := by
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
  have hM := exec_move (a := 2) (b := 1) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 2 []) 1 ((σ₂ 2).reverse ++ σ₂ 1) =
      (ilv_s0 y (enc (clauses w))).st := by
    funext j
    by_cases hj : j < 15
    · interval_cases j <;> simp [σ₂, σ₁, he, enc, trunc, ilv_S.st, ilv_s0]
    · rw [ilv_st_big _ _ (by omega)]
      simp [σ₂, σ₁, he j (by omega), show j ≠ 0 by omega, show j ≠ 1 by omega,
        show j ≠ 2 by omega]
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  have hN : ∀ r ∈ clauses w, r.length + 1 ≤ z.length := by
    intro r hr
    have h1 : r.length ≤ ((clauses w).map List.length).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hr)
    have h2 : 0 < (clauses w).length := List.length_pos_of_mem hr
    omega
  have hR := ilv_ex_rows z.length (clauses w) (ilv_s0 y (enc (clauses w)))
    (by constructor <;> rfl) rfl rfl rfl (sep_not_mem_clauses w) hN rfl
  have hTr := ilv_Trows_le z.length y.length (clauses w)
  have hall := hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm hR))
  refine hall.cast rfl ?_
  rw [htl]
  rw [hsum] at hTr
  have h1 : (trunc w).length * (ilv_Tp z.length + 7 * y.length + 20) ≤
      z.length * (67 * z.length + 120) :=
    Nat.mul_le_mul (by omega) (by simp only [ilv_Tp]; omega)
  have e1 : (ilv_s0 y (enc (clauses w))).Y = y := rfl
  rw [e1]
  unfold ilv_Tver
  nlinarith

theorem ilv_Tver_le (n : ℕ) : ilv_Tver n ≤ tb 9 n := by
  unfold ilv_Tver tb
  have h7 : 2 ^ 7 ≤ (n + 2) ^ 7 := Nat.pow_le_pow_left (by omega) 7
  have e : (n + 2) ^ 9 = (n + 2) ^ 7 * (n + 2) ^ 2 := by ring
  rw [e]
  exact Nat.mul_le_mul_right _ (le_trans (by norm_num) h7)

end Pnp.Karp.ILP
