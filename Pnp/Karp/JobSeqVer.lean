import Pnp.Karp.JobSeq
import Pnp.Karp.TspVer

/-!
# JOB SEQUENCING ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(rows `K :: js`, `Pnp/Karp/JobSeq.lean`) and a certificate `y : List Bool`.

## Certificate

The certificate is a sequence of bit-pair coded segments (`seg`, `Pnp/Oracle/StructLib.lean`):
segment `i` gives a *rank* `ρᵢ` (a binary number, read by `segCmd`) of the `i`-th triple of
rows.  The verifier does not check that the ranks form a permutation: it charges job `j` the
completion time `Cⱼ = ∑_{i : ρᵢ ≤ ρⱼ} Tᵢ` (all triples `i`, including `j` itself and an
incomplete last triple).  Any rank map is realized by a schedule sorted by rank that is at
least as good, and the positions of a schedule give ranks with exactly its completion times
(`Pnp/Karp/JobSeqNP.lean`).

## Program (`jsv_ver`), stacks of `hv_HS` (`Pnp/Karp/HamVer.lean`)

`0` (`R`) the unread certificate; `1` (`M`) the code of the job rows; `2` (`P`) a copy of the
whole certificate; `3` (`Q`) the inner copy of `M`; `5` (`I`) the completion time `C`; `6`, `7`
(`X`, `Y`) sum bits and carry of the adder (`4` (`N`) stays empty); `8` (`Z`) the inner copy of
the certificate; `9` (`S`) the rank `ρⱼ`; `10` (`T`) a temporary; `11` (`K`) the rank `ρᵢ`; `12`
(`XC`) a copy of `ρⱼ`; `13` (`F`) a comparison flag; `14` (`H`) the bound; `15` (`RF`) the penalty
accumulator; `16` (`CT`) the outer copy of `M`; `17` (`CC`), `18` (`G`) the deadline `Dⱼ`.

1. parse (`phaseA`, `trimC 2`, `move 2 1`); read the first row (the bound) into `H`
   (`tv_frL`, halt `false` if there is no row, `move 10 14`); copy the certificate to `P` and
   the job rows to `CT`;
2. outer loop over the triples `t d p` of `CT` (at the end, or at an incomplete triple, halt
   with "penalty `≤` bound", `jsv_fin`): skip `t`, read `d` into `G`, read `ρⱼ`; the inner loop
   (`jsv_iL`) runs over the triples of a fresh copy of `M` and of the certificate, reading
   `ρᵢ` and adding `tᵢ` to `C` iff `ρᵢ ≤ ρⱼ`; then if not `C ≤ d`, add `p` to the penalty,
   otherwise skip `p`.

`jsv_exec_ver`: the program halts with `jsv_vres (dec z).1 (dec z).2` within `jsv_Tver |z|`
steps.
-/

namespace Pnp.Karp.JobSeq

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.Ham Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.Tsp

/-! ## Semantics -/

/-- One inner step: add the row `t` to `C` if the rank read from `Y` is at most `ρ`. -/
def jsv_ad (ρ Y C : Str) (t : List SatSym) : Str :=
  if kv_leF true (seg Y).1.reverse ρ then sv_addL false C (sv_bits t) else C

/-- The inner loop: the completion time for the rank `ρ` (`Y`: the unread certificate). -/
def jsv_in (ρ : Str) : List (List SatSym) → Str → Str → Str
  | [], _, C => C
  | [t], Y, C => jsv_ad ρ Y C t
  | [t, _], Y, C => jsv_ad ρ Y C t
  | t :: _ :: _ :: rest, Y, C => jsv_in ρ rest (seg Y).2 (jsv_ad ρ Y C t)

/-- The outer loop (`js`: all job rows, `Y0`: the whole certificate, `K`: the bound). -/
def jsv_out (js : List (List SatSym)) (Y0 K : Str) : List (List SatSym) → Str → Str → Bool
  | _ :: d :: p :: rest, R, A => jsv_out js Y0 K rest (seg R).2
      (if kv_leF true (jsv_in (seg R).1.reverse js Y0 []) (sv_bits d) then A
        else sv_addL false A (sv_bits p))
  | _, _, A => kv_leF true A K

/-- The answer of the verifier on `(w, y)`. -/
def jsv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | K :: js => jsv_out js y (sv_bits K) js y []

/-! ## Generic commands -/

/-- Look at stack `k`: if it is empty run `e`, otherwise (leaving it unchanged) run `c`. -/
def jsv_pk (k : ℕ) (c e : Cmd) : Cmd := .pop k e (.seq (.push k false) c) (.seq (.push k true) c)

theorem jsv_ex_pk_nil {k : ℕ} {c e : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ} (hk : σ k = [])
    (h : ExecLe e σ r T) : ExecLe (jsv_pk k c e) σ r (T + 1) :=
  ExecLe.pop_nil hk h

theorem jsv_ex_pk_cons {k : ℕ} {c e : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ} (hk : σ k ≠ [])
    (h : ExecLe c σ r T) : ExecLe (jsv_pk k c e) σ r (T + 2) := by
  obtain ⟨b, s, hbs⟩ := List.exists_cons_of_ne_nil hk
  refine ExecLe.pop_cons hbs ?_
  have hp := ExecLe.push k b (update σ k s)
  rw [update_self, update_idem, ← hbs, update_eq_self] at hp
  cases b
  · exact (hp.seq_norm h).cast rfl (by omega)
  · exact (hp.seq_norm h).cast rfl (by omega)

/-- Skip one row (code up to the separator `[false, false]`) on stack `k`. -/
def jsv_skB (k : ℕ) : Cmd :=
  .pop k (.halt false) (.pop k (.halt false) .brk .skip) (.pop k (.halt false) .skip .skip)

def jsv_skL (k : ℕ) : Cmd := .loop (jsv_skB k)

theorem jsv_ex_skL (k : ℕ) (Q' : Str) : ∀ (r : List SatSym) (σ : ℕ → Str), sep ∉ r →
    σ k = r.flatMap ic ++ false :: false :: Q' →
    ExecLe (jsv_skL k) σ (.norm (update σ k Q')) (3 * r.length + 3)
  | [], σ, _, h => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := false :: Q') (by simpa using h)
      (ExecLe.pop_cons (b := false) (s := Q') (by simp) (ExecLe.brk _)))).cast
      (by simp) (by simp)
  | x :: r, σ, hr, h => by
    have hx : x ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    set Q := r.flatMap ic ++ false :: false :: Q'
    have ih := jsv_ex_skL k Q' r (update σ k Q) hr' (by simp [Q])
    rw [update_idem] at ih
    have hb : ExecLe (jsv_skB k) σ (.norm (update σ k Q)) 3 := by
      cases x with
      | sep => exact absurd rfl hx
      | zero =>
        refine ExecLe.pop_cons (b := false) (s := true :: Q) (by simp [h, ic, Q]) ?_
        refine ExecLe.pop_cons (b := true) (s := Q) (by simp) ?_
        exact (ExecLe.skip _).cast (by simp) le_rfl
      | pos =>
        refine ExecLe.pop_cons (b := true) (s := false :: Q) (by simp [h, ic, Q]) ?_
        refine ExecLe.pop_cons (b := false) (s := Q) (by simp) ?_
        exact (ExecLe.skip _).cast (by simp) le_rfl
      | neg =>
        refine ExecLe.pop_cons (b := true) (s := true :: Q) (by simp [h, ic, Q]) ?_
        refine ExecLe.pop_cons (b := true) (s := Q) (by simp) ?_
        exact (ExecLe.skip _).cast (by simp) le_rfl
    exact (ExecLe.loop_norm hb ih).cast rfl (by simp; omega)

/-- Read one row of stack `k` onto stack `d` (bits, most significant on top). -/
def jsv_rdB (k d : ℕ) : Cmd :=
  .pop k (.halt false) (.pop k (.halt false) .brk (.push d false))
    (.pop k (.halt false) (.push d true) (.push d false))

def jsv_rdL (k d : ℕ) : Cmd := .loop (jsv_rdB k d)

theorem jsv_ex_rdL {k d : ℕ} (hkd : k ≠ d) (Q' : Str) : ∀ (r : List SatSym) (σ : ℕ → Str),
    sep ∉ r → σ k = r.flatMap ic ++ false :: false :: Q' →
    ExecLe (jsv_rdL k d) σ (.norm (update (update σ k Q') d ((sv_bits r).reverse ++ σ d)))
      (3 * r.length + 3)
  | [], σ, _, h => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := false :: Q')
      (by simpa using h) (ExecLe.pop_cons (b := false) (s := Q') (by simp) (ExecLe.brk _)))).cast
      (by
        congr 1; funext j; simp only [update_apply, sv_bits]
        split_ifs <;> simp_all) (by simp)
  | x :: r, σ, hr, h => by
    have hx : x ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    set Q := r.flatMap ic ++ false :: false :: Q'
    set σ1 := update (update σ k Q) d (isPos x :: σ d)
    have ih := jsv_ex_rdL hkd Q' r σ1 hr' (by simp [σ1, hkd, Q])
    have hp : ∀ b : Bool, b = isPos x → ExecLe (.push d b) (update σ k Q) (.norm σ1) 1 := by
      rintro b rfl
      exact (ExecLe.push d _ _).cast (by simp [σ1, update_of_ne (Ne.symm hkd)]) le_rfl
    have hb : ExecLe (jsv_rdB k d) σ (.norm σ1) 3 := by
      cases x with
      | sep => exact absurd rfl hx
      | zero =>
        refine ExecLe.pop_cons (b := false) (s := true :: Q) (by simp [h, ic, Q]) ?_
        refine ExecLe.pop_cons (b := true) (s := Q) (by simp) ?_
        simpa [update_idem] using hp false rfl
      | pos =>
        refine ExecLe.pop_cons (b := true) (s := false :: Q) (by simp [h, ic, Q]) ?_
        refine ExecLe.pop_cons (b := false) (s := Q) (by simp) ?_
        simpa [update_idem] using hp true rfl
      | neg =>
        refine ExecLe.pop_cons (b := true) (s := true :: Q) (by simp [h, ic, Q]) ?_
        refine ExecLe.pop_cons (b := true) (s := Q) (by simp) ?_
        simpa [update_idem] using hp false rfl
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [σ1, update_apply, sv_bits]
    split_ifs <;> simp_all

/-! ## Comparison (emptying both operands) -/

section Cmp
variable {a b f : ℕ} (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f)
include hab haf hbf

theorem jsv_ex_cmp : ∀ (A B : Str) (g : Bool) (σ : ℕ → Str), σ a = A → σ b = B →
    σ f = CookLevin.fl g →
    ExecLe (kv_cmpLoop a b f) σ
      (.norm (update (update (update σ a []) b []) f (CookLevin.fl (kv_leF g A B))))
      (5 * (A.length + B.length) + 3)
  | [], [], g, σ, ha, hb, hf =>
    (ExecLe.loop_brk (ExecLe.pop_nil ha (ExecLe.pop_nil hb (ExecLe.brk _)))).cast
      (by
        congr 1; funext j; simp only [update_apply, kv_leF]
        split_ifs <;> simp_all) (by simp)
  | [], y :: B, g, σ, ha, hb, hf => by
    obtain ⟨σ₁, h1, h1a, h1b, h1f, h1j⟩ := kv_ex_cmpB hab haf hbf [] (y :: B) g σ ha hb hf
      (by simp)
    have h2 := jsv_ex_cmp [] B _ σ₁ h1a h1b h1f
    refine (ExecLe.loop_norm h1 h2).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply, kv_leF]
    split_ifs <;> simp_all
  | x :: A, [], g, σ, ha, hb, hf => by
    obtain ⟨σ₁, h1, h1a, h1b, h1f, h1j⟩ := kv_ex_cmpB hab haf hbf (x :: A) [] g σ ha hb hf
      (by simp)
    have h2 := jsv_ex_cmp A [] _ σ₁ h1a h1b h1f
    refine (ExecLe.loop_norm h1 h2).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply, kv_leF]
    split_ifs <;> simp_all
  | x :: A, y :: B, g, σ, ha, hb, hf => by
    obtain ⟨σ₁, h1, h1a, h1b, h1f, h1j⟩ := kv_ex_cmpB hab haf hbf (x :: A) (y :: B) g σ ha hb
      hf (by simp)
    have h2 := jsv_ex_cmp A B _ σ₁ h1a h1b h1f
    refine (ExecLe.loop_norm h1 h2).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply, kv_leF]
    split_ifs <;> simp_all

end Cmp

/-! ## The adders -/

theorem jsv_mix3 (s : hv_HS) (R Q Tv A S : Str) (c : Bool) :
    kv_mix tv_Fa (sv_st R Q Tv A S c) s.st =
      {s with Q := Q, N := Tv, I := A, X := S, Y := CookLevin.fl c}.st := by
  funext j
  by_cases hj : j < 19
  · interval_cases j <;> rfl
  · have hF : tv_Fa j = true := by simp [tv_Fa]; omega
    simp only [kv_mix, hF, if_true]
    rw [hv_st_big _ _ (by omega), hv_st_big _ _ (by omega)]

/-- Add the row on `Q` (stack `3`) to `C` (stack `5`). -/
theorem jsv_ex_add3 (s : hv_HS) (Nacc : ℕ) (t : List SatSym) (Q' : Str) (hsep : sep ∉ t)
    (hQ : s.Q = t.flatMap ic ++ false :: false :: Q') (hN : s.N = []) (hX : s.X = [])
    (hY : s.Y = []) (hl : s.I.length + t.length ≤ Nacc) :
    ExecLe sv_addLoop s.st (.norm {s with Q := Q', I := sv_addL false s.I (sv_bits t)}.st)
      (7 * t.length + 8 * Nacc + 20) := by
  have h := sv_ex_addRow (R := s.R) (T := []) Nacc Q' t s.I [] false hsep (by simp; omega)
  have h' := kv_mix_le s.st h tv_av_add
  simp only [kv_rmap] at h'
  rw [jsv_mix3, jsv_mix3] at h'
  have e0 : ({s with Q := t.flatMap ic ++ false :: false :: Q', N := [], I := s.I, X := [], Y := CookLevin.fl false} :
      hv_HS) = s := by cases s; simp_all [CookLevin.fl]
  rw [e0] at h'
  refine h'.cast ?_ le_rfl
  congr 1; cases s; simp_all [CookLevin.fl]

/-- The renaming of the adder for the penalty: input `3 ↦ 16`, accumulator `5 ↦ 15`. -/
def jsv_π : Equiv.Perm ℕ := Equiv.swap 3 16 * Equiv.swap 5 15

theorem jsv_π_big (j : ℕ) (h : 19 ≤ j) : jsv_π j = j ∧ jsv_π.symm j = j := by
  have e : ∀ a b : ℕ, a < 19 → b < 19 → Equiv.swap a b j = j := fun a b ha hb =>
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · simp only [jsv_π, Equiv.Perm.mul_apply]
    rw [e 5 15 (by omega) (by omega), e 3 16 (by omega) (by omega)]
  · rw [← Equiv.Perm.inv_def]
    simp only [jsv_π, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]
    rw [e 3 16 (by omega) (by omega), e 5 15 (by omega) (by omega)]

theorem jsv_mixP (s : hv_HS) (R Q Tv A S : Str) (c : Bool) :
    kv_mix tv_Fa (sv_st R Q Tv A S c) (s.st ∘ jsv_π) ∘ jsv_π.symm =
      {s with CT := Q, N := Tv, RF := A, X := S, Y := CookLevin.fl c}.st := by
  funext j
  by_cases hj : j < 19
  · interval_cases j <;> rfl
  · obtain ⟨h1, h2⟩ := jsv_π_big j (by omega)
    have hF : tv_Fa j = true := by simp [tv_Fa]; omega
    simp only [comp_apply, h2, kv_mix, hF, if_true, h1]
    rw [hv_st_big _ _ (by omega), hv_st_big _ _ (by omega)]

def jsv_addP : Cmd := kv_ren jsv_π sv_addLoop

/-- Add the row on `CT` (stack `16`) to the penalty (stack `15`). -/
theorem jsv_ex_addP (s : hv_HS) (Nacc : ℕ) (t : List SatSym) (Q' : Str) (hsep : sep ∉ t)
    (hQ : s.CT = t.flatMap ic ++ false :: false :: Q') (hN : s.N = []) (hX : s.X = [])
    (hY : s.Y = []) (hl : s.RF.length + t.length ≤ Nacc) :
    ExecLe jsv_addP s.st (.norm {s with CT := Q', RF := sv_addL false s.RF (sv_bits t)}.st)
      (7 * t.length + 8 * Nacc + 20) := by
  have h := sv_ex_addRow (R := s.R) (T := []) Nacc Q' t s.RF [] false hsep (by simp; omega)
  have h' := kv_ren_le jsv_π (kv_mix_le (s.st ∘ jsv_π) h tv_av_add) kv_nc_add
  simp only [kv_rmap] at h'
  rw [jsv_mixP, jsv_mixP] at h'
  have e0 : ({s with CT := t.flatMap ic ++ false :: false :: Q', N := [], RF := s.RF, X := [], Y := CookLevin.fl false} :
      hv_HS) = s := by cases s; simp_all [CookLevin.fl]
  rw [e0] at h'
  refine h'.cast ?_ le_rfl
  congr 1; cases s; simp_all [CookLevin.fl]

/-! ## The inner loop -/

/-- Read `ρᵢ`, compare it with `ρⱼ`, add `tᵢ` to `C` or skip it. -/
def jsv_iA : Cmd :=
  .seq (segCmd 8 11) (.seq (copyVia 9 12 10) (.seq (.push 13 true) (.seq (kv_cmpLoop 11 12 13)
    (.pop 13 (jsv_skL 3) (jsv_skL 3) sv_addLoop))))

/-- The inner loop body: stop at the end of the rows, or at an incomplete triple. -/
def jsv_ib : Cmd :=
  jsv_pk 3 (.seq jsv_iA (.seq (jsv_pk 3 (jsv_skL 3) .brk) (jsv_pk 3 (jsv_skL 3) .brk))) .brk

def jsv_iL : Cmd := .loop jsv_ib

/-- The empty work stacks of the inner loop. -/
structure jsv_II (s : hv_HS) : Prop where
  hN : s.N = []
  hX : s.X = []
  hY : s.Y = []
  hT : s.T = []
  hK : s.K = []
  hXC : s.XC = []
  hF : s.F = []

theorem jsv_ex_iA (s : hv_HS) (hi : jsv_II s) (Nb : ℕ) (t : List SatSym) (Q' : Str)
    (hsep : sep ∉ t) (hQ : s.Q = t.flatMap ic ++ false :: false :: Q')
    (hl : s.I.length + t.length ≤ Nb) (hZ : s.Z.length ≤ Nb) (hS : s.S.length ≤ Nb) :
    ExecLe jsv_iA s.st (.norm {s with Q := Q', Z := (seg s.Z).2, I := jsv_ad s.S s.Z s.I t}.st)
      (35 * Nb + 40) := by
  set g := kv_leF true (seg s.Z).1.reverse s.S with hg
  have hfin : ExecLe (.pop 13 (jsv_skL 3) (jsv_skL 3) sv_addLoop)
      {s with Z := (seg s.Z).2, K := [], XC := [], F := CookLevin.fl g}.st
      (.norm {s with Q := Q', Z := (seg s.Z).2, I := jsv_ad s.S s.Z s.I t}.st)
      (7 * t.length + 8 * Nb + 21) := by
    unfold jsv_ad
    rw [← hg]
    cases g
    · refine ExecLe.pop_nil (by simp [CookLevin.fl]) ?_
      have := jsv_ex_skL 3 Q' t
        {s with Z := (seg s.Z).2, K := [], XC := [], F := CookLevin.fl false}.st hsep
        (by simp [hQ])
      simp only [hv_u3] at this
      refine this.cast ?_ (by omega)
      simp only [Bool.false_eq_true, if_false]
      have := hi.hK; have := hi.hXC; have := hi.hF
      congr 1; cases s; simp_all [CookLevin.fl]
    · refine ExecLe.pop_cons (b := true) (s := []) (by simp [CookLevin.fl]) ?_
      simp only [if_true, hv_u13]
      have := jsv_ex_add3 {s with Z := (seg s.Z).2, K := [], XC := [], F := []} Nb t Q' hsep
        (by simp [hQ]) hi.hN hi.hX hi.hY (by simp; omega)
      refine this.cast ?_ le_rfl
      have := hi.hK; have := hi.hXC; have := hi.hF
      congr 1; cases s; simp_all
  have h1 := exec_seg (src := 8) (dst := 11) (by decide) s.Z s.st rfl
  simp only [hv_u8, hv_u11, hv_st11] at h1
  have h2 := hv_ex_copy (a := 9) (b := 12) (by decide) (by decide) (by decide)
    {s with Z := (seg s.Z).2, K := (seg s.Z).1.reverse ++ s.K}.st (by simp [hi.hT])
  simp only [hv_st9, hv_st12, hv_u12] at h2
  have h3 := ExecLe.push 13 true
    {s with Z := (seg s.Z).2, K := (seg s.Z).1.reverse ++ s.K, XC := s.S ++ s.XC}.st
  simp only [hv_st13, hv_u13] at h3
  have h4 := jsv_ex_cmp (a := 11) (b := 12) (f := 13) (by decide) (by decide) (by decide)
    (seg s.Z).1.reverse s.S true
    {s with
      Z := (seg s.Z).2, K := (seg s.Z).1.reverse ++ s.K, XC := s.S ++ s.XC,
      F := true :: s.F}.st
    (by simp [hi.hK]) (by simp [hi.hXC]) (by simp [hi.hF, CookLevin.fl])
  simp only [hv_u11, hv_u12, hv_u13] at h4
  have hsl := seg_length s.Z
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm hfin)))).cast rfl ?_
  simp only [List.length_reverse]
  omega

theorem jsv_length_enc_cons (r : List SatSym) (rows : List (List SatSym)) :
    (enc (r :: rows)).length = 2 * r.length + 2 + (enc rows).length := by
  rw [enc_cons, List.length_append, length_flatMap_ic]; simp; omega

theorem jsv_ex_iL (Nb X : ℕ) (hX : 50 * Nb + 60 ≤ X) : ∀ (rows : List (List SatSym)) (s : hv_HS),
    jsv_II s → s.Q = enc rows → (∀ r ∈ rows, sep ∉ r) → s.I.length + (enc rows).length ≤ Nb →
    s.Z.length ≤ Nb → s.S.length ≤ Nb →
    ∃ Z', Z'.length ≤ s.Z.length ∧
      ExecLe jsv_iL s.st (.norm {s with Q := [], Z := Z', I := jsv_in s.S rows s.Z s.I}.st)
        (rows.length * X + X)
  | [], s, _, hQ, _, _, _, _ => ⟨s.Z, le_rfl, (ExecLe.loop_brk (jsv_ex_pk_nil (by simpa [enc] using hQ)
      (ExecLe.brk _))).cast (by congr 1; cases s; simp_all [enc, jsv_in]) (by omega)⟩
  | t :: rest, s, hi, hQ, hsep, hl, hZ, hS => by
    rw [enc_cons] at hQ
    rw [jsv_length_enc_cons] at hl
    have ht : sep ∉ t := hsep t (by simp)
    have hA := jsv_ex_iA s hi Nb t (enc rest) ht hQ (by omega) hZ hS
    have hne : s.st 3 ≠ [] := by simp [hQ]
    have hsl := seg_length s.Z
    have hadl : (jsv_ad s.S s.Z s.I t).length ≤ s.I.length + t.length + 1 := by
      unfold jsv_ad; split_ifs
      · have := sv_addL_length false s.I (sv_bits t)
        rw [show (sv_bits t).length = t.length by simp [sv_bits]] at this; omega
      · omega
    match rest, hsep, hl, hA with
    | [], _, _, hA =>
      have hb : ExecLe jsv_ib s.st
          (.brk {s with Q := enc [], Z := (seg s.Z).2, I := jsv_ad s.S s.Z s.I t}.st)
          (35 * Nb + 40 + 2 + 2) :=
        jsv_ex_pk_cons hne (hA.seq_norm (ExecLe.seq_brk (jsv_ex_pk_nil (by simp [enc])
          (ExecLe.brk _))))
      exact ⟨(seg s.Z).2, by omega, (ExecLe.loop_brk hb).cast (by simp [enc, jsv_in])
        (by simp; omega)⟩
    | [d], hsep, hl, hA =>
      have hd : sep ∉ d := hsep d (by simp)
      have hsk := jsv_ex_skL 3 (enc []) d
        {s with Q := enc [d], Z := (seg s.Z).2, I := jsv_ad s.S s.Z s.I t}.st hd
        (by simp [enc_cons])
      simp only [hv_u3] at hsk
      have hb : ExecLe jsv_ib s.st
          (.brk {s with Q := enc [], Z := (seg s.Z).2, I := jsv_ad s.S s.Z s.I t}.st)
          (35 * Nb + 40 + (3 * d.length + 3 + 2 + (1 + 1)) + 2) :=
        jsv_ex_pk_cons hne (hA.seq_norm ((jsv_ex_pk_cons (by simp [enc_cons]) hsk).seq_norm
          (jsv_ex_pk_nil (by simp [enc]) (ExecLe.brk _))))
      rw [jsv_length_enc_cons] at hl
      exact ⟨(seg s.Z).2, by omega, (ExecLe.loop_brk hb).cast (by simp [enc, jsv_in])
        (by simp; omega)⟩
    | d :: p :: rest', hsep, hl, hA =>
      have hd : sep ∉ d := hsep d (by simp)
      have hp : sep ∉ p := hsep p (by simp)
      have hsk1 := jsv_ex_skL 3 (enc (p :: rest')) d
        {s with Q := enc (d :: p :: rest'), Z := (seg s.Z).2, I := jsv_ad s.S s.Z s.I t}.st hd
        (by simp [enc_cons])
      simp only [hv_u3] at hsk1
      have hsk2 := jsv_ex_skL 3 (enc rest') p
        {s with Q := enc (p :: rest'), Z := (seg s.Z).2, I := jsv_ad s.S s.Z s.I t}.st hp
        (by simp [enc_cons])
      simp only [hv_u3] at hsk2
      have hb : ExecLe jsv_ib s.st
          (.norm {s with Q := enc rest', Z := (seg s.Z).2, I := jsv_ad s.S s.Z s.I t}.st)
          (35 * Nb + 40 + (3 * d.length + 3 + 2 + (3 * p.length + 3 + 2)) + 2) :=
        jsv_ex_pk_cons hne (hA.seq_norm ((jsv_ex_pk_cons (by simp [enc_cons]) hsk1).seq_norm
          (jsv_ex_pk_cons (by simp [enc_cons]) hsk2)))
      rw [jsv_length_enc_cons, jsv_length_enc_cons] at hl
      have hi1 : jsv_II {s with Q := enc rest', Z := (seg s.Z).2, I := jsv_ad s.S s.Z s.I t} := by
        obtain ⟨⟩ := hi; constructor <;> assumption
      obtain ⟨Z', hZ', ih⟩ := jsv_ex_iL Nb X hX rest' _ hi1 rfl
        (fun r hr => hsep r (by simp [hr])) (by simp; omega) (by simp; omega) (by simp; omega)
      refine ⟨Z', by simp at hZ'; omega, (ExecLe.loop_norm hb ih).cast (by simp [jsv_in]) ?_⟩
      simp only [List.length_cons]
      have e : (rest'.length + 1 + 1 + 1) * X = rest'.length * X + 3 * X := by ring
      rw [e]; omega

theorem jsv_length_in (ρ : Str) : ∀ (rows : List (List SatSym)) (Y C : Str),
    (jsv_in ρ rows Y C).length ≤ C.length + (enc rows).length
  | [], _, C => by simp [jsv_in]
  | t :: rest, Y, C => by
    have hadl : (jsv_ad ρ Y C t).length ≤ C.length + t.length + 1 := by
      unfold jsv_ad; split_ifs
      · have := sv_addL_length false C (sv_bits t)
        rw [show (sv_bits t).length = t.length by simp [sv_bits]] at this; omega
      · omega
    match rest with
    | [] => simp only [jsv_in, jsv_length_enc_cons]; omega
    | [d] => simp only [jsv_in, jsv_length_enc_cons]; omega
    | d :: p :: rest' =>
      have := jsv_length_in ρ rest' (seg Y).2 (jsv_ad ρ Y C t)
      simp only [jsv_in, jsv_length_enc_cons]; omega

/-! ## The outer loop -/

/-- Halt with "penalty `≤` bound" (flag on `13`). -/
def jsv_fin : Cmd :=
  .seq (.push 13 true) (.seq (kv_cmpLoop 15 14 13) (.pop 13 (.halt false) (.halt false) (.halt true)))

theorem jsv_ex_fin (s : hv_HS) (hF : s.F = []) :
    ExecLe jsv_fin s.st (.halt (kv_leF true s.RF s.H)) (5 * (s.RF.length + s.H.length) + 6) := by
  have hp := ExecLe.push 13 true s.st
  obtain ⟨σ', h1, h1f, -⟩ := kv_ex_cmp (a := 15) (b := 14) (f := 13) (by decide) (by decide)
    (by decide) s.RF s.H true (update s.st 13 (true :: s.st 13)) (by simp) (by simp)
    (by simp [hF, CookLevin.fl])
  refine (hp.seq_norm (h1.seq_norm (T₂ := 2) ?_)).cast rfl (by omega)
  cases hr : kv_leF true s.RF s.H
  · rw [hr] at h1f
    exact (ExecLe.pop_nil h1f (ExecLe.halt false _)).cast (by simp) (by omega)
  · rw [hr] at h1f
    exact (ExecLe.pop_cons (b := true) (s := []) h1f (ExecLe.halt true _)).cast (by simp)
      (by omega)

/-- The main part of the outer body (after reading `t` and `d`). -/
def jsv_oB : Cmd :=
  .seq (segCmd 0 9) (.seq (copyVia 1 3 10) (.seq (copyVia 2 8 10) (.seq jsv_iL (.seq (drain 8)
    (.seq (drain 9) (.seq (move 17 18) (.seq (.push 13 true) (.seq (kv_cmpLoop 5 18 13)
      (.pop 13 jsv_addP (jsv_skL 16) (jsv_skL 16))))))))))

/-- The outer body: skip `t`, read `d`, check that `p` is there, then `jsv_oB`. -/
def jsv_ob : Cmd :=
  .seq (jsv_pk 16 (jsv_skL 16) jsv_fin) (.seq (jsv_pk 16 (jsv_rdL 16 17) jsv_fin)
    (.seq (jsv_pk 16 .skip jsv_fin) jsv_oB))

def jsv_oL : Cmd := .loop jsv_ob

/-- The invariant of the outer loop (apart from `R`, `RF`, `CT`). -/
structure jsv_OI (js : List (List SatSym)) (Y0 K : Str) (s : hv_HS) : Prop where
  hM : s.M = enc js
  hP : s.P = Y0
  hH : s.H = K
  hQ : s.Q = []
  hN : s.N = []
  hI : s.I = []
  hX : s.X = []
  hY : s.Y = []
  hZ : s.Z = []
  hS : s.S = []
  hT : s.T = []
  hK : s.K = []
  hXC : s.XC = []
  hF : s.F = []
  hCC : s.CC = []
  hG : s.G = []

theorem jsv_ex_oB (js : List (List SatSym)) (Y0 K : Str) (Nb X : ℕ) (hX : 50 * Nb + 60 ≤ X)
    (hjs : ∀ r ∈ js, sep ∉ r) (hM : (enc js).length ≤ Nb) (hY0 : Y0.length ≤ Nb)
    (s : hv_HS) (hi : jsv_OI js Y0 K s) (d p : List SatSym) (rest : List (List SatSym))
    (hp : sep ∉ p) (hCT : s.CT = p.flatMap ic ++ false :: false :: enc rest)
    (hR : s.R.length ≤ Nb) (hd : d.length ≤ Nb) (hA : s.RF.length + p.length ≤ Nb) :
    ExecLe jsv_oB {s with CC := (sv_bits d).reverse}.st
      (.norm {s with
          R := (seg s.R).2, CT := enc rest,
          RF := if kv_leF true (jsv_in (seg s.R).1.reverse js Y0 []) (sv_bits d) then s.RF
            else sv_addL false s.RF (sv_bits p)}.st)
      (js.length * X + X + 60 * Nb + 60) := by
  have hsl := seg_length s.R
  have h1 := exec_seg (src := 0) (dst := 9) (by decide) s.R {s with CC := (sv_bits d).reverse}.st
    rfl
  simp only [hv_u0, hv_u9, hv_st9] at h1
  rw [show (seg s.R).1.reverse ++ s.S = (seg s.R).1.reverse by simp [hi.hS]] at h1
  have h2 := hv_ex_copy (a := 1) (b := 3) (by decide) (by decide) (by decide)
    {s with CC := (sv_bits d).reverse, R := (seg s.R).2, S := (seg s.R).1.reverse}.st
    (by simp [hi.hT])
  simp only [hv_st1, hv_st3, hv_u3] at h2
  rw [show s.M ++ s.Q = enc js by simp [hi.hM, hi.hQ]] at h2
  have h3 := hv_ex_copy (a := 2) (b := 8) (by decide) (by decide) (by decide)
    {s with
      CC := (sv_bits d).reverse, R := (seg s.R).2, S := (seg s.R).1.reverse, Q := enc js}.st
    (by simp [hi.hT])
  simp only [hv_st2, hv_st8, hv_u8] at h3
  rw [show s.P ++ s.Z = Y0 by simp [hi.hP, hi.hZ]] at h3
  have hi3 : jsv_II {s with
      CC := (sv_bits d).reverse, R := (seg s.R).2, S := (seg s.R).1.reverse, Q := enc js,
      Z := Y0} := ⟨hi.hN, hi.hX, hi.hY, hi.hT, hi.hK, hi.hXC, hi.hF⟩
  obtain ⟨Z', hZ', h4⟩ := jsv_ex_iL Nb X hX js _ hi3 rfl hjs (by simp [hi.hI]; omega)
    (by simp; omega) (by simp; omega)
  simp only at h4 hZ'
  rw [show jsv_in (seg s.R).1.reverse js Y0 s.I = jsv_in (seg s.R).1.reverse js Y0 [] by
    rw [hi.hI]] at h4
  have hC : (jsv_in (seg s.R).1.reverse js Y0 []).length ≤ Nb := by
    have := jsv_length_in (seg s.R).1.reverse js Y0 []; simp at this; omega
  have h5 := hv_ex_drain 8
    {s with
      CC := (sv_bits d).reverse, R := (seg s.R).2, S := (seg s.R).1.reverse, Q := [], Z := Z',
      I := jsv_in (seg s.R).1.reverse js Y0 []}.st
  simp only [hv_u8, hv_st8] at h5
  have h6 := hv_ex_drain 9
    {s with
      CC := (sv_bits d).reverse, R := (seg s.R).2, S := (seg s.R).1.reverse, Q := [], Z := [],
      I := jsv_in (seg s.R).1.reverse js Y0 []}.st
  simp only [hv_u9, hv_st9] at h6
  have h7 := exec_move (a := 17) (b := 18) (by decide) _
    {s with
      CC := (sv_bits d).reverse, R := (seg s.R).2, S := [], Q := [], Z := [],
      I := jsv_in (seg s.R).1.reverse js Y0 []}.st rfl
  simp only [hv_u17, hv_u18, hv_st17, hv_st18, List.reverse_reverse] at h7
  rw [show sv_bits d ++ s.G = sv_bits d by simp [hi.hG]] at h7
  have h8 := ExecLe.push 13 true
    {s with
      CC := [], G := sv_bits d, R := (seg s.R).2, S := [], Q := [], Z := [],
      I := jsv_in (seg s.R).1.reverse js Y0 []}.st
  simp only [hv_u13, hv_st13] at h8
  rw [show true :: s.F = [true] by simp [hi.hF]] at h8
  have h9 := jsv_ex_cmp (a := 5) (b := 18) (f := 13) (by decide) (by decide) (by decide)
    (jsv_in (seg s.R).1.reverse js Y0 []) (sv_bits d) true
    {s with
      CC := [], G := sv_bits d, R := (seg s.R).2, S := [], Q := [], Z := [],
      I := jsv_in (seg s.R).1.reverse js Y0 [], F := [true]}.st
    (by simp) (by simp) (by simp [CookLevin.fl])
  simp only [hv_u5, hv_u18, hv_u13] at h9
  have hfin : ExecLe (.pop 13 jsv_addP (jsv_skL 16) (jsv_skL 16))
      {s with
        CC := [], G := [], R := (seg s.R).2, S := [], Q := [], Z := [], I := [],
        F := CookLevin.fl (kv_leF true (jsv_in (seg s.R).1.reverse js Y0 []) (sv_bits d))}.st
      (.norm {s with
        R := (seg s.R).2, CT := enc rest,
        RF := if kv_leF true (jsv_in (seg s.R).1.reverse js Y0 []) (sv_bits d) then s.RF
          else sv_addL false s.RF (sv_bits p)}.st)
      (7 * p.length + 8 * Nb + 21) := by
    generalize kv_leF true (jsv_in (seg s.R).1.reverse js Y0 []) (sv_bits d) = g
    have := hi.hCC; have := hi.hG; have := hi.hS; have := hi.hQ; have := hi.hZ; have := hi.hI
    have := hi.hF
    cases g
    · refine ExecLe.pop_nil (by simp [CookLevin.fl]) ?_
      have := jsv_ex_addP {s with
          CC := [], G := [], R := (seg s.R).2, S := [], Q := [], Z := [], I := [], F := []}
        Nb p (enc rest) hp (by simp [hCT]) hi.hN hi.hX hi.hY (by simpa using hA)
      refine this.cast ?_ le_rfl
      congr 1; cases s; simp_all [CookLevin.fl]
    · refine ExecLe.pop_cons (b := true) (s := []) (by simp [CookLevin.fl]) ?_
      simp only [if_true, hv_u13]
      have := jsv_ex_skL 16 (enc rest) p {s with
          CC := [], G := [], R := (seg s.R).2, S := [], Q := [], Z := [], I := [], F := []}.st
        hp (by simp [hCT])
      simp only [hv_u16] at this
      refine this.cast ?_ (by omega)
      congr 1; cases s; simp_all [CookLevin.fl]
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm (h6.seq_norm
    ((ExecLe.of h7).seq_norm (h8.seq_norm (h9.seq_norm hfin))))))))).cast rfl ?_
  have e1 : s.M.length = (enc js).length := by rw [hi.hM]
  have e2 : s.P.length = Y0.length := by rw [hi.hP]
  simp only [List.length_reverse, sv_bits, List.length_map] at *
  omega

theorem jsv_ex_oL (js : List (List SatSym)) (Y0 K : Str) (Nb X Yc : ℕ) (hX : 50 * Nb + 60 ≤ X)
    (hYc : js.length * X + X + 80 * Nb + 100 ≤ Yc)
    (hjs : ∀ r ∈ js, sep ∉ r) (hM : (enc js).length ≤ Nb) (hY0 : Y0.length ≤ Nb)
    (hK : K.length ≤ Nb) : ∀ (rows : List (List SatSym)) (s : hv_HS), jsv_OI js Y0 K s →
    s.CT = enc rows → (∀ r ∈ rows, sep ∉ r) → s.RF.length + (enc rows).length ≤ Nb →
    s.R.length ≤ Nb →
    ExecLe jsv_oL s.st (.halt (jsv_out js Y0 K rows s.R s.RF)) (rows.length * Yc + Yc)
  | [], s, hi, hCT, _, hl, _ => by
    have hf := jsv_ex_fin s hi.hF
    rw [hi.hH] at hf
    refine (ExecLe.loop_halt (ExecLe.seq_halt (jsv_ex_pk_nil (by simpa [enc] using hCT) hf))).cast
      (by simp [jsv_out]) ?_
    simp only [List.length_nil, zero_mul, zero_add]; omega
  | t :: rest, s, hi, hCT, hsep, hl, hR => by
    rw [enc_cons] at hCT
    rw [jsv_length_enc_cons] at hl
    have eH : s.H.length = K.length := by rw [hi.hH]
    have ht : sep ∉ t := hsep t (by simp)
    have h1 := jsv_ex_skL 16 (enc rest) t s.st ht (by simpa using hCT)
    simp only [hv_u16] at h1
    have hne : s.st 16 ≠ [] := by simp [hCT]
    have hP1 := jsv_ex_pk_cons (e := jsv_fin) hne h1
    match rest, hsep, hl, hP1 with
    | [], _, hl, hP1 =>
      have hf := jsv_ex_fin {s with CT := enc []} hi.hF
      simp only at hf
      rw [show kv_leF true s.RF s.H = kv_leF true s.RF K by rw [hi.hH]] at hf
      refine (ExecLe.loop_halt (hP1.seq_norm (ExecLe.seq_halt (jsv_ex_pk_nil (by simp [enc])
        hf)))).cast (by simp [jsv_out]) ?_
      simp only [List.length_cons, List.length_nil, zero_add, one_mul]; omega
    | [d], hsep, hl, hP1 =>
      have hd : sep ∉ d := hsep d (by simp)
      rw [jsv_length_enc_cons] at hl
      have h2 := jsv_ex_rdL (k := 16) (d := 17) (by decide) (enc []) d
        {s with CT := enc [d]}.st hd (by simp [enc_cons])
      simp only [hv_u16, hv_u17, hv_st17] at h2
      have hP2 := jsv_ex_pk_cons (k := 16) (e := jsv_fin) (by simp [enc_cons]) h2
      have hf := jsv_ex_fin {s with CT := enc [], CC := (sv_bits d).reverse ++ s.CC} hi.hF
      simp only at hf
      rw [show kv_leF true s.RF s.H = kv_leF true s.RF K by rw [hi.hH]] at hf
      refine (ExecLe.loop_halt (hP1.seq_norm (hP2.seq_norm (ExecLe.seq_halt
        (jsv_ex_pk_nil (by simp [enc]) hf))))).cast (by simp [jsv_out]) ?_
      simp only [List.length_cons, List.length_nil, zero_add]; omega
    | d :: p :: rest', hsep, hl, hP1 =>
      have hd : sep ∉ d := hsep d (by simp)
      have hp : sep ∉ p := hsep p (by simp)
      rw [jsv_length_enc_cons, jsv_length_enc_cons] at hl
      have h2 := jsv_ex_rdL (k := 16) (d := 17) (by decide) (enc (p :: rest')) d
        {s with CT := enc (d :: p :: rest')}.st hd (by simp [enc_cons])
      simp only [hv_u16, hv_u17, hv_st17] at h2
      rw [show (sv_bits d).reverse ++ s.CC = (sv_bits d).reverse by simp [hi.hCC]] at h2
      have hP2 := jsv_ex_pk_cons (k := 16) (e := jsv_fin) (by simp [enc_cons]) h2
      have hP3 := jsv_ex_pk_cons (k := 16) (e := jsv_fin)
        (σ := {s with CT := enc (p :: rest'), CC := (sv_bits d).reverse}.st)
        (by simp [enc_cons]) (ExecLe.skip _)
      have hB := jsv_ex_oB js Y0 K Nb X hX hjs hM hY0 {s with CT := enc (p :: rest')}
        (by obtain ⟨⟩ := hi; constructor <;> assumption) d p rest' hp (by simp [enc_cons])
        hR (by omega) (by simp; omega)
      simp only at hB
      set A' := if kv_leF true (jsv_in (seg s.R).1.reverse js Y0 []) (sv_bits d) then s.RF
        else sv_addL false s.RF (sv_bits p) with hA'
      have hA'l : A'.length ≤ s.RF.length + p.length + 1 := by
        rw [hA']; split_ifs
        · omega
        · have := sv_addL_length false s.RF (sv_bits p)
          rw [show (sv_bits p).length = p.length by simp [sv_bits]] at this; omega
      have hsl := seg_length s.R
      have ih := jsv_ex_oL js Y0 K Nb X Yc hX hYc hjs hM hY0 hK rest'
        {s with R := (seg s.R).2, CT := enc rest', RF := A'}
        (by obtain ⟨⟩ := hi; constructor <;> assumption) rfl
        (fun r hr => hsep r (by simp [hr])) (by simp; omega) (by simp; omega)
      simp only at ih
      refine (ExecLe.loop_norm (hP1.seq_norm (hP2.seq_norm (hP3.seq_norm hB))) ih).cast
        (by simp [jsv_out, hA']) ?_
      simp only [List.length_cons]
      have e : (rest'.length + 1 + 1 + 1) * Yc = rest'.length * Yc + 3 * Yc := by ring
      rw [e]; omega

/-! ## The whole verifier -/

def jsv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 1) (.seq tv_frL (.seq (move 10 14)
    (.seq (copyVia 0 2 10) (.seq (copyVia 1 16 10) jsv_oL))))))

/-- Time bound of the verifier. -/
def jsv_Tver (L : ℕ) : ℕ := 200 * (L + 2) ^ 3

theorem jsv_bound (L W t k e y n : ℕ) (hW : 2 * W + y ≤ L) (ht : t ≤ W) (hk : k ≤ W)
    (he : e ≤ 2 * t) (hn : n ≤ L) :
    3 * L + 4 + (4 * W + 6 + (2 * (2 * t) + 2 + (3 * k + 3 + (2 * k + 2 + (5 * y + 4 +
      (5 * e + 4 + (n * (L * (50 * L + 60) + (50 * L + 60) + 80 * L + 100) +
        (L * (50 * L + 60) + (50 * L + 60) + 80 * L + 100)))))))) ≤ jsv_Tver L := by
  set Q := L * (50 * L + 60) + (50 * L + 60) + 80 * L + 100 with hQd
  set m := L + 2 with hm
  have hQ : Q ≤ 50 * m ^ 2 + 80 * m := by rw [hQd, hm]; ring_nf; omega
  have hnq : n * Q + Q ≤ m * (50 * m ^ 2 + 80 * m) := by
    rw [show n * Q + Q = (n + 1) * Q by ring]
    exact Nat.mul_le_mul (by omega) hQ
  have hm3 : m * (50 * m ^ 2 + 80 * m) + 30 * m ≤ 200 * m ^ 3 := by
    have h2 : 2 ≤ m := by omega
    nlinarith
  unfold jsv_Tver
  rw [← hm]
  linarith

theorem jsv_exec_ver (z : Str) :
    ExecLe jsv_ver (init [z]).stk (.halt (jsv_vres (dec z).1 (dec z).2)) (jsv_Tver z.length) := by
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
      (hv_s0 y (enc (clauses w))).st := by
    funext j
    by_cases hj : j < 19
    · interval_cases j <;> simp [σ₂, σ₁, he, enc, trunc, hv_HS.st]
    · rw [hv_st_big _ _ (by omega)]
      simp [σ₂, σ₁, he j (by omega), show j ≠ 0 by omega, show j ≠ 1 by omega,
        show j ≠ 2 by omega]
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ), ExecLe c (hv_s0 y (enc (clauses w))).st r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 1) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have hsep := sep_not_mem_clauses w
  unfold jsv_vres jsv_ver
  rcases hcw : clauses w with _ | ⟨K, js⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq tv_frL (.seq (move 10 14) (.seq (copyVia 0 2 10)
        (.seq (copyVia 1 16 10) jsv_oL)))) (hv_s0 y (enc [])).st (.halt false) 2 :=
      ExecLe.seq_halt (ExecLe.loop_halt ((ExecLe.pop_nil (by simp [enc]) (ExecLe.halt false _)).cast
        rfl le_rfl))
    refine (hpre _ _ _ hf).cast rfl ?_
    have : z.length + 2 ≤ (z.length + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
    simp only [htl, jsv_Tver]; omega
  · rw [hcw] at hsum hsep hpre hcl
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum hcl
    have hF := tv_ex_fr (enc js) K (hv_s0 y (enc (K :: js))) (hsep K (by simp))
      (by simp [enc_cons])
    simp only [List.append_nil] at hF
    have hM2 := exec_move (a := 10) (b := 14) (by decide) _
      {hv_s0 y (enc (K :: js)) with M := enc js, T := (sv_bits K).reverse}.st rfl
    simp only [hv_u10, hv_u14, hv_st10, hv_st14, List.reverse_reverse, List.append_nil] at hM2
    have hC1 := hv_ex_copy (a := 0) (b := 2) (by decide) (by decide) (by decide)
      {hv_s0 y (enc (K :: js)) with M := enc js, T := [], H := sv_bits K}.st rfl
    simp only [hv_st0, hv_st2, hv_u2, List.append_nil] at hC1
    have hC2 := hv_ex_copy (a := 1) (b := 16) (by decide) (by decide) (by decide)
      {hv_s0 y (enc (K :: js)) with M := enc js, T := [], H := sv_bits K, P := y}.st rfl
    simp only [hv_st1, hv_st16, hv_u16, List.append_nil] at hC2
    have hen : (enc js).length = 2 * ((js.map List.length).sum + js.length) := by
      simp only [enc, length_flatMap_ic]; rw [sum_length_le]
    have hKl : (sv_bits K).length = K.length := by simp [sv_bits]
    have hO := jsv_ex_oL js y (sv_bits K) z.length (50 * z.length + 60)
      (z.length * (50 * z.length + 60) + (50 * z.length + 60) + 80 * z.length + 100) le_rfl
      (by have : js.length * (50 * z.length + 60) ≤ z.length * (50 * z.length + 60) :=
            Nat.mul_le_mul_right _ (by omega)
          omega)
      (fun r hr => hsep r (by simp [hr])) (by omega) (by omega) (by omega) js
      {hv_s0 y (enc (K :: js)) with M := enc js, T := [], H := sv_bits K, P := y, CT := enc js}
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
      (fun r hr => hsep r (by simp [hr])) (by simp; omega) (by simp; omega)
    simp only at hO
    refine (hpre _ _ _ (hF.seq_norm ((ExecLe.of hM2).seq_norm (hC1.seq_norm (hC2.seq_norm
      hO))))).cast rfl ?_
    simp only [htl, List.length_reverse, hKl]
    exact jsv_bound z.length w.length (trunc w).length K.length (enc js).length y.length
      js.length (by omega) hw (by omega) (by omega) (by omega)

theorem jsv_Tver_le (n : ℕ) : jsv_Tver n ≤ tb 11 n := by
  unfold jsv_Tver tb
  have h8 : 2 ^ 8 ≤ (n + 2) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  have e : (n + 2) ^ 11 = (n + 2) ^ 8 * (n + 2) ^ 3 := by ring
  rw [e]
  have : 200 ≤ (n + 2) ^ 8 := le_trans (by norm_num) h8
  exact Nat.mul_le_mul_right _ this

end Pnp.Karp.JobSeq
