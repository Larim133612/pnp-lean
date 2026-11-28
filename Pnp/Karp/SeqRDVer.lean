import Pnp.Karp.ThreePartUVer
import Pnp.Karp.SeqRD

/-!
# Unary SEQUENCING WITH RELEASE TIMES AND DEADLINES ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(rows in triples `ℓ, r, d`, values are row lengths, `Pnp/Karp/SeqRD.lean`) and a certificate
`y : List Bool`.

## Certificate

The start times `s₀, s₁, …` in unary, each closed by a `false`: `true^{s₀} false true^{s₁} …`
(`srv_rdU` reads one; a missing number reads as `0`).

## Semantics (`srv_go`)

The tasks are processed in order, keeping the list `P` of the intervals `(sⱼ, sⱼ + ℓⱼ)` of the
earlier tasks.  Task `i` (start `s`) is accepted iff `r ≤ s`, `s + ℓ ≤ d` and for every
`(a, b) ∈ P`: `b ≤ s ∨ s + ℓ ≤ a` (`srv_ok`).  An incomplete last triple is rejected.

## Program (`srv_ver`)

Stacks: `0` the certificate, `3` the code of the rows, `4` the intervals `P` (`srv_pe`), `5`
`ℓ` (then `s + ℓ`), `6` `r`, `7` `d`, `8` `s`, `9` the inner copy of `P`, `10`, `11` the
interval `(a, b)` of the inner loop, `12`, `13` temporaries, `14` the flag of `tpv_test`, `15` the
temporary of `copyVia`; all numbers in unary (`tpuv_u`).

1. `phaseA`, `trimC 2`, `move 2 3`;
2. the outer loop `srv_oL`: at the end of the rows halt `true`; otherwise read `ℓ`, `r`, `d`
   (halt `false` at a missing row), read `s` from the certificate, test `r ≤ s` and `s + ℓ ≤ d`,
   run the inner loop `srv_iL` over a copy of `P` and push `(s, s + ℓ)` onto `P`.
-/

namespace Pnp.Karp.SeqRD

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.JobSeq Pnp.Karp.NAE Pnp.Karp.BinPacking
  Pnp.Karp.ThreePart Pnp.Karp.ThreePartU

/-! ## Semantics -/

/-- Read a unary number (`true`s up to a `false` or the end). -/
def srv_rdU : Str → ℕ × Str
  | [] => (0, [])
  | false :: y => (0, y)
  | true :: y => ((srv_rdU y).1 + 1, (srv_rdU y).2)

theorem srv_rdU_le : ∀ y : Str, (srv_rdU y).1 + (srv_rdU y).2.length ≤ y.length
  | [] => by simp [srv_rdU]
  | false :: y => by simp [srv_rdU]
  | true :: y => by have := srv_rdU_le y; simp [srv_rdU]; omega

theorem srv_rdU_u (n : ℕ) (R : Str) : srv_rdU (tpuv_u n ++ false :: R) = (n, R) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tpuv_u, List.replicate_succ, srv_rdU] at ih ⊢; simp [ih]

/-- The interval `(s, e)` is disjoint from all intervals of `P`. -/
def srv_ok (s e : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | p :: P => (decide (p.2 ≤ s) || decide (e ≤ p.1)) && srv_ok s e P

/-- The checks of one task `(l, r, d)` with the certificate `Y`. -/
def srv_chk (P : List (ℕ × ℕ)) (l r d : List SatSym) (Y : Str) : Bool :=
  decide (r.length ≤ (srv_rdU Y).1) && decide ((srv_rdU Y).1 + l.length ≤ d.length) &&
    srv_ok (srv_rdU Y).1 ((srv_rdU Y).1 + l.length) P

/-- What the main loop computes. -/
def srv_go : List (ℕ × ℕ) → List (List SatSym) → Str → Bool
  | _, [], _ => true
  | _, [_], _ => false
  | _, [_, _], _ => false
  | P, l :: r :: d :: rs, Y => srv_chk P l r d Y &&
      srv_go (((srv_rdU Y).1, (srv_rdU Y).1 + l.length) :: P) rs (srv_rdU Y).2

/-- The answer of the verifier on `(w, y)`. -/
def srv_vres (w : List SatSym) (y : Str) : Bool := srv_go [] (clauses w) y

/-- The code of the interval list. -/
def srv_pe : List (ℕ × ℕ) → Str
  | [] => []
  | p :: P => true :: (tpuv_u p.1 ++ false :: (tpuv_u p.2 ++ false :: srv_pe P))

theorem srv_pe_length_le (N : ℕ) : ∀ P : List (ℕ × ℕ), (∀ p ∈ P, p.1 ≤ N ∧ p.2 ≤ N) →
    (srv_pe P).length ≤ P.length * (2 * N + 3)
  | [], _ => by simp [srv_pe]
  | p :: P, h => by
    have ih := srv_pe_length_le N P (fun q hq => h q (by simp [hq]))
    have hp := h p (by simp)
    simp [srv_pe, tpuv_u_length]
    nlinarith

/-! ## Generic commands -/

/-- Read a row (stack `3`) in unary onto stack `k`. -/
def srv_rdB (k : ℕ) : Cmd :=
  .pop 3 .brk (.pop 3 .brk .brk (.push k true)) (.pop 3 .brk (.push k true) (.push k true))

def srv_rd (k : ℕ) : Cmd := .loop (srv_rdB k)

theorem srv_ex_rd {k : ℕ} (hk : k ≠ 3) : ∀ (r : List SatSym) (σ : ℕ → Str) (Q' : Str), sep ∉ r →
    σ 3 = r.flatMap ic ++ false :: false :: Q' →
    ExecLe (srv_rd k) σ (.norm (update (update σ 3 Q') k (tpuv_u r.length ++ σ k)))
      (3 * r.length + 3)
  | [], σ, Q', _, h3 => by
    have h3' : σ 3 = false :: false :: Q' := by simpa using h3
    refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := false)
      (s := Q') (by simp) (ExecLe.brk _)))).cast ?_ (by simp)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [tpuv_u]
  | s :: r, σ, Q', hr, h3 => by
    have hs' : s ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ht : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    set rest := r.flatMap ic ++ false :: false :: Q'
    have ih := srv_ex_rd hk r (update (update σ 3 rest) k (true :: σ k)) Q' ht
      (by simp [rest, Ne.symm hk])
    have hb : ExecLe (srv_rdB k) σ (.norm (update (update σ 3 rest) k (true :: σ k))) 3 := by
      cases s with
      | sep => exact absurd rfl hs'
      | zero =>
        have h' : σ 3 = false :: true :: rest := by simpa [ic, rest] using h3
        refine (ExecLe.pop_cons (b := false) h' (ExecLe.pop_cons (b := true) (s := rest)
          (by simp) (ExecLe.push k true _))).cast ?_ le_rfl
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all
      | pos =>
        have h' : σ 3 = true :: false :: rest := by simpa [ic, rest] using h3
        refine (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := false) (s := rest)
          (by simp) (ExecLe.push k true _))).cast ?_ le_rfl
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all
      | neg =>
        have h' : σ 3 = true :: true :: rest := by simpa [ic, rest] using h3
        refine (ExecLe.pop_cons (b := true) h' (ExecLe.pop_cons (b := true) (s := rest)
          (by simp) (ExecLe.push k true _))).cast ?_ le_rfl
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1
    simp only [update_self]
    rw [tpuv_u_succ]
    funext j; simp only [update_apply]; split_ifs <;> simp_all

/-- Read a unary number from stack `a` onto stack `b`. -/
def srv_ru (a b : ℕ) : Cmd := .loop (.pop a .brk .brk (.push b true))

theorem srv_ex_ru {a b : ℕ} (hab : a ≠ b) : ∀ (Y : Str) (σ : ℕ → Str), σ a = Y →
    ExecLe (srv_ru a b) σ (.norm (update (update σ a (srv_rdU Y).2) b
      (tpuv_u (srv_rdU Y).1 ++ σ b))) (2 * (srv_rdU Y).1 + 2)
  | [], σ, h => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk _))).cast ?_ (by simp [srv_rdU])
    congr 1; funext j; simp only [update_apply, srv_rdU, tpuv_u]; split_ifs <;> simp_all
  | false :: Y, σ, h => by
    refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) h (ExecLe.brk _))).cast ?_
      (by simp [srv_rdU])
    congr 1; funext j; simp only [update_apply, srv_rdU, tpuv_u]; split_ifs <;> simp_all
  | true :: Y, σ, h => by
    have ih := srv_ex_ru hab Y (update (update σ a Y) b (true :: update σ a Y b)) (by simp [hab])
    refine (ExecLe.loop_norm (ExecLe.pop_cons (b := true) h (ExecLe.push b true _)) ih).cast ?_
      (by simp [srv_rdU]; omega)
    congr 1
    simp only [update_self, update_of_ne (Ne.symm hab)]
    rw [tpuv_u_succ]
    funext j; simp only [update_apply, srv_rdU]; split_ifs <;> simp_all

/-- Peek at stack `k` (run `c` on the unchanged stacks if it is not empty). -/
def srv_pk (k : ℕ) (cn c : Cmd) : Cmd := .pop k cn (.seq (.push k false) c) (.seq (.push k true) c)

theorem srv_ex_pk {k : ℕ} {cn c : Cmd} {σ : ℕ → Str} {x : Bool} {t : Str} {r : Res} {T : ℕ}
    (hk : σ k = x :: t) (h : ExecLe c σ r T) : ExecLe (srv_pk k cn c) σ r (T + 2) := by
  have e : update (update σ k t) k (x :: update σ k t k) = σ := by
    rw [update_idem, update_self, ← hk, update_eq_self]
  refine ExecLe.pop_cons hk ?_
  cases x
  · exact ((ExecLe.push k false _).seq_norm (e ▸ h)).cast rfl (by omega)
  · exact ((ExecLe.push k true _).seq_norm (e ▸ h)).cast rfl (by omega)

/-- A test `a ≤ b` (emptying both) that halts `false` if it fails. -/
def srv_tst (a b : ℕ) : Cmd := tpv_test a b (.halt false) .skip

theorem srv_ex_tst {a b : ℕ} (hab : a ≠ b) (ha : a ≠ 14) (hb : b ≠ 14) {σ : ℕ → Str} {x y : ℕ}
    (hX : σ a = tpuv_u x) (hY : σ b = tpuv_u y) (h14 : σ 14 = []) :
    ExecLe (srv_tst a b) σ (if decide (x ≤ y) then .norm (update (update σ a []) b [])
      else .halt false) (5 * (x + y) + 6) := by
  have h := tpv_ex_test (cn := .halt false) (ct := .skip) (r := if decide (x ≤ y) then
      .norm (update (update σ a []) b []) else .halt false) (T := 1) hab ha hb hX hY h14 (by
    rw [tpuv_le_u]
    cases decide (x ≤ y)
    · exact ExecLe.halt false _
    · exact ExecLe.skip _)
  exact h.cast rfl (by simp [tpuv_u_length])

/-- Sequencing after a command that may halt `false`. -/
theorem srv_sq {c d : Cmd} {σ σ' : ℕ → Str} {b : Bool} {r : Res} {T₁ T₂ : ℕ}
    (h1 : ExecLe c σ (if b then .norm σ' else .halt false) T₁) (h2 : b = true → ExecLe d σ' r T₂) :
    ExecLe (.seq c d) σ (if b then r else .halt false) (T₁ + T₂) := by
  cases b
  · exact (ExecLe.seq_halt h1).mono (by omega)
  · exact h1.seq_norm (h2 rfl)

/-! ## The inner loop -/

def srv_iT : Cmd := tpv_test 11 12 (.seq (copyVia 5 13 15) (srv_tst 13 10)) (drain 10)

def srv_iE : Cmd := .seq (srv_ru 9 10) (.seq (srv_ru 9 11) (.seq (copyVia 8 12 15) srv_iT))

def srv_iB : Cmd := .pop 9 .brk srv_iE srv_iE

def srv_iL : Cmd := .loop srv_iB

theorem srv_ex_iB {σ : ℕ → Str} {a b s e : ℕ} {rest : Str}
    (h9 : σ 9 = true :: (tpuv_u a ++ false :: (tpuv_u b ++ false :: rest)))
    (h8 : σ 8 = tpuv_u s) (h5 : σ 5 = tpuv_u e) (h10 : σ 10 = []) (h11 : σ 11 = [])
    (h12 : σ 12 = []) (h13 : σ 13 = []) (h14 : σ 14 = []) (h15 : σ 15 = []) :
    ExecLe srv_iB σ (if (decide (b ≤ s) || decide (e ≤ a)) then .norm (update σ 9 rest)
      else .halt false) (7 * a + 7 * b + 10 * s + 10 * e + 40) := by
  set σ1 := update σ 9 (tpuv_u a ++ false :: (tpuv_u b ++ false :: rest))
  have h1 := srv_ex_ru (a := 9) (b := 10) (by decide)
    (tpuv_u a ++ false :: (tpuv_u b ++ false :: rest)) σ1 (by simp [σ1])
  rw [srv_rdU_u] at h1
  set σ2 := update (update σ1 9 (tpuv_u b ++ false :: rest)) 10 (tpuv_u a ++ σ1 10)
  have h2 := srv_ex_ru (a := 9) (b := 11) (by decide) (tpuv_u b ++ false :: rest) σ2
    (by simp [σ2])
  rw [srv_rdU_u] at h2
  set σ3 := update (update σ2 9 rest) 11 (tpuv_u b ++ σ2 11)
  have h3 := exec_copyVia (a := 8) (b := 12) (t := 15) (by decide) (by decide) (by decide) σ3
    (by simp [σ3, σ2, σ1, h15])
  set σ4 := update σ3 12 (σ3 8 ++ σ3 12)
  have hX : σ4 11 = tpuv_u b := by simp [σ4, σ3, σ2, σ1, h11]
  have hY : σ4 12 = tpuv_u s := by simp [σ4, σ3, σ2, σ1, h12, h8]
  have h4 : σ4 14 = [] := by simp [σ4, σ3, σ2, σ1, h14]
  set σ5 := update (update σ4 11 []) 12 []
  have hT : ExecLe (if kv_leF true (tpuv_u b) (tpuv_u s) then drain 10
      else .seq (copyVia 5 13 15) (srv_tst 13 10)) σ5
      (if (decide (b ≤ s) || decide (e ≤ a)) then .norm (update σ 9 rest) else .halt false)
      (10 * e + 5 * a + 20) := by
    rw [tpuv_le_u]
    cases hbs : decide (b ≤ s)
    · simp only [Bool.false_or]
      have h6 := exec_copyVia (a := 5) (b := 13) (t := 15) (by decide) (by decide) (by decide) σ5
        (by simp [σ5, σ4, σ3, σ2, σ1, h15])
      set σ6 := update σ5 13 (σ5 5 ++ σ5 13)
      have h7 := srv_ex_tst (a := 13) (b := 10) (x := e) (y := a) (by decide) (by decide)
        (by decide) (σ := σ6) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, h5, h13])
        (by simp [σ6, σ5, σ4, σ3, σ2, σ1, h10]) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, h14])
      have e7 : update (update σ6 13 []) 10 [] = update σ 9 rest := by
        funext j; simp only [σ6, σ5, σ4, σ3, σ2, σ1, update_apply]
        split_ifs <;> simp_all
      rw [e7] at h7
      have h65 : (σ5 5).length = e := by simp [σ5, σ4, σ3, σ2, σ1, h5, tpuv_u_length]
      refine ((ExecLe.of h6).seq_norm h7).cast rfl ?_
      rw [h65]; omega
    · simp only [Bool.true_or, if_true]
      have h6 := exec_drain 10 (tpuv_u a) σ5 (by simp [σ5, σ4, σ3, σ2, σ1, h10])
      have e6 : update σ5 10 [] = update σ 9 rest := by
        funext j; simp only [σ5, σ4, σ3, σ2, σ1, update_apply]
        split_ifs <;> simp_all
      rw [e6] at h6
      exact (ExecLe.of h6).cast rfl (by simp [tpuv_u_length]; omega)
  have hTT := tpv_ex_test (a := 11) (b := 12) (by decide) (by decide) (by decide) hX hY h4 hT
  have hs8 : (σ3 8).length = s := by simp [σ3, σ2, σ1, h8, tpuv_u_length]
  refine ExecLe.pop_cons (b := true) (s := tpuv_u a ++ false :: (tpuv_u b ++ false :: rest))
    h9 ?_
  refine (h1.seq_norm (h2.seq_norm ((ExecLe.of h3).seq_norm hTT))).cast rfl ?_
  simp only [tpuv_u_length, hs8]
  omega

theorem srv_ex_iL {s e N : ℕ} (hs : s ≤ N) (he : e ≤ N) : ∀ (P : List (ℕ × ℕ)) (σ : ℕ → Str),
    (∀ p ∈ P, p.1 ≤ N ∧ p.2 ≤ N) → σ 9 = srv_pe P → σ 8 = tpuv_u s → σ 5 = tpuv_u e →
    σ 10 = [] → σ 11 = [] → σ 12 = [] → σ 13 = [] → σ 14 = [] → σ 15 = [] →
    ExecLe srv_iL σ (if srv_ok s e P then .norm (update σ 9 []) else .halt false)
      (P.length * (34 * N + 40) + 2)
  | [], σ, _, h9, _, _, _, _, _, _, _, _ => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil h9 (ExecLe.brk _))).cast ?_ (by simp)
    have h9' : σ 9 = [] := h9
    simp only [srv_ok, if_true]; rw [← h9', update_eq_self]
  | p :: P, σ, hP, h9, h8, h5, h10, h11, h12, h13, h14, h15 => by
    have hp := hP p (by simp)
    have hB := srv_ex_iB (a := p.1) (b := p.2) (rest := srv_pe P) h9 h8 h5 h10 h11 h12 h13 h14 h15
    rw [show srv_ok s e (p :: P) = ((decide (p.2 ≤ s) || decide (e ≤ p.1)) && srv_ok s e P)
      from rfl]
    by_cases hc : (decide (p.2 ≤ s) || decide (e ≤ p.1)) = true
    swap
    · rw [if_neg hc] at hB
      rw [Bool.eq_false_iff.2 hc, Bool.false_and]
      exact (ExecLe.loop_halt hB).cast (by simp) (by simp; nlinarith)
    · rw [if_pos hc] at hB
      rw [hc, Bool.true_and]
      have ih := srv_ex_iL hs he P (update σ 9 (srv_pe P)) (fun q hq => hP q (by simp [hq]))
        (by simp) (by simp [h8]) (by simp [h5]) (by simp [h10]) (by simp [h11]) (by simp [h12])
        (by simp [h13]) (by simp [h14]) (by simp [h15])
      rw [update_idem] at ih
      exact (ExecLe.loop_norm hB ih).cast (by simp) (by simp; nlinarith)

/-! ## One task -/

/-- Push the interval `(s, e)` (stacks `8`, `5`) onto `P` (stack `4`). -/
def srv_push : Cmd :=
  .seq (.push 4 false) (.seq (move 5 4) (.seq (.push 4 false) (.seq (move 8 4) (.push 4 true))))

theorem srv_ex_push {σ : ℕ → Str} {s e : ℕ} (h5 : σ 5 = tpuv_u e) (h8 : σ 8 = tpuv_u s) :
    ExecLe srv_push σ (.norm (update (update (update σ 4
      (true :: (tpuv_u s ++ false :: (tpuv_u e ++ false :: σ 4)))) 5 []) 8 []))
      (2 * e + 2 * s + 9) := by
  have h1 := ExecLe.push 4 false σ
  set σ1 := update σ 4 (false :: σ 4)
  have h2 := exec_move (a := 5) (b := 4) (by decide) (tpuv_u e) σ1 (by simp [σ1, h5])
  set σ2 := update (update σ1 5 []) 4 ((tpuv_u e).reverse ++ σ1 4)
  have h3 := ExecLe.push 4 false σ2
  set σ3 := update σ2 4 (false :: σ2 4)
  have h4 := exec_move (a := 8) (b := 4) (by decide) (tpuv_u s) σ3 (by simp [σ3, σ2, σ1, h8])
  set σ4 := update (update σ3 8 []) 4 ((tpuv_u s).reverse ++ σ3 4)
  have h5' := ExecLe.push 4 true σ4
  refine (h1.seq_norm ((ExecLe.of h2).seq_norm (h3.seq_norm ((ExecLe.of h4).seq_norm
    h5')))).cast ?_ (by simp [tpuv_u_length]; omega)
  congr 1
  funext j; simp only [σ4, σ3, σ2, σ1, update_apply, tpuv_u_rev]
  split_ifs <;> simp_all

def srv_D : Cmd := .seq (copyVia 4 9 15) (.seq srv_iL srv_push)

def srv_C : Cmd :=
  .seq (srv_ru 0 8) (.seq (copyVia 8 12 15) (.seq (srv_tst 6 12) (.seq (copyVia 8 5 15)
    (.seq (copyVia 5 12 15) (.seq (srv_tst 12 7) srv_D)))))

theorem srv_ex_C {N : ℕ} {σ : ℕ → Str} {Y : Str} {P : List (ℕ × ℕ)} {l r d : ℕ}
    (hd : d ≤ N) (hP : ∀ p ∈ P, p.1 ≤ N ∧ p.2 ≤ N)
    (h0 : σ 0 = Y) (h4 : σ 4 = srv_pe P) (h5 : σ 5 = tpuv_u l) (h6 : σ 6 = tpuv_u r)
    (h7 : σ 7 = tpuv_u d) (h8 : σ 8 = []) (h9 : σ 9 = []) (h10 : σ 10 = []) (h11 : σ 11 = [])
    (h12 : σ 12 = []) (h13 : σ 13 = []) (h14 : σ 14 = []) (h15 : σ 15 = []) :
    ExecLe srv_C σ (if (decide (r ≤ (srv_rdU Y).1) && decide ((srv_rdU Y).1 + l ≤ d) &&
        srv_ok (srv_rdU Y).1 ((srv_rdU Y).1 + l) P)
      then .norm (update (update (update (update (update σ 0 (srv_rdU Y).2) 4
        (srv_pe (((srv_rdU Y).1, (srv_rdU Y).1 + l) :: P))) 5 []) 6 []) 7 [])
      else .halt false)
      (31 * (srv_rdU Y).1 + 12 * l + 5 * r + 5 * d + 5 * (srv_pe P).length +
        P.length * (34 * N + 40) + 60) := by
  set s := (srv_rdU Y).1
  have h1 := srv_ex_ru (a := 0) (b := 8) (by decide) Y σ h0
  set σ1 := update (update σ 0 (srv_rdU Y).2) 8 (tpuv_u s ++ σ 8)
  have h2 := exec_copyVia (a := 8) (b := 12) (t := 15) (by decide) (by decide) (by decide) σ1
    (by simp [σ1, h15])
  set σ2 := update σ1 12 (σ1 8 ++ σ1 12)
  have h3 := srv_ex_tst (a := 6) (b := 12) (x := r) (y := s) (σ := σ2) (by decide) (by decide)
    (by decide) (by simp [σ2, σ1, h6]) (by simp [σ2, σ1, h8, h12]) (by simp [σ2, σ1, h14])
  set σ3 := update (update σ2 6 []) 12 []
  have h4' := exec_copyVia (a := 8) (b := 5) (t := 15) (by decide) (by decide) (by decide) σ3
    (by simp [σ3, σ2, σ1, h15])
  set σ4 := update σ3 5 (σ3 8 ++ σ3 5)
  have h5' := exec_copyVia (a := 5) (b := 12) (t := 15) (by decide) (by decide) (by decide) σ4
    (by simp [σ4, σ3, σ2, σ1, h15])
  set σ5 := update σ4 12 (σ4 5 ++ σ4 12)
  have h6' := srv_ex_tst (a := 12) (b := 7) (x := s + l) (y := d) (σ := σ5) (by decide)
    (by decide) (by decide) (by simp [σ5, σ4, σ3, σ2, σ1, h5, h8, tpuv_u_add])
    (by simp [σ5, σ4, σ3, σ2, σ1, h7]) (by simp [σ5, σ4, σ3, σ2, σ1, h14])
  set σ6 := update (update σ5 12 []) 7 []
  have h7' := exec_copyVia (a := 4) (b := 9) (t := 15) (by decide) (by decide) (by decide) σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, h15])
  set σ7 := update σ6 9 (σ6 4 ++ σ6 9)
  have hl1 : (σ1 8).length = s := by simp [σ1, h8, tpuv_u_length]
  have hl3 : (σ3 8).length = s := by simp [σ3, σ2, σ1, h8, tpuv_u_length]
  have hl4 : (σ4 5).length = s + l := by simp [σ4, σ3, σ2, σ1, h8, h5, tpuv_u_length]
  have hl6 : (σ6 4).length = (srv_pe P).length := by simp [σ6, σ5, σ4, σ3, σ2, σ1, h4]
  have key : ∀ b : Bool, (b = true → ExecLe (Cmd.seq srv_iL srv_push) σ7
      (if srv_ok s (s + l) P then .norm (update (update (update (update (update σ 0
        (srv_rdU Y).2) 4 (srv_pe ((s, s + l) :: P))) 5 []) 6 []) 7 []) else .halt false)
      (P.length * (34 * N + 40) + 2 + (2 * (s + l) + 2 * s + 9))) → b = decide (s + l ≤ d) →
      ExecLe srv_C σ (if (decide (r ≤ s) && b && srv_ok s (s + l) P)
        then .norm (update (update (update (update (update σ 0 (srv_rdU Y).2) 4
          (srv_pe ((s, s + l) :: P))) 5 []) 6 []) 7 []) else .halt false)
        (31 * s + 12 * l + 5 * r + 5 * d + 5 * (srv_pe P).length +
          P.length * (34 * N + 40) + 60) := by
    intro b hk hb
    have hx := srv_sq h3 (fun _ => (ExecLe.of h4').seq_norm ((ExecLe.of h5').seq_norm
      (srv_sq (hb ▸ h6') (fun hb' => (ExecLe.of h7').seq_norm (hk hb')))))
    refine (h1.seq_norm ((ExecLe.of h2).seq_norm hx)).cast ?_ ?_
    · cases decide (r ≤ s) <;> cases b <;> simp
    · simp only [hl1, hl3, hl4, hl6]; omega
  refine key _ ?_ rfl
  intro hb
  have hsd : s + l ≤ d := of_decide_eq_true hb
  have h8' := srv_ex_iL (s := s) (e := s + l) (N := N) (by omega) (by omega) P σ7 hP
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h4, h9]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h8])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h8, h5, tpuv_u_add])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h10]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h11])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h13])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h14]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h15])
  have h9' := srv_ex_push (σ := update σ7 9 []) (s := s) (e := s + l)
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h8, h5, tpuv_u_add])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h8])
  have hx := srv_sq h8' (fun _ => h9')
  refine hx.cast ?_ le_rfl
  congr 2
  funext j
  rcases j with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|j <;>
    simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, srv_pe, h4, h5, h8, h9, h10, h11, h12, h13, h14, h15,
      tpuv_u_add]

/-! ## The main loop -/

def srv_B : Cmd :=
  .seq (srv_rd 5) (srv_pk 3 (.halt false) (.seq (srv_rd 6) (srv_pk 3 (.halt false)
    (.seq (srv_rd 7) srv_C))))

def srv_oB : Cmd := srv_pk 3 (.halt true) srv_B

def srv_oL : Cmd := .loop srv_oB

/-- The stacks of the main loop. -/
def srv_st (Y C P : Str) : ℕ → Str := fun j =>
  if j = 0 then Y else if j = 3 then C else if j = 4 then P else []

/-- The time of one iteration of the main loop. -/
def srv_Ti (N : ℕ) : ℕ := 60 * (N + 2) ^ 2

theorem srv_enc_one (l : List SatSym) : ∃ x t, enc [l] = x :: t := kv_enc_ne l []

theorem srv_ex_oL (N : ℕ) : ∀ (rs : List (List SatSym)) (P : List (ℕ × ℕ)) (Y : Str),
    (∀ r ∈ rs, sep ∉ r) → (∀ r ∈ rs, r.length ≤ N) → P.length + rs.length ≤ N →
    (∀ p ∈ P, p.1 ≤ N ∧ p.2 ≤ N) → Y.length ≤ N →
    ExecLe srv_oL (srv_st Y (enc rs) (srv_pe P)) (.halt (srv_go P rs Y))
      ((rs.length + 1) * srv_Ti N)
  | [], P, Y, _, _, _, _, _ => by
    refine (ExecLe.loop_halt (ExecLe.pop_nil (by simp [srv_st, enc]) (ExecLe.halt true _))).cast
      (by simp [srv_go]) ?_
    simp only [srv_Ti]; nlinarith
  | [l], P, Y, hs, hl, _, _, _ => by
    obtain ⟨x, t, hx⟩ := kv_enc_ne l []
    have h1 := srv_ex_rd (k := 5) (by decide) l (srv_st Y (enc [l]) (srv_pe P)) (enc [])
      (hs l (by simp)) (by simp [srv_st, enc_cons])
    have h2 : ExecLe (srv_pk 3 (.halt false) (.seq (srv_rd 6) (srv_pk 3 (.halt false)
        (.seq (srv_rd 7) srv_C)))) (update (update (srv_st Y (enc [l]) (srv_pe P)) 3 (enc []))
        5 (tpuv_u l.length ++ srv_st Y (enc [l]) (srv_pe P) 5)) (.halt false) 2 :=
      ExecLe.pop_nil (by simp [enc]) (ExecLe.halt false _)
    refine (ExecLe.loop_halt (srv_ex_pk (k := 3) (x := x) (t := t) (by simp [srv_st, hx]) (h1.seq_norm h2))).cast
      (by simp [srv_go]) ?_
    have := hl l (by simp)
    simp only [srv_Ti, List.length_cons, List.length_nil]; nlinarith
  | [l, r], P, Y, hs, hl, _, _, _ => by
    obtain ⟨x, t, hx⟩ := kv_enc_ne l [r]
    obtain ⟨x', t', hx'⟩ := kv_enc_ne r []
    have h1 := srv_ex_rd (k := 5) (by decide) l (srv_st Y (enc [l, r]) (srv_pe P)) (enc [r])
      (hs l (by simp)) (by simp [srv_st, enc_cons])
    set σ1 := update (update (srv_st Y (enc [l, r]) (srv_pe P)) 3 (enc [r])) 5
      (tpuv_u l.length ++ srv_st Y (enc [l, r]) (srv_pe P) 5)
    have h2 := srv_ex_rd (k := 6) (by decide) r σ1 (enc [])
      (hs r (by simp)) (by simp [σ1, enc_cons])
    have h3 : ExecLe (srv_pk 3 (.halt false) (.seq (srv_rd 7) srv_C))
        (update (update σ1 3 (enc [])) 6 (tpuv_u r.length ++ σ1 6)) (.halt false) 2 :=
      ExecLe.pop_nil (by simp [enc]) (ExecLe.halt false _)
    refine (ExecLe.loop_halt (srv_ex_pk (k := 3) (x := x) (t := t) (by simp [srv_st, hx]) (h1.seq_norm
      (srv_ex_pk (k := 3) (x := x') (t := t') (by simp [σ1, hx']) (h2.seq_norm h3))))).cast (by simp [srv_go]) ?_
    have := hl l (by simp)
    have := hl r (by simp)
    simp only [srv_Ti, List.length_cons, List.length_nil]; nlinarith
  | l :: r :: d :: rs, P, Y, hs, hl, hPl, hP, hY => by
    obtain ⟨x, t, hx⟩ := kv_enc_ne l (r :: d :: rs)
    obtain ⟨x', t', hx'⟩ := kv_enc_ne r (d :: rs)
    obtain ⟨x'', t'', hx''⟩ := kv_enc_ne d rs
    have hll := hl l (by simp)
    have hrl := hl r (by simp)
    have hdl := hl d (by simp)
    set σ0 := srv_st Y (enc (l :: r :: d :: rs)) (srv_pe P)
    have h1 := srv_ex_rd (k := 5) (by decide) l σ0 (enc (r :: d :: rs))
      (hs l (by simp)) (by simp [σ0, srv_st, enc_cons])
    set σ1 := update (update σ0 3 (enc (r :: d :: rs))) 5 (tpuv_u l.length ++ σ0 5)
    have h2 := srv_ex_rd (k := 6) (by decide) r σ1 (enc (d :: rs))
      (hs r (by simp)) (by simp [σ1, enc_cons])
    set σ2 := update (update σ1 3 (enc (d :: rs))) 6 (tpuv_u r.length ++ σ1 6)
    have h3 := srv_ex_rd (k := 7) (by decide) d σ2 (enc rs)
      (hs d (by simp)) (by simp [σ2, enc_cons])
    set σ3 := update (update σ2 3 (enc rs)) 7 (tpuv_u d.length ++ σ2 7)
    have h4 := srv_ex_C (N := N) (σ := σ3) (Y := Y) (P := P) (l := l.length) (r := r.length)
      (d := d.length) hdl hP (by simp [σ3, σ2, σ1, σ0, srv_st])
      (by simp [σ3, σ2, σ1, σ0, srv_st]) (by simp [σ3, σ2, σ1, σ0, srv_st])
      (by simp [σ3, σ2, σ1, σ0, srv_st]) (by simp [σ3, σ2, σ1, σ0, srv_st])
      (by simp [σ3, σ2, σ1, σ0, srv_st]) (by simp [σ3, σ2, σ1, σ0, srv_st])
      (by simp [σ3, σ2, σ1, σ0, srv_st]) (by simp [σ3, σ2, σ1, σ0, srv_st])
      (by simp [σ3, σ2, σ1, σ0, srv_st]) (by simp [σ3, σ2, σ1, σ0, srv_st])
      (by simp [σ3, σ2, σ1, σ0, srv_st]) (by simp [σ3, σ2, σ1, σ0, srv_st])
    have hB : ExecLe srv_oB σ0 _ _ := srv_ex_pk (k := 3) (cn := .halt true) (x := x) (t := t) (by simp [σ0, srv_st, hx]) (h1.seq_norm
      (srv_ex_pk (k := 3) (x := x') (t := t') (by simp [σ1, hx']) (h2.seq_norm (srv_ex_pk (k := 3) (x := x'') (t := t'') (by simp [σ2, hx'']) (h3.seq_norm
        h4)))))
    have hs8 := srv_rdU_le Y
    have hpe := srv_pe_length_le N P hP
    simp only [List.length_cons] at hPl
    have hc : 3 * l.length + 3 + (2 + (3 * r.length + 3 + (2 + (3 * d.length + 3 +
        (31 * (srv_rdU Y).1 + 12 * l.length + 5 * r.length + 5 * d.length +
        5 * (srv_pe P).length + P.length * (34 * N + 40) + 60))))) + 2 ≤ srv_Ti N := by
      have hPN : P.length ≤ N := by omega
      have e1 : P.length * (2 * N + 3) ≤ N * (2 * N + 3) := Nat.mul_le_mul_right _ hPN
      have e2 : P.length * (34 * N + 40) ≤ N * (34 * N + 40) := Nat.mul_le_mul_right _ hPN
      simp only [srv_Ti]; nlinarith
    rw [show srv_go P (l :: r :: d :: rs) Y = (srv_chk P l r d Y && srv_go
      (((srv_rdU Y).1, (srv_rdU Y).1 + l.length) :: P) rs (srv_rdU Y).2) from rfl]
    by_cases hk : srv_chk P l r d Y = true
    swap
    · rw [Bool.eq_false_iff.2 hk, Bool.false_and]
      unfold srv_chk at hk
      rw [if_neg hk] at hB
      refine (ExecLe.loop_halt hB).cast rfl ?_
      simp only [List.length_cons]
      nlinarith
    · rw [hk, Bool.true_and]
      unfold srv_chk at hk
      rw [if_pos hk] at hB
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      have ih := srv_ex_oL N rs (((srv_rdU Y).1, (srv_rdU Y).1 + l.length) :: P) (srv_rdU Y).2
        (fun q hq => hs q (by simp [hq])) (fun q hq => hl q (by simp [hq]))
        (by simp; omega) (by
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · simp; omega
          · exact hP q hq) (by omega)
      have e : update (update (update (update (update σ3 0 (srv_rdU Y).2) 4
          (srv_pe (((srv_rdU Y).1, (srv_rdU Y).1 + l.length) :: P))) 5 []) 6 []) 7 [] =
          srv_st (srv_rdU Y).2 (enc rs) (srv_pe (((srv_rdU Y).1, (srv_rdU Y).1 + l.length) :: P)) := by
        funext j
        rcases j with _|_|_|_|_|_|_|_|j <;> simp [σ3, σ2, σ1, σ0, srv_st]
      rw [e] at hB
      refine (ExecLe.loop_norm hB ih).cast rfl ?_
      simp only [List.length_cons]
      nlinarith

/-! ## The whole verifier -/

def srv_ver : Cmd := .seq phaseA (.seq (trimC 2) (.seq (move 2 3) srv_oL))

/-- Time bound of the verifier. -/
def srv_Tver (n : ℕ) : ℕ := 20 * n + 20 + (n + 1) * srv_Ti n

theorem srv_row_le (w : List SatSym) : ∀ r ∈ clauses w, r.length ≤ w.length := by
  intro r hr
  have h1 := sum_length_le (clauses w)
  have h2 := length_trunc_le w
  have h3 : r.length ≤ ((clauses w).map List.length).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hr)
  unfold trunc at h2
  omega

theorem srv_exec_ver (z : Str) :
    ExecLe srv_ver (init [z]).stk (.halt (srv_vres (dec z).1 (dec z).2)) (srv_Tver z.length) := by
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
      srv_st y (enc (clauses w)) (srv_pe []) := by
    funext j
    simp only [σ₂, σ₁, srv_st, update_apply, enc, trunc, srv_pe]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  have hR := srv_ex_oL z.length (clauses w) [] y (sep_not_mem_clauses w)
    (fun r hr => (srv_row_le w r hr).trans (by omega)) (by simp; omega) (by simp) (by omega)
  refine (hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm hR))).cast rfl ?_
  have hk : ((clauses w).length + 1) * srv_Ti z.length ≤ (z.length + 1) * srv_Ti z.length :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [htl, srv_Tver]
  omega

theorem srv_Tver_le (n : ℕ) : srv_Tver n ≤ tb 9 n := by
  unfold srv_Tver srv_Ti tb
  have h6 : 2 ^ 6 ≤ (n + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have e : (n + 2) ^ 9 = (n + 2) * (n + 2) * (n + 2) * (n + 2) ^ 6 := by ring
  have h1 : 20 * n + 20 + (n + 1) * (60 * (n + 2) ^ 2) ≤ (n + 2) * (n + 2) * (n + 2) * 64 := by
    nlinarith
  rw [e]
  exact h1.trans (Nat.mul_le_mul_left _ (by simpa using h6))

end Pnp.Karp.SeqRD
