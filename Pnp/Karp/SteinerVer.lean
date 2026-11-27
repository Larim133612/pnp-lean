import Pnp.Karp.Steiner
import Pnp.Karp.HamVer

/-!
# STEINER TREE ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/Steiner.lean`, rows `kr :: tr :: rows`, `n = |rows|`) and a certificate
`y : List Bool`.  The certificate lists vertices `v₀, v₁, …, v_m` as one-hot blocks of `n` bits
(`hv_tk n`, as for HAMILTONIAN CYCLE, `Pnp/Karp/HamVer.lean`), each block preceded by a `true`
bit; a `false` bit (or the end of `y`) ends the list.  With `S` the set of the vertices listed so
far (a bit vector of length `n`, initially empty), the verifier checks:

* the first block `v₀` is one-hot (`hv_permOk`), `S := {v₀}`;
* every further block `v_i` costs one unit of the budget `|kr|`, is joined to `S` by a `pos`
  entry (in one of the two directions, `hv_edgeB rows S v_i`), is one-hot and not yet in `S`
  (`hv_permOk v_i S`); `S := S ∪ {v_i}`;
* at the end, every terminal `t < n` (`pos` at position `t` of `tr`) is in `S` (`stv_tc`).

So the edges used to attach `v₁, …, v_m` form a tree with `m ≤ |kr|` edges containing all
terminals.

Stacks: those of `hv_HS` (`Pnp/Karp/HamVer.lean`); besides the stacks used by the reused
commands (`hv_takeN`, `hv_permC`, `hv_edgeC`, `hv_cntL`, `hv_initS`), stack `2` (`P`) holds the
terminal flags `tr.map isPos` and stack `5` (`I`) the remaining budget (unary).

Program (`stv_ver`):
1. parse (`phaseA`, `trimC 2`, `move 2 1`); read the budget row onto `I` (`stv_bdL`) and the
   terminal row as flags onto `P` (`stv_trL`, `move 10 2`), halting `false` if a row is
   missing; count the remaining rows (`hv_cntL`) and set `S := false^n` (`hv_initS`);
2. `stv_rest`: pop a bit of the certificate; if `true` read and check the first block
   (`hv_takeN`, `hv_permC`) and run the main loop `stv_mainL`; per iteration pop a bit (`false`
   or the end: run the final check `stv_fin`), pop the budget (halt `false` if empty), read the
   next block, check the edge (`hv_edgeC` against a copy of `S`) and the block (`hv_permC`);
3. `stv_fin`: the terminal check (`stv_tcL`), then accept.

`stv_exec_ver`: the program halts with `stv_vres (dec z).1 (dec z).2` on every input `z`,
within `hv_Tver |z|` steps.
-/

namespace Pnp.Karp.Steiner

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.Ham

/-! ## Semantics -/

/-- Every flag of `P` at a position `< |S|` has its bit set in `S`. -/
def stv_tc : Str → Str → Bool
  | _, [] => true
  | P, s :: S => (s || !(P.headD false)) && stv_tc P.tail S

/-- What the main loop computes (`c`: the remaining budget, `R`: the unread certificate, `S`:
the vertices listed so far). -/
def stv_mainF (rows : List (List SatSym)) (n : ℕ) (P : Str) : ℕ → Str → Str → Bool
  | _, [], S => stv_tc P S
  | _, false :: _, S => stv_tc P S
  | 0, true :: _, _ => false
  | c + 1, true :: R, S => hv_edgeB rows S (hv_tk n R) && hv_permOk (hv_tk n R) S &&
      stv_mainF rows n P c (R.drop n) (hv_orV (hv_tk n R) S)

/-- The answer of the verifier after the first certificate bit. -/
def stv_restF (rows : List (List SatSym)) (n : ℕ) (P : Str) (c : ℕ) : Str → Bool
  | true :: y => hv_permOk (hv_tk n y) (List.replicate n false) &&
      stv_mainF rows n P c (y.drop n) (hv_orV (hv_tk n y) (List.replicate n false))
  | _ => stv_tc P (List.replicate n false)

/-- The answer of the verifier on `(w, y)`. -/
def stv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | kr :: tr :: rows => stv_restF rows rows.length (tr.map isPos) kr.length y
  | _ => false

/-! ## Reading the budget and the terminal row -/

def stv_bdB : Cmd :=
  .pop 1 (.halt false) (.pop 1 (.halt false) .brk (.push 5 true))
    (.pop 1 (.halt false) (.push 5 true) (.push 5 true))

def stv_bdL : Cmd := .loop stv_bdB

theorem stv_ex_bdL (Q' : Str) : ∀ (t : List SatSym) (s : hv_HS), sep ∉ t →
    s.M = t.flatMap ic ++ false :: false :: Q' →
    ExecLe stv_bdL s.st (.norm {s with M := Q', I := List.replicate t.length true ++ s.I}.st)
      (3 * t.length + 3)
  | [], s, _, h => by
    refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := false :: Q') (by simp [h])
      (ExecLe.pop_cons (b := false) (s := Q') (by simp) (ExecLe.brk _)))).cast ?_ (by simp)
    congr 1; cases s; simp_all
  | x :: t, s, hr, h => by
    have hx : x ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := stv_ex_bdL Q' t {s with M := t.flatMap ic ++ false :: false :: Q', I := true :: s.I} (fun e => hr (List.mem_cons_of_mem _ e)) rfl
    have e : ({ ({s with M := t.flatMap ic ++ false :: false :: Q', I := true :: s.I} : hv_HS)
        with M := Q', I := List.replicate t.length true ++ true :: s.I } : hv_HS) =
        {s with M := Q', I := List.replicate (x :: t).length true ++ s.I} := by
      simp [List.replicate_succ']
    simp only at ih e
    rw [e] at ih
    cases x with
    | sep => exact absurd rfl hx
    | zero =>
      exact (ExecLe.loop_norm (ExecLe.pop_cons (b := false)
        (s := true :: (t.flatMap ic ++ false :: false :: Q')) (by simp [h, ic])
        (ExecLe.pop_cons (b := true) (s := t.flatMap ic ++ false :: false :: Q') (by simp)
          ((ExecLe.push 5 true _).cast (by simp) le_rfl))) ih).cast rfl (by simp; omega)
    | pos =>
      exact (ExecLe.loop_norm (ExecLe.pop_cons (b := true)
        (s := false :: (t.flatMap ic ++ false :: false :: Q')) (by simp [h, ic])
        (ExecLe.pop_cons (b := false) (s := t.flatMap ic ++ false :: false :: Q') (by simp)
          ((ExecLe.push 5 true _).cast (by simp) le_rfl))) ih).cast rfl (by simp; omega)
    | neg =>
      exact (ExecLe.loop_norm (ExecLe.pop_cons (b := true)
        (s := true :: (t.flatMap ic ++ false :: false :: Q')) (by simp [h, ic])
        (ExecLe.pop_cons (b := true) (s := t.flatMap ic ++ false :: false :: Q') (by simp)
          ((ExecLe.push 5 true _).cast (by simp) le_rfl))) ih).cast rfl (by simp; omega)

theorem stv_ex_bdL_nil (s : hv_HS) (h : s.M = []) : ExecLe stv_bdL s.st (.halt false) 2 :=
  ExecLe.loop_halt (ExecLe.pop_nil (by simpa) (ExecLe.halt false _))

def stv_trB : Cmd :=
  .pop 1 (.halt false) (.pop 1 (.halt false) .brk (.push 10 false))
    (.pop 1 (.halt false) (.push 10 true) (.push 10 false))

def stv_trL : Cmd := .loop stv_trB

theorem stv_ex_trL (Q' : Str) : ∀ (t : List SatSym) (s : hv_HS), sep ∉ t →
    s.M = t.flatMap ic ++ false :: false :: Q' →
    ExecLe stv_trL s.st (.norm {s with M := Q', T := (t.map isPos).reverse ++ s.T}.st)
      (3 * t.length + 3)
  | [], s, _, h => by
    refine (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := false :: Q') (by simp [h])
      (ExecLe.pop_cons (b := false) (s := Q') (by simp) (ExecLe.brk _)))).cast ?_ (by simp)
    congr 1; cases s; simp_all
  | x :: t, s, hr, h => by
    have hx : x ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have ih := stv_ex_trL Q' t {s with M := t.flatMap ic ++ false :: false :: Q', T := isPos x :: s.T} (fun e => hr (List.mem_cons_of_mem _ e)) rfl
    have e : ({ ({s with M := t.flatMap ic ++ false :: false :: Q', T := isPos x :: s.T} : hv_HS)
        with M := Q', T := (t.map isPos).reverse ++ isPos x :: s.T } : hv_HS) =
        {s with M := Q', T := ((x :: t).map isPos).reverse ++ s.T} := by
      simp
    simp only at ih e
    rw [e] at ih
    cases x with
    | sep => exact absurd rfl hx
    | zero =>
      exact (ExecLe.loop_norm (ExecLe.pop_cons (b := false)
        (s := true :: (t.flatMap ic ++ false :: false :: Q')) (by simp [h, ic])
        (ExecLe.pop_cons (b := true) (s := t.flatMap ic ++ false :: false :: Q') (by simp)
          ((ExecLe.push 10 false _).cast (by simp [isPos]) le_rfl))) ih).cast rfl
        (by simp; omega)
    | pos =>
      exact (ExecLe.loop_norm (ExecLe.pop_cons (b := true)
        (s := false :: (t.flatMap ic ++ false :: false :: Q')) (by simp [h, ic])
        (ExecLe.pop_cons (b := false) (s := t.flatMap ic ++ false :: false :: Q') (by simp)
          ((ExecLe.push 10 true _).cast (by simp [isPos]) le_rfl))) ih).cast rfl
        (by simp; omega)
    | neg =>
      exact (ExecLe.loop_norm (ExecLe.pop_cons (b := true)
        (s := true :: (t.flatMap ic ++ false :: false :: Q')) (by simp [h, ic])
        (ExecLe.pop_cons (b := true) (s := t.flatMap ic ++ false :: false :: Q') (by simp)
          ((ExecLe.push 10 false _).cast (by simp [isPos]) le_rfl))) ih).cast rfl
        (by simp; omega)

theorem stv_ex_trL_nil (s : hv_HS) (h : s.M = []) : ExecLe stv_trL s.st (.halt false) 2 :=
  ExecLe.loop_halt (ExecLe.pop_nil (by simpa) (ExecLe.halt false _))

/-! ## The terminal check -/

def stv_tcB : Cmd := .pop 9 .brk (.pop 2 .skip .skip (.halt false)) (.pop 2 .skip .skip .skip)

def stv_tcL : Cmd := .loop stv_tcB

/-- The final check: all terminals listed; accept. -/
def stv_fin : Cmd := .seq stv_tcL (.halt true)

theorem stv_ex_tcB (b : Bool) (S : Str) (s : hv_HS) (h : s.S = b :: S) :
    ExecLe stv_tcB s.st (if (b || !(s.P.headD false)) then .norm {s with S := S, P := s.P.tail}.st
      else .halt false) 3 := by
  refine ExecLe.pop_cons (b := b) (s := S) (by simp [h]) ?_
  rcases hP : s.P with _ | ⟨_ | _, P'⟩ <;> cases b
  · exact (ExecLe.pop_nil (by simp [hP]) (ExecLe.skip _)).cast (by simp [hP]) le_rfl
  · exact (ExecLe.pop_nil (by simp [hP]) (ExecLe.skip _)).cast (by simp [hP]) le_rfl
  · exact (ExecLe.pop_cons (b := false) (s := P') (by simp [hP]) (ExecLe.skip _)).cast
      (by simp [hP]) le_rfl
  · exact (ExecLe.pop_cons (b := false) (s := P') (by simp [hP]) (ExecLe.skip _)).cast
      (by simp [hP]) le_rfl
  · exact (ExecLe.pop_cons (b := true) (s := P') (by simp [hP]) (ExecLe.halt false _)).cast
      (by simp) (by omega)
  · exact (ExecLe.pop_cons (b := true) (s := P') (by simp [hP]) (ExecLe.skip _)).cast
      (by simp [hP]) le_rfl

theorem stv_ex_tcL : ∀ (S : Str) (s : hv_HS), s.S = S →
    ExecLe stv_tcL s.st (if stv_tc s.P S then .norm {s with S := [], P := s.P.drop S.length}.st
      else .halt false) (3 * S.length + 2)
  | [], s, h => (ExecLe.loop_brk (ExecLe.pop_nil (by simpa) (ExecLe.brk _))).cast
      (by simp only [stv_tc, if_true]; congr 1; cases s; simp_all) (by simp)
  | b :: S, s, h => by
    have ih := stv_ex_tcL S {s with S := S, P := s.P.tail} rfl
    simp only at ih
    have hb := stv_ex_tcB b S s h
    simp only [stv_tc]
    by_cases hc : (b || !(s.P.headD false)) = true
    · rw [if_pos hc] at hb
      simp only [hc, Bool.true_and]
      refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
      split_ifs
      · simp [List.drop_tail]
      · rfl
    · rw [if_neg hc] at hb
      simp only [Bool.eq_false_iff.mpr hc, Bool.false_and]
      exact (ExecLe.loop_halt hb).cast (by simp) (by simp; omega)

theorem stv_ex_fin (s : hv_HS) :
    ExecLe stv_fin s.st (.halt (stv_tc s.P s.S)) (3 * s.S.length + 3) := by
  have h := stv_ex_tcL s.S s rfl
  unfold stv_fin
  by_cases hc : stv_tc s.P s.S = true
  · rw [if_pos hc] at h
    exact (h.seq_norm (ExecLe.halt true _)).cast (by rw [hc]) le_rfl
  · rw [if_neg hc] at h
    exact (ExecLe.seq_halt h).cast (by simp only [Bool.not_eq_true] at hc; rw [hc]) (by omega)

/-! ## One step of the main loop -/

/-- Read the next block `Y`, check the edge between `S` and `Y` (on a copy `X` of `S`), check
`Y` against `S` and add it to `S`. -/
def stv_body : Cmd :=
  .seq hv_takeN (.seq (copyVia 9 6 10) (.seq hv_edgeC (.seq (drain 6) (.seq (hv_mvo 7 6)
    (.seq hv_permC (drain 6))))))

/-- The invariant of the main loop (apart from `R`, `P`, `I`, `S`, `Z`). -/
structure stv_Inv (rows : List (List SatSym)) (n : ℕ) (s : hv_HS) : Prop where
  hN : s.N = List.replicate n true
  hM : s.M = enc rows
  hK : s.K = []
  hT : s.T = []
  hX : s.X = []
  hY : s.Y = []
  hXC : s.XC = []
  hF : s.F = []
  hQ : s.Q = []
  hCC : s.CC = []
  hG : s.G = []
  hH : s.H = []
  hRF : s.RF = []
  hCT : s.CT = []
  hS : s.S.length = n

/-- Cost of the loop body. -/
def stv_Tb (n Lm Ts : ℕ) : ℕ := 90 * n + 10 * Lm + 2 * Ts + 90

theorem stv_ex_body (rows : List (List SatSym)) (n : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r)
    (s : hv_HS) (hi : stv_Inv rows n s) :
    ExecLe stv_body s.st
      (if hv_edgeB rows s.S (hv_tk n s.R) && hv_permOk (hv_tk n s.R) s.S then
        .norm {s with R := s.R.drop n, S := hv_orV (hv_tk n s.R) s.S}.st
      else .halt false) (stv_Tb n s.M.length (hv_Tsc n rows)) := by
  have h1 := hv_ex_takeN n s hi.hN hi.hK hi.hT hi.hY
  have h2 := hv_ex_copy (a := 9) (b := 6) (by decide) (by decide) (by decide)
    {s with R := s.R.drop n, Y := hv_tk n s.R}.st (by simpa using hi.hT)
  have eX : s.S ++ s.X = s.S := by rw [hi.hX, List.append_nil]
  simp only [hv_st9, hv_st6, hv_u6, eX] at h2
  have h3 := hv_ex_edgeC rows n {s with R := s.R.drop n, Y := hv_tk n s.R, X := s.S} hsep
    hi.hM hi.hQ hi.hCC hi.hG hi.hT hi.hH hi.hRF hi.hCT (by simp [hi.hS])
    (by simp [hv_length_tk])
  simp only at h3
  have h4 := hv_ex_drain 6 {s with R := s.R.drop n, Y := hv_tk n s.R, X := s.S}.st
  simp only [hv_u6, hv_st6] at h4
  have h5 := hv_ex_mvo (a := 7) (b := 6) (by decide) (by decide) (by decide)
    {s with R := s.R.drop n, Y := hv_tk n s.R, X := []}.st (by simpa using hi.hT)
  simp only [hv_u6, hv_st6, hv_u7, hv_st7, List.append_nil] at h5
  have h6 := hv_ex_permC {s with R := s.R.drop n, Y := [], X := hv_tk n s.R} hi.hXC hi.hF
    hi.hT (by simp [hi.hS, hv_length_tk])
  simp only at h6
  have h7 := hv_ex_drain 6
    {s with R := s.R.drop n, Y := [], X := hv_tk n s.R, S := hv_orV (hv_tk n s.R) s.S}.st
  simp only [hv_u6, hv_st6] at h7
  have hTb : 10 * n + 8 + (5 * s.S.length + 4 + (10 * s.M.length + 52 * n +
      2 * hv_Tsc n rows + 50 + (2 * s.S.length + 2 + (4 * (hv_tk n s.R).length + 4 +
      (12 * (hv_tk n s.R).length + 10 + (2 * (hv_tk n s.R).length + 2)))))) ≤
      stv_Tb n s.M.length (hv_Tsc n rows) := by
    simp only [stv_Tb, hv_length_tk, hi.hS]; omega
  by_cases he : hv_edgeB rows s.S (hv_tk n s.R) = true
  · rw [if_pos he] at h3
    by_cases hp : hv_permOk (hv_tk n s.R) s.S = true
    · rw [if_pos hp] at h6
      rw [if_pos (by simp [hp, he])]
      refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm
        (h6.seq_norm h7)))))).cast ?_ hTb
      have hY := hi.hY
      have hX := hi.hX
      congr 1; cases s; simp_all
    · rw [if_neg hp] at h6
      rw [if_neg (by simp [hp, he])]
      exact (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm
        (ExecLe.seq_halt h6)))))).cast rfl (by omega)
  · rw [if_neg he] at h3
    rw [if_neg (by simp [he])]
    exact (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3))).cast rfl (by omega)

/-! ## The main loop -/

def stv_step : Cmd := .pop 5 (.halt false) stv_body stv_body

def stv_mainL : Cmd := .loop (.pop 0 stv_fin stv_fin stv_step)

theorem stv_ex_mainL (rows : List (List SatSym)) (n : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∀ (c : ℕ) (s : hv_HS), stv_Inv rows n s → s.I = List.replicate c true →
    ExecLe stv_mainL s.st (.halt (stv_mainF rows n s.P c s.R s.S))
      ((c + 1) * (stv_Tb n s.M.length (hv_Tsc n rows) + 2) + 3 * n + 4) := by
  intro c
  induction c with
  | zero =>
    intro s hi hI
    rcases hR : s.R with _ | ⟨_ | _, R'⟩
    · exact (ExecLe.loop_halt (ExecLe.pop_nil (by simpa using hR) (stv_ex_fin s))).cast
        (by simp [stv_mainF]) (by rw [hi.hS]; omega)
    · exact (ExecLe.loop_halt (ExecLe.pop_cons (b := false) (s := R') (by simpa using hR)
        (by simpa using stv_ex_fin {s with R := R'}))).cast
        (by simp [stv_mainF]) (by rw [hi.hS]; omega)
    · exact (ExecLe.loop_halt (ExecLe.pop_cons (b := true) (s := R') (by simpa using hR)
        (ExecLe.pop_nil (by simpa using hI) (ExecLe.halt false _)))).cast
        (by simp [stv_mainF]) (by omega)
  | succ k ih =>
    intro s hi hI
    rcases hR : s.R with _ | ⟨_ | _, R'⟩
    · exact (ExecLe.loop_halt (ExecLe.pop_nil (by simpa using hR) (stv_ex_fin s))).cast
        (by simp [stv_mainF]) (by rw [hi.hS]; nlinarith)
    · exact (ExecLe.loop_halt (ExecLe.pop_cons (b := false) (s := R') (by simpa using hR)
        (by simpa using stv_ex_fin {s with R := R'}))).cast
        (by simp [stv_mainF]) (by rw [hi.hS]; nlinarith)
    · have hb := stv_ex_body rows n hsep {s with R := R', I := List.replicate k true}
        (by obtain ⟨⟩ := hi; constructor <;> assumption)
      simp only at hb
      have hpop : ∀ (r : Res) (T : ℕ), ExecLe stv_body
          {s with R := R', I := List.replicate k true}.st r T →
          ExecLe (.pop 0 stv_fin stv_fin stv_step) s.st r (T + 2) := by
        intro r T h
        refine ExecLe.pop_cons (b := true) (s := R') (by simpa using hR) ?_
        refine ExecLe.pop_cons (b := true) (s := List.replicate k true)
          (by simp [hI, List.replicate_succ]) ?_
        simpa using h
      simp only [stv_mainF]
      by_cases hc : (hv_edgeB rows s.S (hv_tk n R') && hv_permOk (hv_tk n R') s.S) = true
      · rw [if_pos hc] at hb
        have hi' : stv_Inv rows n
            {s with R := R'.drop n, I := List.replicate k true, S := hv_orV (hv_tk n R') s.S} := by
          obtain ⟨⟩ := hi; constructor <;> simp_all [hv_length_tk, hv_length_orV]
        have ih' := ih _ hi' rfl
        simp only at ih'
        simp only [hc, Bool.true_and]
        refine (ExecLe.loop_norm (hpop _ _ hb) ih').cast rfl ?_
        simp only [Nat.succ_mul]; omega
      · rw [if_neg hc] at hb
        simp only [Bool.eq_false_iff.mpr hc, Bool.false_and]
        refine (ExecLe.loop_halt (hpop _ _ hb)).cast rfl ?_
        simp only [Nat.succ_mul]; omega

/-! ## After the parsing -/

def stv_root : Cmd :=
  .seq hv_takeN (.seq (hv_mvo 7 6) (.seq hv_permC (.seq (drain 6) stv_mainL)))

def stv_rest : Cmd := .pop 0 stv_fin stv_fin stv_root

theorem stv_ex_rest (rows : List (List SatSym)) (n : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) (c : ℕ)
    (s : hv_HS) (hi : stv_Inv rows n s) (hI : s.I = List.replicate c true)
    (hS : s.S = List.replicate n false) :
    ExecLe stv_rest s.st (.halt (stv_restF rows n s.P c s.R))
      ((c + 1) * (stv_Tb n s.M.length (hv_Tsc n rows) + 2) + 31 * n + 30) := by
  rcases hR : s.R with _ | ⟨_ | _, y⟩
  · exact (ExecLe.pop_nil (by simpa using hR) (stv_ex_fin s)).cast
      (by simp [stv_restF, hS]) (by rw [hi.hS]; nlinarith)
  · exact (ExecLe.pop_cons (b := false) (s := y) (by simpa using hR)
      (by simpa using stv_ex_fin {s with R := y})).cast
      (by simp [stv_restF, hS]) (by rw [hi.hS]; nlinarith)
  · have h1 := hv_ex_takeN n {s with R := y} hi.hN hi.hK hi.hT hi.hY
    simp only at h1
    have h2 := hv_ex_mvo (a := 7) (b := 6) (by decide) (by decide) (by decide)
      {s with R := y.drop n, Y := hv_tk n y}.st (by simpa using hi.hT)
    have eX : hv_tk n y ++ s.X = hv_tk n y := by rw [hi.hX, List.append_nil]
    simp only [hv_u6, hv_st6, hv_u7, hv_st7, eX] at h2
    have h3 := hv_ex_permC {s with R := y.drop n, Y := [], X := hv_tk n y} hi.hXC hi.hF
      hi.hT (by simp [hi.hS, hv_length_tk])
    simp only at h3
    have h4 := hv_ex_drain 6
      {s with R := y.drop n, Y := [], X := hv_tk n y, S := hv_orV (hv_tk n y) s.S}.st
    simp only [hv_u6, hv_st6] at h4
    have hi' : stv_Inv rows n
        {s with R := y.drop n, X := [], Y := [], S := hv_orV (hv_tk n y) s.S} := by
      obtain ⟨⟩ := hi; constructor <;> simp_all [hv_length_tk, hv_length_orV]
    have h5 := stv_ex_mainL rows n hsep c _ hi' hI
    simp only at h5
    have hpre : ∀ (r : Res) (T : ℕ), ExecLe stv_root {s with R := y}.st r T →
        ExecLe stv_rest s.st r (T + 1) := fun r T h =>
      ExecLe.pop_cons (b := true) (s := y) (by simpa using hR) (by simpa using h)
    simp only [stv_restF]
    rw [← hS]
    by_cases hp : hv_permOk (hv_tk n y) s.S = true
    · rw [if_pos hp] at h3
      simp only [hp, Bool.true_and]
      have hY := hi.hY
      have hX := hi.hX
      refine (hpre _ _ (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm h5))))).cast rfl ?_
      simp only [hv_length_tk]; omega
    · rw [if_neg hp] at h3
      simp only [Bool.eq_false_iff.mpr hp, Bool.false_and]
      exact (hpre _ _ (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3)))).cast rfl
        (by simp only [hv_length_tk]; nlinarith)

/-! ## The whole verifier -/

def stv_pre : Cmd :=
  .seq stv_bdL (.seq stv_trL (.seq (move 10 2) (.seq (copyVia 1 3 10) (.seq hv_cntL hv_initS))))

def stv_ver : Cmd := .seq phaseA (.seq (trimC 2) (.seq (move 2 1) (.seq stv_pre stv_rest)))

/-- Time bound of the verifier after parsing (`L ≥ |trunc w|`). -/
def stv_Trun (L : ℕ) : ℕ := (L + 1) * (14 * (L * L) + 174 * L + 108) + 60 * L + 60

/-- The states of the parsing phase. -/
abbrev stv_s (y M P Q N I S T : Str) : hv_HS :=
  ⟨y, M, P, Q, N, I, [], [], [], S, T, [], [], [], [], [], [], [], []⟩

theorem stv_ex_run (w : List SatSym) (y : Str) :
    ExecLe (.seq stv_pre stv_rest) (hv_s0 y (enc (clauses w))).st (.halt (stv_vres w y))
      (stv_Trun (trunc w).length) := by
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hsep := sep_not_mem_clauses w
  unfold stv_vres
  rcases hc : clauses w with _ | ⟨kr, _ | ⟨tr, rows⟩⟩
  · exact (ExecLe.seq_halt (ExecLe.seq_halt (stv_ex_bdL_nil _ (by simp [enc])))).cast rfl
      (by unfold stv_Trun; omega)
  · rw [hc] at hsep
    have h1 : ExecLe stv_bdL (hv_s0 y (enc [kr])).st
        (.norm (stv_s y [] [] [] [] (List.replicate kr.length true) [] []).st) (3 * kr.length + 3) :=
      (stv_ex_bdL [] kr (hv_s0 y (enc [kr])) (hsep kr (by simp))
        (by simp [enc, ic])).cast (by simp) le_rfl
    have h2 := stv_ex_trL_nil (stv_s y [] [] [] [] (List.replicate kr.length true) [] []) rfl
    rw [hc] at hsum
    simp at hsum
    exact (ExecLe.seq_halt (h1.seq_norm (ExecLe.seq_halt h2))).cast rfl
      (by unfold stv_Trun; nlinarith)
  · rw [hc] at hsep hsum
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hsr : ∀ r ∈ rows, sep ∉ r := fun r hr => hsep r (by simp [hr])
    have hlen : (enc rows).length = 2 * ((rows.map List.length).sum + rows.length) := by
      simp only [enc, length_flatMap_ic]; rw [sum_length_le]
    set n := rows.length with hn
    set a := kr.length with ha
    set E := enc rows with hE
    set Ptr := tr.map isPos with hPtr
    have h1 : ExecLe stv_bdL (hv_s0 y (enc (kr :: tr :: rows))).st
        (.norm (stv_s y (tr.flatMap ic ++ false :: false :: E) [] [] []
          (List.replicate a true) [] []).st) (3 * a + 3) :=
      (stv_ex_bdL (tr.flatMap ic ++ false :: false :: E) kr _ (hsep kr (by simp))
        (by simp [enc_cons, E])).cast (by (simp; rfl)) le_rfl
    have h2 : ExecLe stv_trL
        (stv_s y (tr.flatMap ic ++ false :: false :: E) [] [] [] (List.replicate a true) [] []).st
        (.norm (stv_s y E [] [] [] (List.replicate a true) [] Ptr.reverse).st) (3 * tr.length + 3) :=
      (stv_ex_trL E tr _ (hsep tr (by simp)) rfl).cast (by simp [Ptr]) le_rfl
    have h3 : ExecLe (move 10 2)
        (stv_s y E [] [] [] (List.replicate a true) [] Ptr.reverse).st
        (.norm (stv_s y E Ptr [] [] (List.replicate a true) [] []).st) (2 * tr.length + 2) :=
      (ExecLe.of (exec_move (a := 10) (b := 2) (by decide) _ _ rfl)).cast
        (by simp) (by simp [Ptr])
    have h4 : ExecLe (copyVia 1 3 10)
        (stv_s y E Ptr [] [] (List.replicate a true) [] []).st
        (.norm (stv_s y E Ptr E [] (List.replicate a true) [] []).st) (5 * E.length + 4) :=
      (hv_ex_copy (a := 1) (b := 3) (by decide) (by decide) (by decide) _ rfl).cast
        (by simp) le_rfl
    have h5 : ExecLe hv_cntL
        (stv_s y E Ptr E [] (List.replicate a true) [] []).st
        (.norm (stv_s y E Ptr [] (List.replicate n true) (List.replicate a true) [] []).st)
        (3 * (rows.flatMap (· ++ [sep])).length + 2) :=
      (hv_ex_cntL (rows.flatMap (· ++ [sep])) _ (by simp [E, enc])).cast
        (by rw [hv_count_sep rows hsr]; (simp; rfl)) le_rfl
    have h6 : ExecLe hv_initS
        (stv_s y E Ptr [] (List.replicate n true) (List.replicate a true) [] []).st
        (.norm (stv_s y E Ptr [] (List.replicate n true) (List.replicate a true)
          (List.replicate n false) []).st) (7 * n + 6) :=
      (hv_ex_initS n _ rfl rfl rfl).cast (by simp) le_rfl
    have hi : stv_Inv rows n
        (stv_s y E Ptr [] (List.replicate n true) (List.replicate a true)
          (List.replicate n false) []) := by
      constructor <;> simp [E]
    have h7 := stv_ex_rest rows n hsr a _ hi rfl rfl
    simp only [hlen, hv_Tsc_eq] at h7
    have hP : ExecLe stv_pre _ _ _ :=
      h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm h6))))
    refine (hP.seq_norm h7).cast rfl ?_
    have hrl : (rows.flatMap (· ++ [sep])).length = (rows.map List.length).sum + n :=
      (sum_length_le rows).symm
    rw [hrl, hlen, show rows.length = n from rfl]
    have hL : a + tr.length + (rows.map List.length).sum + n + 2 = (trunc w).length := by omega
    have hX : stv_Tb n (2 * ((rows.map List.length).sum + n))
        (10 * (rows.map List.length).sum + n * (7 * n + 20) + 2 * n + 8) + 2 ≤
        14 * ((trunc w).length * (trunc w).length) + 174 * (trunc w).length + 108 := by
      unfold stv_Tb
      have : n * (7 * n + 20) ≤ (trunc w).length * (7 * (trunc w).length + 20) :=
        Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    have hY := Nat.mul_le_mul (show a + 1 ≤ (trunc w).length + 1 by omega) hX
    unfold stv_Trun
    generalize (a + 1) * (stv_Tb n (2 * ((rows.map List.length).sum + n))
        (10 * (rows.map List.length).sum + n * (7 * n + 20) + 2 * n + 8) + 2) = X at hY ⊢
    generalize ((trunc w).length + 1) * (14 * ((trunc w).length * (trunc w).length) +
      174 * (trunc w).length + 108) = Y at hY ⊢
    omega

theorem stv_Trun_mono {a b : ℕ} (h : a ≤ b) : stv_Trun a ≤ stv_Trun b := by
  unfold stv_Trun
  have h1 : a * a ≤ b * b := Nat.mul_le_mul h h
  have h2 := Nat.mul_le_mul (show a + 1 ≤ b + 1 by omega)
    (show 14 * (a * a) + 174 * a + 108 ≤ 14 * (b * b) + 174 * b + 108 by omega)
  omega

theorem stv_bound (L : ℕ) : stv_Trun L + 7 * L + 12 ≤ hv_Tver L := by
  unfold stv_Trun hv_Tver
  nlinarith [Nat.zero_le L, Nat.zero_le (L * L), Nat.zero_le (L * L * L)]

theorem stv_exec_ver (z : Str) :
    ExecLe stv_ver (init [z]).stk (.halt (stv_vres (dec z).1 (dec z).2)) (hv_Tver z.length) := by
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
  have hR := stv_ex_run w y
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  refine (hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm hR))).cast rfl ?_
  rw [htl]
  have h1 := stv_Trun_mono (show (trunc w).length ≤ z.length by omega)
  have h2 := stv_bound z.length
  omega

end Pnp.Karp.Steiner
