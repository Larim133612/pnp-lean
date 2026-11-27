import Pnp.Karp.Ham
import Pnp.Karp.CliqueVer

/-!
# HAMILTONIAN CYCLE ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(`Pnp/Karp/Ham.lean`) and a certificate `y : List Bool`.  Let `n = |clauses w|`; the certificate
is read as `n` blocks of `n` bits, `B_i = hv_tk n (y.drop (i n))` (missing bits `false`), and
`B_i[u]` should say `σᵢ = u`.

Stacks (fields of `hv_HS`): `0` the unread certificate `R`; `1` the code `M` of the rows; `3` a
working copy `Q` of `M`; `4` the unary `n`; `5` the iteration counter; `6`, `7` the blocks `X`
(current) and `Y` (next); `8` a copy `Z` of `B_0`; `9` the "seen" vector `S`; `10` a temporary;
`11` a counter; `12` a copy of `X`; `13` a flag; `14` the "edge found" flag; `15` the row
flags; `16` the column template; `17` the current column bits; `18` the current row flag.

Program (`hv_ver`):
1. parse (`phaseA`, `trimC 2`, `move 2 1`); count the rows (`hv_cnt`); check `n ≥ 3`
   (`hv_chk3`); set the counter to `n - 1`, `S` to `n` times `false`; read `B_0` into `X`, `Z`;
2. `n - 1` times `hv_body`: read the next block `Y`; check that `X` has exactly one `true` bit,
   disjoint from `S`, and update `S` (`hv_permC`); check that some `pos` entry joins `X` and
   `Y` in one of the two directions (`hv_edgeC`, two row-major scans of the matrix); `X := Y`;
3. replace the certificate by `Z` and run `hv_body` once more (the wrap-around edge); accept.

`hv_exec_ver`: the program halts with `hv_vres (dec z).1 (dec z).2` within `hv_Tver |z|` steps.
-/

namespace Pnp.Karp.Ham

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Stack layout -/

/-- The stacks of the verifier. -/
structure hv_HS where
  R : Str
  M : Str
  P : Str
  Q : Str
  N : Str
  I : Str
  X : Str
  Y : Str
  Z : Str
  S : Str
  T : Str
  K : Str
  XC : Str
  F : Str
  H : Str
  RF : Str
  CT : Str
  CC : Str
  G : Str

/-- The stack assignment of a record. -/
def hv_HS.st (s : hv_HS) : ℕ → Str := fun j =>
  if j = 0 then s.R else if j = 1 then s.M else if j = 2 then s.P else if j = 3 then s.Q else
  if j = 4 then s.N else if j = 5 then s.I else if j = 6 then s.X else if j = 7 then s.Y else
  if j = 8 then s.Z else if j = 9 then s.S else if j = 10 then s.T else if j = 11 then s.K else
  if j = 12 then s.XC else if j = 13 then s.F else if j = 14 then s.H else
  if j = 15 then s.RF else if j = 16 then s.CT else if j = 17 then s.CC else
  if j = 18 then s.G else []

theorem hv_st_big (s : hv_HS) (j : ℕ) (h : 19 ≤ j) : s.st j = [] := by
  unfold hv_HS.st; repeat rw [if_neg (by omega)]

local macro "hvx" : tactic =>
  `(tactic| (funext j; by_cases h : j < 19
             · interval_cases j <;> rfl
             · rw [update_of_ne (by omega), hv_st_big _ _ (by omega), hv_st_big _ _ (by omega)]))

section St
variable (s : hv_HS) (v : Str)
@[simp] theorem hv_st0 : s.st 0 = s.R := rfl
@[simp] theorem hv_st1 : s.st 1 = s.M := rfl
@[simp] theorem hv_st2 : s.st 2 = s.P := rfl
@[simp] theorem hv_st3 : s.st 3 = s.Q := rfl
@[simp] theorem hv_st4 : s.st 4 = s.N := rfl
@[simp] theorem hv_st5 : s.st 5 = s.I := rfl
@[simp] theorem hv_st6 : s.st 6 = s.X := rfl
@[simp] theorem hv_st7 : s.st 7 = s.Y := rfl
@[simp] theorem hv_st8 : s.st 8 = s.Z := rfl
@[simp] theorem hv_st9 : s.st 9 = s.S := rfl
@[simp] theorem hv_st10 : s.st 10 = s.T := rfl
@[simp] theorem hv_st11 : s.st 11 = s.K := rfl
@[simp] theorem hv_st12 : s.st 12 = s.XC := rfl
@[simp] theorem hv_st13 : s.st 13 = s.F := rfl
@[simp] theorem hv_st14 : s.st 14 = s.H := rfl
@[simp] theorem hv_st15 : s.st 15 = s.RF := rfl
@[simp] theorem hv_st16 : s.st 16 = s.CT := rfl
@[simp] theorem hv_st17 : s.st 17 = s.CC := rfl
@[simp] theorem hv_st18 : s.st 18 = s.G := rfl
@[simp] theorem hv_u0 : update s.st 0 v = {s with R := v}.st := by hvx
@[simp] theorem hv_u1 : update s.st 1 v = {s with M := v}.st := by hvx
@[simp] theorem hv_u2 : update s.st 2 v = {s with P := v}.st := by hvx
@[simp] theorem hv_u3 : update s.st 3 v = {s with Q := v}.st := by hvx
@[simp] theorem hv_u4 : update s.st 4 v = {s with N := v}.st := by hvx
@[simp] theorem hv_u5 : update s.st 5 v = {s with I := v}.st := by hvx
@[simp] theorem hv_u6 : update s.st 6 v = {s with X := v}.st := by hvx
@[simp] theorem hv_u7 : update s.st 7 v = {s with Y := v}.st := by hvx
@[simp] theorem hv_u8 : update s.st 8 v = {s with Z := v}.st := by hvx
@[simp] theorem hv_u9 : update s.st 9 v = {s with S := v}.st := by hvx
@[simp] theorem hv_u10 : update s.st 10 v = {s with T := v}.st := by hvx
@[simp] theorem hv_u11 : update s.st 11 v = {s with K := v}.st := by hvx
@[simp] theorem hv_u12 : update s.st 12 v = {s with XC := v}.st := by hvx
@[simp] theorem hv_u13 : update s.st 13 v = {s with F := v}.st := by hvx
@[simp] theorem hv_u14 : update s.st 14 v = {s with H := v}.st := by hvx
@[simp] theorem hv_u15 : update s.st 15 v = {s with RF := v}.st := by hvx
@[simp] theorem hv_u16 : update s.st 16 v = {s with CT := v}.st := by hvx
@[simp] theorem hv_u17 : update s.st 17 v = {s with CC := v}.st := by hvx
@[simp] theorem hv_u18 : update s.st 18 v = {s with G := v}.st := by hvx
end St

/-! ## Generic commands -/

theorem hv_pop3 {k : ℕ} {c : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ}
    (h : ExecLe c (update σ k (σ k).tail) r T) : ExecLe (.pop k c c c) σ r (T + 1) := by
  cases hk : σ k with
  | nil =>
    rw [hk, List.tail_nil, ← hk, update_eq_self] at h
    exact ExecLe.pop_nil hk h
  | cons b s =>
    rw [hk, List.tail_cons] at h
    exact ExecLe.pop_same hk h

/-- Move stack `a` onto `b` keeping the order (via the temporary `10`). -/
def hv_mvo (a b : ℕ) : Cmd := .seq (move a 10) (move 10 b)

theorem hv_ex_mvo {a b : ℕ} (ha : a ≠ 10) (hb : b ≠ 10) (hab : a ≠ b) (σ : ℕ → Str)
    (ht : σ 10 = []) :
    ExecLe (hv_mvo a b) σ (.norm (update (update σ a []) b (σ a ++ σ b)))
      (4 * (σ a).length + 4) := by
  have h1 := exec_move ha (σ a) σ rfl
  have h2 := exec_move (Ne.symm hb) ((σ a).reverse)
    (update (update σ a []) 10 ((σ a).reverse ++ σ 10)) (by simp [ht])
  refine (ExecLe.of (Exec.seq_norm h1 h2)).cast ?_ (by simp; omega)
  congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all

theorem hv_ex_copy {a b : ℕ} (hab : a ≠ b) (ha : a ≠ 10) (hb : b ≠ 10) (σ : ℕ → Str)
    (ht : σ 10 = []) :
    ExecLe (copyVia a b 10) σ (.norm (update σ b (σ a ++ σ b))) (5 * (σ a).length + 4) :=
  ExecLe.of (exec_copyVia hab ha hb σ ht)

theorem hv_ex_drain (k : ℕ) (σ : ℕ → Str) :
    ExecLe (drain k) σ (.norm (update σ k [])) (2 * (σ k).length + 2) :=
  ExecLe.of (exec_drain k _ σ rfl)

/-! ## Reading a block -/

/-- The first `k` bits of `L` (missing bits `false`). -/
def hv_tk : ℕ → Str → Str
  | 0, _ => []
  | k + 1, L => L.headD false :: hv_tk k L.tail

theorem hv_length_tk : ∀ (k : ℕ) (L : Str), (hv_tk k L).length = k
  | 0, _ => rfl
  | k + 1, L => by simp [hv_tk, hv_length_tk k]

def hv_tb : Cmd := .pop 0 (.push 10 false) (.push 10 false) (.push 10 true)
def hv_tkL : Cmd := .loop (.pop 11 .brk hv_tb hv_tb)

/-- Read `n` bits of the certificate into `Y`. -/
def hv_takeN : Cmd := .seq (copyVia 4 11 10) (.seq hv_tkL (move 10 7))

theorem hv_ex_tb (s : hv_HS) :
    ExecLe hv_tb s.st (.norm {s with R := s.R.tail, T := s.R.headD false :: s.T}.st) 2 := by
  rcases hR : s.R with _ | ⟨b, R'⟩
  · exact (ExecLe.pop_nil (by simp [hR]) (ExecLe.push 10 false _)).cast (by simp [hR]) le_rfl
  · refine (ExecLe.pop_cons (b := b) (s := R') (by simp [hR]) ?_).cast rfl le_rfl
    cases b
    · exact (ExecLe.push 10 false _).cast (by simp) le_rfl
    · exact (ExecLe.push 10 true _).cast (by simp) le_rfl

theorem hv_ex_tkL : ∀ (k : ℕ) (s : hv_HS), s.K = List.replicate k true →
    ExecLe hv_tkL s.st
      (.norm {s with K := [], R := s.R.drop k, T := (hv_tk k s.R).reverse ++ s.T}.st) (3 * k + 2)
  | 0, s, h => (ExecLe.loop_brk (ExecLe.pop_nil (by simp [h]) (ExecLe.brk _))).cast
      (by cases s; simp_all [hv_tk]) (by omega)
  | k + 1, s, h => by
    have hb := hv_ex_tb {s with K := List.replicate k true}
    have ih := hv_ex_tkL k
      {s with K := List.replicate k true, R := s.R.tail, T := s.R.headD false :: s.T} rfl
    refine (ExecLe.loop_norm (ExecLe.pop_cons (b := true) (s := List.replicate k true)
      (by simp [h, List.replicate_succ]) (by simpa using hb)) ih).cast ?_ (by omega)
    simp [hv_tk, List.drop_tail]

theorem hv_ex_takeN (n : ℕ) (s : hv_HS) (hN : s.N = List.replicate n true) (hK : s.K = [])
    (hT : s.T = []) (hY : s.Y = []) :
    ExecLe hv_takeN s.st (.norm {s with R := s.R.drop n, Y := hv_tk n s.R}.st) (10 * n + 8) := by
  have h1 := hv_ex_copy (a := 4) (b := 11) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st4, hv_st11, hv_u11] at h1
  have h2 := hv_ex_tkL n {s with K := s.N ++ s.K} (by simp [hN, hK])
  refine (h1.seq_norm (h2.seq_norm (ExecLe.of (exec_move (by decide) _ _ rfl)))).cast ?_ ?_
  · simp only [hv_u10, hv_u7, hv_st10, hv_st7]; congr 1; cases s; simp_all
  · simp [hT, hN, hv_length_tk]; omega

/-! ## Counting the rows, initialization -/

def hv_cntL : Cmd :=
  .loop (.pop 3 .brk (.pop 3 (.halt false) (.push 4 true) .skip) (.pop 3 (.halt false) .skip .skip))

theorem hv_ex_cntL : ∀ (l : List SatSym) (s : hv_HS), s.Q = l.flatMap ic →
    ExecLe hv_cntL s.st
      (.norm {s with Q := [], N := List.replicate (l.count sep) true ++ s.N}.st) (3 * l.length + 2)
  | [], s, h => (ExecLe.loop_brk (ExecLe.pop_nil (by simpa using h) (ExecLe.brk _))).cast
      (by cases s; simp_all) (by simp)
  | x :: l, s, h => by
    have ih := hv_ex_cntL l
    cases x with
    | sep =>
      have := ih {s with Q := l.flatMap ic, N := true :: s.N} rfl
      refine (ExecLe.loop_norm (ExecLe.pop_cons (b := false) (s := false :: l.flatMap ic)
        (by simp [h, ic]) (ExecLe.pop_cons (b := false) (s := l.flatMap ic) (by simp)
          ((ExecLe.push 4 true _).cast (by simp) le_rfl))) this).cast ?_ (by simp; omega)
      simp [List.replicate_succ']
    | zero =>
      have := ih {s with Q := l.flatMap ic} rfl
      refine (ExecLe.loop_norm (ExecLe.pop_cons (b := false) (s := true :: l.flatMap ic)
        (by simp [h, ic]) (ExecLe.pop_cons (b := true) (s := l.flatMap ic) (by simp)
          ((ExecLe.skip _).cast (by simp) le_rfl))) this).cast ?_ (by simp; omega)
      simp
    | pos =>
      have := ih {s with Q := l.flatMap ic} rfl
      refine (ExecLe.loop_norm (ExecLe.pop_cons (b := true) (s := false :: l.flatMap ic)
        (by simp [h, ic]) (ExecLe.pop_cons (b := false) (s := l.flatMap ic) (by simp)
          ((ExecLe.skip _).cast (by simp) le_rfl))) this).cast ?_ (by simp; omega)
      simp
    | neg =>
      have := ih {s with Q := l.flatMap ic} rfl
      refine (ExecLe.loop_norm (ExecLe.pop_cons (b := true) (s := true :: l.flatMap ic)
        (by simp [h, ic]) (ExecLe.pop_cons (b := true) (s := l.flatMap ic) (by simp)
          ((ExecLe.skip _).cast (by simp) le_rfl))) this).cast ?_ (by simp; omega)
      simp

def hv_p3 : Cmd := .pop 11 (.halt false) .skip .skip

/-- Halt `false` unless `n ≥ 3`. -/
def hv_chk3 : Cmd := .seq (copyVia 4 11 10) (.seq hv_p3 (.seq hv_p3 (.seq hv_p3 (drain 11))))

theorem hv_ex_p3_nil (s : hv_HS) (h : s.K = []) : ExecLe hv_p3 s.st (.halt false) 2 :=
  ExecLe.pop_nil (by simpa) (ExecLe.halt false _)

theorem hv_ex_p3_cons (s : hv_HS) (L : Str) (h : s.K = true :: L) :
    ExecLe hv_p3 s.st (.norm {s with K := L}.st) 2 :=
  ExecLe.pop_cons (b := true) (s := L) (by simpa) ((ExecLe.skip _).cast (by simp) le_rfl)

theorem hv_ex_chk3 (n : ℕ) (s : hv_HS) (hN : s.N = List.replicate n true) (hK : s.K = [])
    (hT : s.T = []) :
    ExecLe hv_chk3 s.st (if 3 ≤ n then .norm s.st else .halt false) (7 * n + 20) := by
  have h1 := hv_ex_copy (a := 4) (b := 11) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st4, hv_st11, hv_u11, hK, List.append_nil] at h1
  set s1 : hv_HS := {s with K := s.N} with hs1
  have hl : s.N.length = n := by simp [hN]
  rcases n with _ | _ | _ | n
  · exact (h1.seq_norm (ExecLe.seq_halt (hv_ex_p3_nil s1 (by simp [s1, hN])))).cast (by simp)
      (by omega)
  · exact (h1.seq_norm ((hv_ex_p3_cons s1 [] (by simp [s1, hN])).seq_norm
      (ExecLe.seq_halt (hv_ex_p3_nil {s1 with K := []} rfl)))).cast (by simp) (by omega)
  · exact (h1.seq_norm ((hv_ex_p3_cons s1 [true] (by simp [s1, hN])).seq_norm
      ((hv_ex_p3_cons {s1 with K := [true]} [] rfl).seq_norm
        (ExecLe.seq_halt (hv_ex_p3_nil {s1 with K := []} rfl))))).cast
      (by simp) (by omega)
  · have e : s1.K = true :: true :: true :: List.replicate n true := by
      simp [s1, hN, List.replicate_succ]
    refine (h1.seq_norm ((hv_ex_p3_cons s1 _ e).seq_norm
      ((hv_ex_p3_cons _ _ rfl).seq_norm ((hv_ex_p3_cons _ _ rfl).seq_norm
        (hv_ex_drain 11 _))))).cast ?_ (by simp; omega)
    simp only [hv_u11, if_pos (show 3 ≤ n + 1 + 1 + 1 by omega)]
    congr 1; cases s; simp_all

/-- The iteration counter `n - 1`. -/
def hv_initI : Cmd := .seq (copyVia 4 5 10) (.pop 5 .skip .skip .skip)

theorem hv_ex_initI (n : ℕ) (s : hv_HS) (hN : s.N = List.replicate n true) (hI : s.I = [])
    (hT : s.T = []) :
    ExecLe hv_initI s.st (.norm {s with I := List.replicate (n - 1) true}.st) (5 * n + 6) := by
  have h1 := hv_ex_copy (a := 4) (b := 5) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st4, hv_st5, hv_u5, hI, List.append_nil] at h1
  exact (h1.seq_norm (hv_pop3 (ExecLe.skip _))).cast (by simp [hN]) (by simp [hN])

def hv_fsL : Cmd := .loop (.pop 11 .brk (.push 9 false) (.push 9 false))

theorem hv_ex_fsL : ∀ (k : ℕ) (s : hv_HS), s.K = List.replicate k true →
    ExecLe hv_fsL s.st (.norm {s with K := [], S := List.replicate k false ++ s.S}.st)
      (2 * k + 2)
  | 0, s, h => (ExecLe.loop_brk (ExecLe.pop_nil (by simp [h]) (ExecLe.brk _))).cast
      (by cases s; simp_all) (by omega)
  | k + 1, s, h => by
    have ih := hv_ex_fsL k {s with K := List.replicate k true, S := false :: s.S} rfl
    refine (ExecLe.loop_norm (ExecLe.pop_cons (b := true) (s := List.replicate k true)
      (by simp [h, List.replicate_succ]) ((ExecLe.push 9 false _).cast (by simp) le_rfl)) ih).cast
      ?_ (by omega)
    simp [List.replicate_succ']

/-- The seen vector: `n` times `false`. -/
def hv_initS : Cmd := .seq (copyVia 4 11 10) hv_fsL

theorem hv_ex_initS (n : ℕ) (s : hv_HS) (hN : s.N = List.replicate n true) (hK : s.K = [])
    (hT : s.T = []) :
    ExecLe hv_initS s.st (.norm {s with S := List.replicate n false ++ s.S}.st) (7 * n + 6) := by
  have h1 := hv_ex_copy (a := 4) (b := 11) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st4, hv_st11, hv_u11, hK, List.append_nil] at h1
  refine (h1.seq_norm (hv_ex_fsL n _ (by simp [hN]))).cast ?_ (by simp [hN]; omega)
  congr 1; cases s; simp_all

/-! ## The permutation check of one block -/

def hv_zok : Str → Str → Bool → Bool
  | [], _, _ => true
  | false :: X, S, f => hv_zok X S.tail f
  | true :: X, S, f => !(S.headD false) && !f && hv_zok X S.tail true

def hv_orV : Str → Str → Str
  | [], _ => []
  | x :: X, S => (x || S.headD false) :: hv_orV X S.tail

def hv_anyT : Str → Bool
  | [] => false
  | x :: X => x || hv_anyT X

/-- `X` has exactly one `true` bit, and no `true` bit where `S` has one. -/
def hv_permOk (X S : Str) : Bool := hv_zok X S false && hv_anyT X

theorem hv_length_orV : ∀ (X S : Str), (hv_orV X S).length = X.length
  | [], _ => rfl
  | x :: X, S => by simp [hv_orV, hv_length_orV X]

def hv_of : Cmd := .pop 13 (.push 13 true) (.halt false) (.halt false)
def hv_zf : Cmd := .pop 9 (.push 10 false) (.push 10 false) (.push 10 true)
def hv_zt : Cmd := .pop 9 (.seq (.push 10 true) hv_of) (.seq (.push 10 true) hv_of) (.halt false)
def hv_zL : Cmd := .loop (.pop 12 .brk hv_zf hv_zt)

def hv_permC : Cmd :=
  .seq (copyVia 6 12 10) (.seq hv_zL (.seq (.pop 13 (.halt false) (.halt false) .skip) (move 10 9)))

theorem hv_ex_zf (s : hv_HS) :
    ExecLe hv_zf s.st (.norm {s with S := s.S.tail, T := s.S.headD false :: s.T}.st) 2 := by
  rcases hS : s.S with _ | ⟨b, S'⟩
  · exact (ExecLe.pop_nil (by simp [hS]) (ExecLe.push 10 false _)).cast (by simp [hS]) le_rfl
  · refine (ExecLe.pop_cons (b := b) (s := S') (by simp [hS]) ?_).cast rfl le_rfl
    cases b
    · exact (ExecLe.push 10 false _).cast (by simp) le_rfl
    · exact (ExecLe.push 10 true _).cast (by simp) le_rfl

theorem hv_ex_of (s : hv_HS) (f : Bool) (hF : s.F = CookLevin.fl f) :
    ExecLe hv_of s.st (if f then .halt false else .norm {s with F := CookLevin.fl true}.st) 2 := by
  cases f
  · exact (ExecLe.pop_nil (by simp [hF, CookLevin.fl]) (ExecLe.push 13 true _)).cast (by simp [hF, CookLevin.fl])
      le_rfl
  · exact (ExecLe.pop_cons (b := true) (s := []) (by simp [hF, CookLevin.fl]) (ExecLe.halt false _)).cast
      (by simp) le_rfl

theorem hv_ex_zt (s : hv_HS) (f : Bool) (hF : s.F = CookLevin.fl f) :
    ExecLe hv_zt s.st (if !(s.S.headD false) && !f then
      .norm {s with S := s.S.tail, T := true :: s.T, F := CookLevin.fl true}.st else .halt false) 4 := by
  rcases hS : s.S with _ | ⟨b, S'⟩
  · have := hv_ex_of {s with T := true :: s.T} f hF
    refine (ExecLe.pop_nil (by simp [hS])
      (((ExecLe.push 10 true _).cast (by simp) le_rfl).seq_norm this)).cast ?_ le_rfl
    cases f <;> simp [hS]
  · cases b
    · have := hv_ex_of {s with S := S', T := true :: s.T} f hF
      refine (ExecLe.pop_cons (b := false) (s := S') (by simp [hS])
        (((ExecLe.push 10 true _).cast (by simp) le_rfl).seq_norm this)).cast ?_ le_rfl
      cases f <;> simp
    · exact (ExecLe.pop_cons (b := true) (s := S') (by simp [hS]) (ExecLe.halt false _)).cast
        (by simp) (by omega)

theorem hv_ex_zL : ∀ (X : Str) (s : hv_HS) (f : Bool), s.XC = X → s.F = CookLevin.fl f →
    ExecLe hv_zL s.st (if hv_zok X s.S f then
      .norm {s with XC := [], S := s.S.drop X.length,
                    F := CookLevin.fl (f || hv_anyT X), T := (hv_orV X s.S).reverse ++ s.T}.st
      else .halt false) (5 * X.length + 2)
  | [], s, f, hX, hF => (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hX]) (ExecLe.brk _))).cast
      (by simp only [hv_zok, if_true]; congr 1; cases s; simp_all [hv_anyT, hv_orV]) (by simp)
  | false :: X, s, f, hX, hF => by
    have hb := hv_ex_zf {s with XC := X}
    have ih := hv_ex_zL X {s with XC := X, S := s.S.tail, T := s.S.headD false :: s.T} f rfl hF
    refine (ExecLe.loop_norm (ExecLe.pop_cons (b := false) (s := X) (by simp [hX])
      (by simpa using hb)) ih).cast ?_ (by simp; omega)
    simp only [hv_zok]
    split_ifs
    · simp [hv_anyT, hv_orV, List.drop_tail]
    · rfl
  | true :: X, s, f, hX, hF => by
    have hb := hv_ex_zt {s with XC := X} f hF
    simp only at hb
    by_cases hc : (!(s.S.headD false) && !f) = true
    · rw [if_pos hc] at hb
      have e : hv_zok (true :: X) s.S f = hv_zok X s.S.tail true := by
        simp only [hv_zok, hc, Bool.true_and]
      rw [e]
      have ih := hv_ex_zL X
        {s with XC := X, S := s.S.tail, T := true :: s.T, F := CookLevin.fl true} true rfl rfl
      refine (ExecLe.loop_norm (ExecLe.pop_cons (b := true) (s := X) (by simp [hX])
        (by simpa using hb)) ih).cast ?_ (by simp; omega)
      split_ifs
      · simp [hv_anyT, hv_orV, List.drop_tail]
      · rfl
    · rw [if_neg hc] at hb
      have e : hv_zok (true :: X) s.S f = false := by
        simp only [hv_zok, Bool.eq_false_iff.mpr hc, Bool.false_and]
      rw [e]
      exact (ExecLe.loop_halt (ExecLe.pop_cons (b := true) (s := X) (by simp [hX])
        (by simpa using hb))).cast (by simp) (by simp; omega)

theorem hv_ex_permC (s : hv_HS) (hXC : s.XC = []) (hF : s.F = []) (hT : s.T = [])
    (hS : s.S.length ≤ s.X.length) :
    ExecLe hv_permC s.st (if hv_permOk s.X s.S then .norm {s with S := hv_orV s.X s.S}.st
      else .halt false) (12 * s.X.length + 10) := by
  have h1 := hv_ex_copy (a := 6) (b := 12) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st6, hv_st12, hv_u12, hXC, List.append_nil] at h1
  have h2 := hv_ex_zL s.X {s with XC := s.X} false rfl (by simp [hF, CookLevin.fl])
  simp only at h2
  cases hz : hv_zok s.X s.S false
  · simp only [hz] at h2
    simp only [hv_permOk, hz, Bool.false_and]
    exact (h1.seq_norm (ExecLe.seq_halt h2)).cast (by simp) (by omega)
  · simp only [hz, if_true, Bool.false_or] at h2
    cases ha : hv_anyT s.X
    · simp only [ha] at h2
      simp only [hv_permOk, hz, ha, Bool.and_false]
      exact (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt (ExecLe.pop_nil (by simp [CookLevin.fl])
        (ExecLe.halt false _))))).cast (by simp) (by omega)
    · simp only [ha] at h2
      simp only [hv_permOk, hz, ha, Bool.and_true, if_true]
      refine (h1.seq_norm (h2.seq_norm ((ExecLe.pop_cons (b := true) (s := [])
        (by simp [CookLevin.fl]) (ExecLe.skip _)).seq_norm
        (ExecLe.of (exec_move (by decide) _ _ rfl))))).cast ?_ ?_
      · congr 1; cases s; simp_all [List.drop_eq_nil_of_le]
      · simp [hT, hv_length_orV]; omega

/-! ## The edge check: row-major scans of the matrix -/

/-- Some `pos` symbol of the row `r` sits at a column with a `true` bit of `C`. -/
def hv_anyHit : List SatSym → Str → Bool
  | [], _ => false
  | x :: r, C => (isPos x && C.headD false) || hv_anyHit r C.tail

/-- Some row with a `true` flag in `RF` has a hit with the column bits `C`. -/
def hv_goS (C : Str) : List (List SatSym) → Str → Bool
  | [], _ => false
  | r :: rows, RF => (RF.headD false && hv_anyHit r C) || hv_goS C rows RF.tail

theorem hv_goS_cons_headD (C : Str) (rows : List (List SatSym)) (L : Str) :
    hv_goS C rows (L.headD false :: L.tail) = hv_goS C rows L := by
  cases rows <;> simp [hv_goS]

def hv_setH : Cmd := .seq (.pop 14 .skip .skip .skip) (.push 14 true)
def hv_hitS : Cmd := .pop 18 .skip .skip (.seq (.push 18 true) hv_setH)
def hv_colS (ok : Bool) : Cmd := .pop 17 .skip .skip (if ok then hv_hitS else .skip)
def hv_endS : Cmd := .seq (drain 17) (drain 18)
def hv_srS : Cmd := .seq (copyVia 16 17 10) (.pop 15 .skip .skip (.push 18 true))

def hv_scB : Cmd :=
  .pop 3 (.seq hv_endS .brk) (.pop 3 (.halt false) (.seq hv_endS hv_srS) (hv_colS false))
    (.pop 3 (.halt false) (hv_colS true) (hv_colS false))

def hv_scL : Cmd := .loop hv_scB

/-- One scan: row flags `RF`, column template `CT`; sets the flag `H` on a hit. -/
def hv_scanCore : Cmd :=
  .seq (copyVia 1 3 10) (.seq hv_srS (.seq hv_scL (.seq (drain 15) (drain 16))))

def hv_scanP (a b : ℕ) : Cmd := .seq (copyVia a 15 10) (.seq (copyVia b 16 10) hv_scanCore)

def hv_edgeC : Cmd :=
  .seq (hv_scanP 6 7) (.seq (hv_scanP 7 6) (.pop 14 (.halt false) (.halt false) .skip))

theorem hv_ex_setH (s : hv_HS) (h : Bool) (hH : s.H = CookLevin.fl h) :
    ExecLe hv_setH s.st (.norm {s with H := CookLevin.fl true}.st) 3 := by
  exact ((hv_pop3 (ExecLe.skip _)).seq_norm (ExecLe.push 14 true _)).cast
    (by cases h <;> simp [hH, CookLevin.fl]) le_rfl

theorem hv_ex_hitS (s : hv_HS) (g h : Bool) (hG : s.G = CookLevin.fl g)
    (hH : s.H = CookLevin.fl h) :
    ExecLe hv_hitS s.st (.norm {s with H := CookLevin.fl (h || g)}.st) 5 := by
  cases g
  · exact (ExecLe.pop_nil (by simp [hG, CookLevin.fl]) (ExecLe.skip _)).cast
      (by simp only [Bool.or_false, ← hH]) (by omega)
  · have hs := hv_ex_setH {s with G := [true]} h hH
    refine (ExecLe.pop_cons (b := true) (s := []) (by simp [hG, CookLevin.fl])
      (((ExecLe.push 18 true _).cast (by simp) le_rfl).seq_norm hs)).cast ?_ (by omega)
    simp only [Bool.or_true]; congr 1; cases s; simp_all [CookLevin.fl]

theorem hv_ex_colS (ok : Bool) (s : hv_HS) (g h : Bool) (hG : s.G = CookLevin.fl g)
    (hH : s.H = CookLevin.fl h) :
    ExecLe (hv_colS ok) s.st
      (.norm {s with CC := s.CC.tail, H := CookLevin.fl (h || (ok && s.CC.headD false && g))}.st)
      6 := by
  rcases hC : s.CC with _ | ⟨_ | _, C'⟩
  · exact (ExecLe.pop_nil (by simp [hC]) (ExecLe.skip _)).cast
      (by congr 1; cases s; simp_all) (by omega)
  · exact (ExecLe.pop_cons (b := false) (s := C') (by simp [hC]) (ExecLe.skip _)).cast
      (by simp [← hH]) (by omega)
  · cases ok
    · exact (ExecLe.pop_cons (b := true) (s := C') (by simp [hC]) (ExecLe.skip _)).cast
        (by simp [← hH]) (by omega)
    · exact (ExecLe.pop_cons (b := true) (s := C') (by simp [hC])
        (by simpa using hv_ex_hitS {s with CC := C'} g h hG hH)).cast (by simp) (by omega)

theorem hv_ex_endS (s : hv_HS) :
    ExecLe hv_endS s.st (.norm {s with CC := [], G := []}.st)
      (2 * s.CC.length + 2 * s.G.length + 4) :=
  ((hv_ex_drain 17 _).seq_norm (hv_ex_drain 18 _)).cast (by simp) (by simp; omega)

theorem hv_ex_srS (s : hv_HS) (hT : s.T = []) (hC : s.CC = []) (hG : s.G = []) :
    ExecLe hv_srS s.st
      (.norm {s with CC := s.CT, G := CookLevin.fl (s.RF.headD false), RF := s.RF.tail}.st)
      (5 * s.CT.length + 6) := by
  have h1 := hv_ex_copy (a := 16) (b := 17) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st16, hv_st17, hv_u17, hC, List.append_nil] at h1
  rcases hR : s.RF with _ | ⟨_ | _, R'⟩
  · exact (h1.seq_norm (ExecLe.pop_nil (by simp [hR]) (ExecLe.skip _))).cast
      (by congr 1; cases s; simp_all [CookLevin.fl]) (by omega)
  · exact (h1.seq_norm (ExecLe.pop_cons (b := false) (s := R') (by simp [hR])
      ((ExecLe.skip _).cast rfl le_rfl))).cast
      (by congr 1; cases s; simp_all [CookLevin.fl]) (by omega)
  · exact (h1.seq_norm (ExecLe.pop_cons (b := true) (s := R') (by simp [hR])
      ((ExecLe.push 18 true _).cast rfl le_rfl))).cast
      (by simp [hG, CookLevin.fl]) (by omega)

theorem hv_bool_row (a b c d e : Bool) :
    (a || (b && ((c && d) || e))) = ((a || (c && d && b)) || (b && e)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

theorem hv_ex_row (C : Str) (Nb : ℕ) (hC : C.length ≤ Nb) (Q' : Str) :
    ∀ (r : List SatSym) (s : hv_HS) (g h h' : Bool), sep ∉ r →
    s.Q = r.flatMap ic ++ false :: false :: Q' → s.CT = C → s.G = CookLevin.fl g →
    s.H = CookLevin.fl h → s.T = [] → s.CC.length ≤ Nb → h' = (h || (g && hv_anyHit r s.CC)) →
    ∀ (res : Res) (T' : ℕ), ExecLe hv_scL
      {s with Q := Q', CC := C, G := CookLevin.fl (s.RF.headD false), RF := s.RF.tail,
              H := CookLevin.fl h'}.st res T' →
    ExecLe hv_scL s.st res (T' + (10 * r.length + 7 * Nb + 20))
  | [], s, g, h, h', _, hQ, hCT, hG, hH, hT, hCC, hh, res, T', hk => by
    have he := hv_ex_endS {s with Q := Q'}
    have hs := hv_ex_srS {s with Q := Q', CC := [], G := []} hT rfl rfl
    have hGl : s.G.length ≤ 1 := by rw [hG]; cases g <;> simp [CookLevin.fl]
    have hb : ExecLe hv_scB s.st
        (.norm {s with Q := Q', CC := C, G := CookLevin.fl (s.RF.headD false), RF := s.RF.tail, H := CookLevin.fl h'}.st)
        (7 * Nb + 16) := by
      refine ExecLe.pop_cons (b := false) (s := false :: Q') (by simp [hQ]) ?_
      refine ExecLe.pop_cons (b := false) (s := Q') (by simp) ?_
      simp only [hv_u3, Bool.false_eq_true, if_false]
      refine (he.seq_norm hs).cast ?_ (by simp [hCT]; omega)
      simp only [hv_anyHit, Bool.and_false, Bool.or_false] at hh
      congr 1; cases s; simp_all
    exact (ExecLe.loop_norm hb hk).cast rfl (by simp; omega)
  | x :: r, s, g, h, h', hr, hQ, hCT, hG, hH, hT, hCC, hh, res, T', hk => by
    have hx : x ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    set Q1 := r.flatMap ic ++ false :: false :: Q'
    have hc := hv_ex_colS (isPos x) {s with Q := Q1} g h hG hH
    simp only at hc
    have hb : ExecLe hv_scB s.st
        (.norm {s with Q := Q1, CC := s.CC.tail, H := CookLevin.fl (h || (isPos x && s.CC.headD false && g))}.st) 8 := by
      unfold hv_scB
      cases x with
      | sep => exact absurd rfl hx
      | zero =>
        exact ExecLe.pop_cons (σ := s.st) (k := 3) (b := false) (s := true :: Q1) (by simp [hQ, ic, Q1])
          (ExecLe.pop_cons (b := true) (s := Q1) (by simp) (by simpa [isPos] using hc))
      | pos =>
        exact ExecLe.pop_cons (σ := s.st) (k := 3) (b := true) (s := false :: Q1) (by simp [hQ, ic, Q1])
          (ExecLe.pop_cons (b := false) (s := Q1) (by simp) (by simpa [isPos] using hc))
      | neg =>
        exact ExecLe.pop_cons (σ := s.st) (k := 3) (b := true) (s := true :: Q1) (by simp [hQ, ic, Q1])
          (ExecLe.pop_cons (b := true) (s := Q1) (by simp) (by simpa [isPos] using hc))
    have ih := hv_ex_row C Nb hC Q' r
      {s with Q := Q1, CC := s.CC.tail, H := CookLevin.fl (h || (isPos x && s.CC.headD false && g))} g
      (h || (isPos x && s.CC.headD false && g)) h' hr' rfl hCT hG rfl hT (by simp; omega)
      (by rw [hh]; simp only [hv_anyHit]; exact hv_bool_row _ _ _ _ _) res T' hk
    exact (ExecLe.loop_norm hb ih).cast rfl (by simp; omega)

/-- Cost of the scan loop. -/
def hv_Tsc (Nb : ℕ) : List (List SatSym) → ℕ
  | [] => 2 * Nb + 8
  | r :: rows => 10 * r.length + 7 * Nb + 20 + hv_Tsc Nb rows

theorem hv_Tsc_eq (Nb : ℕ) : ∀ rows : List (List SatSym),
    hv_Tsc Nb rows = 10 * (rows.map List.length).sum + rows.length * (7 * Nb + 20) + 2 * Nb + 8
  | [] => by simp [hv_Tsc]
  | r :: rows => by simp only [hv_Tsc, hv_Tsc_eq Nb rows, List.map_cons, List.sum_cons,
      List.length_cons]; ring

theorem hv_ex_rows (C : Str) (Nb : ℕ) (hC : C.length ≤ Nb) :
    ∀ (rows : List (List SatSym)) (s : hv_HS) (g h : Bool), (∀ r ∈ rows, sep ∉ r) →
    s.Q = enc rows → s.CT = C → s.CC = C → s.G = CookLevin.fl g → s.H = CookLevin.fl h →
    s.T = [] →
    ExecLe hv_scL s.st
      (.norm {s with Q := [], CC := [], G := [], RF := s.RF.drop rows.length, H := CookLevin.fl (h || hv_goS C rows (g :: s.RF))}.st)
      (hv_Tsc Nb rows)
  | [], s, g, h, _, hQ, hCT, hCC, hG, hH, hT => by
    have he := hv_ex_endS s
    have hGl : s.G.length ≤ 1 := by rw [hG]; cases g <;> simp [CookLevin.fl]
    refine (ExecLe.loop_brk (ExecLe.pop_nil (by simpa [enc] using hQ)
      (he.seq_norm (ExecLe.brk _)))).cast ?_ (by simp [hv_Tsc, hCC]; omega)
    simp only [hv_goS, Bool.or_false]
    congr 1; cases s; simp_all [enc]
  | r :: rows, s, g, h, hrows, hQ, hCT, hCC, hG, hH, hT => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    rw [enc_cons] at hQ
    have ih := (hv_ex_rows C Nb hC rows
        {s with Q := enc rows, CC := C, G := CookLevin.fl (s.RF.headD false), RF := s.RF.tail, H := CookLevin.fl (h || (g && hv_anyHit r C))}
        (s.RF.headD false) (h || (g && hv_anyHit r C)) hrs rfl hCT rfl rfl rfl hT).cast
      (r' := .norm {s with Q := [], CC := [], G := [], RF := s.RF.drop (r :: rows).length, H := CookLevin.fl (h || hv_goS C (r :: rows) (g :: s.RF))}.st)
      (by simp only [hv_goS_cons_headD]; simp [hv_goS, List.drop_tail, Bool.or_assoc]) le_rfl
    exact (hv_ex_row C Nb hC (enc rows) r s g h _ hr hQ hCT hG hH hT (by rw [hCC]; exact hC)
      (by rw [hCC]) _ _ ih).cast rfl (by simp [hv_Tsc]; omega)

theorem hv_ex_scanCore (rows : List (List SatSym)) (Nb : ℕ) (s : hv_HS) (h : Bool)
    (hsep : ∀ r ∈ rows, sep ∉ r) (hM : s.M = enc rows) (hQ : s.Q = []) (hCC : s.CC = [])
    (hG : s.G = []) (hT : s.T = []) (hH : s.H = CookLevin.fl h) (hCT : s.CT.length ≤ Nb) :
    ExecLe hv_scanCore s.st
      (.norm {s with RF := [], CT := [], H := CookLevin.fl (h || hv_goS s.CT rows s.RF)}.st)
      (5 * s.M.length + 9 * Nb + 2 * s.RF.length + hv_Tsc Nb rows + 16) := by
  have h1 := hv_ex_copy (a := 1) (b := 3) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st1, hv_st3, hv_u3, hQ, List.append_nil] at h1
  have h2 := hv_ex_srS {s with Q := s.M} hT hCC hG
  simp only at h2
  have h3 := hv_ex_rows s.CT Nb hCT rows
    {s with Q := s.M, CC := s.CT, G := CookLevin.fl (s.RF.headD false), RF := s.RF.tail}
    (s.RF.headD false) h hsep hM rfl rfl rfl hH hT
  simp only [hv_goS_cons_headD] at h3
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm ((hv_ex_drain 15 _).seq_norm
    (hv_ex_drain 16 _))))).cast ?_ ?_
  · congr 1; cases s; simp_all
  · simp; omega

theorem hv_ex_scan67 (rows : List (List SatSym)) (Nb : ℕ) (s : hv_HS) (h : Bool)
    (hsep : ∀ r ∈ rows, sep ∉ r) (hM : s.M = enc rows) (hQ : s.Q = []) (hCC : s.CC = [])
    (hG : s.G = []) (hT : s.T = []) (hH : s.H = CookLevin.fl h) (hRF : s.RF = [])
    (hCT : s.CT = []) (hX : s.X.length ≤ Nb) (hY : s.Y.length ≤ Nb) :
    ExecLe (hv_scanP 6 7) s.st
      (.norm {s with H := CookLevin.fl (h || hv_goS s.Y rows s.X)}.st)
      (5 * s.M.length + 26 * Nb + hv_Tsc Nb rows + 24) := by
  have h1 := hv_ex_copy (a := 6) (b := 15) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st6, hv_st15, hv_u15, hRF, List.append_nil] at h1
  have h2 := hv_ex_copy (a := 7) (b := 16) (by decide) (by decide) (by decide)
    {s with RF := s.X}.st (by simpa)
  simp only [hv_st7, hv_st16, hv_u16] at h2
  have h3 := hv_ex_scanCore rows Nb {s with RF := s.X, CT := s.Y ++ s.CT} h hsep hM hQ hCC hG hT
    hH (by simp [hCT]; omega)
  simp only at h3
  refine (h1.seq_norm (h2.seq_norm h3)).cast ?_ (by omega)
  congr 1; cases s; simp_all

theorem hv_ex_scan76 (rows : List (List SatSym)) (Nb : ℕ) (s : hv_HS) (h : Bool)
    (hsep : ∀ r ∈ rows, sep ∉ r) (hM : s.M = enc rows) (hQ : s.Q = []) (hCC : s.CC = [])
    (hG : s.G = []) (hT : s.T = []) (hH : s.H = CookLevin.fl h) (hRF : s.RF = [])
    (hCT : s.CT = []) (hX : s.X.length ≤ Nb) (hY : s.Y.length ≤ Nb) :
    ExecLe (hv_scanP 7 6) s.st
      (.norm {s with H := CookLevin.fl (h || hv_goS s.X rows s.Y)}.st)
      (5 * s.M.length + 26 * Nb + hv_Tsc Nb rows + 24) := by
  have h1 := hv_ex_copy (a := 7) (b := 15) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st7, hv_st15, hv_u15, hRF, List.append_nil] at h1
  have h2 := hv_ex_copy (a := 6) (b := 16) (by decide) (by decide) (by decide)
    {s with RF := s.Y}.st (by simpa)
  simp only [hv_st6, hv_st16, hv_u16] at h2
  have h3 := hv_ex_scanCore rows Nb {s with RF := s.Y, CT := s.X ++ s.CT} h hsep hM hQ hCC hG hT
    hH (by simp [hCT]; omega)
  simp only at h3
  refine (h1.seq_norm (h2.seq_norm h3)).cast ?_ (by omega)
  congr 1; cases s; simp_all

/-- Some `pos` entry joins `X` and `Y` (in one of the two directions). -/
def hv_edgeB (rows : List (List SatSym)) (X Y : Str) : Bool :=
  hv_goS Y rows X || hv_goS X rows Y

theorem hv_ex_edgeC (rows : List (List SatSym)) (Nb : ℕ) (s : hv_HS)
    (hsep : ∀ r ∈ rows, sep ∉ r) (hM : s.M = enc rows) (hQ : s.Q = []) (hCC : s.CC = [])
    (hG : s.G = []) (hT : s.T = []) (hH : s.H = []) (hRF : s.RF = [])
    (hCT : s.CT = []) (hX : s.X.length ≤ Nb) (hY : s.Y.length ≤ Nb) :
    ExecLe hv_edgeC s.st (if hv_edgeB rows s.X s.Y then .norm s.st else .halt false)
      (10 * s.M.length + 52 * Nb + 2 * hv_Tsc Nb rows + 50) := by
  have h1 := hv_ex_scan67 rows Nb s false hsep hM hQ hCC hG hT (by simp [hH, CookLevin.fl])
    hRF hCT hX hY
  have h2 := hv_ex_scan76 rows Nb {s with H := CookLevin.fl (false || hv_goS s.Y rows s.X)}
    (false || hv_goS s.Y rows s.X) hsep hM hQ hCC hG hT rfl hRF hCT hX hY
  simp only at h2
  unfold hv_edgeB
  cases hb : (hv_goS s.Y rows s.X || hv_goS s.X rows s.Y)
  · refine (h1.seq_norm (h2.seq_norm (ExecLe.pop_nil ?_ (ExecLe.halt false _)))).cast
      (by simp) (by omega)
    simp [Bool.false_or, hb, CookLevin.fl]
  · refine (h1.seq_norm (h2.seq_norm (ExecLe.pop_cons (b := true) (s := []) ?_
      (ExecLe.skip _)))).cast ?_ (by omega)
    · simp [Bool.false_or, hb, CookLevin.fl]
    · simp only [if_true]; congr 1; cases s; simp_all

/-! ## One step of the main loop -/

/-- Read the next block, check the current block and the edge, shift. -/
def hv_body : Cmd :=
  .seq hv_takeN (.seq hv_permC (.seq hv_edgeC (.seq (drain 6) (hv_mvo 7 6))))

/-- The invariant of the main loop (apart from `R`, `I`, `X`, `Z`, `S`). -/
structure hv_Inv (rows : List (List SatSym)) (n : ℕ) (s : hv_HS) : Prop where
  hN : s.N = List.replicate n true
  hM : s.M = enc rows
  hK : s.K = []
  hT : s.T = []
  hY : s.Y = []
  hXC : s.XC = []
  hF : s.F = []
  hQ : s.Q = []
  hCC : s.CC = []
  hG : s.G = []
  hH : s.H = []
  hRF : s.RF = []
  hCT : s.CT = []
  hX : s.X.length = n
  hS : s.S.length = n

/-- Cost of the loop body. -/
def hv_Tb (n Lm Ts : ℕ) : ℕ := 80 * n + 10 * Lm + 2 * Ts + 80

theorem hv_ex_body (rows : List (List SatSym)) (n : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r)
    (s : hv_HS) (hi : hv_Inv rows n s) :
    ExecLe hv_body s.st
      (if hv_permOk s.X s.S && hv_edgeB rows s.X (hv_tk n s.R) then
        .norm {s with R := s.R.drop n, X := hv_tk n s.R, S := hv_orV s.X s.S}.st
      else .halt false) (hv_Tb n s.M.length (hv_Tsc n rows)) := by
  have h1 := hv_ex_takeN n s hi.hN hi.hK hi.hT hi.hY
  have h2 := hv_ex_permC {s with R := s.R.drop n, Y := hv_tk n s.R} hi.hXC hi.hF hi.hT
    (by simp [hi.hX, hi.hS])
  simp only at h2
  have h3 := hv_ex_edgeC rows n
    {s with R := s.R.drop n, Y := hv_tk n s.R, S := hv_orV s.X s.S} hsep hi.hM hi.hQ hi.hCC
    hi.hG hi.hT hi.hH hi.hRF hi.hCT (by simp [hi.hX]) (by simp [hv_length_tk])
  simp only at h3
  have h4 := hv_ex_drain 6 {s with R := s.R.drop n, Y := hv_tk n s.R, S := hv_orV s.X s.S}.st
  simp only [hv_u6, hv_st6] at h4
  have h5 := hv_ex_mvo (a := 7) (b := 6) (by decide) (by decide) (by decide)
    {s with R := s.R.drop n, Y := hv_tk n s.R, S := hv_orV s.X s.S, X := []}.st (by simpa using hi.hT)
  simp only [hv_u6, hv_st6, hv_u7, hv_st7, List.append_nil] at h5
  have hTb : 10 * n + 8 + (12 * s.X.length + 10 + (10 * s.M.length + 52 * n + 2 * hv_Tsc n rows +
      50 + (2 * s.X.length + 2 + (4 * (hv_tk n s.R).length + 4)))) ≤
      hv_Tb n s.M.length (hv_Tsc n rows) := by
    simp only [hv_Tb, hv_length_tk, hi.hX]; omega
  by_cases hp : hv_permOk s.X s.S = true
  · rw [if_pos hp] at h2
    by_cases he : hv_edgeB rows s.X (hv_tk n s.R) = true
    · rw [if_pos he] at h3
      rw [if_pos (by simp [hp, he])]
      refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm h5)))).cast ?_ hTb
      have hY := hi.hY
      congr 1; cases s; simp_all
    · rw [if_neg he] at h3
      rw [if_neg (by simp [hp, he])]
      exact (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3))).cast rfl (by omega)
  · rw [if_neg hp] at h2
    rw [if_neg (by simp [hp])]
    exact (h1.seq_norm (ExecLe.seq_halt h2)).cast rfl (by omega)

/-! ## The main loop -/

/-- The last iteration: check the last block against the copy `Z` of `B_0`. -/
def hv_finB : Cmd := .seq (drain 0) (.seq (hv_mvo 8 0) (.seq hv_body (.halt true)))

def hv_mainL : Cmd := .loop (.pop 5 hv_finB hv_body hv_body)

/-- What the main loop computes (`k`: the remaining ordinary iterations). -/
def hv_mainF (rows : List (List SatSym)) (n : ℕ) (Z : Str) : ℕ → Str → Str → Str → Bool
  | 0, _, X, S => hv_permOk X S && hv_edgeB rows X (hv_tk n Z)
  | k + 1, R, X, S => hv_permOk X S && hv_edgeB rows X (hv_tk n R) &&
      hv_mainF rows n Z k (R.drop n) (hv_tk n R) (hv_orV X S)

theorem hv_ex_mainL (rows : List (List SatSym)) (n Lr : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∀ (k : ℕ) (s : hv_HS), hv_Inv rows n s → s.I = List.replicate k true → s.R.length ≤ Lr →
    s.Z.length = n →
    ExecLe hv_mainL s.st (.halt (hv_mainF rows n s.Z k s.R s.X s.S))
      ((k + 1) * (hv_Tb n s.M.length (hv_Tsc n rows) + 1) + 2 * Lr + 4 * n + 10)
  | 0, s, hi, hI, hR, hZ => by
    have h1 := hv_ex_drain 0 s.st
    simp only [hv_u0, hv_st0] at h1
    have h2 := hv_ex_mvo (a := 8) (b := 0) (by decide) (by decide) (by decide)
      {s with R := []}.st (by simpa using hi.hT)
    simp only [hv_u0, hv_st0, hv_u8, hv_st8, List.append_nil] at h2
    have hi' : hv_Inv rows n {s with R := s.Z, Z := []} := by
      obtain ⟨⟩ := hi; constructor <;> assumption
    have h3 := hv_ex_body rows n hsep _ hi'
    simp only at h3
    have hfin : ExecLe hv_finB s.st (.halt (hv_mainF rows n s.Z 0 s.R s.X s.S))
        (2 * s.R.length + 2 + (4 * s.Z.length + 4 + (hv_Tb n s.M.length (hv_Tsc n rows) + 1))) := by
      simp only [hv_mainF, hv_finB]
      by_cases hc : (hv_permOk s.X s.S && hv_edgeB rows s.X (hv_tk n s.Z)) = true
      · rw [if_pos hc] at h3
        exact (h1.seq_norm (h2.seq_norm (h3.seq_norm (ExecLe.halt true _)))).cast (by simp [hc])
          le_rfl
      · rw [if_neg hc] at h3
        exact (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3))).cast
          (by simp only [Bool.not_eq_true] at hc; rw [hc]) (by omega)
    refine (ExecLe.loop_halt (ExecLe.pop_nil (by simpa using hI) hfin)).cast rfl ?_
    simp only [hZ]; omega
  | k + 1, s, hi, hI, hR, hZ => by
    have hb := hv_ex_body rows n hsep {s with I := List.replicate k true}
      (by obtain ⟨⟩ := hi; constructor <;> assumption)
    simp only at hb
    simp only [hv_mainF]
    by_cases hc : (hv_permOk s.X s.S && hv_edgeB rows s.X (hv_tk n s.R)) = true
    · rw [if_pos hc] at hb
      have hi' : hv_Inv rows n
          {s with I := List.replicate k true, R := s.R.drop n, X := hv_tk n s.R, S := hv_orV s.X s.S} := by
        obtain ⟨⟩ := hi; constructor <;> simp_all [hv_length_tk, hv_length_orV]
      have ih := hv_ex_mainL rows n Lr hsep k _ hi' rfl (by simp; omega) hZ
      simp only at ih
      rw [hc, Bool.true_and]
      refine (ExecLe.loop_norm (ExecLe.pop_cons (b := true) (s := List.replicate k true)
        (by simp [hI, List.replicate_succ]) (by simpa using hb)) ih).cast rfl ?_
      simp only [Nat.succ_mul]; omega
    · rw [if_neg hc] at hb
      rw [Bool.eq_false_iff.mpr hc, Bool.false_and]
      refine (ExecLe.loop_halt (ExecLe.pop_cons (b := true) (s := List.replicate k true)
        (by simp [hI, List.replicate_succ]) (by simpa using hb))).cast rfl ?_
      simp only [Nat.succ_mul]; omega

/-! ## The whole verifier -/

def hv_pre : Cmd :=
  .seq (copyVia 1 3 10) (.seq hv_cntL (.seq hv_chk3 (.seq hv_initI (.seq hv_initS
    (.seq hv_takeN (.seq (copyVia 7 8 10) (hv_mvo 7 6)))))))

def hv_ver : Cmd := .seq phaseA (.seq (trimC 2) (.seq (move 2 1) (.seq hv_pre hv_mainL)))

/-- The answer of the verifier on `(w, y)`. -/
def hv_vres (w : List SatSym) (y : Str) : Bool :=
  decide (3 ≤ (clauses w).length) &&
    hv_mainF (clauses w) (clauses w).length (hv_tk (clauses w).length y)
      ((clauses w).length - 1) (y.drop (clauses w).length) (hv_tk (clauses w).length y)
      (List.replicate (clauses w).length false)

/-- The state after parsing. -/
abbrev hv_s0 (y M : Str) : hv_HS := ⟨y, M, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
  [], []⟩

theorem hv_count_sep : ∀ L : List (List SatSym), (∀ c ∈ L, sep ∉ c) →
    (L.flatMap (· ++ [sep])).count sep = L.length
  | [], _ => rfl
  | c :: L, h => by
    have ih := hv_count_sep L (fun c' hc => h c' (by simp [hc]))
    have hc : c.count sep = 0 := List.count_eq_zero.mpr (h c (by simp))
    simp [List.flatMap_cons, List.count_append, ih, hc]

theorem hv_ex_run (rows : List (List SatSym)) (y : Str) (Lr : ℕ) (hy : y.length ≤ Lr)
    (hsep : ∀ r ∈ rows, sep ∉ r) :
    ExecLe (.seq hv_pre hv_mainL) (hv_s0 y (enc rows)).st
      (.halt (decide (3 ≤ rows.length) && hv_mainF rows rows.length (hv_tk rows.length y)
        (rows.length - 1) (y.drop rows.length) (hv_tk rows.length y)
        (List.replicate rows.length false)))
      (10 * (enc rows).length + 60 * rows.length + 3 * Lr + 70 +
        rows.length * (hv_Tb rows.length (enc rows).length (hv_Tsc rows.length rows) + 1)) := by
  set n := rows.length
  have h1 := hv_ex_copy (a := 1) (b := 3) (by decide) (by decide) (by decide)
    (hv_s0 y (enc rows)).st rfl
  simp only [hv_st1, hv_st3, hv_u3, List.append_nil] at h1
  have h2 := hv_ex_cntL (rows.flatMap (· ++ [sep])) {hv_s0 y (enc rows) with Q := enc rows}
    (by simp [enc])
  rw [hv_count_sep rows hsep] at h2
  simp only [List.append_nil] at h2
  set s2 : hv_HS := {hv_s0 y (enc rows) with Q := [], N := List.replicate n true}
  have h3 := hv_ex_chk3 n s2 rfl rfl rfl
  have hlen : (enc rows).length = 2 * ((rows.map List.length).sum + rows.length) := by
    simp only [enc, length_flatMap_ic]; rw [sum_length_le]
  by_cases hn : 3 ≤ n
  · rw [if_pos hn] at h3
    have h4 := hv_ex_initI n s2 rfl rfl rfl
    have h5 := hv_ex_initS n {s2 with I := List.replicate (n - 1) true} rfl rfl rfl
    simp only at h5
    have h6 := hv_ex_takeN n
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ []} rfl rfl rfl rfl
    simp only at h6
    have h7 := hv_ex_copy (a := 7) (b := 8) (by decide) (by decide) (by decide)
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := hv_tk n y}.st rfl
    simp only [hv_st7, hv_st8, hv_u8] at h7
    have h8 := hv_ex_mvo (a := 7) (b := 6) (by decide) (by decide) (by decide)
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := hv_tk n y, Z := hv_tk n y ++ []}.st rfl
    simp only [hv_st7, hv_st6, hv_u7, hv_u6] at h8
    set s9 : hv_HS := {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := [], Z := hv_tk n y ++ [], X := hv_tk n y ++ []}
    have hi : hv_Inv rows n s9 := by
      constructor <;> simp [s9, s2, hv_length_tk]
    have h9 := hv_ex_mainL rows n Lr hsep (n - 1) s9 hi rfl (by simp [s9]; omega)
      (by simp [s9, hv_length_tk])
    simp only [s9, s2, List.append_nil] at h3 h4 h5 h6 h7 h8 h9
    rw [show (n - 1 + 1) = n by omega] at h9
    refine (ExecLe.seq_norm (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm
      (h6.seq_norm (h7.seq_norm h8))))))) h9).cast (by simp [hn]) ?_
    simp [hv_length_tk]
    omega
  · rw [if_neg hn] at h3
    refine (ExecLe.seq_halt (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3)))).cast
      (by simp [hn]) ?_
    simp
    omega

/-- Time bound of the verifier. -/
def hv_Tver (L : ℕ) : ℕ := 200 * (L + 2) ^ 3

theorem hv_bound (L n t S : ℕ) (hn : n ≤ L) (ht : t ≤ L) (hS : S ≤ L) :
    (3 * L + 4) + (4 * L + 6) + (2 * (2 * t) + 2) + (10 * (2 * t) + 60 * n + 3 * L + 70 +
      n * (80 * n + 10 * (2 * t) + 2 * (10 * S + n * (7 * n + 20) + 2 * n + 8) + 80 + 1)) ≤
    hv_Tver L := by
  have hnn : n * n ≤ L * L := Nat.mul_le_mul hn hn
  have hX : 80 * n + 10 * (2 * t) + 2 * (10 * S + n * (7 * n + 20) + 2 * n + 8) + 80 + 1 ≤
      14 * (L * L) + 164 * L + 97 := by nlinarith
  have hY := Nat.mul_le_mul hn hX
  unfold hv_Tver
  nlinarith

theorem hv_exec_ver (z : Str) :
    ExecLe hv_ver (init [z]).stk (.halt (hv_vres (dec z).1 (dec z).2)) (hv_Tver z.length) := by
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
  have hR := hv_ex_run (clauses w) y z.length (by omega) (sep_not_mem_clauses w)
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  have hen : (enc (clauses w)).length = 2 * (trunc w).length := by
    simp only [enc, trunc, length_flatMap_ic]
  refine (hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm hR))).cast rfl ?_
  rw [hv_Tsc_eq]
  simp only [hv_Tb, htl, hen]
  have hb := hv_bound z.length (clauses w).length (trunc w).length
    ((clauses w).map List.length).sum (by omega) (by omega) (by omega)
  omega

theorem hv_Tver_le (n : ℕ) : hv_Tver n ≤ tb 11 n := by
  unfold hv_Tver tb
  have h8 : 2 ^ 8 ≤ (n + 2) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  have e : (n + 2) ^ 11 = (n + 2) ^ 8 * (n + 2) ^ 3 := by ring
  rw [e]
  have : 200 ≤ (n + 2) ^ 8 := le_trans (by norm_num) h8
  exact Nat.mul_le_mul_right _ this

end Pnp.Karp.Ham
