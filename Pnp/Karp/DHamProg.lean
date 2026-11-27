import Pnp.Karp.DHam
import Pnp.Karp.HamVer
import Pnp.Karp.CliqueProg

/-!
# The DIRECTED HAMILTONIAN CYCLE reduction program: HAMILTONIAN CYCLE ≤ₚ DIRECTED HAMILTONIAN CYCLE

`dp_redCmd`, on the bit string `x` on stack `0`, prints `symG w` (`w = dec2 x`,
`Pnp/Karp/DHam.lean`) on stack `0`.  It uses the stack layout `hv_HS` of the HAMILTONIAN CYCLE
verifier (`Pnp/Karp/HamVer.lean`) and its row-major matrix scans `hv_scanP`:

1. `parseLoop`, `trimC 4`, `move 4 1`: stack `1` holds the code `enc rows` of the rows
   `rows = clauses w`;
2. count the rows (`hv_cntL`: `N` is `n` in unary) and set the outer counter `I := N`;
3. for `u < n` (`dp_outL`, `X` the one-hot vector `dp_oh u`), for `v < n` (`dp_inL`,
   `Y = dp_oh v`): the two scans `hv_scanP 6 7`, `hv_scanP 7 6` set the flag `H` to
   `dp_e rows u v` (the entry `(u, v)` or `(v, u)` is `pos`, `dp_goS_oh`, `dp_anyHit_oh`); print
   `pos` or `zero`; after each row print `sep`.

`dp_exec_redCmd` bounds the run by `2000 (|x| + 2)^4 ≤ tb 15 |x|`, and `uham_le_dham_of` follows
from `FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.Ham

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## One-hot vectors and the scans -/

/-- The one-hot vector with its `true` bit at position `u`. -/
def dp_oh : ℕ → Str
  | 0 => [true]
  | u + 1 => false :: dp_oh u

theorem dp_length_oh : ∀ u, (dp_oh u).length = u + 1
  | 0 => rfl
  | u + 1 => by simp [dp_oh, dp_length_oh u]

theorem dp_anyHit_nil : ∀ r : List SatSym, hv_anyHit r [] = false
  | [] => rfl
  | x :: r => by simp [hv_anyHit, dp_anyHit_nil r]

theorem dp_anyHit_oh : ∀ (r : List SatSym) (v : ℕ), hv_anyHit r (dp_oh v) = isPos (r.getD v zero)
  | [], v => by simp [hv_anyHit, isPos]
  | x :: r, 0 => by simp [hv_anyHit, dp_oh, dp_anyHit_nil]
  | x :: r, v + 1 => by simp [hv_anyHit, dp_oh, dp_anyHit_oh r v]

theorem dp_goS_nil (C : Str) : ∀ rows : List (List SatSym), hv_goS C rows [] = false
  | [] => rfl
  | r :: rows => by simp [hv_goS, dp_goS_nil C rows]

theorem dp_goS_oh (C : Str) : ∀ (rows : List (List SatSym)) (u : ℕ),
    hv_goS C rows (dp_oh u) = hv_anyHit (rows.getD u []) C
  | [], u => by simp [hv_goS, hv_anyHit]
  | r :: rows, 0 => by simp [hv_goS, dp_oh, dp_goS_nil]
  | r :: rows, u + 1 => by simp [hv_goS, dp_oh, dp_goS_oh C rows u]

/-- The entry `(u, v)` or the entry `(v, u)` is `pos` (as computed by the two scans). -/
def dp_e (rows : List (List SatSym)) (u v : ℕ) : Bool :=
  hv_goS (dp_oh v) rows (dp_oh u) || hv_goS (dp_oh u) rows (dp_oh v)

def dp_sym (b : Bool) : SatSym := if b then pos else zero

theorem dp_sym_e (w : List SatSym) (u v : ℕ) :
    dp_sym (dp_e (clauses w) u v) = if ent w u v = pos ∨ ent w v u = pos then pos else zero := by
  simp only [dp_sym, dp_e, dp_goS_oh, dp_anyHit_oh, ent]
  have key : ∀ a b : SatSym,
      (if (isPos a || isPos b) = true then pos else zero) = if a = pos ∨ b = pos then pos else zero := by
    intro a b; cases a <;> cases b <;> simp [isPos]
  exact key _ _

/-- The row `u` printed by the program. -/
def dp_rowL (rows : List (List SatSym)) (n u : ℕ) : List SatSym :=
  (List.range n).map fun v => dp_sym (dp_e rows u v)

theorem dp_out_eq (w : List SatSym) :
    (List.range' 0 (clauses w).length).flatMap
      (fun u => dp_rowL (clauses w) (clauses w).length u ++ [sep]) = symG w := by
  rw [symG, List.flatMap_map, List.range_eq_range']
  congr 1; funext u
  simp only [dp_rowL, symRow, dp_sym_e, List.range_eq_range']

/-- The entries `v, …, v + k - 1` of row `u`. -/
def dp_seg (rows : List (List SatSym)) (u v k : ℕ) : List SatSym :=
  (List.range' v k).map fun v => dp_sym (dp_e rows u v)

/-- The rows `u, …, u + k - 1`, each followed by `sep`. -/
def dp_rows (rows : List (List SatSym)) (u k : ℕ) : List SatSym :=
  (List.range' u k).flatMap fun u => dp_rowL rows rows.length u ++ [sep]

/-! ## The program -/

/-- Print the symbols `L` on stack `0`. -/
def dp_em (L : List SatSym) : Cmd := pushList 0 (rv L)

theorem dp_ex_em (L E : List SatSym) (s : hv_HS) (hR : s.R = rv E) :
    ExecLe (dp_em L) s.st (.norm {s with R := rv (E ++ L)}.st) (2 * L.length + 1) := by
  refine (ExecLe.of (exec_pushList 0 (rv L) s.st)).cast ?_
    (by simp only [rv, List.length_reverse, length_flatMap_ic]; omega)
  rw [hv_u0, hv_st0, hR, rv_append]

/-- Print the flag `H`. -/
def dp_out : Cmd := .pop 14 (dp_em [zero]) (dp_em [zero]) (dp_em [pos])

theorem dp_ex_out (b : Bool) (s : hv_HS) (E : List SatSym) (hR : s.R = rv E)
    (hH : s.H = CookLevin.fl b) :
    ExecLe dp_out s.st (.norm {s with H := [], R := rv (E ++ [dp_sym b])}.st) 6 := by
  cases b
  · exact (ExecLe.pop_nil (by simp [hH, CookLevin.fl]) (dp_ex_em [zero] E s hR)).cast
      (by congr 1; cases s; simp_all [dp_sym, CookLevin.fl]) (by simp)
  · refine (ExecLe.pop_cons (b := true) (s := [])
      (r := .norm ({s with H := [], R := rv (E ++ [pos])} : hv_HS).st) (T := 3)
      (by simp [hH, CookLevin.fl]) ?_).cast (by simp [dp_sym]) (by omega)
    rw [hv_u14, if_pos rfl]; exact dp_ex_em [pos] E {s with H := []} hR

/-- One entry `(u, v)`. -/
def dp_pair : Cmd :=
  .seq (hv_scanP 6 7) (.seq (hv_scanP 7 6) (.seq dp_out (.push 7 false)))

/-- The cost of one entry. -/
def dp_P (rows : List (List SatSym)) (Nb : ℕ) : ℕ :=
  2 * (5 * (enc rows).length + 26 * Nb + hv_Tsc Nb rows + 24) + 7

/-- The clean part of the state: everything the scans need is empty. -/
structure dp_Cl (rows : List (List SatSym)) (s : hv_HS) : Prop where
  hM : s.M = enc rows
  hQ : s.Q = []
  hCC : s.CC = []
  hG : s.G = []
  hT : s.T = []
  hH : s.H = []
  hRF : s.RF = []
  hCT : s.CT = []

theorem dp_ex_pair (rows : List (List SatSym)) (Nb : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r)
    (s : hv_HS) (E : List SatSym) (u v : ℕ) (hc : dp_Cl rows s)
    (hX : s.X = dp_oh u) (hY : s.Y = dp_oh v) (hu : u < Nb) (hv : v < Nb) (hR : s.R = rv E) :
    ExecLe dp_pair s.st
      (.norm {s with R := rv (E ++ [dp_sym (dp_e rows u v)]), Y := dp_oh (v + 1)}.st)
      (dp_P rows Nb) := by
  obtain ⟨hM, hQ, hCC, hG, hT, hH, hRF, hCT⟩ := hc
  have hXl : s.X.length ≤ Nb := by rw [hX, dp_length_oh]; omega
  have hYl : s.Y.length ≤ Nb := by rw [hY, dp_length_oh]; omega
  have hMl : s.M.length = (enc rows).length := by rw [hM]
  have h1 := hv_ex_scan67 rows Nb s false hsep hM hQ hCC hG hT (by simp [hH, CookLevin.fl])
    hRF hCT hXl hYl
  have h2 := hv_ex_scan76 rows Nb {s with H := CookLevin.fl (false || hv_goS s.Y rows s.X)}
    (false || hv_goS s.Y rows s.X) hsep hM hQ hCC hG hT rfl hRF hCT hXl hYl
  simp only at h2
  have e2 : ({s with H := CookLevin.fl ((false || hv_goS s.Y rows s.X) ||
      hv_goS s.X rows s.Y)} : hv_HS) = {s with H := CookLevin.fl (dp_e rows u v)} := by
    rw [hX, hY]; simp [dp_e]
  have h3 := dp_ex_out (dp_e rows u v) {s with H := CookLevin.fl (dp_e rows u v)} E hR rfl
  have h4 := ExecLe.push 7 false
    ({s with H := [], R := rv (E ++ [dp_sym (dp_e rows u v)])} : hv_HS).st
  rw [hv_u7] at h4
  have h2' := h2.cast (congrArg (fun t : hv_HS => Res.norm t.st) e2) le_rfl
  refine (h1.seq_norm (h2'.seq_norm (h3.seq_norm h4))).cast ?_ ?_
  · congr 1; cases s; simp_all [dp_oh]
  · simp only [dp_P]; omega

/-- The inner loop over `v`, counter `K`. -/
def dp_inL : Cmd := .loop (.pop 11 .brk dp_pair dp_pair)

theorem dp_ex_inL (rows : List (List SatSym)) (Nb : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) (u : ℕ)
    (hu : u < Nb) : ∀ (k v : ℕ) (s : hv_HS) (E : List SatSym), v + k ≤ Nb →
    s.K = List.replicate k true → dp_Cl rows s → s.X = dp_oh u → s.Y = dp_oh v →
    s.R = rv E →
    ExecLe dp_inL s.st
      (.norm {s with R := rv (E ++ dp_seg rows u v k), Y := dp_oh (v + k), K := []}.st)
      (k * (dp_P rows Nb + 1) + 2)
  | 0, v, s, E, _, hK, _, _, hY, hR =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hK]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all [dp_seg]) (by omega)
  | k + 1, v, s, E, hk, hK, hc, hX, hY, hR => by
    have hp := dp_ex_pair rows Nb hsep {s with K := List.replicate k true} E u v
      ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ hX hY hu (by omega) hR
    have ih := dp_ex_inL rows Nb hsep u hu k (v + 1)
      {s with K := List.replicate k true, R := rv (E ++ [dp_sym (dp_e rows u v)]),
              Y := dp_oh (v + 1)} (E ++ [dp_sym (dp_e rows u v)]) (by omega) rfl
      ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ hX rfl rfl
    have hb : ExecLe (.pop 11 .brk dp_pair dp_pair) s.st (.norm
        {s with K := List.replicate k true, R := rv (E ++ [dp_sym (dp_e rows u v)]),
                Y := dp_oh (v + 1)}.st) (dp_P rows Nb + 1) :=
      ExecLe.pop_same (b := true) (s := List.replicate k true)
        (by simp [hK, List.replicate_succ]) (by simpa using hp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by rw [Nat.succ_mul]; omega)
    simp only [dp_seg, List.range'_succ, List.map_cons, List.append_assoc, List.singleton_append,
      show v + 1 + k = v + (k + 1) by omega]

/-- One row `u`. -/
def dp_row : Cmd :=
  .seq (.push 7 true) (.seq (copyVia 4 11 10) (.seq dp_inL (.seq (drain 7)
    (.seq (dp_em [sep]) (.push 6 false)))))

/-- The cost of one row. -/
def dp_Pr (rows : List (List SatSym)) (Nb : ℕ) : ℕ :=
  rows.length * (dp_P rows Nb + 1) + 7 * rows.length + 20

theorem dp_ex_row (rows : List (List SatSym)) (Nb : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) (u : ℕ)
    (hu : u < Nb) (hn : rows.length ≤ Nb) (s : hv_HS) (E : List SatSym)
    (hN : s.N = List.replicate rows.length true) (hK : s.K = []) (hYe : s.Y = [])
    (hc : dp_Cl rows s) (hX : s.X = dp_oh u) (hR : s.R = rv E) :
    ExecLe dp_row s.st
      (.norm {s with R := rv (E ++ dp_rowL rows rows.length u ++ [sep]), X := dp_oh (u + 1)}.st)
      (dp_Pr rows Nb) := by
  have h1 := ExecLe.push 7 true s.st
  rw [hv_u7, hv_st7, hYe] at h1
  have h2 := hv_ex_copy (a := 4) (b := 11) (by decide) (by decide) (by decide)
    {s with Y := [true]}.st (by simpa using hc.hT)
  simp only [hv_st4, hv_st11, hv_u11] at h2
  have h3 := dp_ex_inL rows Nb hsep u hu rows.length 0 {s with Y := [true], K := s.N ++ s.K} E (by omega)
    (by simp [hK, hN]) ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ hX rfl hR
  have h4 := hv_ex_drain 7
    {s with Y := dp_oh (0 + rows.length), K := [],
            R := rv (E ++ dp_seg rows u 0 rows.length)}.st
  simp only [hv_st7, hv_u7] at h4
  have h5 := dp_ex_em [sep] (E ++ dp_seg rows u 0 rows.length)
    {s with Y := [], K := [],
            R := rv (E ++ dp_seg rows u 0 rows.length)} rfl
  have h6 := ExecLe.push 6 false
    ({s with Y := [], K := [],
             R := rv (E ++ dp_seg rows u 0 rows.length ++ [sep])} : hv_HS).st
  rw [hv_u6] at h6
  refine (h1.seq_norm (h2.seq_norm
    (h3.seq_norm (h4.seq_norm (h5.seq_norm h6))))).cast ?_ ?_
  · congr 1; cases s; simp_all [dp_rowL, dp_seg, dp_oh, List.range_eq_range']
  · simp only [dp_Pr, hN, List.length_replicate, dp_length_oh]
    simp; omega

/-- The outer loop over `u`, counter `I`. -/
def dp_outL : Cmd := .loop (.pop 5 .brk dp_row dp_row)

theorem dp_ex_outL (rows : List (List SatSym)) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∀ (k u : ℕ) (s : hv_HS) (E : List SatSym), u + k ≤ rows.length →
    s.I = List.replicate k true → s.N = List.replicate rows.length true → s.K = [] →
    s.Y = [] → dp_Cl rows s → s.X = dp_oh u → s.R = rv E →
    ExecLe dp_outL s.st
      (.norm {s with R := rv (E ++ dp_rows rows u k), X := dp_oh (u + k), I := []}.st)
      (k * (dp_Pr rows rows.length + 1) + 2)
  | 0, u, s, E, _, hI, _, _, _, _, _, _ =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hI]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all [dp_rows]) (by omega)
  | k + 1, u, s, E, hk, hI, hN, hK, hY, hc, hX, hR => by
    have hp := dp_ex_row rows rows.length hsep u (by omega) le_rfl
      {s with I := List.replicate k true} E hN hK hY
      ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ hX hR
    have ih := dp_ex_outL rows hsep k (u + 1)
      {s with I := List.replicate k true, R := rv (E ++ dp_rowL rows rows.length u ++ [sep]),
              X := dp_oh (u + 1)} (E ++ dp_rowL rows rows.length u ++ [sep]) (by omega) rfl hN hK hY
      ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ rfl rfl
    have hb : ExecLe (.pop 5 .brk dp_row dp_row) s.st (.norm
        {s with I := List.replicate k true, R := rv (E ++ dp_rowL rows rows.length u ++ [sep]),
                X := dp_oh (u + 1)}.st) (dp_Pr rows rows.length + 1) :=
      ExecLe.pop_same (b := true) (s := List.replicate k true)
        (by simp [hI, List.replicate_succ]) (by simpa using hp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by rw [Nat.succ_mul]; omega)
    simp only [dp_rows, List.range'_succ, List.flatMap_cons, List.append_assoc,
      show u + 1 + k = u + (k + 1) by omega]

/-- Everything after parsing. -/
def dp_main : Cmd :=
  .seq (copyVia 1 3 10) (.seq hv_cntL (.seq (copyVia 4 5 10) (.seq (.push 6 true) dp_outL)))

theorem dp_ex_main (rows : List (List SatSym)) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∃ s : hv_HS, ExecLe dp_main (hv_s0 [] (enc rows)).st (.norm s.st)
      (18 * (enc rows).length + 10 * rows.length + 20 +
        rows.length * (dp_Pr rows rows.length + 1)) ∧
      s.R = rv (dp_rows rows 0 rows.length) := by
  have h1 := hv_ex_copy (a := 1) (b := 3) (by decide) (by decide) (by decide)
    (hv_s0 [] (enc rows)).st rfl
  simp only [hv_st1, hv_st3, hv_u3, List.append_nil] at h1
  have h2 := hv_ex_cntL (rows.flatMap (· ++ [sep])) {hv_s0 [] (enc rows) with Q := enc rows}
    (by simp [enc])
  rw [hv_count_sep rows hsep] at h2
  simp only [List.append_nil] at h2
  set s2 : hv_HS := {hv_s0 [] (enc rows) with Q := [], N := List.replicate rows.length true}
  have h3 := hv_ex_copy (a := 4) (b := 5) (by decide) (by decide) (by decide) s2.st rfl
  simp only [hv_st4, hv_st5, hv_u5] at h3
  have h4 := ExecLe.push 6 true {s2 with I := s2.N ++ s2.I}.st
  rw [hv_u6] at h4
  have h5 := dp_ex_outL rows hsep rows.length 0 {s2 with I := s2.N ++ s2.I, X := true :: s2.X} [] (by omega)
    (by simp [s2]) rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
  have hall := h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm h5)))
  refine ⟨_, hall.cast rfl ?_, rfl⟩
  have hl : (rows.flatMap (· ++ [sep])).length ≤ (enc rows).length := by
    simp only [enc, length_flatMap_ic]; omega
  have hsl := sum_length_le rows
  simp [s2]
  omega

/-- The reduction program. -/
def dp_redCmd : Cmd := .seq parseLoop (.seq (trimC 4) (.seq (move 4 1) dp_main))

/-- The time bound. -/
def dp_Tred (L : ℕ) : ℕ := 2000 * (L + 2) ^ 4

theorem dp_bound (L n t S : ℕ) (hn : n ≤ L) (ht : t ≤ L) (hS : S ≤ L) :
    (2 * L + 3) + (4 * L + 6) + (2 * (2 * t) + 2) + (18 * (2 * t) + 10 * n + 20 +
      n * (n * (2 * (5 * (2 * t) + 26 * n + (10 * S + n * (7 * n + 20) + 2 * n + 8) + 24) + 7
        + 1) + 7 * n + 20 + 1)) ≤ dp_Tred L := by
  unfold dp_Tred
  set A := L + 2
  have hn' : n ≤ A := by omega
  have ht' : t ≤ A := by omega
  have hS' : S ≤ A := by omega
  have hA : 2 ≤ A := by omega
  have hP : 2 * (5 * (2 * t) + 26 * n + (10 * S + n * (7 * n + 20) + 2 * n + 8) + 24) + 7 + 1
      ≤ 400 * (A * A) := by nlinarith [Nat.mul_le_mul hn' hn']
  have hR : n * (2 * (5 * (2 * t) + 26 * n + (10 * S + n * (7 * n + 20) + 2 * n + 8) + 24) + 7
      + 1) + 7 * n + 20 + 1 ≤ 420 * (A * A * A) := by
    have := Nat.mul_le_mul hn' hP
    nlinarith [Nat.mul_le_mul (Nat.mul_le_mul hA hA) hA]
  have hT : _ ≤ 420 * (A * (A * A * A)) := calc
    _ ≤ A * (420 * (A * A * A)) := Nat.mul_le_mul hn' hR
    _ = 420 * (A * (A * A * A)) := by ring
  have e : A ^ 4 = A * (A * A * A) := by ring
  rw [e]
  have h3 : 8 ≤ A * A * A := by nlinarith [Nat.mul_le_mul (Nat.mul_le_mul hA hA) hA]
  have h4 : 8 * A ≤ A * (A * A * A) := by nlinarith
  have h5 : 16 ≤ A * (A * A * A) := by nlinarith
  omega

theorem dp_exec_redCmd (x : Str) : ∃ σ', ExecLe dp_redCmd (init [x]).stk (.norm σ')
    (dp_Tred x.length) ∧ σ' 0 = ((symG (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ₁ := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := exec_trimC_word 4 w σ₁ (by simp [σ₁, he 4 (by decide)])
  set σ₂ := update σ₁ 4 (((trunc w).flatMap ic).reverse)
  have p3 := exec_move (a := 4) (b := 1) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 4 []) 1 ((σ₂ 4).reverse ++ σ₂ 1) =
      (hv_s0 [] (enc (clauses w))).st := by
    funext j
    by_cases hj : j < 19
    · interval_cases j <;> simp [σ₂, σ₁, he, enc, trunc, hv_HS.st]
    · rw [hv_st_big _ _ (by omega)]
      simp [σ₂, σ₁, he j (by omega), show j ≠ 0 by omega, show j ≠ 1 by omega,
        show j ≠ 4 by omega]
  rw [hσ] at p3
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  obtain ⟨s, p4, hs⟩ := dp_ex_main (clauses w) (sep_not_mem_clauses w)
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm p4))).cast rfl ?_, ?_⟩
  · have htl : (σ₂ 4).length = 2 * (trunc w).length := by
      simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
    have hen : (enc (clauses w)).length = 2 * (trunc w).length := by
      simp only [enc, trunc, length_flatMap_ic]
    simp only [dp_Pr, dp_P, hv_Tsc_eq, htl, hen]
    have hb := dp_bound x.length (clauses w).length (trunc w).length
      ((clauses w).map List.length).sum (by omega) (by omega) (by omega)
    omega
  · rw [hv_st0, hs, dp_rows, dp_out_eq]; rfl

theorem dp_Tred_le (n : ℕ) : dp_Tred n ≤ tb 15 n := by
  unfold dp_Tred tb
  have h11 : 2 ^ 11 ≤ (n + 2) ^ 11 := Nat.pow_le_pow_left (by omega) 11
  have e : (n + 2) ^ 15 = (n + 2) ^ 11 * (n + 2) ^ 4 := by ring
  rw [e]
  have : 2000 ≤ (n + 2) ^ 11 := le_trans (by norm_num) h11
  exact Nat.mul_le_mul_right _ this

/-! ## The reduction -/

/-- **HAMILTONIAN CYCLE ≤ₚ DIRECTED HAMILTONIAN CYCLE** (official polynomial-time many-one
reducibility), given the correctness of the reduction instance `symG`. -/
theorem uham_le_dham_of (h : ∀ w, UHamLang w ↔ DHamLang (symG w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) UHamLang DHamLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    dp_redCmd 0 15 (fun x => symG (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := dp_exec_redCmd x
      exact ⟨σ', h1.mono (dp_Tred_le _), h2⟩)
    symG (fun t => (congrArg symG (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨symG, hc, h⟩

end Pnp.Karp.Ham
