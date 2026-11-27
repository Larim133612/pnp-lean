import Pnp.Karp.HPath
import Pnp.Karp.DHamProg

/-!
# The HAMILTONIAN PATH reduction program: HAMILTONIAN CYCLE ≤ₚ HAMILTONIAN PATH

`hq_redCmd`, on the bit string `x` on stack `0`, prints `hpI w` (`w = dec2 x`,
`Pnp/Karp/HPath.lean`) on stack `0`.  It reuses the stack layout `hv_HS`, the row counter
`hv_cntL` (`Pnp/Karp/HamVer.lean`) and the entry / row loops of `Pnp/Karp/DHamProg.lean`:

1. parse as `dp_redCmd`; count the rows (`N` is `n` in unary);
2. `hq_br`: pop a copy of `N` three times; if it runs out, print `[sep, sep]` and stop;
3. otherwise (`hq_big`), for `u < n` (`hq_outL`, `hq_row`) print the symmetric entries
   `dp_e rows u v` (`v < n`), three `zero`s and `sep`;
4. `hq_tail`: row `n` (`zero`, then `dp_e rows 0 v` for `1 ≤ v < n` via `dp_inL` started at
   `v = 1`, then three `zero`s), row `n + 1` (`pos`, `n + 2` times `zero`), row `n + 2`
   (`n` times `zero`, `pos`, `zero`, `zero`), each followed by `sep`.

The printed list is `hq_outP (clauses w)`, equal to `hpI w` by `hq_out_eq`.
`hq_exec_redCmd` bounds the run by `4000 (|x| + 2)^4 ≤ tb 16 |x|`, and `uham_le_uhpath_of`
follows from `FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.Ham

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## The output -/

/-- The rows `u, …, u + k - 1` of the graph part, each followed by three `zero`s and `sep`. -/
def hq_rows (rows : List (List SatSym)) (u k : ℕ) : List SatSym :=
  (List.range' u k).flatMap fun u => dp_rowL rows rows.length u ++ [zero, zero, zero, sep]

/-- The last three rows. -/
def hq_tailL (rows : List (List SatSym)) (n : ℕ) : List SatSym :=
  [zero] ++ dp_seg rows 0 1 (n - 1) ++ [zero, zero, zero, sep, pos, zero, zero] ++
    List.replicate n zero ++ [sep] ++ List.replicate n zero ++ [pos, zero, zero, sep]

theorem hq_map_zero (f : ℕ → SatSym) (k : ℕ) (h : ∀ v < k, f v = zero) :
    (List.range k).map f = List.replicate k zero := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp, ?_⟩
  intro b hb
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
  exact h v (List.mem_range.mp hv)

theorem hq_range3 (n : ℕ) : List.range (n + 3) = List.range n ++ [n, n + 1, n + 2] := by
  simp [List.range_succ]

theorem hq_row_lt (w : List SatSym) (u : ℕ) (hu : u < (clauses w).length) :
    hpRow w u ++ [sep] = dp_rowL (clauses w) (clauses w).length u ++ [zero, zero, zero, sep] := by
  set n := (clauses w).length with hn
  simp only [hpRow, ← hn, hq_range3, List.map_append, dp_rowL, List.append_assoc]
  congr 1
  · refine List.map_congr_left fun v hv => ?_
    have hv' := List.mem_range.mp hv
    rw [dp_sym_e]; simp [hpE, ← hn, hu, hv']
  · simp [hpE, ← hn]
    split_ifs <;> omega

theorem hq_row_n (w : List SatSym) (h3 : 3 ≤ (clauses w).length) :
    hpRow w (clauses w).length = [zero] ++ dp_seg (clauses w) 0 1 ((clauses w).length - 1) ++
      [zero, zero, zero] := by
  set n := (clauses w).length with hn
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [hpRow, ← hn, hq_range3, List.map_append]
  congr 1
  · rw [hm, List.range_succ_eq_map, List.map_cons]
    simp only [dp_seg, List.range'_eq_map_range, List.map_map]
    simp only [List.cons_append, List.nil_append, show m + 1 - 1 = m by omega]
    congr 1
    · simp [hpE, ← hn, hm]
    · refine List.map_congr_left fun v hv => ?_
      have hv' := List.mem_range.mp hv
      simp only [Function.comp, dp_sym_e, show 1 + v = v + 1 by omega]
      simp [hpE, ← hn, hm, hv']
  · simp [hpE, ← hn]

theorem hq_row_n1 (w : List SatSym) :
    hpRow w ((clauses w).length + 1) = [pos, zero, zero] ++ List.replicate (clauses w).length zero := by
  set n := (clauses w).length with hn
  rw [hpRow, ← hn, List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [hq_map_zero _ (n + 2) (fun v hv => by simp [hpE, ← hn])]
  simp [hpE, ← hn, List.replicate_succ]

theorem hq_row_n2 (w : List SatSym) :
    hpRow w ((clauses w).length + 2) = List.replicate (clauses w).length zero ++ [pos, zero, zero] := by
  set n := (clauses w).length with hn
  simp only [hpRow, ← hn, hq_range3, List.map_append]
  rw [hq_map_zero _ n (fun v hv => by simp [hpE, ← hn]; omega)]
  simp [hpE, ← hn]

theorem hq_out_eq (w : List SatSym) (h3 : 3 ≤ (clauses w).length) :
    hq_rows (clauses w) 0 (clauses w).length ++ hq_tailL (clauses w) (clauses w).length = hpI w := by
  set n := (clauses w).length with hn
  rw [hpI, if_neg (by omega), ← hn, hq_range3, List.map_append, List.flatMap_append]
  congr 1
  · rw [hq_rows, List.flatMap_map, List.range_eq_range']
    exact List.flatMap_congr fun u hu => (hq_row_lt w u (by simp at hu; omega)).symm
  · simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, hq_row_n w h3,
      hn, hq_row_n1, hq_row_n2, hq_tailL]
    simp

/-! ## The program -/

/-- One row `u < n`: as `dp_row`, followed by three `zero`s. -/
def hq_row : Cmd :=
  .seq (.push 7 true) (.seq (copyVia 4 11 10) (.seq dp_inL (.seq (drain 7)
    (.seq (dp_em [zero, zero, zero, sep]) (.push 6 false)))))

/-- The cost of one row. -/
def hq_Pr (rows : List (List SatSym)) (Nb : ℕ) : ℕ := dp_Pr rows Nb + 6

theorem hq_ex_row (rows : List (List SatSym)) (Nb : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) (u : ℕ)
    (hu : u < Nb) (hn : rows.length ≤ Nb) (s : hv_HS) (E : List SatSym)
    (hN : s.N = List.replicate rows.length true) (hK : s.K = []) (hYe : s.Y = [])
    (hc : dp_Cl rows s) (hX : s.X = dp_oh u) (hR : s.R = rv E) :
    ExecLe hq_row s.st
      (.norm {s with
        R := rv (E ++ dp_rowL rows rows.length u ++ [zero, zero, zero, sep]),
        X := dp_oh (u + 1)}.st)
      (hq_Pr rows Nb) := by
  have h1 := ExecLe.push 7 true s.st
  rw [hv_u7, hv_st7, hYe] at h1
  have h2 := hv_ex_copy (a := 4) (b := 11) (by decide) (by decide) (by decide)
    {s with Y := [true]}.st (by simpa using hc.hT)
  simp only [hv_st4, hv_st11, hv_u11] at h2
  have h3 := dp_ex_inL rows Nb hsep u hu rows.length 0 {s with Y := [true], K := s.N ++ s.K} E
    (by omega) (by simp [hK, hN]) ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩
    hX rfl hR
  have h4 := hv_ex_drain 7
    {s with Y := dp_oh (0 + rows.length), K := [],
            R := rv (E ++ dp_seg rows u 0 rows.length)}.st
  simp only [hv_st7, hv_u7] at h4
  have h5 := dp_ex_em [zero, zero, zero, sep] (E ++ dp_seg rows u 0 rows.length)
    {s with Y := [], K := [],
            R := rv (E ++ dp_seg rows u 0 rows.length)} rfl
  have h6 := ExecLe.push 6 false
    ({s with Y := [], K := [],
             R := rv (E ++ dp_seg rows u 0 rows.length ++ [zero, zero, zero, sep])} : hv_HS).st
  rw [hv_u6] at h6
  refine (h1.seq_norm (h2.seq_norm
    (h3.seq_norm (h4.seq_norm (h5.seq_norm h6))))).cast ?_ ?_
  · congr 1; cases s; simp_all [dp_rowL, dp_seg, dp_oh, List.range_eq_range']
  · simp only [hq_Pr, dp_Pr, hN, List.length_replicate, dp_length_oh]
    simp; omega

/-- The loop over the rows `u < n`, counter `I`. -/
def hq_outL : Cmd := .loop (.pop 5 .brk hq_row hq_row)

theorem hq_ex_outL (rows : List (List SatSym)) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∀ (k u : ℕ) (s : hv_HS) (E : List SatSym), u + k ≤ rows.length →
    s.I = List.replicate k true → s.N = List.replicate rows.length true → s.K = [] →
    s.Y = [] → dp_Cl rows s → s.X = dp_oh u → s.R = rv E →
    ExecLe hq_outL s.st
      (.norm {s with R := rv (E ++ hq_rows rows u k), X := dp_oh (u + k), I := []}.st)
      (k * (hq_Pr rows rows.length + 1) + 2)
  | 0, u, s, E, _, hI, _, _, _, _, _, _ =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hI]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all [hq_rows]) (by omega)
  | k + 1, u, s, E, hk, hI, hN, hK, hY, hc, hX, hR => by
    have hp := hq_ex_row rows rows.length hsep u (by omega) le_rfl
      {s with I := List.replicate k true} E hN hK hY
      ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ hX hR
    have ih := hq_ex_outL rows hsep k (u + 1)
      {s with I := List.replicate k true,
              R := rv (E ++ dp_rowL rows rows.length u ++ [zero, zero, zero, sep]),
              X := dp_oh (u + 1)} (E ++ dp_rowL rows rows.length u ++ [zero, zero, zero, sep])
      (by omega) rfl hN hK hY
      ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ rfl rfl
    have hb : ExecLe (.pop 5 .brk hq_row hq_row) s.st (.norm
        {s with I := List.replicate k true,
                R := rv (E ++ dp_rowL rows rows.length u ++ [zero, zero, zero, sep]),
                X := dp_oh (u + 1)}.st) (hq_Pr rows rows.length + 1) :=
      ExecLe.pop_same (b := true) (s := List.replicate k true)
        (by simp [hI, List.replicate_succ]) (by simpa using hp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by rw [Nat.succ_mul]; omega)
    simp only [hq_rows, List.range'_succ, List.flatMap_cons, List.append_assoc,
      show u + 1 + k = u + (k + 1) by omega]

/-- Print `k` times `zero` (counter `K`). -/
def hq_zL : Cmd := .loop (.pop 11 .brk (dp_em [zero]) (dp_em [zero]))

theorem hq_ex_zL : ∀ (k : ℕ) (s : hv_HS) (E : List SatSym), s.K = List.replicate k true →
    s.R = rv E →
    ExecLe hq_zL s.st (.norm {s with K := [], R := rv (E ++ List.replicate k zero)}.st)
      (4 * k + 2)
  | 0, s, E, hK, hR => (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hK]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all) (by omega)
  | k + 1, s, E, hK, hR => by
    have hp := dp_ex_em [zero] E {s with K := List.replicate k true} hR
    have ih := hq_ex_zL k {s with K := List.replicate k true, R := rv (E ++ [zero])}
      (E ++ [zero]) rfl rfl
    have hb : ExecLe (.pop 11 .brk (dp_em [zero]) (dp_em [zero])) s.st (.norm
        {s with K := List.replicate k true, R := rv (E ++ [zero])}.st) 4 :=
      ExecLe.pop_same (b := true) (s := List.replicate k true)
        (by simp [hK, List.replicate_succ]) (by simpa using hp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    simp [List.replicate_succ]

/-- Print `n` times `zero`. -/
def hq_zeros : Cmd := .seq (copyVia 4 11 10) hq_zL

theorem hq_ex_zeros (n : ℕ) (s : hv_HS) (E : List SatSym) (hN : s.N = List.replicate n true)
    (hK : s.K = []) (hT : s.T = []) (hR : s.R = rv E) :
    ExecLe hq_zeros s.st (.norm {s with R := rv (E ++ List.replicate n zero)}.st) (9 * n + 6) := by
  have h1 := hv_ex_copy (a := 4) (b := 11) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st4, hv_st11, hv_u11, hK, List.append_nil] at h1
  refine (h1.seq_norm (hq_ex_zL n _ E (by simp [hN]) hR)).cast ?_ (by simp [hN]; omega)
  congr 1; cases s; simp_all

/-- Set up row `n`: `X := dp_oh 0`, `Y := dp_oh 1`, `K := n - 1`. -/
def hq_tA0 : Cmd :=
  .seq (drain 6) (.seq (.push 6 true) (.seq (.push 7 true) (.seq (.push 7 false)
    (.seq (copyVia 4 11 10) (.pop 11 .skip .skip .skip)))))

theorem hq_ex_tA0 (n : ℕ) (s : hv_HS) (hN : s.N = List.replicate n true) (hK : s.K = [])
    (hY : s.Y = []) (hT : s.T = []) :
    ExecLe hq_tA0 s.st
      (.norm {s with X := [true], Y := [false, true], K := List.replicate (n - 1) true}.st)
      (2 * s.X.length + 5 * n + 12) := by
  have h1 := hv_ex_drain 6 s.st
  simp only [hv_u6, hv_st6] at h1
  have h2 := ExecLe.push 6 true ({s with X := []} : hv_HS).st
  simp only [hv_u6, hv_st6] at h2
  have h3 := ExecLe.push 7 true ({s with X := [true]} : hv_HS).st
  simp only [hv_u7, hv_st7] at h3
  have h4 := ExecLe.push 7 false ({s with X := [true], Y := true :: s.Y} : hv_HS).st
  simp only [hv_u7, hv_st7] at h4
  have h5 := hv_ex_copy (a := 4) (b := 11) (by decide) (by decide) (by decide)
    ({s with X := [true], Y := false :: true :: s.Y} : hv_HS).st (by simpa using hT)
  simp only [hv_u11, hv_st11, hv_st4] at h5
  have h6 := hv_pop3 (k := 11) (ExecLe.skip
    (update ({s with X := [true], Y := false :: true :: s.Y, K := s.N ++ s.K} : hv_HS).st 11
      (({s with X := [true], Y := false :: true :: s.Y, K := s.N ++ s.K} : hv_HS).st 11).tail))
  simp only [hv_u11, hv_st11] at h6
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm h6))))).cast ?_ ?_
  · congr 1; cases s; simp_all
  · simp [hN]; omega

/-- Row `n` up to its last three entries. -/
def hq_tA : Cmd := .seq hq_tA0 (.seq (dp_em [zero]) dp_inL)

theorem hq_ex_tA (rows : List (List SatSym)) (hsep : ∀ r ∈ rows, sep ∉ r) (h1 : 1 ≤ rows.length)
    (s : hv_HS) (E : List SatSym) (hN : s.N = List.replicate rows.length true) (hK : s.K = [])
    (hY : s.Y = []) (hc : dp_Cl rows s) (hR : s.R = rv E) :
    ExecLe hq_tA s.st
      (.norm {s with
        X := [true], Y := dp_oh (1 + (rows.length - 1)), K := [],
        R := rv (E ++ [zero] ++ dp_seg rows 0 1 (rows.length - 1))}.st)
      (2 * s.X.length + 5 * rows.length + rows.length * (dp_P rows rows.length + 1) + 17) := by
  have h0 := hq_ex_tA0 rows.length s hN hK hY hc.hT
  set s1 : hv_HS := {s with
    X := [true], Y := [false, true], K := List.replicate (rows.length - 1) true}
  have h2 := dp_ex_em [zero] E s1 hR
  have h3 := dp_ex_inL rows rows.length hsep 0 (by omega) (rows.length - 1) 1
    {s1 with R := rv (E ++ [zero])} (E ++ [zero]) (by omega) rfl
    ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ rfl rfl rfl
  refine (h0.seq_norm (h2.seq_norm h3)).cast ?_ ?_
  · congr 1
  · have : (rows.length - 1) * (dp_P rows rows.length + 1) ≤
        rows.length * (dp_P rows rows.length + 1) := Nat.mul_le_mul_right _ (by omega)
    simp; omega

/-- The rest: the last three entries of row `n`, the rows `n + 1` and `n + 2`. -/
def hq_tB : Cmd :=
  .seq (dp_em [zero, zero, zero, sep, pos, zero, zero]) (.seq hq_zeros (.seq (dp_em [sep])
    (.seq hq_zeros (dp_em [pos, zero, zero, sep]))))

theorem hq_ex_tB (n : ℕ) (s : hv_HS) (E : List SatSym) (hN : s.N = List.replicate n true)
    (hK : s.K = []) (hT : s.T = []) (hR : s.R = rv E) :
    ExecLe hq_tB s.st
      (.norm {s with
        R := rv (E ++ [zero, zero, zero, sep, pos, zero, zero] ++
          List.replicate n zero ++ [sep] ++ List.replicate n zero ++ [pos, zero, zero, sep])}.st)
      (18 * n + 40) := by
  have h1 := dp_ex_em [zero, zero, zero, sep, pos, zero, zero] E s hR
  set E1 := E ++ [zero, zero, zero, sep, pos, zero, zero]
  have h2 := hq_ex_zeros n {s with R := rv E1} E1 hN hK hT rfl
  set E2 := E1 ++ List.replicate n zero
  have h3 := dp_ex_em [sep] E2 {s with R := rv E2} rfl
  set E3 := E2 ++ [sep]
  have h4 := hq_ex_zeros n {s with R := rv E3} E3 hN hK hT rfl
  set E4 := E3 ++ List.replicate n zero
  have h5 := dp_ex_em [pos, zero, zero, sep] E4 {s with R := rv E4} rfl
  exact (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm h5)))).cast rfl (by simp; omega)

/-- The tail: the rows `n`, `n + 1`, `n + 2`. -/
def hq_tail : Cmd := .seq hq_tA hq_tB

/-! ## The branch on `n ≥ 3` -/

/-- Pop the counter `K`; on empty print the constant output `[sep, sep]`. -/
def hq_p (c : Cmd) : Cmd := .pop 11 (dp_em [sep, sep]) c c

theorem hq_ex_p_nil (c : Cmd) (s : hv_HS) (hK : s.K = []) (hR : s.R = []) :
    ExecLe (hq_p c) s.st (.norm {s with R := rv [sep, sep]}.st) 6 :=
  (ExecLe.pop_nil (by simpa using hK) (dp_ex_em [sep, sep] [] s (by simp [hR, rv]))).cast
    rfl (by simp)

theorem hq_ex_p_cons (c : Cmd) (s : hv_HS) (L : Str) (hK : s.K = true :: L) {r : Res} {T : ℕ}
    (h : ExecLe c {s with K := L}.st r T) : ExecLe (hq_p c) s.st r (T + 1) :=
  ExecLe.pop_same (b := true) (s := L) (by simpa using hK) (by simpa using h)

/-- Print `[sep, sep]` if `n < 3`, otherwise run `c`. -/
def hq_br (c : Cmd) : Cmd :=
  .seq (copyVia 4 11 10) (hq_p (hq_p (hq_p (.seq (drain 11) c))))

theorem hq_ex_br (n : ℕ) (s : hv_HS) (hN : s.N = List.replicate n true) (hK : s.K = [])
    (hT : s.T = []) (hR : s.R = []) (c : Cmd) (r : Res) (Tb : ℕ)
    (hc : 3 ≤ n → ExecLe c s.st r Tb) :
    ExecLe (hq_br c) s.st (if 3 ≤ n then r else .norm {s with R := rv [sep, sep]}.st)
      (7 * n + 30 + Tb) := by
  have h1 := hv_ex_copy (a := 4) (b := 11) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st4, hv_st11, hv_u11, hK, List.append_nil] at h1
  set s1 : hv_HS := {s with K := s.N} with hs1
  have hl : s.N.length = n := by simp [hN]
  rcases n with _ | _ | _ | n
  · refine (h1.seq_norm (hq_ex_p_nil _ s1 (by simp [s1, hN]) hR)).cast ?_ (by omega)
    simp only [if_neg (show ¬ 3 ≤ 0 by omega)]; congr 1; cases s; simp_all
  · refine (h1.seq_norm (hq_ex_p_cons _ s1 [] (by simp [s1, hN])
      (hq_ex_p_nil _ {s1 with K := []} rfl hR))).cast ?_ (by omega)
    simp only [if_neg (show ¬ 3 ≤ 0 + 1 by omega)]; congr 1; cases s; simp_all
  · refine (h1.seq_norm (hq_ex_p_cons _ s1 [true] (by simp [s1, hN])
      (hq_ex_p_cons _ {s1 with K := [true]} [] rfl
        (hq_ex_p_nil _ {s1 with K := []} rfl hR)))).cast ?_ (by omega)
    simp only [if_neg (show ¬ 3 ≤ 0 + 1 + 1 by omega)]; congr 1; cases s; simp_all
  · have e : s1.K = true :: true :: true :: List.replicate n true := by
      simp [s1, hN, List.replicate_succ]
    have h2 := hv_ex_drain 11 {s1 with K := List.replicate n true}.st
    simp only [hv_u11, hv_st11] at h2
    have e2 : ({s1 with K := []} : hv_HS) = s := by cases s; simp_all [s1]
    rw [e2] at h2
    refine (h1.seq_norm (hq_ex_p_cons _ s1 _ e
      (hq_ex_p_cons _ {s1 with K := true :: true :: List.replicate n true}
        (true :: List.replicate n true) rfl
      (hq_ex_p_cons _ {s1 with K := true :: List.replicate n true} (List.replicate n true) rfl
      (h2.seq_norm (hc (by omega))))))).cast ?_ (by simp; omega)
    rw [if_pos (by omega)]

/-! ## The main part -/

/-- The case `n ≥ 3`: the rows `u < n`, then the tail. -/
def hq_big : Cmd :=
  .seq (copyVia 4 5 10) (.seq (.push 6 true) (.seq hq_outL hq_tail))

/-- The cost of `hq_big`. -/
def hq_Tb (rows : List (List SatSym)) : ℕ :=
  30 * rows.length + 70 + rows.length * (hq_Pr rows rows.length + 1) +
    rows.length * (dp_P rows rows.length + 1)

theorem hq_ex_big (rows : List (List SatSym)) (hsep : ∀ r ∈ rows, sep ∉ r)
    (h1 : 1 ≤ rows.length) :
    ∃ s : hv_HS, ExecLe hq_big
      ({hv_s0 [] (enc rows) with Q := [], N := List.replicate rows.length true} : hv_HS).st
      (.norm s.st) (hq_Tb rows) ∧
      s.R = rv (hq_rows rows 0 rows.length ++ hq_tailL rows rows.length) := by
  set s2 : hv_HS := {hv_s0 [] (enc rows) with Q := [], N := List.replicate rows.length true}
  have h3 := hv_ex_copy (a := 4) (b := 5) (by decide) (by decide) (by decide) s2.st rfl
  simp only [hv_st4, hv_st5, hv_u5] at h3
  have h4 := ExecLe.push 6 true {s2 with I := s2.N ++ s2.I}.st
  rw [hv_u6] at h4
  have h5 := hq_ex_outL rows hsep rows.length 0 {s2 with I := s2.N ++ s2.I, X := true :: s2.X} []
    (by omega) (by simp [s2]) rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
  set s5 : hv_HS := {s2 with
    I := [], X := dp_oh (0 + rows.length), R := rv ([] ++ hq_rows rows 0 rows.length)}
  have h6 := hq_ex_tA rows hsep h1 s5 ([] ++ hq_rows rows 0 rows.length) rfl rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
  have h7 := hq_ex_tB rows.length
    {s5 with
      X := [true], Y := dp_oh (1 + (rows.length - 1)), K := [],
      R := rv ([] ++ hq_rows rows 0 rows.length ++ [zero] ++ dp_seg rows 0 1 (rows.length - 1))}
    _ rfl rfl rfl rfl
  refine ⟨_, (h3.seq_norm (h4.seq_norm (h5.seq_norm (h6.seq_norm h7)))).cast rfl ?_, ?_⟩
  · simp only [hq_Tb, s5, dp_length_oh]
    simp [s2]; omega
  · simp [hq_tailL]

/-- Everything after parsing. -/
def hq_main : Cmd := .seq (copyVia 1 3 10) (.seq hv_cntL (hq_br hq_big))

/-- The output of the program. -/
def hq_outP (rows : List (List SatSym)) : List SatSym :=
  if rows.length < 3 then [sep, sep] else hq_rows rows 0 rows.length ++ hq_tailL rows rows.length

theorem hq_ex_main (rows : List (List SatSym)) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∃ s : hv_HS, ExecLe hq_main (hv_s0 [] (enc rows)).st (.norm s.st)
      (8 * (enc rows).length + 7 * rows.length + 36 + hq_Tb rows) ∧ s.R = rv (hq_outP rows) := by
  have h1 := hv_ex_copy (a := 1) (b := 3) (by decide) (by decide) (by decide)
    (hv_s0 [] (enc rows)).st rfl
  simp only [hv_st1, hv_st3, hv_u3, List.append_nil] at h1
  have h2 := hv_ex_cntL (rows.flatMap (· ++ [sep])) {hv_s0 [] (enc rows) with Q := enc rows}
    (by simp [enc])
  rw [hv_count_sep rows hsep] at h2
  simp only [List.append_nil] at h2
  set s2 : hv_HS := {hv_s0 [] (enc rows) with Q := [], N := List.replicate rows.length true}
  have hl : (rows.flatMap (· ++ [sep])).length ≤ (enc rows).length := by
    simp only [enc, length_flatMap_ic]; omega
  by_cases h3 : 3 ≤ rows.length
  · obtain ⟨sb, hb, hR⟩ := hq_ex_big rows hsep (by omega)
    have hbr := hq_ex_br rows.length s2 rfl rfl rfl rfl hq_big (.norm sb.st) (hq_Tb rows)
      (fun _ => hb)
    rw [if_pos h3] at hbr
    refine ⟨sb, (h1.seq_norm (h2.seq_norm hbr)).cast rfl (by simp at hl ⊢; omega), ?_⟩
    rw [hq_outP, if_neg (by omega)]; exact hR
  · have hbr := hq_ex_br rows.length s2 rfl rfl rfl rfl hq_big (.norm s2.st) (hq_Tb rows)
      (fun h => absurd h h3)
    rw [if_neg h3] at hbr
    refine ⟨_, (h1.seq_norm (h2.seq_norm hbr)).cast rfl (by simp at hl ⊢; omega), ?_⟩
    rw [hq_outP, if_pos (by omega)]

/-! ## The whole program and its running time -/

/-- The reduction program. -/
def hq_redCmd : Cmd := .seq parseLoop (.seq (trimC 4) (.seq (move 4 1) hq_main))

/-- The time bound. -/
def hq_Tred (L : ℕ) : ℕ := 4000 * (L + 2) ^ 4

theorem hq_bound_aux (L n t Q : ℕ) (hn : n ≤ L) (ht : t ≤ L) (hQ : Q ≤ 400 * ((L + 2) * (L + 2))) :
    (2 * L + 3) + (4 * L + 6) + (2 * (2 * t) + 2) + (8 * (2 * t) + 7 * n + 36 +
      (30 * n + 70 + n * (n * Q + 7 * n + 20 + 6 + 1) + n * Q)) ≤ hq_Tred L := by
  unfold hq_Tred
  generalize hA : L + 2 = A at hQ
  have hn' : n ≤ A := by omega
  have ht' : t ≤ A := by omega
  have hA2 : 2 ≤ A := by omega
  have h1 : n * Q ≤ 400 * (A * A * A) := by
    calc n * Q ≤ A * (400 * (A * A)) := Nat.mul_le_mul hn' hQ
      _ = 400 * (A * A * A) := by ring
  have hAA : 2 * A ≤ A * A := Nat.mul_le_mul_right A hA2
  have hAAA : 2 * (A * A) ≤ A * A * A := by
    have := Nat.mul_le_mul_right (A * A) hA2; linarith
  have hA4 : 2 * (A * A * A) ≤ A * (A * A * A) := by
    have := Nat.mul_le_mul_right (A * A * A) hA2; linarith
  have h2 : n * (n * Q + 7 * n + 20 + 6 + 1) ≤ 400 * (A * (A * A * A)) + 34 * (A * A) := by
    calc _ ≤ A * (400 * (A * A * A) + 34 * A) := Nat.mul_le_mul hn' (by omega)
      _ = 400 * (A * (A * A * A)) + 34 * (A * A) := by ring
  have e : A ^ 4 = A * (A * A * A) := by ring
  rw [e]
  omega

theorem hq_bound (L n t S : ℕ) (hn : n ≤ L) (ht : t ≤ L) (hS : S ≤ L) :
    (2 * L + 3) + (4 * L + 6) + (2 * (2 * t) + 2) + (8 * (2 * t) + 7 * n + 36 +
      (30 * n + 70 +
        n * (n * (2 * (5 * (2 * t) + 26 * n + (10 * S + n * (7 * n + 20) + 2 * n + 8) + 24) + 7
          + 1) + 7 * n + 20 + 6 + 1) +
        n * (2 * (5 * (2 * t) + 26 * n + (10 * S + n * (7 * n + 20) + 2 * n + 8) + 24) + 7 + 1)))
      ≤ hq_Tred L := by
  apply hq_bound_aux L n t _ hn ht
  have hn' : n ≤ L + 2 := by omega
  nlinarith [Nat.mul_le_mul hn' hn']

theorem hq_exec_redCmd (x : Str) : ∃ σ', ExecLe hq_redCmd (init [x]).stk (.norm σ')
    (hq_Tred x.length) ∧ σ' 0 = ((hq_outP (clauses (FunBridge.dec2 x))).flatMap ic).reverse := by
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
  obtain ⟨s, p4, hs⟩ := hq_ex_main (clauses w) (sep_not_mem_clauses w)
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm p4))).cast rfl ?_, ?_⟩
  · have htl : (σ₂ 4).length = 2 * (trunc w).length := by
      simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
    have hen : (enc (clauses w)).length = 2 * (trunc w).length := by
      simp only [enc, trunc, length_flatMap_ic]
    simp only [hq_Tb, hq_Pr, dp_Pr, dp_P, hv_Tsc_eq, htl, hen]
    have hb := hq_bound x.length (clauses w).length (trunc w).length
      ((clauses w).map List.length).sum (by omega) (by omega) (by omega)
    omega
  · rw [hv_st0, hs]; rfl

theorem hq_Tred_le (n : ℕ) : hq_Tred n ≤ tb 16 n := by
  unfold hq_Tred tb
  have h12 : 2 ^ 12 ≤ (n + 2) ^ 12 := Nat.pow_le_pow_left (by omega) 12
  have e : (n + 2) ^ 16 = (n + 2) ^ 12 * (n + 2) ^ 4 := by ring
  rw [e]
  have : 4000 ≤ (n + 2) ^ 12 := le_trans (by norm_num) h12
  exact Nat.mul_le_mul_right _ this

theorem hq_outP_eq (w : List SatSym) : hq_outP (clauses w) = hpI w := by
  by_cases h3 : 3 ≤ (clauses w).length
  · rw [hq_outP, if_neg (by omega)]; exact hq_out_eq w h3
  · rw [hq_outP, if_pos (by omega), hpI, if_pos (by omega)]

/-! ## The reduction -/

/-- **HAMILTONIAN CYCLE ≤ₚ HAMILTONIAN PATH** (official polynomial-time many-one reducibility),
given the correctness of the reduction instance `hpI`. -/
theorem uham_le_uhpath_of (h : ∀ w, UHamLang w ↔ UHPathLang (hpI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) UHamLang UHPathLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    hq_redCmd 0 16 (fun x => hpI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := hq_exec_redCmd x
      exact ⟨σ', h1.mono (hq_Tred_le _), by rw [h2, hq_outP_eq]⟩)
    hpI (fun t => (congrArg hpI (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨hpI, hc, h⟩

end Pnp.Karp.Ham
