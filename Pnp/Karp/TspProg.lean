import Pnp.Karp.Tsp
import Pnp.Karp.DHamProg

/-!
# The TRAVELING SALESMAN reduction program: HAMILTONIAN CYCLE ≤ₚ TRAVELING SALESMAN

`tp_redCmd`, on the bit string `x` on stack `0`, prints `tspI w` (`w = dec2 x`,
`Pnp/Karp/Tsp.lean`) on stack `0`.  It is the program `dp_redCmd` of
`Pnp/Karp/DHamProg.lean` with two changes:

1. before the rows it prints one `sep` (the empty budget row);
2. for each entry `(u, v)` it prints `neg` when the flag `dp_e rows u v` is set (weight `0`, the
   empty chunk) and `pos neg` otherwise (weight `1`).

The scans (`hv_scanP`) and the loop structure are those of `dp_redCmd`, and the costs are the
same (`dp_P`, `dp_Pr`), so `tp_exec_redCmd` bounds the run by `2001 (|x| + 2)^4 ≤ tb 15 |x|`, and
`uham_le_tsp_of` follows from `FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.Tsp

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.Ham

/-! ## The printed entries -/

/-- The chunk of an entry followed by `neg`: weight `0` on an edge, weight `1` otherwise. -/
def tp_sym (b : Bool) : List SatSym := if b then [neg] else [pos, neg]

theorem tp_sym_e (w : List SatSym) (u v : ℕ) :
    tp_sym (dp_e (clauses w) u v) = tEnt w u v ++ [neg] := by
  have h := dp_sym_e w u v
  unfold tp_sym tEnt
  cases hb : dp_e (clauses w) u v <;> simp only [dp_sym, hb] at h <;>
    split_ifs at h ⊢ <;> simp_all

/-- The row `u` printed by the program. -/
def tp_rowL (rows : List (List SatSym)) (n u : ℕ) : List SatSym :=
  (List.range n).flatMap fun v => tp_sym (dp_e rows u v)

/-- The entries `v, …, v + k - 1` of row `u`. -/
def tp_seg (rows : List (List SatSym)) (u v k : ℕ) : List SatSym :=
  (List.range' v k).flatMap fun v => tp_sym (dp_e rows u v)

/-- The rows `u, …, u + k - 1`, each followed by `sep`. -/
def tp_rows (rows : List (List SatSym)) (u k : ℕ) : List SatSym :=
  (List.range' u k).flatMap fun u => tp_rowL rows rows.length u ++ [sep]

theorem tp_out_eq (w : List SatSym) :
    [sep] ++ tp_rows (clauses w) 0 (clauses w).length = tspI w := by
  rw [tspI, List.flatMap_cons, List.flatMap_map, List.range_eq_range', tp_rows]
  congr 2; funext u
  simp only [tp_rowL, tRow, tp_sym_e, List.range_eq_range']

/-! ## The program -/

/-- Print the entry for the flag `H`. -/
def tp_out : Cmd := .pop 14 (dp_em [pos, neg]) (dp_em [pos, neg]) (dp_em [neg])

theorem tp_ex_out (b : Bool) (s : hv_HS) (E : List SatSym) (hR : s.R = rv E)
    (hH : s.H = CookLevin.fl b) :
    ExecLe tp_out s.st (.norm {s with H := [], R := rv (E ++ tp_sym b)}.st) 6 := by
  cases b
  · exact (ExecLe.pop_nil (by simp [hH, CookLevin.fl]) (dp_ex_em [pos, neg] E s hR)).cast
      (by congr 1; cases s; simp_all [tp_sym, CookLevin.fl]) (by simp)
  · refine (ExecLe.pop_cons (b := true) (s := [])
      (r := .norm ({s with H := [], R := rv (E ++ [neg])} : hv_HS).st) (T := 3)
      (by simp [hH, CookLevin.fl]) ?_).cast (by simp [tp_sym]) (by omega)
    rw [hv_u14, if_pos rfl]; exact dp_ex_em [neg] E {s with H := []} hR

/-- One entry `(u, v)`. -/
def tp_pair : Cmd :=
  .seq (hv_scanP 6 7) (.seq (hv_scanP 7 6) (.seq tp_out (.push 7 false)))

theorem tp_ex_pair (rows : List (List SatSym)) (Nb : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r)
    (s : hv_HS) (E : List SatSym) (u v : ℕ) (hc : dp_Cl rows s)
    (hX : s.X = dp_oh u) (hY : s.Y = dp_oh v) (hu : u < Nb) (hv : v < Nb) (hR : s.R = rv E) :
    ExecLe tp_pair s.st
      (.norm {s with R := rv (E ++ tp_sym (dp_e rows u v)), Y := dp_oh (v + 1)}.st)
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
  have h3 := tp_ex_out (dp_e rows u v) {s with H := CookLevin.fl (dp_e rows u v)} E hR rfl
  have h4 := ExecLe.push 7 false
    ({s with H := [], R := rv (E ++ tp_sym (dp_e rows u v))} : hv_HS).st
  rw [hv_u7] at h4
  have h2' := h2.cast (congrArg (fun t : hv_HS => Res.norm t.st) e2) le_rfl
  refine (h1.seq_norm (h2'.seq_norm (h3.seq_norm h4))).cast ?_ ?_
  · congr 1; cases s; simp_all [dp_oh]
  · simp only [dp_P]; omega

/-- The inner loop over `v`, counter `K`. -/
def tp_inL : Cmd := .loop (.pop 11 .brk tp_pair tp_pair)

theorem tp_ex_inL (rows : List (List SatSym)) (Nb : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) (u : ℕ)
    (hu : u < Nb) : ∀ (k v : ℕ) (s : hv_HS) (E : List SatSym), v + k ≤ Nb →
    s.K = List.replicate k true → dp_Cl rows s → s.X = dp_oh u → s.Y = dp_oh v →
    s.R = rv E →
    ExecLe tp_inL s.st
      (.norm {s with R := rv (E ++ tp_seg rows u v k), Y := dp_oh (v + k), K := []}.st)
      (k * (dp_P rows Nb + 1) + 2)
  | 0, v, s, E, _, hK, _, _, hY, hR =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hK]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all [tp_seg]) (by omega)
  | k + 1, v, s, E, hk, hK, hc, hX, hY, hR => by
    have hp := tp_ex_pair rows Nb hsep {s with K := List.replicate k true} E u v
      ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ hX hY hu (by omega) hR
    have ih := tp_ex_inL rows Nb hsep u hu k (v + 1)
      {s with K := List.replicate k true, R := rv (E ++ tp_sym (dp_e rows u v)),
              Y := dp_oh (v + 1)} (E ++ tp_sym (dp_e rows u v)) (by omega) rfl
      ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ hX rfl rfl
    have hb : ExecLe (.pop 11 .brk tp_pair tp_pair) s.st (.norm
        {s with K := List.replicate k true, R := rv (E ++ tp_sym (dp_e rows u v)),
                Y := dp_oh (v + 1)}.st) (dp_P rows Nb + 1) :=
      ExecLe.pop_same (b := true) (s := List.replicate k true)
        (by simp [hK, List.replicate_succ]) (by simpa using hp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by rw [Nat.succ_mul]; omega)
    simp only [tp_seg, List.range'_succ, List.flatMap_cons, List.append_assoc,
      show v + 1 + k = v + (k + 1) by omega]

/-- One row `u`. -/
def tp_row : Cmd :=
  .seq (.push 7 true) (.seq (copyVia 4 11 10) (.seq tp_inL (.seq (drain 7)
    (.seq (dp_em [sep]) (.push 6 false)))))

theorem tp_ex_row (rows : List (List SatSym)) (Nb : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) (u : ℕ)
    (hu : u < Nb) (hn : rows.length ≤ Nb) (s : hv_HS) (E : List SatSym)
    (hN : s.N = List.replicate rows.length true) (hK : s.K = []) (hYe : s.Y = [])
    (hc : dp_Cl rows s) (hX : s.X = dp_oh u) (hR : s.R = rv E) :
    ExecLe tp_row s.st
      (.norm {s with R := rv (E ++ tp_rowL rows rows.length u ++ [sep]), X := dp_oh (u + 1)}.st)
      (dp_Pr rows Nb) := by
  have h1 := ExecLe.push 7 true s.st
  rw [hv_u7, hv_st7, hYe] at h1
  have h2 := hv_ex_copy (a := 4) (b := 11) (by decide) (by decide) (by decide)
    {s with Y := [true]}.st (by simpa using hc.hT)
  simp only [hv_st4, hv_st11, hv_u11] at h2
  have h3 := tp_ex_inL rows Nb hsep u hu rows.length 0 {s with Y := [true], K := s.N ++ s.K} E
    (by omega) (by simp [hK, hN]) ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩
    hX rfl hR
  have h4 := hv_ex_drain 7
    {s with Y := dp_oh (0 + rows.length), K := [],
            R := rv (E ++ tp_seg rows u 0 rows.length)}.st
  simp only [hv_st7, hv_u7] at h4
  have h5 := dp_ex_em [sep] (E ++ tp_seg rows u 0 rows.length)
    {s with Y := [], K := [],
            R := rv (E ++ tp_seg rows u 0 rows.length)} rfl
  have h6 := ExecLe.push 6 false
    ({s with Y := [], K := [],
             R := rv (E ++ tp_seg rows u 0 rows.length ++ [sep])} : hv_HS).st
  rw [hv_u6] at h6
  refine (h1.seq_norm (h2.seq_norm
    (h3.seq_norm (h4.seq_norm (h5.seq_norm h6))))).cast ?_ ?_
  · congr 1; cases s; simp_all [tp_rowL, tp_seg, dp_oh, List.range_eq_range']
  · simp only [dp_Pr, hN, List.length_replicate, dp_length_oh]
    simp; omega

/-- The outer loop over `u`, counter `I`. -/
def tp_outL : Cmd := .loop (.pop 5 .brk tp_row tp_row)

theorem tp_ex_outL (rows : List (List SatSym)) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∀ (k u : ℕ) (s : hv_HS) (E : List SatSym), u + k ≤ rows.length →
    s.I = List.replicate k true → s.N = List.replicate rows.length true → s.K = [] →
    s.Y = [] → dp_Cl rows s → s.X = dp_oh u → s.R = rv E →
    ExecLe tp_outL s.st
      (.norm {s with R := rv (E ++ tp_rows rows u k), X := dp_oh (u + k), I := []}.st)
      (k * (dp_Pr rows rows.length + 1) + 2)
  | 0, u, s, E, _, hI, _, _, _, _, _, _ =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hI]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all [tp_rows]) (by omega)
  | k + 1, u, s, E, hk, hI, hN, hK, hY, hc, hX, hR => by
    have hp := tp_ex_row rows rows.length hsep u (by omega) le_rfl
      {s with I := List.replicate k true} E hN hK hY
      ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ hX hR
    have ih := tp_ex_outL rows hsep k (u + 1)
      {s with I := List.replicate k true, R := rv (E ++ tp_rowL rows rows.length u ++ [sep]),
              X := dp_oh (u + 1)} (E ++ tp_rowL rows rows.length u ++ [sep]) (by omega) rfl hN
      hK hY ⟨hc.hM, hc.hQ, hc.hCC, hc.hG, hc.hT, hc.hH, hc.hRF, hc.hCT⟩ rfl rfl
    have hb : ExecLe (.pop 5 .brk tp_row tp_row) s.st (.norm
        {s with I := List.replicate k true, R := rv (E ++ tp_rowL rows rows.length u ++ [sep]),
                X := dp_oh (u + 1)}.st) (dp_Pr rows rows.length + 1) :=
      ExecLe.pop_same (b := true) (s := List.replicate k true)
        (by simp [hI, List.replicate_succ]) (by simpa using hp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by rw [Nat.succ_mul]; omega)
    simp only [tp_rows, List.range'_succ, List.flatMap_cons, List.append_assoc,
      show u + 1 + k = u + (k + 1) by omega]

/-- Everything after parsing: the budget row, then the matrix rows. -/
def tp_main : Cmd :=
  .seq (copyVia 1 3 10) (.seq hv_cntL (.seq (copyVia 4 5 10) (.seq (.push 6 true)
    (.seq (dp_em [sep]) tp_outL))))

theorem tp_ex_main (rows : List (List SatSym)) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∃ s : hv_HS, ExecLe tp_main (hv_s0 [] (enc rows)).st (.norm s.st)
      (18 * (enc rows).length + 10 * rows.length + 23 +
        rows.length * (dp_Pr rows rows.length + 1)) ∧
      s.R = rv ([sep] ++ tp_rows rows 0 rows.length) := by
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
  have h4' := dp_ex_em [sep] [] {s2 with I := s2.N ++ s2.I, X := true :: s2.X} (by simp [s2])
  have h5 := tp_ex_outL rows hsep rows.length 0
    {s2 with I := s2.N ++ s2.I, X := true :: s2.X, R := rv ([] ++ [sep])} ([] ++ [sep])
    (by omega) (by simp [s2]) rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
  have hall := h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h4'.seq_norm h5))))
  refine ⟨_, hall.cast rfl ?_, by simp⟩
  have hl : (rows.flatMap (· ++ [sep])).length ≤ (enc rows).length := by
    simp only [enc, length_flatMap_ic]; omega
  have hsl := sum_length_le rows
  simp [s2]
  omega

/-- The reduction program. -/
def tp_redCmd : Cmd := .seq parseLoop (.seq (trimC 4) (.seq (move 4 1) tp_main))

/-- The time bound. -/
def tp_Tred (L : ℕ) : ℕ := 2001 * (L + 2) ^ 4

theorem tp_exec_redCmd (x : Str) : ∃ σ', ExecLe tp_redCmd (init [x]).stk (.norm σ')
    (tp_Tred x.length) ∧ σ' 0 = ((tspI (FunBridge.dec2 x)).flatMap ic).reverse := by
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
  obtain ⟨s, p4, hs⟩ := tp_ex_main (clauses w) (sep_not_mem_clauses w)
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm p4))).cast rfl ?_, ?_⟩
  · have htl : (σ₂ 4).length = 2 * (trunc w).length := by
      simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
    have hen : (enc (clauses w)).length = 2 * (trunc w).length := by
      simp only [enc, trunc, length_flatMap_ic]
    simp only [dp_Pr, dp_P, hv_Tsc_eq, htl, hen]
    have hb := dp_bound x.length (clauses w).length (trunc w).length
      ((clauses w).map List.length).sum (by omega) (by omega) (by omega)
    have h4 : 3 ≤ (x.length + 2) ^ 4 := le_trans (by norm_num)
      (Nat.pow_le_pow_left (show 2 ≤ x.length + 2 by omega) 4)
    simp only [dp_Tred] at hb
    simp only [tp_Tred]
    omega
  · rw [hv_st0, hs, tp_out_eq]; rfl

theorem tp_Tred_le (n : ℕ) : tp_Tred n ≤ tb 15 n := by
  unfold tp_Tred tb
  have h11 : 2 ^ 11 ≤ (n + 2) ^ 11 := Nat.pow_le_pow_left (by omega) 11
  have e : (n + 2) ^ 15 = (n + 2) ^ 11 * (n + 2) ^ 4 := by ring
  rw [e]
  have : 2001 ≤ (n + 2) ^ 11 := le_trans (by norm_num) h11
  exact Nat.mul_le_mul_right _ this

/-! ## The reduction -/

/-- **HAMILTONIAN CYCLE ≤ₚ TRAVELING SALESMAN** (official polynomial-time many-one
reducibility), given the correctness of the reduction instance `tspI`. -/
theorem uham_le_tsp_of (h : ∀ w, Pnp.Karp.Ham.UHamLang w ↔ TSPLang (tspI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) Pnp.Karp.Ham.UHamLang TSPLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    tp_redCmd 0 15 (fun x => tspI (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := tp_exec_redCmd x
      exact ⟨σ', h1.mono (tp_Tred_le _), h2⟩)
    tspI (fun t => (congrArg tspI (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨tspI, hc, h⟩

end Pnp.Karp.Tsp
