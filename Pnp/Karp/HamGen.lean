import Pnp.Karp.HamProg
import Pnp.CookLevin.FunBridge

/-!
# The HAMILTONIAN CYCLE reduction program, part 2: the whole program and SAT ≤ₚ UHAM

`hg_redCmd` (loops: `Pnp/Karp/HamProg.lean`), on the bit string `x` on stack `0`:

1. `parseLoop`, `trimC 4`, `move 4 2` (as for CLIQUE): stack `2` holds the code `W` of
   `trunc w`, `w = dec2 x`;
2. `hg_cntLoop`: `N = |trunc w| + 1`, `M = m` (the number of clauses); `D = 3m`;
3. `hg_clLoop`: the rows of the clause vertices (`hg_clP`);
4. `X = 3m`, `J = N`, `hg_jLoop`: the rows of the variable rows (`hg_jP`); `hg_zRows`: the rows
   of the final hub (`hg_zP`).

`hg_H_eq` shows that this prints `H w`; `hg_exec_redCmd` bounds the run by a polynomial, and
`sat_le_ham_of` follows from `FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.Ham

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## The printing form of `H w` -/

theorem hg_range_fm {β : Type} (f : SatSym → List β) : ∀ (c : List SatSym) (N : ℕ),
    c.length ≤ N → (List.range N).flatMap (fun j => f (c.getD j zero)) =
      c.flatMap f ++ (List.replicate (N - c.length) (f zero)).flatten
  | [], 0, _ => rfl
  | [], N + 1, _ => by
    have ih := hg_range_fm f [] N (by simp)
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getD_nil, List.flatMap_nil, List.nil_append, List.length_nil,
      Nat.sub_zero] at ih ⊢
    rw [ih, List.replicate_succ, List.flatten_cons]
  | a :: c, 0, h => by simp at h
  | a :: c, N + 1, h => by
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Nat.succ_eq_add_one, List.getD_cons_succ, List.getD_cons_zero]
    rw [hg_range_fm f c N (by simp at h; omega)]
    simp [List.append_assoc]

local macro "blkt" : tactic => `(tactic| (simp only [List.replicate_add, List.append_assoc,
  List.singleton_append, List.cons_append, List.nil_append]))

theorem hg_zblk (m k : ℕ) (hk : k < m) :
    zs (3 * RW m) = hg_blkP (3 * k) (3 * (m - k - 1)) (zs 21) := by
  unfold hg_blkP
  rw [show 3 * RW m = 3 * (3 * k) + 21 + 3 * (3 * (m - k - 1)) by unfold RW; omega]
  blkt

theorem hg_blkIn_eq (m k : ℕ) (hk : k < m) (a : SatSym) (ha : a ≠ sep) :
    blkIn m k a = hg_blkP (3 * k) (3 * (m - k - 1)) (hg_midIn a) := by
  cases a with
  | sep => exact absurd rfl ha
  | zero => exact hg_zblk m k hk
  | pos =>
    simp only [blkIn, hg_midIn, hg_blkP, one]
    rw [show 11 + 9 * k = 3 * (3 * k) + 11 by ring,
      show 3 * RW m - 12 - 9 * k = 9 + 3 * (3 * (m - k - 1)) by unfold RW; omega]
    blkt
  | neg =>
    simp only [blkIn, hg_midIn, hg_blkP, one]
    rw [show 14 + 9 * k = 3 * (3 * k) + 14 by ring,
      show 3 * RW m - 15 - 9 * k = 6 + 3 * (3 * (m - k - 1)) by unfold RW; omega]
    blkt

theorem hg_blkOut_eq (m k : ℕ) (hk : k < m) (a : SatSym) (ha : a ≠ sep) :
    blkOut m k a = hg_blkP (3 * k) (3 * (m - k - 1)) (hg_midOut a) := by
  cases a with
  | sep => exact absurd rfl ha
  | zero => exact hg_zblk m k hk
  | pos =>
    simp only [blkOut, hg_midOut, hg_blkP, one]
    rw [show 12 + 9 * k = 3 * (3 * k) + 12 by ring,
      show 3 * RW m - 13 - 9 * k = 8 + 3 * (3 * (m - k - 1)) by unfold RW; omega]
    blkt
  | neg =>
    simp only [blkOut, hg_midOut, hg_blkP, one]
    rw [show 9 + 9 * k = 3 * (3 * k) + 9 by ring,
      show 3 * RW m - 10 - 9 * k = 11 + 3 * (3 * (m - k - 1)) by unfold RW; omega]
    blkt

theorem hg_len_le_flatMap {c : List SatSym} : ∀ {L : List (List SatSym)}, c ∈ L →
    c.length ≤ (L.flatMap (· ++ [sep])).length
  | [], h => by simp at h
  | d :: L, h => by
    simp only [List.mem_cons] at h
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
    rcases h with rfl | h
    · omega
    · have := hg_len_le_flatMap h; omega

theorem hg_clause_facts (w : List SatSym) (k : ℕ) (hk : k < mC w) :
    sep ∉ (clauses w).getD k [] ∧ ((clauses w).getD k []).length ≤ NV w := by
  have hmem : (clauses w).getD k [] ∈ clauses w := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  refine ⟨sep_not_mem_clauses w _ hmem, ?_⟩
  have := hg_len_le_flatMap hmem
  unfold NV trunc; omega

theorem hg_inC_eq (w : List SatSym) (k : ℕ) (hk : k < mC w) :
    inC w k ++ [sep] = hg_inP (NV w) (3 * k) (3 * (mC w - k - 1)) ((clauses w).getD k []) := by
  obtain ⟨hs, hl⟩ := hg_clause_facts w k hk
  set c := (clauses w).getD k []
  unfold inC hg_inP
  rw [show (fun j => blkIn (mC w) k (sy w k j)) = fun j => blkIn (mC w) k (c.getD j zero) from rfl,
    hg_range_fm _ c _ hl,
    List.flatMap_congr (fun a ha => hg_blkIn_eq (mC w) k hk a (fun e => hs (e ▸ ha))),
    show blkIn (mC w) k zero = zs (3 * RW (mC w)) from rfl, hg_zblk _ k hk,
    show 3 * mC w - 3 * k - 2 = 3 * (mC w - k - 1) + 1 by omega]
  simp only [one, List.replicate_add, List.append_assoc]
  simp

theorem hg_outC_eq (w : List SatSym) (k : ℕ) (hk : k < mC w) :
    outC w k ++ [sep] = hg_outP (NV w) (3 * k) (3 * (mC w - k - 1)) ((clauses w).getD k []) := by
  obtain ⟨hs, hl⟩ := hg_clause_facts w k hk
  set c := (clauses w).getD k []
  unfold outC hg_outP
  rw [show (fun j => blkOut (mC w) k (sy w k j)) = fun j => blkOut (mC w) k (c.getD j zero)
      from rfl,
    hg_range_fm _ c _ hl,
    List.flatMap_congr (fun a ha => hg_blkOut_eq (mC w) k hk a (fun e => hs (e ▸ ha))),
    show blkOut (mC w) k zero = zs (3 * RW (mC w)) from rfl, hg_zblk _ k hk,
    show 3 * mC w = 3 * k + 3 + 3 * (mC w - k - 1) by omega]
  simp only [List.replicate_add, List.append_assoc]

theorem hg_clP_eq (N : ℕ) : ∀ (l : List (List SatSym)) (k : ℕ), hg_clP N k l =
    (List.range l.length).flatMap (fun i => hg_cl1 N (3 * (k + i)) (3 * (l.length - i - 1))
      (l.getD i []))
  | [], _ => rfl
  | c :: l, k => by
    rw [hg_clP, hg_clP_eq N l (k + 1), List.length_cons, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    simp only [Nat.add_zero, List.getD_cons_zero, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.succ_eq_add_one, List.getD_cons_succ]
    congr 1
    refine List.flatMap_congr fun i hi => ?_
    rw [show k + (i + 1) = k + 1 + i by omega, show l.length + 1 - (i + 1) - 1 = l.length - i - 1
      by omega]

theorem hg_tP_eq : ∀ (n X : ℕ), hg_tP X n = (List.range n).flatMap fun i => hg_vtxN (X + 3 * i)
  | 0, _ => rfl
  | n + 1, X => by
    rw [hg_tP, hg_tP_eq n (X + 3), List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Nat.mul_zero, Nat.add_zero, Nat.succ_eq_add_one]
    congr 1
    refine List.flatMap_congr fun i _ => ?_
    rw [show X + 3 + 3 * i = X + 3 * (i + 1) by ring]

theorem hg_jP_eq (K : ℕ) : ∀ (n X : ℕ),
    hg_jP K X n = (List.range n).flatMap fun j => hg_rowP K (X + j * (3 * K + 12))
  | 0, _ => rfl
  | n + 1, X => by
    rw [hg_jP, hg_jP_eq K n (X + 3 * K + 12), List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp only [Nat.zero_mul, Nat.add_zero, Nat.succ_eq_add_one]
    congr 1
    refine List.flatMap_congr fun i _ => ?_
    rw [show X + 3 * K + 12 + i * (3 * K + 12) = X + (i + 1) * (3 * K + 12) by ring]

theorem hg_outV_sp (m j t : ℕ) (ht : t < 2) :
    outV m j t = two (3 * (m + j * RW m + t) + 3) (3 * (3 * m) + 5) := by
  unfold outV
  have hR : 4 ≤ RW m := by unfold RW; omega
  interval_cases t
  · simp only [d1, d2, if_true]; congr 1
  · simp only [d1, d2, if_true, one_ne_zero, if_false, true_or]
    congr 1

theorem hg_outV_nm (m j t : ℕ) (ht : 2 ≤ t) (ht' : t < RW m) :
    outV m j t = two (3 * (m + j * RW m + t) - 3) 5 := by
  unfold outV d1 d2
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  · omega
  · split_ifs with h
    · rcases h with h | h <;> omega
    · omega

theorem hg_rowsV_eq (m j t : ℕ) (ht : t < RW m) :
    (rowsV m j t).flatMap (· ++ [sep]) = if t < 2
      then hg_vtxS (3 * m) (3 * m + j * (3 * (3 * m) + 12) + 3 * t)
      else hg_vtxN (3 * m + j * (3 * (3 * m) + 12) + 3 * t) := by
  have e : 3 * (m + j * RW m + t) = 3 * m + j * (3 * (3 * m) + 12) + 3 * t := by
    unfold RW; ring
  unfold rowsV
  split_ifs with h
  · rw [hg_outV_sp m j t h, e]; simp [hg_vtxS]
  · rw [hg_outV_nm m j t (by omega) ht, e]; simp [hg_vtxN]

theorem hg_rowj (m j : ℕ) :
    ((List.range (RW m)).flatMap (rowsV m j)).flatMap (· ++ [sep]) =
      hg_rowP (3 * m) (3 * m + j * (3 * (3 * m) + 12)) := by
  set X := 3 * m + j * (3 * (3 * m) + 12)
  have hR : RW m = 3 * m + 2 + 1 + 1 := by unfold RW; ring
  rw [List.flatMap_assoc]
  have e : ∀ t ∈ List.range (RW m), (rowsV m j t).flatMap (· ++ [sep]) = if t < 2
      then hg_vtxS (3 * m) (X + 3 * t) else hg_vtxN (X + 3 * t) :=
    fun t ht => hg_rowsV_eq m j t (List.mem_range.1 ht)
  rw [List.flatMap_congr e, hR, List.range_succ_eq_map, List.range_succ_eq_map]
  simp only [List.flatMap_cons, List.map_cons, List.map_map, List.flatMap_map]
  rw [hg_rowP, hg_tP_eq]
  simp only [Function.comp, Nat.succ_eq_add_one, Nat.zero_add, show (0 : ℕ) < 2 by norm_num,
    show (1 : ℕ) < 2 by norm_num, if_true, Nat.mul_zero, Nat.add_zero, Nat.mul_one,
    List.append_assoc]
  congr 2
  refine List.flatMap_congr fun i _ => ?_
  rw [if_neg (by omega), show X + 3 * (i + 1 + 1) = X + 6 + 3 * i by ring]

/-- **`H w` as printed by the program.** -/
theorem hg_H_eq (w : List SatSym) : H w = hg_clP (NV w) 0 (clauses w) ++
    hg_jP (3 * mC w) (3 * mC w) (NV w) ++
    hg_zP (3 * mC w) (3 * mC w + NV w * (3 * (3 * mC w) + 12)) := by
  unfold H hRows
  rw [List.flatMap_append, List.flatMap_append]
  congr 1
  congr 1
  · rw [List.flatMap_assoc, hg_clP_eq]
    refine List.flatMap_congr fun k hk => ?_
    have hk : k < mC w := List.mem_range.1 hk
    simp only [rowsC, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.zero_add, hg_cl1]
    rw [show (clauses w).length = mC w from rfl, ← hg_inC_eq w k hk, ← hg_outC_eq w k hk]
    rw [one, show 3 * k + 2 = 3 * k + 1 + 1 by ring]
    simp [List.replicate_succ']
  · rw [List.flatMap_assoc, hg_jP_eq]
    exact List.flatMap_congr fun j _ => hg_rowj (mC w) j
  · have e : 3 * (mC w + NV w * RW (mC w)) = 3 * mC w + NV w * (3 * (3 * mC w) + 12) := by
      unfold RW; ring
    simp [rowsZ, hg_zP, e]

/-! ## The whole program -/

theorem hg_cpW3 (W Q : Str) (E : List SatSym) (s : hg_R) :
    ExecLe (copyVia 2 3 11) (hg_S W [] Q E s) (.norm (hg_S W W Q E s)) (5 * W.length + 4) := by
  refine (ExecLe.of (exec_copyVia (a := 2) (b := 3) (t := 11) (by decide) (by decide)
    (by decide) _ (by rw [hg_Sreg _ _ _ _ _ (by norm_num), hg_rg11]; rfl))).cast ?_
    (by simp [hg_S])
  simp only [hg_S, st2_2, st2_3, List.append_nil]; rw [upd2_3]

theorem hg_cpW4 (W O : Str) (E : List SatSym) (s : hg_R) :
    ExecLe (copyVia 2 4 11) (hg_S W O [] E s) (.norm (hg_S W O W E s)) (5 * W.length + 4) :=
  ex_copyW _ _ (hg_rg11 s)

/-- The reduction program. -/
def hg_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq (copyVia 2 4 11) (.seq (.push 5 true)
  (.seq hg_cntLoop (.seq (copyVia 9 8 11) (.seq (copyVia 9 8 11) (.seq (copyVia 9 8 11)
  (.seq (copyVia 2 3 11) (.seq (copyVia 2 4 11) (.seq hg_clLoop (.seq (copyVia 6 12 11)
  (.seq (copyVia 5 13 11) (.seq hg_jLoop hg_zRows))))))))))))))

/-- A bound on all register values. -/
def hg_V (n : ℕ) : ℕ := 12 * (n + 1) * (n + 1)

/-- Time bound of the program. -/
def hg_Tred (n : ℕ) : ℕ :=
  (n + 1) * (hg_Bc (hg_V n) + 1) + (n + 1) * (hg_Bj (hg_V n) + 1) + 30 * hg_V n + 200 * n + 300

set_option maxHeartbeats 800000 in
theorem hg_exec_redCmd (x : Str) : ∃ σ', ExecLe hg_redCmd (init [x]).stk (.norm σ')
    (hg_Tred x.length) ∧ σ' 1 = ((H (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  set L := trunc w
  set W := L.flatMap ic
  set m := mC w
  set N := NV w
  set V := hg_V x.length
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have hLw : L.length ≤ w.length := length_trunc_le w
  have hmw : m ≤ w.length := length_clauses_le w
  have hW : W.length = 2 * L.length := length_flatMap_ic L
  have hN : N = L.length + 1 := rfl
  have hcnt : (L.flatMap hg).length = m := by
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
      hg_S W [] [] [] ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ := by
    simp only [hg_S]; rw [← hg_rg_zero]
    funext j
    simp only [σ2, σ1, Clique.st2, update_apply, rv_nil, W, L]
    split_ifs <;> simp_all
  rw [e3] at p3
  have q1 := hg_cpW4 W [] [] ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
  have q2 := hg_pushN W [] W [] ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
  have q3 : ExecLe hg_cntLoop (hg_S W [] W [] ⟨0 + 1, 0, 0, 0, 0, 0, 0, 0⟩)
      (.norm (hg_S W [] [] [] ⟨N, 0, 0, m, 0, 0, 0, 0⟩)) (4 * L.length + 2) :=
    (hg_ex_cnt W [] L [] ⟨0 + 1, 0, 0, 0, 0, 0, 0, 0⟩).cast
      (by simp only [hcnt]; congr 3 <;> omega) le_rfl
  have q4 := hg_cp9_8 W [] [] [] ⟨N, 0, 0, m, 0, 0, 0, 0⟩
  have q5 := hg_cp9_8 W [] [] [] ⟨N, 0, 0 + m, m, 0, 0, 0, 0⟩
  have q6 : ExecLe (copyVia 9 8 11) (hg_S W [] [] [] ⟨N, 0, 0 + m + m, m, 0, 0, 0, 0⟩)
      (.norm (hg_S W [] [] [] ⟨N, 0, 3 * m, m, 0, 0, 0, 0⟩)) (5 * m + 4) :=
    (hg_cp9_8 W [] [] [] ⟨N, 0, 0 + m + m, m, 0, 0, 0, 0⟩).cast (by congr 3; simp only; omega)
      le_rfl
  have q7 := hg_cpW3 W [] [] ⟨N, 0, 3 * m, m, 0, 0, 0, 0⟩
  have q8 := hg_cpW4 W W [] ⟨N, 0, 3 * m, m, 0, 0, 0, 0⟩
  have hNV : N ≤ V := by simp only [V, hg_V]; nlinarith
  have hmV : 3 * (0 + m) ≤ V := by simp only [V, hg_V]; nlinarith
  have hXV : 3 * m + N * (3 * (3 * m) + 12) ≤ V := by
    have h1 : N * (3 * (3 * m) + 12) ≤ (x.length + 1) * (9 * x.length + 12) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [V, hg_V]; nlinarith
  have q9 := hg_ex_clLoop W N V (clauses w) 0 [] ⟨N, 0, 3 * m, m, 0, 0, 0, 0⟩
    (fun c hc => by
      refine ⟨sep_not_mem_clauses w c hc, ?_⟩
      have := hg_len_le_flatMap hc
      simp only [N, NV, trunc] at this ⊢; omega)
    rfl rfl rfl rfl rfl hNV hmV
  set E1 := [] ++ hg_clP N 0 (clauses w)
  have q10 : ExecLe (copyVia 6 12 11) (hg_S W [] [] E1 ⟨N, 3 * (0 + m), 0, 0, 0, 0, 0, 0⟩)
      (.norm (hg_S W [] [] E1 ⟨N, 3 * m, 0, 0, 0, 3 * m, 0, 0⟩)) (5 * (3 * m) + 4) :=
    (hg_cp6_12 W [] [] E1 ⟨N, 3 * (0 + m), 0, 0, 0, 0, 0, 0⟩).cast (by simp) (by simp)
  have q11 := hg_cp5_13 W [] [] E1 ⟨N, 3 * m, 0, 0, 0, 3 * m, 0, 0⟩
  have q12 := hg_ex_jLoop V W [] [] N E1 ⟨N, 3 * m, 0, 0, 0, 3 * m, 0 + N, 0⟩
    (by simp only; omega) rfl hXV
  have q13 := hg_em_zRows ⟨N, 3 * m, 0, 0, 0, 3 * m + N * (3 * (3 * m) + 12), 0, 0⟩ W [] []
    (E1 ++ hg_jP (3 * m) (3 * m) N)
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm (q1.seq_norm (q2.seq_norm
    (q3.seq_norm (q4.seq_norm (q5.seq_norm (q6.seq_norm (q7.seq_norm (q8.seq_norm (q9.seq_norm
    (q10.seq_norm (q11.seq_norm (q12.seq_norm q13))))))))))))))).cast rfl ?_, ?_⟩
  · simp only [σ2, update_self, List.length_reverse, hW, hg_Tred]
    have hm : m ≤ x.length := by omega
    have hL : L.length ≤ x.length := by omega
    have hNx : N ≤ x.length + 1 := by omega
    have b1 : m * (hg_Bc V + 1) ≤ (x.length + 1) * (hg_Bc V + 1) := Nat.mul_le_mul (by omega) le_rfl
    have b2 : N * (hg_Bj V + 1) ≤ (x.length + 1) * (hg_Bj V + 1) := Nat.mul_le_mul hNx le_rfl
    have hcl : (clauses w).length = m := rfl
    clear p1 p2 p3 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
    have hW' : (List.flatMap ic L).length = 2 * L.length := hW
    rw [show hg_V x.length = V from rfl, hcl, hW']
    have hX18 : 18 * (3 * m + N * (3 * (3 * m) + 12)) ≤ 18 * V := by omega
    generalize 18 * (3 * m + N * (3 * (3 * m) + 12)) = A at hX18 ⊢
    generalize m * (hg_Bc V + 1) = B1 at b1 ⊢
    generalize N * (hg_Bj V + 1) = B2 at b2 ⊢
    generalize (x.length + 1) * (hg_Bc V + 1) = C1 at b1 ⊢
    generalize (x.length + 1) * (hg_Bj V + 1) = C2 at b2 ⊢
    clear_value E1 V N m W L w σ1 σ2
    omega
  · simp only [hg_S1, rv, E1, List.nil_append]
    rw [hg_H_eq w]

theorem hg_Tred_le (n : ℕ) : hg_Tred n ≤ tb 22 n := by
  unfold hg_Tred tb
  set P := n + 2
  set V := hg_V n
  have hP : 2 ≤ P := by omega
  have hV1 : V + 1 ≤ 13 * P ^ 2 := by simp only [V, hg_V, P]; nlinarith
  have hB : hg_Bc V + 1 + (hg_Bj V + 1) ≤ 600 * (V + 1) ^ 2 := by
    unfold hg_Bc hg_Bj; nlinarith
  have hQ : (V + 1) ^ 2 ≤ 169 * P ^ 4 := by
    calc (V + 1) ^ 2 ≤ (13 * P ^ 2) ^ 2 := Nat.pow_le_pow_left hV1 2
      _ = 169 * P ^ 4 := by ring
  have h1 : (n + 1) * (hg_Bc V + 1) + (n + 1) * (hg_Bj V + 1) ≤ P * (600 * (169 * P ^ 4)) := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul (by omega) (le_trans hB (by omega))
  have hP2 : P ^ 2 ≤ P ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hP1 : P ≤ P ^ 5 := by
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hP0 : 1 ≤ P ^ 5 := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 ^ 17 ≤ P ^ 17 := Nat.pow_le_pow_left hP 17
  have e : P ^ 22 = P ^ 17 * P ^ 5 := by ring
  have e5 : P * (600 * (169 * P ^ 4)) = 101400 * P ^ 5 := by ring
  rw [e]
  have h3 : 2 ^ 17 * P ^ 5 ≤ P ^ 17 * P ^ 5 := Nat.mul_le_mul h2 le_rfl
  have hV2 : V ≤ 13 * P ^ 2 := by omega
  norm_num at h3
  omega

/-! ## The reduction -/

/-- **SAT ≤ₚ (undirected) HAMILTONIAN CYCLE** (official polynomial-time many-one
reducibility), given the correctness of the reduction graph `H`. -/
theorem sat_le_ham_of (h : ∀ w, SATLang w ↔ UHamLang (H w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang UHamLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    hg_redCmd 1 22 (fun x => H (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := hg_exec_redCmd x
      exact ⟨σ', h1.mono (hg_Tred_le _), h2⟩)
    H (fun t => (congrArg H (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨H, hc, h⟩

end Pnp.Karp.Ham
