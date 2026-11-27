import Pnp.Karp.VertexCover

/-!
# The reduction SAT ≤ₚ VERTEX COVER

For a formula `w` with `m` finished clauses, the INDEPENDENT SET instance `cmap (G w)`
(`Pnp/Karp/IndSet.lean`) has `n = |trunc w| + 1` vertices and bound `k = m + 1 ≤ n`.  The VERTEX
COVER instance `cmap (GV w)` has the same adjacency rows and bound `n - k = |trunc w| - m`, the
number of non-`sep` symbols of `trunc w` (`kRowV`), so
`sat_iff_vc : SATLang w ↔ VCLang (cmap (GV w))` follows from `sat_iff_is` and
`isBody_iff_vcBody`.

`redCmdV` is the CLIQUE reduction program `redCmd` (`Pnp/Karp/CliqueProg.lean`) with the header
replaced: `hdrCV` prints one `zero` per non-`sep` symbol of `trunc w`, then `sep`.  Composed with
the complement map (`cmap_computable`) this gives `sat_le_vc : SATLang ≤ₚ VCLang`.
-/

namespace Pnp.Karp.VertexCover

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.IndSet

/-! ## The instance -/

/-- Header symbols: one `zero` per non-`sep` symbol. -/
def hgV (s : SatSym) : List SatSym := if s = sep then [] else [zero]

/-- The row encoding the bound `n - k`. -/
def kRowV (w : List SatSym) : List SatSym := (trunc w).flatMap hgV

/-- The (uncomplemented) VERTEX COVER instance of the formula `w`. -/
def GV (w : List SatSym) : List SatSym := (kRowV w :: gRows w).flatMap (· ++ [sep])

theorem hgV_row : ∀ c : List SatSym, sep ∉ c → c.flatMap hgV = List.replicate c.length zero
  | [], _ => rfl
  | s :: c, h => by
    have hs : s ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    simp [hgV, hs, hgV_row c (fun e => h (List.mem_cons_of_mem _ e)), List.replicate_succ]

theorem length_hgV_rows : ∀ L : List (List SatSym), (∀ c ∈ L, sep ∉ c) →
    ((L.flatMap (· ++ [sep])).flatMap hgV).length = (L.map List.length).sum
  | [], _ => rfl
  | c :: L, h => by
    simp only [List.flatMap_cons, List.flatMap_append, hgV_row c (h c (by simp)),
      List.length_append, List.length_replicate, List.map_cons, List.sum_cons,
      length_hgV_rows L (fun c' hc' => h c' (by simp [hc']))]
    simp [hgV]

theorem length_kRowV (w : List SatSym) :
    (kRowV w).length + (clauses w).length = (trunc w).length := by
  rw [kRowV, trunc, length_hgV_rows _ (sep_not_mem_clauses w)]
  exact sum_length_le _

theorem sep_not_mem_kRowV (w : List SatSym) : sep ∉ kRowV w := by
  simp only [kRowV, List.mem_flatMap, not_exists, not_and]
  intro s _ h; unfold hgV at h; split at h <;> simp_all

theorem clauses_GV (w : List SatSym) : clauses (GV w) = kRowV w :: gRows w := by
  refine clauses_flatMap _ fun c hc => ?_
  rcases List.mem_cons.1 hc with rfl | hc
  · exact sep_not_mem_kRowV w
  · exact sep_not_mem_gRows w c hc

/-- **Correctness of the reduction SAT ≤ VERTEX COVER.** -/
theorem sat_iff_vc (w : List SatSym) : SATLang w ↔ VCLang (cmap (GV w)) := by
  rw [sat_iff_is]
  unfold ISLang VCLang
  rw [clauses_cmap, clauses_cmap, clauses_G, clauses_GV]
  simp only [List.map_cons]
  have hlen := length_kRowV w
  have hrows : (gRows w).length = (trunc w).length + 1 := by
    simp [gRows, annW, length_ann]
  refine isBody_iff_vcBody _ _ _ ?_ ?_
  · simp [kRow]; omega
  · simp [kRow]; omega

/-! ## The program -/

def hdrCV : Cmd := .seq (copyVia 2 4 11) (.seq (mapLoop hgV) (emL [sep]))

def redCmdV : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq hdrCV (.seq uRowC (.seq initO outerLoop)))))

/-- The output of the program equals `GV w`. -/
theorem out_eqV (w : List SatSym) :
    [] ++ ((trunc w).flatMap hgV ++ [sep]) ++ ([zero] ++ (trunc w).flatMap
      (fun s => [ent (isLit s)]) ++ [sep]) ++
      (ann (trunc w) 0 0).flatMap (fun a => vRow (annW w) a ++ [sep]) = GV w := by
  simp only [GV, gRows, kRowV, litRow, annW, List.flatMap_cons, List.nil_append,
    List.append_assoc]
  congr 1
  simp only [List.cons_append, List.cons.injEq, true_and]
  have e : (trunc w).flatMap (fun s => [ent (isLit s)]) =
      (ann (trunc w) 0 0).map fun b => ent (isLit b.1) := by
    conv_lhs => rw [← ann_fst (trunc w) 0 0]
    rw [List.flatMap_map, flatMap_single]
  rw [e]
  congr 1
  simp [List.flatMap_map]

theorem exec_redCmdV (x : Str) :
    ∃ σ', ExecLe redCmdV (init [x]).stk (.norm σ') (Tred x.length) ∧
      σ' 1 = ((GV (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  set L := trunc w
  set W := L.flatMap ic
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have hLw : L.length ≤ w.length := length_trunc_le w
  have hW : W.length = 2 * L.length := length_flatMap_ic L
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
      st2 W [] [] (rv []) fun _ => 0 := by
    funext j
    simp only [σ2, σ1, Clique.st2, update_apply, rv_nil, W, L]
    split_ifs <;> simp_all
  rw [e3] at p3
  -- header
  have q1 := ex_copyW (W := W) (O := []) (rv []) (fun _ => 0) rfl
  have q2 := ex_mapLoop W [] (fun _ => 0) hgV (fun s => by unfold hgV; split_ifs <;> simp) L []
  have q3 := ex_emL (W := W) (O := []) (Q := []) [sep] ([] ++ L.flatMap hgV) (fun _ => 0)
  set E1 := [] ++ L.flatMap hgV ++ [sep]
  -- universal row
  have r1 := ex_emL (W := W) (O := []) (Q := []) [zero] E1 (fun _ => 0)
  have r2 := ex_copyW (W := W) (O := []) (rv (E1 ++ [zero])) (fun _ => 0) rfl
  have r3 := ex_mapLoop W [] (fun _ => 0) (fun s => [ent (isLit s)]) (fun s => by simp) L
    (E1 ++ [zero])
  have r4 := ex_emL (W := W) (O := []) (Q := []) [sep]
    (E1 ++ [zero] ++ L.flatMap fun s => [ent (isLit s)]) (fun _ => 0)
  set E2 := E1 ++ [zero] ++ (L.flatMap fun s => [ent (isLit s)]) ++ [sep]
  -- outer loop
  have i1 : ExecLe (copyVia 2 3 11) (st2 W [] [] (rv E2) fun _ => 0)
      (.norm (st2 W W [] (rv E2) fun _ => 0)) (5 * W.length + 4) := by
    refine (ExecLe.of (exec_copyVia (a := 2) (b := 3) (t := 11) (by decide) (by decide)
      (by decide) _ (by rw [st2_reg (by norm_num)]; rfl))).cast ?_ (by simp)
    rw [st2_2, st2_3, List.append_nil, upd2_3]
  have i2 := ex_push_reg (W := W) (O := W) (Q := []) (r := 5) (by norm_num) (rv E2) (fun _ => 0)
  obtain ⟨v', o1⟩ := ex_outer L (annW w) rfl L 0 0 E2
    (update (fun _ : ℕ => (0 : ℕ)) 5 ((fun _ : ℕ => (0 : ℕ)) 5 + 1))
    ⟨by simp, by simp, by simp, by simp,
      by simp, by simp, by simp⟩ (by omega)
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm
    ((q1.seq_norm (q2.seq_norm q3)).seq_norm
    ((r1.seq_norm (r2.seq_norm (r3.seq_norm r4))).seq_norm ((i1.seq_norm i2).seq_norm o1)))))).cast
    rfl ?_, ?_⟩
  · simp only [σ2, update_self, List.length_reverse, hW, Tred, List.length_cons, List.length_nil,
      rowT]
    have : L.length ≤ x.length := by omega
    have h1 : L.length * (7 * L.length * L.length + 80 * L.length + 100) ≤
        x.length * (7 * x.length * x.length + 80 * x.length + 100) :=
      Nat.mul_le_mul this (by nlinarith)
    nlinarith
  · simp only [st2_1, rv]
    congr 2
    simp only [E2, E1, List.append_assoc]
    rw [← out_eqV w]
    simp only [List.append_assoc, List.nil_append]
    rfl

/-! ## The reduction -/

/-- `GV` is polynomial-time computable. -/
theorem GV_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    GV) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    redCmdV 1 10 (fun x => GV (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := exec_redCmdV x
      exact ⟨σ', h1.mono (Tred_le _), h2⟩)
    GV (fun t => (congrArg GV (FunBridge.dec2_flatMap_ic t)).symm)

/-- **SAT ≤ₚ VERTEX COVER** (official polynomial-time many-one reducibility). -/
theorem sat_le_vc :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang VCLang := by
  obtain ⟨hG⟩ := GV_computable
  obtain ⟨hc⟩ := cmap_computable
  exact ⟨cmap ∘ GV, Pnp.TM2Comp.comp hG hc, sat_iff_vc⟩

end Pnp.Karp.VertexCover
