import Pnp.Karp.ThreePartUProgB

/-!
# Unary 3-PARTITION reduction program, part E: the transformer computes the instance

`tpup_F_DMI`: on the 3DM instance `DMI w`, the transformer `tpup_F` outputs `TPUI w`.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.ThreePartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.BinPacking Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

/-- The unary row of an item. -/
abbrev tpupe_row (q M : ℕ) (x : El) : List SatSym := uRow (uval q M x)

theorem tpupe_item {cnt : ℕ → ℕ} {q M : ℕ} (ip : ℕ → ℕ × ℕ) (x : El) (sp : List (List ℕ))
    (hs : sp = tpup_sp ip x) (hF : tpup_FH cnt q M)
    (hI : ∀ c' < 3, tpup_okS cnt q (ip c') (shI x c'))
    (hL : ∀ c' < 3, tpup_okS cnt M (5, 6) (shL x c')) :
    tpup_itO cnt (uR M) sp = tpupe_row q M x ++ [sep] := by
  subst hs; exact tpup_sp_val ip x hF hI hL

theorem tpupe_blkO_eq {q M : ℕ} (cnt : ℕ → ℕ) :
    ∀ (its : List (List (List ℕ))) (xs : List El),
    List.Forall₂ (fun ds x => tpup_itO cnt (uR M) ds = tpupe_row q M x ++ [sep]) its xs →
    tpup_blkO cnt (uR M) its = (xs.map (tpupe_row q M)).flatMap (· ++ [sep])
  | [], [], _ => rfl
  | p :: ps, x :: xs, h => by
    rcases List.forall₂_cons.1 h with ⟨h1, h2⟩
    simp only [tpup_blkO, List.flatMap_cons, List.map_cons] at h1 ⊢
    rw [h1]
    exact congrArg _ (tpupe_blkO_eq cnt ps xs h2)

theorem tpupe_pf_oh {q a : ℕ} (h : a < q) : tpup_pf (ohB q a) = a := by
  rw [← tpp_tagB q a h, tagB, tpup_pf_tag]

theorem tpupe_sf_oh {q a : ℕ} (h : a < q) : (tpup_sf (ohB q a)).length = q - 1 - a := by
  rw [← tpp_tagB q a h, tagB, tpup_sf_tag, List.length_replicate]

theorem tpupe_row_eq (q M t : ℕ) (_ht : t < M) (x : ℕ × ℕ × ℕ)
    (hx : x.1 < q ∧ x.2.1 < q ∧ x.2.2 < q) :
    tpup_rowO q M (triRow q x) t = ((triBlk t x).map (tpupe_row q M)).flatMap (· ++ [sep]) := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨ha, hb, hc⟩ := hx
  dsimp only at ha hb hc
  have hr : (triRow q (a, b, c)).map tpp_bb = ohB q a ++ ohB q b ++ ohB q c := by
    simp [triRow, tpp_oh_bb]
  have hR : ((triRow q (a, b, c)).map tpp_bb).reverse =
      (ohB q c).reverse ++ (ohB q b).reverse ++ (ohB q a).reverse := by
    rw [hr]; simp
  have eC : (((triRow q (a, b, c)).map tpp_bb).reverse.take q).reverse = ohB q c := by
    rw [hR, List.append_assoc, List.take_left' (by simp)]; simp
  have eB : ((((triRow q (a, b, c)).map tpp_bb).reverse.drop q).take q).reverse = ohB q b := by
    rw [hR, List.append_assoc, List.drop_left' (by simp), List.take_left' (by simp)]; simp
  have eA : ((((triRow q (a, b, c)).map tpp_bb).reverse.drop q).drop q).reverse = ohB q a := by
    rw [hR, List.append_assoc, List.drop_left' (by simp), List.drop_left' (by simp)]; simp
  unfold tpup_rowO
  simp only []
  rw [eA, eB, eC]
  have pa := tpupe_pf_oh ha; have pb := tpupe_pf_oh hb; have pc := tpupe_pf_oh hc
  have sa := tpupe_sf_oh ha; have sb := tpupe_sf_oh hb; have sc := tpupe_sf_oh hc
  have hF : tpup_FH (tpup_rc q M t (ohB q a) (ohB q b) (ohB q c)) q M := by
    simp [tpup_FH, tpup_rc, tpup_fc]
  apply tpupe_blkO_eq
  simp only [tpup_rowSp, triBlk, List.map_cons, List.map_nil, List.forall₂_cons,
    List.Forall₂.nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    refine tpupe_item tpup_ipR _ _ ?_ hF ?_ ?_ <;>
    first
    | rfl
    | (intro c' hc'; interval_cases c' <;>
        simp [tpup_okS, shI, shL, tpup_ipR, tpup_rc, pa, pb, pc, sa, sb, sc])

theorem tpupe_gad_eq (q K M c e : ℕ) (hc : c < 3) (_he : e < q) (_hP : K + c * q + e < M) :
    tpup_blkO (tpup_gc q M (K + c * q + e) e) (uR M) (tpup_gadSp c) =
      ((gadBlk q K c e).map (tpupe_row q M)).flatMap (· ++ [sep]) := by
  have hF : tpup_FH (tpup_gc q M (K + c * q + e) e) q M := by
    simp [tpup_FH, tpup_gc, tpup_fc]
  apply tpupe_blkO_eq
  interval_cases c <;>
  simp only [tpup_gadSp, gadBlk, List.map_cons, List.map_nil, List.forall₂_cons,
    List.Forall₂.nil, and_true] <;>
  refine ⟨?_, ?_, ?_⟩ <;>
    refine tpupe_item (fun _ => (12, 13)) _ _ ?_ hF ?_ ?_ <;>
    first
    | rfl
    | (intro c' hc'; interval_cases c' <;> simp [tpup_okS, shI, shL, tpup_gc])

theorem tpupe_gadO_eq (q K M c : ℕ) (hc : c < 3) (hM : K + 3 * q ≤ M) :
    tpup_gadO q K M c = (((List.range q).flatMap fun e => gadBlk q K c e).map
      (tpupe_row q M)).flatMap (· ++ [sep]) := by
  unfold tpup_gadO
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro e he
  rw [List.mem_range] at he
  apply tpupe_gad_eq q K M c e hc he
  have : c * q + q ≤ 3 * q := by
    have := Nat.mul_le_mul_right q (show c + 1 ≤ 3 by omega); rw [Nat.add_mul] at this; omega
  omega

theorem tpupe_bO_eq (q M : ℕ) : tpup_bO q M = uRow (uB M) ++ [sep] := by
  simp only [tpup_bO, tpup_blkO, tpup_bSp, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    tpup_itO, tpup_iv_eq, pow_zero, one_mul, uB]
  simp [tpup_fc]

theorem tpupe_rows_eq (q M : ℕ) : ∀ (ts : List (ℕ × ℕ × ℕ)) (t : ℕ), t + ts.length ≤ M →
    (∀ x ∈ ts, x.1 < q ∧ x.2.1 < q ∧ x.2.2 < q) →
    tpup_rowsO q M (ts.map (triRow q)) t =
      (((List.range ts.length).flatMap fun l => triBlk (t + l) (ts.getD l (0, 0, 0))).map
        (tpupe_row q M)).flatMap (· ++ [sep])
  | [], t, _, _ => rfl
  | x :: ts, t, h, hx => by
    have ih := tpupe_rows_eq q M ts (t + 1) (by simp at h; omega)
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, tpup_rowsO, List.length_cons, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map, List.getD_cons_zero, List.getD_cons_succ,
      Nat.add_zero, List.map_append, List.flatMap_append]
    have hf : (fun a => triBlk (t + (a + 1)) (ts.getD a (0, 0, 0))) =
        fun l => triBlk (t + 1 + l) (ts.getD l (0, 0, 0)) :=
      funext fun l => by rw [show t + (l + 1) = t + 1 + l by omega]
    rw [hf, ih, tpupe_row_eq q M t (by simp at h; omega) x (hx x List.mem_cons_self),
      List.flatMap_map, List.flatMap_map]

/-- **The transformer maps the 3DM instance to the unary 3-PARTITION instance.** -/
theorem tpup_F_DMI (w : List SatSym) : tpup_F (DMI w) = TPUI w := by
  have hc : clauses (DMI w) = List.replicate (qB w) zero :: triRows w := by
    unfold DMI
    apply Pnp.Karp.Clique.clauses_flatMap
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · simp
    · simp only [triRows, List.mem_map] at hc
      obtain ⟨t, -, rfl⟩ := hc
      simp only [triRow, oh, List.mem_append, List.mem_map, not_or]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro ⟨i, -, hi⟩ <;> split_ifs at hi
  have hlt := dr_tris_lt w
  unfold tpup_F tpup_Fc
  rw [hc]
  simp only [List.headD_cons, List.tail_cons, List.length_replicate, triRows, List.length_map]
  unfold TPUI TPUW els mT
  set q := qB w
  set ts := tris w
  rw [tpupe_rows_eq q _ ts 0 (by omega) hlt, tpp_range3, tpupe_gadO_eq q _ _ 0 (by omega) le_rfl,
    tpupe_gadO_eq q _ _ 1 (by omega) le_rfl, tpupe_gadO_eq q _ _ 2 (by omega) le_rfl,
    tpupe_bO_eq]
  simp only [List.map_append, List.flatMap_append, Nat.zero_add, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

end Pnp.Karp.ThreePartU
