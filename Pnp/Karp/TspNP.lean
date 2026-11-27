import Pnp.Karp.TspVer
import Pnp.Karp.HamNP
import Pnp.Karp.KnapNP

/-!
# TRAVELING SALESMAN ∈ NP (official definition)

The checking relation is `tv_vres w y = true` (`Pnp/Karp/TspVer.lean`): with
`clauses w = Bd :: M` and `n = |M|`, the certificate `y` is read as the blocks `B_i = hv_B n y i`
of `n` bits (as in `Pnp/Karp/HamNP.lean`), and the verifier checks `n ≥ 3`, that every block has
exactly one `true` bit, at a position no earlier block has (`hv_permOk` against `hv_Sacc`), and
that the sum over `i < n` of the values of the extracted chunks `tv_goE B_{i+1} M B_i`
(cyclically) is at most `bv Bd`.  For one-hot blocks at `u` and `v` the extracted chunk is
`wchunk (M.getD u []) v` (`tv_goE_hot`), whose value is `wt M u v`.

* `tv_vres_iff`: this characterization of `tv_vres`;
* `tspLang_iff`: `TSPLang w ↔ ∃ y, |y| ≤ |w|^2 ∧ tv_vres w y`;
* `tsp_in_np`: `TSPLang ∈ NP`, via `tv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.Tsp

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.Ham Pnp.Karp.SubsetSum Pnp.Karp.Knapsack

/-! ## Extraction at one-hot flags -/

theorem tv_headD_eq (C : Str) : C.headD false = C.getD 0 false := by cases C <;> rfl

theorem tv_rowE_false : ∀ (r : List SatSym) (C : Str), tv_rowE r C false = []
  | [], _ => rfl
  | x :: r, C => by
    by_cases hx : x = neg
    · simp only [tv_rowE, hx, if_true]; exact tv_rowE_false r _
    · simp only [tv_rowE, hx, if_false, Bool.false_and, Bool.false_eq_true, List.nil_append]
      exact tv_rowE_false r C

theorem tv_rowE_zero : ∀ (r : List SatSym) (C : Str) (g : Bool),
    (∀ j, C.getD j false = false) → tv_rowE r C g = []
  | [], _, _, _ => rfl
  | x :: r, C, g, h => by
    have h0 : C.headD false = false := by rw [tv_headD_eq]; exact h 0
    by_cases hx : x = neg
    · simp only [tv_rowE, hx, if_true]
      exact tv_rowE_zero r _ g (fun j => by rw [hv_getD_tail]; exact h _)
    · simp only [tv_rowE, hx, if_false, h0, Bool.and_false, Bool.false_eq_true, List.nil_append]
      exact tv_rowE_zero r C g h

theorem tv_wchunk_nil (v : ℕ) : wchunk [] v = [] := by cases v <;> rfl

theorem tv_rowE_hot : ∀ (r : List SatSym) (v : ℕ) (C : Str),
    (∀ j, C.getD j false = decide (j = v)) → tv_rowE r C true = wchunk r v
  | [], v, _, _ => (tv_wchunk_nil v).symm
  | x :: r, 0, C, h => by
    have h0 : C.headD false = true := by rw [tv_headD_eq, h 0]; rfl
    by_cases hx : x = neg
    · simp only [tv_rowE, wchunk, hx, if_true]
      exact tv_rowE_zero r _ true (fun j => by rw [hv_getD_tail, h]; simp)
    · simp only [tv_rowE, wchunk, hx, if_false, h0, Bool.and_self, if_true, List.singleton_append]
      rw [tv_rowE_hot r 0 C h]
  | x :: r, v + 1, C, h => by
    have h0 : C.headD false = false := by rw [tv_headD_eq, h 0]; simp
    by_cases hx : x = neg
    · simp only [tv_rowE, wchunk, hx, if_true]
      exact tv_rowE_hot r v _ (fun j => by rw [hv_getD_tail, h]; simp)
    · simp only [tv_rowE, wchunk, hx, if_false, h0, Bool.and_false, Bool.false_eq_true,
        List.nil_append]
      exact tv_rowE_hot r (v + 1) C h

theorem tv_goE_zero (C : Str) : ∀ (rows : List (List SatSym)) (RF : Str),
    (∀ j, RF.getD j false = false) → tv_goE C rows RF = []
  | [], _, _ => rfl
  | r :: rows, RF, h => by
    have h0 : RF.headD false = false := by rw [tv_headD_eq]; exact h 0
    simp only [tv_goE, h0, tv_rowE_false, List.nil_append]
    exact tv_goE_zero C rows _ (fun j => by rw [hv_getD_tail]; exact h _)

theorem tv_goE_hot (C : Str) (v : ℕ) (hC : ∀ j, C.getD j false = decide (j = v)) :
    ∀ (rows : List (List SatSym)) (RF : Str) (u : ℕ), (∀ j, RF.getD j false = decide (j = u)) →
    tv_goE C rows RF = wchunk (rows.getD u []) v
  | [], _, u, _ => by simp [tv_goE, tv_wchunk_nil]
  | r :: rows, RF, 0, h => by
    have h0 : RF.headD false = true := by rw [tv_headD_eq, h 0]; rfl
    simp only [tv_goE, h0, tv_rowE_hot r v C hC, List.getD_cons_zero]
    rw [tv_goE_zero C rows _ (fun j => by rw [hv_getD_tail, h]; simp), List.append_nil]
  | r :: rows, RF, u + 1, h => by
    have h0 : RF.headD false = false := by rw [tv_headD_eq, h 0]; simp
    simp only [tv_goE, h0, tv_rowE_false, List.nil_append, List.getD_cons_succ]
    exact tv_goE_hot C v hC rows _ u (fun j => by rw [hv_getD_tail, h]; simp)

theorem tv_bval_acc (A : Str) (e : List SatSym) : sv_bval (tv_acc A e) = sv_bval A + bv e := by
  simp [tv_acc, sv_bval_addL, sv_bval_bits]

/-! ## The main loop -/

/-- The value of the chunks extracted at step `i` (the last step `m` wraps to `Z`). -/
def tv_stW (rows : List (List SatSym)) (n : ℕ) (y Z : Str) (m i : ℕ) : ℕ :=
  bv (tv_goE (if i = m then hv_tk n Z else hv_B n y (i + 1)) rows (hv_B n y i))

theorem tv_mainF_iff (rows : List (List SatSym)) (n : ℕ) (y Z B : Str) : ∀ (k j : ℕ) (A : Str),
    tv_mainF rows n Z B k (y.drop ((j + 1) * n)) (hv_B n y j) (hv_Sacc n y j) A = true ↔
      (∀ i, j ≤ i → i ≤ j + k → hv_permOk (hv_B n y i) (hv_Sacc n y i) = true) ∧
        sv_bval A + ∑ t ∈ Finset.range (k + 1), tv_stW rows n y Z (j + k) (j + t) ≤ sv_bval B
  | 0, j, A => by
    rw [tv_mainF, Bool.and_eq_true, kv_le_iff, tv_bval_acc]
    simp only [Nat.zero_add, Finset.sum_range_one, tv_stW, add_zero, if_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi1 hi2 => ?_, h2⟩
      obtain rfl : i = j := by omega
      exact h1
    · rintro ⟨h1, h2⟩
      exact ⟨h1 j le_rfl (by omega), h2⟩
  | k + 1, j, A => by
    have ih := tv_mainF_iff rows n y Z B k (j + 1)
    have e1 : (y.drop ((j + 1) * n)).drop n = y.drop ((j + 1 + 1) * n) := by
      rw [List.drop_drop]; congr 1; ring
    have e2 : hv_tk n (y.drop ((j + 1) * n)) = hv_B n y (j + 1) := rfl
    have e3 : hv_orV (hv_B n y j) (hv_Sacc n y j) = hv_Sacc n y (j + 1) := rfl
    rw [tv_mainF, e1, e2, e3, Bool.and_eq_true, ih, tv_bval_acc]
    have es : ∑ t ∈ Finset.range (k + 1 + 1), tv_stW rows n y Z (j + (k + 1)) (j + t) =
        (∑ t ∈ Finset.range (k + 1), tv_stW rows n y Z (j + 1 + k) (j + 1 + t)) +
          bv (tv_goE (hv_B n y (j + 1)) rows (hv_B n y j)) := by
      rw [Finset.sum_range_succ']
      congr 1
      · refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [show j + 1 + k = j + (k + 1) by omega, show j + 1 + t = j + (t + 1) by omega]
      · simp only [tv_stW, add_zero, if_neg (show j ≠ j + (k + 1) by omega)]
    rw [es]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun i hi1 hi2 => ?_, by omega⟩
      rcases Nat.eq_or_lt_of_le hi1 with rfl | hi1
      · exact h1
      · exact h2 i (by omega) (by omega)
    · rintro ⟨h1, h2⟩
      exact ⟨h1 j le_rfl (by omega), fun i hi1 hi2 => h1 i (by omega) (by omega), by omega⟩

theorem tv_vres_aux (M : List (List SatSym)) (Bd : List SatSym) (y : Str) (hn : 3 ≤ M.length) :
    tv_mainF M M.length (hv_tk M.length y) (sv_bits Bd) (M.length - 1) (y.drop M.length)
      (hv_tk M.length y) (List.replicate M.length false) [] = true ↔
    ((∀ i < M.length, hv_permOk (hv_B M.length y i) (hv_Sacc M.length y i) = true) ∧
      ∑ i ∈ Finset.range M.length,
        bv (tv_goE (hv_B M.length y ((i + 1) % M.length)) M (hv_B M.length y i)) ≤ bv Bd) := by
    set n := M.length
    have h := tv_mainF_iff M n y (hv_tk n y) (sv_bits Bd) (n - 1) 0 []
    have e0 : hv_B n y 0 = hv_tk n y := by simp [hv_B]
    have eS : hv_Sacc n y 0 = List.replicate n false := rfl
    rw [e0, eS, show (0 + 1) * n = n by ring] at h
    rw [h, sv_bval_bits, show sv_bval [] = 0 from rfl, show n - 1 + 1 = n by omega]
    simp only [Nat.zero_add]
    have esum : ∑ t ∈ Finset.range n, tv_stW M n y (hv_tk n y) (n - 1) t =
        ∑ i ∈ Finset.range n, bv (tv_goE (hv_B n y ((i + 1) % n)) M (hv_B n y i)) := by
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have ht : t < n := Finset.mem_range.1 ht
      simp only [tv_stW]
      by_cases hl : t = n - 1
      · rw [if_pos hl, hv_tk_tk, ← e0,
          show (t + 1) % n = 0 by rw [show t + 1 = n by omega, Nat.mod_self]]
      · rw [if_neg hl, Nat.mod_eq_of_lt (by omega)]
    rw [esum]
    refine and_congr_left fun _ => ?_
    constructor
    · intro H i hi; exact H i (by omega) (by omega)
    · intro H i _ hi; exact H i (by omega)

theorem tv_vres_iff (w : List SatSym) (y : Str) :
    tv_vres w y = true ↔ ∃ Bd M, clauses w = Bd :: M ∧ 3 ≤ M.length ∧
      (∀ i < M.length, hv_permOk (hv_B M.length y i) (hv_Sacc M.length y i) = true) ∧
      ∑ i ∈ Finset.range M.length,
        bv (tv_goE (hv_B M.length y ((i + 1) % M.length)) M (hv_B M.length y i)) ≤ bv Bd := by
  unfold tv_vres
  rcases hcw : clauses w with _ | ⟨Bd, M⟩
  · simp
  · have key : (3 ≤ M.length ∧ tv_mainF M M.length (hv_tk M.length y) (sv_bits Bd)
          (M.length - 1) (y.drop M.length) (hv_tk M.length y) (List.replicate M.length false) []
          = true) ↔ (3 ≤ M.length ∧
          (∀ i < M.length, hv_permOk (hv_B M.length y i) (hv_Sacc M.length y i) = true) ∧
          ∑ i ∈ Finset.range M.length,
            bv (tv_goE (hv_B M.length y ((i + 1) % M.length)) M (hv_B M.length y i)) ≤ bv Bd) :=
        and_congr_right fun hn => tv_vres_aux M Bd y hn
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    rw [key]
    constructor
    · intro h; exact ⟨Bd, M, rfl, h⟩
    · rintro ⟨Bd', M', he, h⟩
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact h

/-! ## Short certificates -/

theorem tv_sum_range (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, tv_sum_range f n,
      Finset.sum_range_succ]
    simp

theorem tspLang_iff (w : List SatSym) :
    TSPLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ tv_vres w y = true := by
  have hcl := length_clauses_le w
  unfold TSPLang
  simp only [tv_vres_iff]
  constructor
  · rintro ⟨Bd, M, hw, hn, σ, hp, hcost⟩
    rw [hw] at hcl
    simp only [List.length_cons] at hcl
    set n := M.length
    have hlen : σ.length = n := by simpa using hp.length_eq
    have hnd : σ.Nodup := hp.nodup_iff.mpr List.nodup_range
    set sg : ℕ → ℕ := fun i => σ.getD i 0 with hsgdef
    have hsg : ∀ i < n, sg i < n := fun i hi => by
      have hm : σ.getD i 0 ∈ σ := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      exact List.mem_range.1 (hp.subset hm)
    have hinj : ∀ i < n, ∀ j < n, sg i = sg j → i = j := by
      intro i hi j hj h
      simp only [sg, List.getD_eq_getElem _ _ (show i < σ.length by omega),
        List.getD_eq_getElem _ _ (show j < σ.length by omega)] at h
      exact (hnd.getElem_inj_iff).1 h
    set y : Str := (List.range (n * n)).map fun p => decide (sg (p / n) = p % n) with hy
    have hB : ∀ i < n, ∀ v, (hv_B n y i).getD v false = decide (v = sg i) := by
      intro i hi v
      rw [hv_B_bit]
      by_cases hv : v < n
      · have hp' : i * n + v < n * n := by nlinarith
        simp only [y, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp',
          Option.map_some, Option.getD_some]
        have hn0 : 0 < n := by omega
        rw [show (i * n + v) / n = i by
              rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn0, Nat.div_eq_of_lt hv]; simp,
            show (i * n + v) % n = v by
              rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]]
        simp [hv, eq_comm]
      · have := hsg i hi
        simp only [hv, decide_false, Bool.false_and]
        symm; simp only [decide_eq_false_iff_not]; omega
    refine ⟨y, ?_, Bd, M, hw, hn, fun i hi => ?_, ?_⟩
    · simp only [y, List.length_map, List.length_range]
      have : n * n ≤ w.length * w.length := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    · rw [hv_permOk_iff]
      refine ⟨sg i, hB i hi, ?_⟩
      rcases h : (hv_Sacc n y i).getD (sg i) false
      · rfl
      · obtain ⟨i', hi', h'⟩ := (hv_Sacc_bit n y i (sg i)).1 h
        rw [hB i' (by omega), decide_eq_true_iff] at h'
        have := hinj i hi i' (by omega) h'
        omega
    · refine le_trans (le_of_eq ?_) hcost
      unfold tourCost
      rw [hlen, tv_sum_range]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi : i < n := Finset.mem_range.1 hi
      have hj : (i + 1) % n < n := Nat.mod_lt _ (by omega)
      rw [tv_goE_hot _ (sg ((i + 1) % n)) (hB _ hj) M _ (sg i) (hB i hi)]
      rfl
  · rintro ⟨y, -, Bd, M, hw, hn, H, hsum⟩
    set n := M.length
    have hex : ∀ i, i < n → ∃ u, (∀ v, (hv_B n y i).getD v false = decide (v = u)) ∧
        (hv_Sacc n y i).getD u false = false := fun i hi => (hv_permOk_iff _ _).1 (H i hi)
    choose! sg hsg1 hsg2 using hex
    have hlt : ∀ i < n, sg i < n := by
      intro i hi
      have := hsg1 i hi (sg i)
      rw [hv_B_bit] at this
      simp only [decide_true, Bool.and_eq_true, decide_eq_true_iff] at this
      exact this.1
    have hinj : ∀ i < n, ∀ j < n, sg i = sg j → i = j := by
      intro i hi j hj h
      by_contra hne
      wlog hij : j < i generalizing i j
      · exact this j hj i hi h.symm (Ne.symm hne) (by omega)
      have hb : (hv_B n y j).getD (sg i) false = true := by rw [hsg1 j hj, h]; simp
      have := (hv_Sacc_bit n y i (sg i)).2 ⟨j, hij, hb⟩
      rw [hsg2 i hi] at this
      exact absurd this (by simp)
    refine ⟨Bd, M, hw, hn, (List.range n).map sg, ?_, ?_⟩
    · have hnd : ((List.range n).map sg).Nodup :=
        List.Nodup.map_on (fun a ha b hb h => hinj a (List.mem_range.1 ha) b
          (List.mem_range.1 hb) h) List.nodup_range
      have hsub : (List.range n).map sg ⊆ List.range n := by
        intro x hx
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        simpa using hlt a ha
      exact (List.subperm_of_subset hnd hsub).perm_of_length_le (by simp)
    · refine le_trans (le_of_eq ?_) hsum
      unfold tourCost
      rw [List.length_map, List.length_range, tv_sum_range]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi : i < n := Finset.mem_range.1 hi
      have hj : (i + 1) % n < n := Nat.mod_lt _ (by omega)
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hj)]
      simp only [List.getElem_map, List.getElem_range]
      rw [tv_goE_hot _ (sg ((i + 1) % n)) (hsg1 _ hj) M _ (sg i) (hsg1 i hi)]
      rfl

/-! ## Transfer to the official class -/

/-- **TRAVELING SALESMAN ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem tsp_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      TSPLang := by
  classical
  have hrun := fun z => ((tv_exec_ver z).mono (tv_Tver_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg tv_ver) (tb 12 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg tv_ver, 12, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => tv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => tv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [tspLang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.Tsp
