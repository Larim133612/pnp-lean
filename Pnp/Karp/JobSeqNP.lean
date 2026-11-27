import Pnp.Karp.JobSeqVer
import Pnp.Karp.TspNP

/-!
# JOB SEQUENCING ∈ NP (official definition)

The checking relation is `jsv_vres w y = true` (`Pnp/Karp/JobSeqVer.lean`): with
`clauses w = K :: js`, `m = ⌊|js| / 3⌋` jobs and `m' = ⌈|js| / 3⌉` triples of rows (the last
one possibly incomplete), the certificate `y` gives every triple `i < m'` a rank
`jsv_r y i` (the value of its `seg`-segment), and the verifier accepts iff
`jsv_pen js (jsv_r y) ≤ bv K`, where job `j < m` is charged the completion time
`∑_{i < m', rᵢ ≤ rⱼ} T i` (`jsv_vres_iff`).

* `jsv_latePen_le`, `jsv_latePen_eq`: along a schedule sorted (strictly) by rank, the late
  penalty is at most (equal to) the penalty with these rank-based completion times;
* `jsv_lang_iff`: `JSLang w ↔ ∃ y, |y| ≤ |w|^2 ∧ jsv_vres w y`.  Soundness: sort the jobs by
  rank (`List.mergeSort`).  Completeness: give the job at position `k` of the schedule the
  rank `2^k - 1` (segment `true^k`), and the incomplete triple the rank `2^m - 1`;
* `js_in_np`: `JSLang ∈ NP`, via `jsv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.JobSeq

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.Ham Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.Tsp

/-! ## Semantics of the verifier -/

/-- The certificate after `i` segments. -/
def jsv_yd : ℕ → Str → Str
  | 0, Y => Y
  | i + 1, Y => jsv_yd i (seg Y).2

/-- The rank of triple `i`. -/
def jsv_r (Y : Str) (i : ℕ) : ℕ := sv_bval (seg (jsv_yd i Y)).1.reverse

theorem jsv_r_succ (Y : Str) (i : ℕ) : jsv_r Y (i + 1) = jsv_r (seg Y).2 i := rfl

theorem jsv_getD3 {α : Type} (a b c : α) (l : List α) (n : ℕ) (d : α) :
    (a :: b :: c :: l).getD (n + 3) d = l.getD n d := by simp

theorem jsv_bval_ad (ρ Y C : Str) (t : List SatSym) :
    sv_bval (jsv_ad ρ Y C t) = sv_bval C + if jsv_r Y 0 ≤ sv_bval ρ then bv t else 0 := by
  unfold jsv_ad jsv_r jsv_yd
  by_cases h : sv_bval (seg Y).1.reverse ≤ sv_bval ρ
  · rw [if_pos ((kv_le_iff _ _).2 h), if_pos h, sv_bval_addL, sv_bval_bits]; simp
  · rw [if_neg (fun h' => h ((kv_le_iff _ _).1 h')), if_neg h]; simp

theorem jsv_bval_in (ρ : Str) : ∀ (rows : List (List SatSym)) (Y C : Str),
    sv_bval (jsv_in ρ rows Y C) = sv_bval C + ∑ i ∈ Finset.range ((rows.length + 2) / 3),
      if jsv_r Y i ≤ sv_bval ρ then bv (rows.getD (3 * i) []) else 0
  | [], _, C => by simp [jsv_in]
  | [t], Y, C => by simp [jsv_in, jsv_bval_ad]
  | [t, _], Y, C => by simp [jsv_in, jsv_bval_ad]
  | t :: d :: p :: rest, Y, C => by
    rw [jsv_in, jsv_bval_in ρ rest, jsv_bval_ad,
      show ((t :: d :: p :: rest).length + 2) / 3 = (rest.length + 2) / 3 + 1 by simp; omega,
      Finset.sum_range_succ']
    simp only [jsv_r_succ, Nat.mul_succ, jsv_getD3, Nat.mul_zero, List.getD_cons_zero]
    ring

/-- The rank-based completion time of job `j` (`m'` triples). -/
def jsv_C (js : List (List SatSym)) (r : ℕ → ℕ) (m' j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m', if r i ≤ r j then jT js i else 0

/-- The penalty of job `k` if it completes at time `x`. -/
def jsv_late (js : List (List SatSym)) (k x : ℕ) : ℕ := if jD js k < x then jP js k else 0

/-- The penalty with the rank-based completion times. -/
def jsv_pen (js : List (List SatSym)) (r : ℕ → ℕ) : ℕ :=
  ∑ j ∈ Finset.range (js.length / 3), jsv_late js j (jsv_C js r ((js.length + 2) / 3) j)

theorem jsv_out_iff (js : List (List SatSym)) (Y0 K : Str) : ∀ (rows : List (List SatSym))
    (R A : Str), jsv_out js Y0 K rows R A = true ↔
      sv_bval A + ∑ j ∈ Finset.range (rows.length / 3),
        (if sv_bval (jsv_in (seg (jsv_yd j R)).1.reverse js Y0 []) ≤ bv (rows.getD (3 * j + 1) [])
          then 0 else bv (rows.getD (3 * j + 2) [])) ≤ sv_bval K
  | t :: d :: p :: rest, R, A => by
    rw [jsv_out, jsv_out_iff js Y0 K rest,
      show (t :: d :: p :: rest).length / 3 = rest.length / 3 + 1 by simp; omega,
      Finset.sum_range_succ']
    simp only [jsv_yd, Nat.mul_succ, Nat.mul_zero, Nat.zero_add]
    have e1 : ∀ i, 3 * i + 3 + 1 = (3 * i + 1) + 3 := fun i => by ring
    have e2 : ∀ i, 3 * i + 3 + 2 = (3 * i + 2) + 3 := fun i => by ring
    simp only [e1, e2, List.getD_cons_succ, List.getD_cons_zero]
    have hk := kv_le_iff (jsv_in (seg R).1.reverse js Y0 []) (sv_bits d)
    rw [sv_bval_bits] at hk
    by_cases h : sv_bval (jsv_in (seg R).1.reverse js Y0 []) ≤ bv d
    · rw [if_pos (hk.2 h), if_pos h]; omega
    · rw [if_neg (fun h' => h (hk.1 h')), if_neg h, sv_bval_addL, sv_bval_bits]
      simp only [Bool.false_eq_true, if_false]; omega
  | [], R, A => by simp [jsv_out, kv_le_iff]
  | [_], R, A => by simp [jsv_out, kv_le_iff]
  | [_, _], R, A => by simp [jsv_out, kv_le_iff]

theorem jsv_vres_iff (w : List SatSym) (y : Str) :
    jsv_vres w y = true ↔ ∃ K js, clauses w = K :: js ∧ jsv_pen js (jsv_r y) ≤ bv K := by
  unfold jsv_vres
  rcases hcw : clauses w with _ | ⟨K, js⟩
  · simp
  · rw [jsv_out_iff]
    have e : ∀ j, (if sv_bval (jsv_in (seg (jsv_yd j y)).1.reverse js y []) ≤
        bv (js.getD (3 * j + 1) []) then 0 else bv (js.getD (3 * j + 2) [])) =
        jsv_late js j (jsv_C js (jsv_r y) ((js.length + 2) / 3) j) := by
      intro j
      rw [jsv_bval_in]
      unfold jsv_late jsv_C jT jD jP jsv_r
      simp only [sv_bval, zero_add]
      split_ifs <;> omega
    simp only [e, sv_bval, zero_add, sv_bval_bits, jsv_pen]
    constructor
    · intro h; exact ⟨K, js, rfl, h⟩
    · rintro ⟨K', js', he, h⟩
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact h

/-! ## Schedules sorted by rank -/

theorem jsv_late_mono (js : List (List SatSym)) (k : ℕ) {x y : ℕ} (h : x ≤ y) :
    jsv_late js k x ≤ jsv_late js k y := by
  unfold jsv_late; split_ifs <;> omega

theorem jsv_latePen_le (js : List (List SatSym)) (r : ℕ → ℕ) : ∀ (π : List ℕ) (s : ℕ),
    π.Pairwise (fun a b => r a ≤ r b) →
    latePen js s π ≤ (π.map fun k => jsv_late js k
      (s + (π.map fun i => if r i ≤ r k then jT js i else 0).sum)).sum
  | [], _, _ => by simp [latePen]
  | j :: π, s, hp => by
    rw [List.pairwise_cons] at hp
    have ih := jsv_latePen_le js r π (s + jT js j) hp.2
    have e : (π.map fun k => jsv_late js k (s + ((j :: π).map fun i =>
        if r i ≤ r k then jT js i else 0).sum)) =
        π.map fun k => jsv_late js k (s + jT js j + (π.map fun i =>
          if r i ≤ r k then jT js i else 0).sum) := by
      refine List.map_congr_left (fun k hk => ?_)
      simp only [List.map_cons, List.sum_cons, if_pos (hp.1 k hk)]; ring_nf
    rw [List.map_cons, List.sum_cons, e, latePen]
    refine Nat.add_le_add ?_ ih
    refine jsv_late_mono js j ?_
    simp

theorem jsv_latePen_eq (js : List (List SatSym)) (r : ℕ → ℕ) : ∀ (π : List ℕ) (s : ℕ),
    π.Pairwise (fun a b => r a < r b) →
    latePen js s π = (π.map fun k => jsv_late js k
      (s + (π.map fun i => if r i ≤ r k then jT js i else 0).sum)).sum
  | [], _, _ => by simp [latePen]
  | j :: π, s, hp => by
    rw [List.pairwise_cons] at hp
    have ih := jsv_latePen_eq js r π (s + jT js j) hp.2
    have e : (π.map fun k => jsv_late js k (s + ((j :: π).map fun i =>
        if r i ≤ r k then jT js i else 0).sum)) =
        π.map fun k => jsv_late js k (s + jT js j + (π.map fun i =>
          if r i ≤ r k then jT js i else 0).sum) := by
      refine List.map_congr_left (fun k hk => ?_)
      simp only [List.map_cons, List.sum_cons, if_pos (le_of_lt (hp.1 k hk))]; ring_nf
    have e0 : (π.map fun i => if r i ≤ r j then jT js i else 0) = π.map fun _ => 0 :=
      List.map_congr_left (fun i hi => if_neg (by have := hp.1 i hi; omega))
    rw [List.map_cons, List.sum_cons, e, latePen, ih]
    congr 1
    simp only [List.map_cons, List.sum_cons, le_refl, if_true, e0, List.map_const',
      List.sum_replicate, smul_eq_mul, mul_zero, add_zero]
    rfl

theorem jsv_sum_perm {π : List ℕ} {m : ℕ} (hp : π.Perm (List.range m)) (f : ℕ → ℕ) :
    (π.map f).sum = ∑ i ∈ Finset.range m, f i := by
  rw [(hp.map f).sum_eq, tv_sum_range]

/-- Soundness: a rank map gives a schedule (sorted by rank) that is at least as good. -/
theorem jsv_sound (js : List (List SatSym)) (r : ℕ → ℕ) (K : ℕ) (h : jsv_pen js r ≤ K) :
    ∃ π : List ℕ, π.Perm (List.range (js.length / 3)) ∧ latePen js 0 π ≤ K := by
  set m := js.length / 3
  set π := (List.range m).mergeSort (fun a b => decide (r a ≤ r b))
  have hp : π.Perm (List.range m) := List.mergeSort_perm _ _
  have hs : π.Pairwise (fun a b => r a ≤ r b) := by
    have := List.pairwise_mergeSort (le := fun a b => decide (r a ≤ r b))
      (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) (List.range m)
    exact this.imp (by simp)
  refine ⟨π, hp, le_trans (jsv_latePen_le js r π 0 hs) (le_trans ?_ h)⟩
  rw [jsv_sum_perm hp]
  unfold jsv_pen
  refine Finset.sum_le_sum (fun k _ => jsv_late_mono js k ?_)
  rw [jsv_sum_perm hp, zero_add]
  unfold jsv_C
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))

/-! ## Certificates from schedules -/

/-- The certificate with the segments `bs`. -/
def jsv_cert (bs : List Str) : Str := bs.flatMap fun b => dbl b ++ [true, true]

theorem jsv_yd_cert : ∀ (j : ℕ) (bs : List Str), jsv_yd j (jsv_cert bs) = jsv_cert (bs.drop j)
  | 0, bs => rfl
  | j + 1, [] => by
    show jsv_yd j (seg []).2 = _
    simp only [seg]
    rw [show ([] : Str) = jsv_cert [] from rfl, jsv_yd_cert j []]; simp [jsv_cert]
  | j + 1, b :: bs => by
    show jsv_yd j (seg (dbl b ++ [true, true] ++ jsv_cert bs)).2 = _
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, seg_dbl_sep,
      jsv_yd_cert j bs]
    rfl

theorem jsv_r_cert (bs : List Str) (j : ℕ) (hj : j < bs.length) :
    jsv_r (jsv_cert bs) j = sv_bval bs[j].reverse := by
  unfold jsv_r
  rw [jsv_yd_cert, List.drop_eq_getElem_cons hj]
  show sv_bval (seg (dbl bs[j] ++ [true, true] ++ jsv_cert (bs.drop (j + 1)))).1.reverse = _
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, seg_dbl_sep]

theorem jsv_length_cert (B : ℕ) : ∀ bs : List Str, (∀ b ∈ bs, b.length ≤ B) →
    (jsv_cert bs).length ≤ bs.length * (2 * B + 2)
  | [], _ => by simp [jsv_cert]
  | b :: bs, h => by
    have ih := jsv_length_cert B bs (fun b' hb => h b' (by simp [hb]))
    have hb := h b (by simp)
    have hd : (dbl b).length = 2 * b.length := by
      unfold dbl; induction b <;> simp_all; omega
    have e : jsv_cert (b :: bs) = dbl b ++ [true, true] ++ jsv_cert bs := rfl
    rw [e]
    simp only [List.length_append, hd, List.length_cons, List.length_nil]
    rw [Nat.add_mul, one_mul]; omega

theorem jsv_bval_rep : ∀ k : ℕ, sv_bval (List.replicate k true) = 2 ^ k - 1
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, sv_bval, jsv_bval_rep k, pow_succ]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    simp only [if_true]; omega

theorem jsv_pow_le (a b : ℕ) : 2 ^ a - 1 ≤ 2 ^ b - 1 ↔ a ≤ b := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  rw [show (2 ^ a - 1 ≤ 2 ^ b - 1) ↔ 2 ^ a ≤ 2 ^ b by omega]
  exact Nat.pow_le_pow_iff_right (by norm_num)

/-- Completeness: the positions of a schedule as ranks. -/
theorem jsv_complete (js : List (List SatSym)) (π : List ℕ)
    (hp : π.Perm (List.range (js.length / 3))) :
    let bs := (List.range ((js.length + 2) / 3)).map fun j => List.replicate (π.idxOf j) true
    jsv_pen js (jsv_r (jsv_cert bs)) = latePen js 0 π ∧
      (jsv_cert bs).length ≤ (js.length + 2) / 3 * (2 * (js.length / 3) + 2) := by
  intro bs
  set m := js.length / 3
  set m' := (js.length + 2) / 3
  have hmm : m ≤ m' := by omega
  have hlen : π.length = m := by simpa using hp.length_eq
  have hnd : π.Nodup := hp.nodup_iff.mpr List.nodup_range
  have hr : ∀ j < m', jsv_r (jsv_cert bs) j = 2 ^ (π.idxOf j) - 1 := by
    intro j hj
    rw [jsv_r_cert bs j (by simp [bs]; omega)]
    simp [bs, jsv_bval_rep]
  have hmem : ∀ j, j ∈ π ↔ j < m := fun j => by rw [hp.mem_iff]; simp
  have hidx : ∀ j, j < m → π.idxOf j < m := fun j hj => by
    rw [← hlen]; exact List.idxOf_lt_length_iff.2 ((hmem j).2 hj)
  have hidx' : ∀ j, m ≤ j → π.idxOf j = m := fun j hj => by
    rw [← hlen]; exact List.idxOf_eq_length (fun h => by have := (hmem j).1 h; omega)
  -- the rank-based completion times are the completion times of `π`
  have hC : ∀ k < m, jsv_C js (jsv_r (jsv_cert bs)) m' k =
      ((π.map fun i => if jsv_r (jsv_cert bs) i ≤ jsv_r (jsv_cert bs) k then jT js i
        else 0).sum) := by
    intro k hk
    rw [jsv_sum_perm hp]
    unfold jsv_C
    obtain ⟨e, he⟩ : ∃ e, m' = m + e := ⟨m' - m, by omega⟩
    rw [he, Finset.sum_range_add]
    have hz : ∑ i ∈ Finset.range e, (if jsv_r (jsv_cert bs) (m + i) ≤ jsv_r (jsv_cert bs) k
        then jT js (m + i) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => if_neg ?_)
      have hi : i < e := Finset.mem_range.1 hi
      rw [hr (m + i) (by omega), hr k (by omega), jsv_pow_le, hidx' (m + i) (by omega)]
      have := hidx k hk
      omega
    rw [hz, add_zero]
  have hs : π.Pairwise (fun a b => jsv_r (jsv_cert bs) a < jsv_r (jsv_cert bs) b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have ha : π[i] < m := (hmem _).1 (List.getElem_mem _)
    have hb : π[j] < m := (hmem _).1 (List.getElem_mem _)
    rw [hr _ (by omega), hr _ (by omega), hnd.idxOf_getElem, hnd.idxOf_getElem]
    have h1 := (jsv_pow_le j i).not
    have : ¬ j ≤ i := by omega
    rw [← h1] at this
    omega
  refine ⟨?_, ?_⟩
  · rw [jsv_latePen_eq js _ π 0 hs, jsv_sum_perm hp]
    unfold jsv_pen
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [zero_add, hC k (Finset.mem_range.1 hk)]
  · have := jsv_length_cert m bs (fun b hb => by
      simp only [bs, List.mem_map, List.mem_range] at hb
      obtain ⟨j, -, rfl⟩ := hb
      simp only [List.length_replicate]
      rw [← hlen]; exact List.idxOf_le_length)
    simpa [bs] using this

/-! ## Short certificates -/

theorem jsv_lang_iff (w : List SatSym) :
    JSLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ jsv_vres w y = true := by
  have hcl := length_clauses_le w
  unfold JSLang
  simp only [jsv_vres_iff]
  constructor
  · rintro ⟨K, js, hw, π, hp, hpen⟩
    obtain ⟨h1, h2⟩ := jsv_complete js π hp
    refine ⟨_, ?_, K, js, hw, h1 ▸ hpen⟩
    rw [hw] at hcl
    simp only [List.length_cons] at hcl
    refine le_trans h2 ?_
    set n := js.length
    have ha : (n + 2) / 3 ≤ n := by omega
    have hb : 2 * (n / 3) + 2 ≤ n + 2 := by omega
    have := Nat.mul_le_mul ha hb
    nlinarith
  · rintro ⟨y, -, K, js, hw, h⟩
    exact ⟨K, js, hw, jsv_sound js _ _ h⟩

/-! ## Transfer to the official class -/

/-- **JOB SEQUENCING ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem js_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      JSLang := by
  classical
  have hrun := fun z => ((jsv_exec_ver z).mono (jsv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg jsv_ver) (tb 11 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg jsv_ver, 11, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => jsv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => jsv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [jsv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.JobSeq
