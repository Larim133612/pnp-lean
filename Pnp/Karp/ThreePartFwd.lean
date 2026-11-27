import Pnp.Karp.ThreePartArith

/-!
# 3-PARTITION: an exact cover gives a partition (forward direction)

The group of item number `i` (`tpf_f`): items `12 l .. 12 l + 11` are the block of triple `l`,
items `12 K + 3 u + j` the gadget of `u = c q + e`.  Groups `4 l + c` (`c < 3`) and `4 l + 3`
belong to triple `l`, group `4 K + u` to gadget `u`.  `tpf_idx g` lists the three items of
group `g`; `tpf_P1`, `tpf_P2` (pure arithmetic) show that the items of group `g` are exactly
`tpf_idx g`, and `tpf_P3` that they form an intended pattern.
-/

namespace Pnp.Karp.ThreePart

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM


theorem tpf_len_fm {α : Type} (B : ℕ) (f : ℕ → List α) (hf : ∀ j, (f j).length = B) :
    ∀ n, ((List.range n).flatMap f).length = B * n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, tpf_len_fm B f hf n]
    simp [hf, Nat.mul_succ]

theorem tpf_getD_fm {α : Type} (B : ℕ) (f : ℕ → List α) (hf : ∀ j, (f j).length = B) (d : α) :
    ∀ n l j, l < n → j < B → ((List.range n).flatMap f).getD (B * l + j) d = (f l).getD j d
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, l, j, hl, hj => by
    rw [List.range_succ, List.flatMap_append]
    have hlen := tpf_len_fm B f hf n
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with h | h
    · have hlt : B * l + j < ((List.range n).flatMap f).length := by
        rw [hlen]; nlinarith
      rw [List.getD_append _ _ _ _ hlt, tpf_getD_fm B f hf d n l j h hj]
    · subst h
      have : B * l + j = ((List.range l).flatMap f).length + j := by rw [hlen]
      rw [this, List.getD_append_right _ _ _ _ (by omega)]
      simp

theorem tpf_cov_zero (q : ℕ) (p : ℕ) : ∀ (ts : List (ℕ × ℕ × ℕ)) (y : List Bool),
    covT q ts y p = 0 → ∀ l < ts.length, y.getD l false = true →
      ¬ (p = (ts.getD l (0,0,0)).1 ∨ p = q + (ts.getD l (0,0,0)).2.1 ∨
        p = 2 * q + (ts.getD l (0,0,0)).2.2)
  | [], _, _, l, hl, _ => absurd hl (Nat.not_lt_zero _)
  | t :: ts, y, h, l, hl, hs => by
    simp only [covT] at h
    cases l with
    | zero =>
      cases y with
      | nil => simp at hs
      | cons b y =>
        simp only [List.getD_cons_zero] at hs
        subst hs
        intro hp
        simp at h hp; tauto
    | succ l =>
      have h2 : covT q ts y.tail p = 0 := by omega
      have := tpf_cov_zero q p ts y.tail h2 l (by simpa using hl)
      cases y with
      | nil => simp at hs
      | cons b y => simpa using this hs

theorem tpf_cov_one (q : ℕ) (p : ℕ) : ∀ (ts : List (ℕ × ℕ × ℕ)) (y : List Bool),
    covT q ts y p = 1 → ∃ l < ts.length, y.getD l false = true ∧
      (p = (ts.getD l (0,0,0)).1 ∨ p = q + (ts.getD l (0,0,0)).2.1 ∨
        p = 2 * q + (ts.getD l (0,0,0)).2.2) ∧
      ∀ l' < ts.length, y.getD l' false = true → (p = (ts.getD l' (0,0,0)).1 ∨
        p = q + (ts.getD l' (0,0,0)).2.1 ∨ p = 2 * q + (ts.getD l' (0,0,0)).2.2) → l' = l
  | [], _, h => by simp [covT] at h
  | t :: ts, y, h => by
    simp only [covT] at h
    by_cases ha : (y.headD false && decide (p = t.1 ∨ p = q + t.2.1 ∨ p = 2 * q + t.2.2)) = true
    · rw [if_pos ha] at h
      have h0 : covT q ts y.tail p = 0 := by omega
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
      refine ⟨0, by simp, ?_, by simpa using ha.2, ?_⟩
      · cases y <;> simp_all
      · intro l' hl' hs hp
        cases l' with
        | zero => rfl
        | succ l' =>
          exfalso
          refine tpf_cov_zero q p ts y.tail h0 l' (by simpa using hl') ?_ (by simpa using hp)
          cases y <;> simp_all
    · rw [if_neg ha] at h
      simp only [Nat.zero_add] at h
      obtain ⟨l, hl, hs, hp, hu⟩ := tpf_cov_one q p ts y.tail h
      refine ⟨l + 1, by simpa using hl, ?_, by simpa using hp, ?_⟩
      · cases y <;> simp_all
      · intro l' hl' hs' hp'
        cases l' with
        | zero =>
          exfalso; apply ha
          cases y <;> simp_all
        | succ l' =>
          congr 1
          refine hu l' (by simpa using hl') ?_ (by simpa using hp')
          cases y <;> simp_all


section
variable (q K : ℕ) (sel : ℕ → Bool) (cr ch : ℕ → ℕ → ℕ)

def tpf_fT (l j : ℕ) : ℕ :=
  if j < 3 then (if sel l then 4 * K + j * q + cr l j else 4 * l + j)
  else if j < 9 then (if decide ((j - 3) % 2 = 0) = sel l then 4 * l + (j - 3) / 2 else 4 * l + 3)
  else 4 * l + (j - 9)

def tpf_fG (u j : ℕ) : ℕ :=
  if j = 0 then 4 * ch (u / q) (u % q) + u / q else 4 * K + u

def tpf_f (i : ℕ) : ℕ :=
  if i < 12 * K then tpf_fT q K sel cr (i / 12) (i % 12)
  else tpf_fG q K ch ((i - 12 * K) / 3) ((i - 12 * K) % 3)

def tpf_iT (l c : ℕ) : List ℕ :=
  if c < 3 then
    (if sel l then [12 * K + 3 * (c * q + cr l c), 12 * l + 3 + 2 * c, 12 * l + 9 + c]
     else [12 * l + c, 12 * l + 4 + 2 * c, 12 * l + 9 + c])
  else (if sel l then [12 * l + 4, 12 * l + 6, 12 * l + 8] else [12 * l + 3, 12 * l + 5, 12 * l + 7])

def tpf_iG (c e : ℕ) : List ℕ :=
  [12 * ch c e + c, 12 * K + 3 * (c * q + e) + 1, 12 * K + 3 * (c * q + e) + 2]

def tpf_idx (g : ℕ) : List ℕ :=
  if g < 4 * K then tpf_iT q K sel cr (g / 4) (g % 4)
  else tpf_iG q K ch ((g - 4 * K) / q) ((g - 4 * K) % q)

theorem tpf_dm {c e : ℕ} (he : e < q) : (c * q + e) / q = c ∧ (c * q + e) % q = e :=
  (Nat.div_mod_unique (by omega)).mpr ⟨by rw [Nat.mul_comm]; omega, he⟩

theorem tpf_f_T {l j : ℕ} (hl : l < K) (hj : j < 12) :
    tpf_f q K sel cr ch (12 * l + j) = tpf_fT q K sel cr l j := by
  unfold tpf_f
  rw [if_pos (by omega)]
  congr 1 <;> omega

theorem tpf_f_G (u j : ℕ) (hj : j < 3) :
    tpf_f q K sel cr ch (12 * K + 3 * u + j) = tpf_fG q K ch u j := by
  unfold tpf_f
  rw [if_neg (by omega)]
  congr 1 <;> omega

theorem tpf_idx_T {l c : ℕ} (hl : l < K) (hc : c < 4) :
    tpf_idx q K sel cr ch (4 * l + c) = tpf_iT q K sel cr l c := by
  unfold tpf_idx
  rw [if_pos (by omega)]
  congr 1 <;> omega

theorem tpf_idx_G {c e : ℕ} (he : e < q) :
    tpf_idx q K sel cr ch (4 * K + (c * q + e)) = tpf_iG q K ch c e := by
  unfold tpf_idx
  rw [if_neg (by omega), Nat.add_sub_cancel_left, (tpf_dm q he).1, (tpf_dm q he).2]

theorem tpf_fG0 {c e : ℕ} (he : e < q) :
    tpf_fG q K ch (c * q + e) 0 = 4 * ch c e + c := by
  simp [tpf_fG, (tpf_dm q he).1, (tpf_dm q he).2]

variable (hq : 2 ≤ q) (hcr : ∀ l < K, ∀ c < 3, cr l c < q)
  (hch : ∀ c < 3, ∀ e < q, ch c e < K ∧ sel (ch c e) = true ∧ cr (ch c e) c = e)
  (hu : ∀ c < 3, ∀ l < K, sel l = true → ch c (cr l c) = l)
include hq hcr hch hu

theorem tpf_P1 (i : ℕ) (hi : i < 12 * K + 9 * q) :
    tpf_f q K sel cr ch i < 4 * K + 3 * q ∧ i ∈ tpf_idx q K sel cr ch (tpf_f q K sel cr ch i) := by
  by_cases h : i < 12 * K
  · obtain ⟨l, j, hl, hj, rfl⟩ : ∃ l j, l < K ∧ j < 12 ∧ i = 12 * l + j :=
      ⟨i / 12, i % 12, by omega, by omega, by omega⟩
    rw [tpf_f_T q K sel cr ch hl hj]
    have hcl := hcr l hl
    by_cases hj3 : j < 3
    · cases hs : sel l
      · have e1 : tpf_fT q K sel cr l j = 4 * l + j := by simp [tpf_fT, hj3, hs]
        rw [e1, tpf_idx_T q K sel cr ch hl (by omega)]
        refine ⟨by omega, ?_⟩
        simp [tpf_iT, hj3, hs]
      · have e1 : tpf_fT q K sel cr l j = 4 * K + (j * q + cr l j) := by
          simp [tpf_fT, hj3, hs, Nat.add_assoc]
        rw [e1, tpf_idx_G q K sel cr ch (hcr l hl j hj3), tpf_iG, hu j hj3 l hl hs]
        refine ⟨?_, by simp⟩
        have := hcr l hl j hj3
        interval_cases j <;> omega
    by_cases hj9 : j < 9
    · by_cases hm : decide ((j - 3) % 2 = 0) = sel l
      · have e1 : tpf_fT q K sel cr l j = 4 * l + (j - 3) / 2 := by simp [tpf_fT, hj3, hj9, hm]
        rw [e1, tpf_idx_T q K sel cr ch hl (by omega)]
        refine ⟨by omega, ?_⟩
        have hc : (j - 3) / 2 < 3 := by omega
        cases hs : sel l <;> rw [hs] at hm <;> simp at hm <;>
          simp only [tpf_iT, hc, hs, if_true, if_false, Bool.false_eq_true, List.mem_cons,
            List.not_mem_nil] <;> omega
      · have e1 : tpf_fT q K sel cr l j = 4 * l + 3 := by simp [tpf_fT, hj3, hj9, hm]
        rw [e1, tpf_idx_T q K sel cr ch hl (by omega)]
        refine ⟨by omega, ?_⟩
        cases hs : sel l <;> rw [hs] at hm <;> simp at hm <;>
          simp only [tpf_iT, hs, if_true, if_false, Bool.false_eq_true, List.mem_cons,
            List.not_mem_nil, Nat.lt_irrefl] <;> omega
    · have e1 : tpf_fT q K sel cr l j = 4 * l + (j - 9) := by simp [tpf_fT, hj3, hj9]
      rw [e1, tpf_idx_T q K sel cr ch hl (by omega)]
      refine ⟨by omega, ?_⟩
      have hc : j - 9 < 3 := by omega
      cases hs : sel l <;> simp only [tpf_iT, hc, hs, if_true, if_false, Bool.false_eq_true,
        List.mem_cons, List.not_mem_nil] <;> omega
  · obtain ⟨c, e, j, hc, he, hj, rfl⟩ : ∃ c e j, c < 3 ∧ e < q ∧ j < 3 ∧
        i = 12 * K + 3 * (c * q + e) + j := by
      have h1 := Nat.div_add_mod ((i - 12 * K) / 3) q
      have h2 : (i - 12 * K) / 3 < 3 * q := by omega
      refine ⟨(i - 12 * K) / 3 / q, (i - 12 * K) / 3 % q, (i - 12 * K) % 3,
        (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega), Nat.mod_lt _ (by omega), by omega, ?_⟩
      rw [Nat.mul_comm _ q, h1]; omega
    rw [tpf_f_G q K sel cr ch _ _ hj]
    obtain ⟨h1, h2, h3⟩ := hch c hc e he
    by_cases hj0 : j = 0
    · subst hj0
      rw [tpf_fG0 q K ch he, tpf_idx_T q K sel cr ch h1 (by omega)]
      refine ⟨by omega, ?_⟩
      simp [tpf_iT, hc, h2, h3]
    · have e1 : tpf_fG q K ch (c * q + e) j = 4 * K + (c * q + e) := by simp [tpf_fG, hj0]
      rw [e1, tpf_idx_G q K sel cr ch he, tpf_iG]
      refine ⟨by interval_cases c <;> omega, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil]; omega
theorem tpf_P2 (g : ℕ) (hg : g < 4 * K + 3 * q) :
    (tpf_idx q K sel cr ch g).Nodup ∧ ∀ i ∈ tpf_idx q K sel cr ch g,
      i < 12 * K + 9 * q ∧ tpf_f q K sel cr ch i = g := by
  by_cases h : g < 4 * K
  · obtain ⟨l, c, hl, hc, rfl⟩ : ∃ l c, l < K ∧ c < 4 ∧ g = 4 * l + c :=
      ⟨g / 4, g % 4, by omega, by omega, by omega⟩
    rw [tpf_idx_T q K sel cr ch hl hc]
    have hT : ∀ j < 12, tpf_f q K sel cr ch (12 * l + j) = tpf_fT q K sel cr l j :=
      fun j hj => tpf_f_T q K sel cr ch hl hj
    by_cases hc3 : c < 3
    · have hC : tpf_f q K sel cr ch (12 * l + 9 + c) = 4 * l + c := by
        rw [Nat.add_assoc, hT _ (by omega)]
        simp [tpf_fT, show ¬ 9 + c < 3 by omega, show ¬ 9 + c < 9 by omega]
      have hcl := hcr l hl c hc3
      cases hs : sel l
      · simp only [tpf_iT, hc3, hs, if_true, if_false, Bool.false_eq_true]
        have hA : tpf_f q K sel cr ch (12 * l + c) = 4 * l + c := by
          rw [hT _ (by omega)]; simp [tpf_fT, hc3, hs]
        have hB : tpf_f q K sel cr ch (12 * l + 4 + 2 * c) = 4 * l + c := by
          rw [Nat.add_assoc, hT _ (by omega)]
          simp [tpf_fT, show ¬ 4 + 2 * c < 3 by omega, show 4 + 2 * c < 9 by omega, hs,
            show (4 + 2 * c - 3) % 2 = 1 by omega, show (4 + 2 * c - 3) / 2 = c by omega]
        refine ⟨by simp; omega, ?_⟩
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · exact ⟨by omega, hA⟩
        · exact ⟨by omega, hB⟩
        · exact ⟨by omega, hC⟩
      · simp only [tpf_iT, hc3, hs, if_true]
        have hA : tpf_f q K sel cr ch (12 * K + 3 * (c * q + cr l c)) = 4 * l + c := by
          rw [← Nat.add_zero (12 * K + 3 * (c * q + cr l c)), tpf_f_G q K sel cr ch _ _ (by omega),
            tpf_fG0 q K ch hcl, hu c hc3 l hl hs]
        have hB : tpf_f q K sel cr ch (12 * l + 3 + 2 * c) = 4 * l + c := by
          rw [Nat.add_assoc, hT _ (by omega)]
          simp [tpf_fT, show ¬ 3 + 2 * c < 3 by omega, show 3 + 2 * c < 9 by omega, hs]
        have hA' : c * q + cr l c < 3 * q := by interval_cases c <;> omega
        refine ⟨by simp; omega, ?_⟩
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · exact ⟨by omega, hA⟩
        · exact ⟨by omega, hB⟩
        · exact ⟨by omega, hC⟩
    · have hc' : c = 3 := by omega
      subst hc'
      cases hs : sel l
      · simp only [tpf_iT, hs, Nat.lt_irrefl, if_false, Bool.false_eq_true]
        refine ⟨by simp, ?_⟩
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;>
          exact ⟨by omega, by rw [hT _ (by omega)]; simp [tpf_fT, hs]⟩
      · simp only [tpf_iT, hs, Nat.lt_irrefl, if_false, if_true]
        refine ⟨by simp, ?_⟩
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;>
          exact ⟨by omega, by rw [hT _ (by omega)]; simp [tpf_fT, hs]⟩
  · obtain ⟨c, e, hc, he, rfl⟩ : ∃ c e, c < 3 ∧ e < q ∧ g = 4 * K + (c * q + e) := by
      have h1 := Nat.div_add_mod (g - 4 * K) q
      refine ⟨(g - 4 * K) / q, (g - 4 * K) % q,
        (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega), Nat.mod_lt _ (by omega), ?_⟩
      rw [Nat.mul_comm _ q, h1]; omega
    rw [tpf_idx_G q K sel cr ch he, tpf_iG]
    obtain ⟨h1, h2, h3⟩ := hch c hc e he
    have hA' : c * q + e < 3 * q := by interval_cases c <;> omega
    have hA : tpf_f q K sel cr ch (12 * ch c e + c) = 4 * K + (c * q + e) := by
      rw [tpf_f_T q K sel cr ch h1 (by omega)]
      simp [tpf_fT, hc, h2, h3, Nat.add_assoc]
    have hB : ∀ j, 0 < j → j < 3 →
        tpf_f q K sel cr ch (12 * K + 3 * (c * q + e) + j) = 4 * K + (c * q + e) := by
      intro j hj0 hj
      rw [tpf_f_G q K sel cr ch _ _ hj]
      simp [tpf_fG, show j ≠ 0 by omega]
    refine ⟨by simp; omega, ?_⟩
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨by omega, hA⟩
    · exact ⟨by omega, hB 1 (by omega) (by omega)⟩
    · exact ⟨by omega, hB 2 (by omega) (by omega)⟩
end

theorem tpf_dec {q : ℕ} (hq : 0 < q) {u : ℕ} (hu : u < 3 * q) :
    ∃ c e, c < 3 ∧ e < q ∧ u = c * q + e := by
  have h1 := Nat.div_add_mod u q
  refine ⟨u / q, u % q, (Nat.div_lt_iff_lt_mul hq).mpr (by omega), Nat.mod_lt _ hq, ?_⟩
  rw [Nat.mul_comm _ q, h1]

theorem tpf_len_els (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) :
    (els q ts).length = 12 * ts.length + 9 * q := by
  unfold els
  rw [List.length_append, tpf_len_fm 12 _ (fun l => by simp [triBlk]),
    tpf_len_fm 3 _ (fun u => by simp [gadBlk])]
  omega

theorem tpf_elT (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (d : El) {l j : ℕ} (hl : l < ts.length)
    (hj : j < 12) :
    (els q ts).getD (12 * l + j) d = (triBlk l (ts.getD l (0, 0, 0))).getD j d := by
  unfold els
  rw [List.getD_append _ _ _ _ (by rw [tpf_len_fm 12 _ (fun l => by simp [triBlk])]; omega)]
  exact tpf_getD_fm 12 (fun l => triBlk l (ts.getD l (0, 0, 0))) (fun l => by simp [triBlk]) d
    _ l j hl hj

theorem tpf_elG (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (d : El) {c e j : ℕ} (hc : c < 3) (he : e < q)
    (hj : j < 3) :
    (els q ts).getD (12 * ts.length + 3 * (c * q + e) + j) d =
      (gadBlk q ts.length c e).getD j d := by
  unfold els
  have h1 := tpf_len_fm 12 (fun l => triBlk l (ts.getD l (0, 0, 0)))
    (fun l => by simp [triBlk]) ts.length
  rw [List.getD_append_right _ _ _ _ (by omega), h1,
    show 12 * ts.length + 3 * (c * q + e) + j - 12 * ts.length = 3 * (c * q + e) + j by omega,
    tpf_getD_fm 3 _ (fun u => by simp [gadBlk]) d _ _ _ (by interval_cases c <;> omega) hj,
    (tpf_dm q he).1, (tpf_dm q he).2]

theorem tpf_ok (q : ℕ) (hq : 2 ≤ q) (ts : List (ℕ × ℕ × ℕ))
    (hts : ∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) :
    ∀ x ∈ els q ts, OkEl q (mT q ts) x := by
  intro x hx
  unfold els at hx
  rw [List.mem_append, List.mem_flatMap, List.mem_flatMap] at hx
  rcases hx with ⟨l, hl, hx⟩ | ⟨u, hu, hx⟩
  · rw [List.mem_range] at hl
    have ht := hts (ts.getD l (0, 0, 0)) (by rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _)
    simp only [triBlk, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [OkEl, mT] <;> omega
  · rw [List.mem_range] at hu
    obtain ⟨c, e, hc, he, rfl⟩ := tpf_dec (by omega) hu
    rw [(tpf_dm q he).1, (tpf_dm q he).2] at hx
    have : c * q + e < 3 * q := by interval_cases c <;> omega
    simp only [gadBlk, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h <;> subst h <;> simp only [OkEl, mT] <;> omega

theorem tpf_P3 (q : ℕ) (hq : 2 ≤ q) (ts : List (ℕ × ℕ × ℕ)) (y : List Bool) (ch : ℕ → ℕ → ℕ)
    (hcr : ∀ l < ts.length, ∀ c < 3, crd (ts.getD l (0, 0, 0)) c < q)
    (hch : ∀ c < 3, ∀ e < q, ch c e < ts.length ∧ y.getD (ch c e) false = true ∧
      crd (ts.getD (ch c e) (0, 0, 0)) c = e)
    (d : El) (g : ℕ) (hg : g < 4 * ts.length + 3 * q) :
    IsPat ((tpf_idx q ts.length (fun l => y.getD l false)
      (fun l c => crd (ts.getD l (0, 0, 0)) c) ch g).map fun i => (els q ts).getD i d) := by
  by_cases h : g < 4 * ts.length
  · obtain ⟨l, c, hl, hc, rfl⟩ : ∃ l c, l < ts.length ∧ c < 4 ∧ g = 4 * l + c :=
      ⟨g / 4, g % 4, by omega, by omega, by omega⟩
    rw [tpf_idx_T _ _ _ _ _ hl hc]
    have hT : ∀ j < 12, (els q ts).getD (12 * l + j) d =
        (triBlk l (ts.getD l (0, 0, 0))).getD j d := fun j hj => tpf_elT q ts d hl hj
    by_cases hc3 : c < 3
    · cases hs : y.getD l false
      · simp only [tpf_iT, hc3, hs, if_true, if_false, Bool.false_eq_true, List.map_cons,
          List.map_nil]
        rw [hT _ (by omega), Nat.add_assoc, hT _ (by omega), Nat.add_assoc, hT _ (by omega)]
        left
        refine ⟨c, crd (ts.getD l (0, 0, 0)) c, l, false, ?_⟩
        interval_cases c <;> simp [triBlk, crd]
      · simp only [tpf_iT, hc3, hs, if_true, List.map_cons, List.map_nil]
        rw [← Nat.add_zero (12 * ts.length + 3 * (c * q + crd (ts.getD l (0, 0, 0)) c)),
          tpf_elG q ts d hc3 (hcr l hl c hc3) (by omega), Nat.add_assoc, hT _ (by omega),
          Nat.add_assoc, hT _ (by omega)]
        left
        refine ⟨c, crd (ts.getD l (0, 0, 0)) c, l, true, ?_⟩
        interval_cases c <;> simp [triBlk, gadBlk, crd]
    · have hc' : c = 3 := by omega
      subst hc'
      right
      cases hs : y.getD l false
      · simp only [tpf_iT, hs, Nat.lt_irrefl, if_false, Bool.false_eq_true, List.map_cons,
          List.map_nil]
        rw [hT _ (by omega), hT _ (by omega), hT _ (by omega)]
        exact ⟨l, true, by simp [triBlk]⟩
      · simp only [tpf_iT, hs, Nat.lt_irrefl, if_false, if_true, List.map_cons, List.map_nil]
        rw [hT _ (by omega), hT _ (by omega), hT _ (by omega)]
        exact ⟨l, false, by simp [triBlk]⟩
  · obtain ⟨c, e, hc, he, hge⟩ := tpf_dec (q := q) (u := g - 4 * ts.length) (by omega) (by omega)
    rw [show g = 4 * ts.length + (c * q + e) by omega, tpf_idx_G _ _ _ _ _ he, tpf_iG]
    obtain ⟨h1, h2, h3⟩ := hch c hc e he
    simp only [List.map_cons, List.map_nil]
    rw [tpf_elT q ts d h1 (by omega), tpf_elG q ts d hc he (by omega),
      tpf_elG q ts d hc he (by omega)]
    left
    refine ⟨c, e, ts.length + c * q + e, false, ?_⟩
    interval_cases c <;> simp only [crd] at h3 <;>
      simp only [triBlk, gadBlk, List.getD_cons_zero, List.getD_cons_succ, h3] <;> simp

theorem tp_of_cov (q : ℕ) (hq : 2 ≤ q) (ts : List (ℕ × ℕ × ℕ))
    (hts : ∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (y : List Bool)
    (hy : ∀ p < 3 * q, covT q ts y p = 1) : TPLang (TPW q ts) := by
  have hgm : ∀ l < ts.length, ts.getD l (0, 0, 0) ∈ ts := fun l hl => by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _
  have hcr : ∀ l < ts.length, ∀ c < 3, crd (ts.getD l (0, 0, 0)) c < q := by
    intro l hl c hc
    have := hts _ (hgm l hl)
    interval_cases c <;> simp only [crd] <;> omega
  have hex : ∀ c < 3, ∀ e < q, ∃ l, l < ts.length ∧ y.getD l false = true ∧
      crd (ts.getD l (0, 0, 0)) c = e ∧ ∀ l' < ts.length, y.getD l' false = true →
        crd (ts.getD l' (0, 0, 0)) c = e → l' = l := by
    intro c hc e he
    have hc3 : c * q + e < 3 * q := by interval_cases c <;> omega
    obtain ⟨l, hl, hs, hp, hu⟩ := tpf_cov_one q _ ts y (hy _ hc3)
    have key : ∀ l' < ts.length, (c * q + e = (ts.getD l' (0, 0, 0)).1 ∨
        c * q + e = q + (ts.getD l' (0, 0, 0)).2.1 ∨
        c * q + e = 2 * q + (ts.getD l' (0, 0, 0)).2.2) ↔ crd (ts.getD l' (0, 0, 0)) c = e := by
      intro l' hl'
      have := hts _ (hgm l' hl')
      interval_cases c <;> simp only [crd] <;> omega
    exact ⟨l, hl, hs, (key l hl).1 hp, fun l' hl' hs' hc' => hu l' hl' hs' ((key l' hl').2 hc')⟩
  choose! ch hch using hex
  have hch' : ∀ c < 3, ∀ e < q, ch c e < ts.length ∧ y.getD (ch c e) false = true ∧
      crd (ts.getD (ch c e) (0, 0, 0)) c = e :=
    fun c hc e he => ⟨(hch c hc e he).1, (hch c hc e he).2.1, (hch c hc e he).2.2.1⟩
  have hu : ∀ c < 3, ∀ l < ts.length, y.getD l false = true →
      ch c (crd (ts.getD l (0, 0, 0)) c) = l :=
    fun c hc l hl hs => ((hch c hc _ (hcr l hl c hc)).2.2.2 l hl hs rfl).symm
  have P1 := tpf_P1 q ts.length (fun l => y.getD l false)
    (fun l c => crd (ts.getD l (0, 0, 0)) c) ch hq hcr hch' hu
  have P2 := tpf_P2 q ts.length (fun l => y.getD l false)
    (fun l c => crd (ts.getD l (0, 0, 0)) c) ch hq hcr hch' hu
  have hlen := tpf_len_els q ts
  unfold TPLang TPW
  refine ⟨(els q ts).map (elRow q (mT q ts)), bRow q (mT q ts), ?_, ?_, ?_,
    tpf_f q ts.length (fun l => y.getD l false) (fun l c => crd (ts.getD l (0, 0, 0)) c) ch,
    ?_, ?_⟩
  · rw [clauses_flatMap]
    intro r hr
    rw [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨x, -, rfl⟩ | rfl
    · simp only [elRow, List.mem_flatMap, not_exists, not_and]
      intro b _
      cases b <;> simp
    · simp [bRow]
  · rw [List.length_map, hlen]; omega
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨x, -, rfl⟩ := hr
    exact tp_el_bounds q _ x
  · intro i hi
    rw [List.length_map, hlen] at hi ⊢
    have := (P1 i hi).1
    omega
  · intro g hg
    rw [List.length_map, hlen] at hg
    have hg' : g < 4 * ts.length + 3 * q := by omega
    rw [tp_binSum_eq, List.length_map, hlen]
    obtain ⟨hnd, hmem⟩ := P2 g hg'
    have hperm : ((List.range (12 * ts.length + 9 * q)).filter fun i => decide
        (tpf_f q ts.length (fun l => y.getD l false) (fun l c => crd (ts.getD l (0, 0, 0)) c) ch i
          = g)).Perm (tpf_idx q ts.length (fun l => y.getD l false)
            (fun l c => crd (ts.getD l (0, 0, 0)) c) ch g) :=
      (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnd).mpr (by
      intro i
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨hi, rfl⟩; exact (P1 i hi).2
      · intro h; exact hmem i h)
    rw [(hperm.map _).sum_eq]
    rw [show ((tpf_idx q ts.length (fun l => y.getD l false)
        (fun l c => crd (ts.getD l (0, 0, 0)) c) ch g).map
          fun i => bv (((els q ts).map (elRow q (mT q ts))).getD i [])) =
        (((tpf_idx q ts.length (fun l => y.getD l false)
          (fun l c => crd (ts.getD l (0, 0, 0)) c) ch g).map
          fun i => (els q ts).getD i (El.cp 0 0 false)).map
            fun x => bv (elRow q (mT q ts) x)) from by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      have hi' := (hmem i hi).1
      simp only [Function.comp]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hlen]; exact hi'),
        List.getElem_map, List.getD_eq_getElem _ _ (by rw [hlen]; exact hi')]]
    rw [tp_sum_iff q _ hq _ ?_]
    · exact tpf_P3 q hq ts y ch hcr hch' _ g hg'
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine tpf_ok q hq ts hts _ ?_
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact (hmem i hi).1)]
      exact List.getElem_mem _

end Pnp.Karp.ThreePart
