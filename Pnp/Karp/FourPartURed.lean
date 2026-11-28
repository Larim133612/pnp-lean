import Pnp.Karp.FourPartU
import Pnp.Karp.ThreePartUWf
import Pnp.Karp.CliqueVer

/-!
# Unary 4-PARTITION: correctness of the reduction from unary 3-PARTITION

`fpr_tpu_iff`: for a unary 3-PARTITION instance `u` whose rows are `items ++ [Bv]` with
`3 ∣ |items|` and sizes strictly between `B/4` and `B/2`, `TPULang u ↔ FPULang (fpuT u)`.
`sat_iff_fpu`: `SATLang w ↔ FPULang (FPUI w)`.
-/

namespace Pnp.Karp.FourPartU

open Pnp.CookLevin SatSym Pnp.Karp.ThreePartU

/-- The number of rows in group `b`. -/
def fpr_cnt : List (List SatSym) → (ℕ → ℕ) → ℕ → ℕ
  | [], _, _ => 0
  | _ :: rs, f, b => (if f 0 = b then 1 else 0) + fpr_cnt rs (fun i => f (i + 1)) b

theorem fpr_unSum_append (A B : List (List SatSym)) (f : ℕ → ℕ) (g : ℕ) :
    unSum (A ++ B) f g = unSum A f g + unSum B (fun i => f (A.length + i)) g := by
  induction A generalizing f with
  | nil => simp [unSum]
  | cons r rs ih =>
    simp only [List.cons_append, unSum, ih, List.length_cons]
    have : (fun i => f (rs.length + 1 + i)) = (fun i => f (rs.length + i + 1)) := by
      funext i; congr 1; omega
    rw [this]; omega

theorem fpr_unSum_congr (rs : List (List SatSym)) (f h : ℕ → ℕ) (g : ℕ)
    (hfh : ∀ i < rs.length, f i = h i) : unSum rs f g = unSum rs h g := by
  induction rs generalizing f h with
  | nil => simp [unSum]
  | cons r rs ih =>
    simp only [unSum]
    rw [hfh 0 (by simp), ih (fun i => f (i + 1)) (fun i => h (i + 1))
      (fun i hi => hfh (i + 1) (by simp; omega))]

theorem fpr_cnt_congr (rs : List (List SatSym)) (f h : ℕ → ℕ) (g : ℕ)
    (hfh : ∀ i < rs.length, f i = h i) : fpr_cnt rs f g = fpr_cnt rs h g := by
  induction rs generalizing f h with
  | nil => simp [fpr_cnt]
  | cons r rs ih =>
    simp only [fpr_cnt]
    rw [hfh 0 (by simp), ih (fun i => f (i + 1)) (fun i => h (i + 1))
      (fun i hi => hfh (i + 1) (by simp; omega))]

theorem fpr_unSum_map (c : ℕ) (rs : List (List SatSym)) (f : ℕ → ℕ) (g : ℕ) :
    unSum (rs.map fun r => uRow (c + r.length)) f g = c * fpr_cnt rs f g + unSum rs f g := by
  induction rs generalizing f with
  | nil => simp [unSum, fpr_cnt]
  | cons r rs ih =>
    simp only [List.map_cons, unSum, fpr_cnt, ih, tpu_uRow_len]
    split_ifs <;> ring

theorem fpr_unSum_const (c : ℕ) (rs : List (List SatSym)) (hc : ∀ r ∈ rs, r.length = c)
    (f : ℕ → ℕ) (g : ℕ) : unSum rs f g = c * fpr_cnt rs f g := by
  induction rs generalizing f with
  | nil => simp [unSum, fpr_cnt]
  | cons r rs ih =>
    simp only [unSum, fpr_cnt, ih (fun r hr => hc r (by simp [hr])), hc r (by simp)]
    split_ifs <;> ring

theorem fpr_cnt_rep (x : List SatSym) (m : ℕ) : ∀ (s g : ℕ),
    fpr_cnt (List.replicate m x) (fun j => j + s) g = if s ≤ g ∧ g < s + m then 1 else 0 := by
  induction m with
  | zero => intro s g; simp [fpr_cnt]
  | succ m ih =>
    intro s g
    simp only [List.replicate_succ, fpr_cnt]
    have := ih (s + 1) g
    have e : (fun i => i + 1 + s) = (fun j => j + (s + 1)) := by funext i; omega
    rw [e, this]
    split_ifs <;> omega

theorem fpr_unSum_le (rs : List (List SatSym)) (f : ℕ → ℕ) (g : ℕ) :
    unSum rs f g ≤ (rs.map List.length).sum := by
  induction rs generalizing f with
  | nil => simp [unSum]
  | cons r rs ih =>
    simp only [unSum, List.map_cons, List.sum_cons]
    have := ih (fun i => f (i + 1))
    split_ifs <;> omega

theorem fpr_cnt_bounds (B : ℕ) (rs : List (List SatSym))
    (hb : ∀ r ∈ rs, B < 4 * r.length ∧ 2 * r.length < B) (f : ℕ → ℕ) (g : ℕ) :
    fpr_cnt rs f g * (B + 1) ≤ 4 * unSum rs f g ∧
      2 * unSum rs f g + fpr_cnt rs f g ≤ fpr_cnt rs f g * B := by
  induction rs generalizing f with
  | nil => simp [unSum, fpr_cnt]
  | cons r rs ih =>
    simp only [unSum, fpr_cnt]
    have hih := ih (fun r hr => hb r (by simp [hr])) (fun i => f (i + 1))
    have := hb r (by simp)
    split_ifs
    · constructor <;> nlinarith
    · simpa using hih

/-- A group of items summing to `B` has exactly three items. -/
theorem fpr_cnt_three (B : ℕ) (rs : List (List SatSym))
    (hb : ∀ r ∈ rs, B < 4 * r.length ∧ 2 * r.length < B) (hB : 0 < B) (f : ℕ → ℕ) (g : ℕ)
    (hs : unSum rs f g = B) : fpr_cnt rs f g = 3 := by
  obtain ⟨h1, h2⟩ := fpr_cnt_bounds B rs hb f g
  rw [hs] at h1 h2
  rcases Nat.lt_or_ge (fpr_cnt rs f g) 4 with h | h
  · interval_cases (fpr_cnt rs f g) <;> omega
  · nlinarith

theorem fpr_div (x y s b N : ℕ) (hs : s < N) (hb : b < N) (h : x * N + s = y * N + b) :
    x = y ∧ s = b := by
  have h1 : (x * N + s) / N = x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs]; simp
  have h2 : (y * N + b) / N = y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb]; simp
  have hxy : x = y := by rw [← h1, ← h2, h]
  subst hxy; exact ⟨rfl, by omega⟩

theorem fpr_clauses (u : List SatSym) (items : List (List SatSym)) (Bv : List SatSym)
    (hu : clauses u = items ++ [Bv]) :
    clauses (fpuT u) = items.map (fun r => uRow (5 * u.length + r.length)) ++
      List.replicate (items.length / 3) (uRow (6 * u.length)) ++
      [uRow (21 * u.length + Bv.length)] := by
  unfold fpuT
  rw [hu, List.dropLast_concat, List.getLastD_eq_getLast?, List.getLast?_concat]
  simp only [Option.getD_some]
  apply Pnp.Karp.Clique.clauses_flatMap
  intro r hr
  simp only [List.mem_append, List.mem_map, List.mem_replicate, List.mem_singleton] at hr
  rcases hr with (⟨x, -, rfl⟩ | ⟨-, rfl⟩) | rfl <;> exact tpu_sep_nmem _

/-- The sizes of the rows are below the length of the word. -/
theorem fpr_rows_lt (u : List SatSym) (items : List (List SatSym)) (Bv : List SatSym)
    (hu : clauses u = items ++ [Bv]) :
    (items.map List.length).sum + Bv.length < u.length := by
  have h1 := Pnp.Karp.Clique.sum_length_le (clauses u)
  have h2 := Pnp.Karp.Clique.length_trunc_le u
  unfold Pnp.Karp.Clique.trunc at h2
  rw [hu] at h1 h2
  simp only [List.map_append, List.sum_append, List.length_append, List.map_singleton,
    List.sum_singleton, List.length_singleton] at h1
  omega

/-- **The generic reduction**: unary 3-PARTITION to unary 4-PARTITION. -/
theorem fpr_tpu_iff (u : List SatSym) (items : List (List SatSym)) (Bv : List SatSym)
    (hu : clauses u = items ++ [Bv]) (h3 : items.length % 3 = 0)
    (hb : ∀ r ∈ items, Bv.length < 4 * r.length ∧ 2 * r.length < Bv.length) :
    TPULang u ↔ FPULang (fpuT u) := by
  have hc := fpr_clauses u items Bv hu
  have hlt := fpr_rows_lt u items Bv hu
  set N := u.length with hN
  set B := Bv.length with hBdef
  set m := items.length / 3 with hm
  have hL : items.length = 3 * m := by omega
  set its := items.map (fun r => uRow (5 * N + r.length)) with hits
  set fil := List.replicate m (uRow (6 * N)) with hfil
  have hitsL : its.length = 3 * m := by simp [its, hL]
  have hfilL : fil.length = m := by simp [fil]
  have hBN : B < N := by omega
  have hrN : (items.map List.length).sum < N := by omega
  -- the group sums of the 4-PARTITION instance
  have hsum : ∀ (f : ℕ → ℕ) (g : ℕ), unSum (its ++ fil) f g =
      5 * N * fpr_cnt items f g + unSum items f g +
        6 * N * fpr_cnt fil (fun i => f (3 * m + i)) g := by
    intro f g
    rw [fpr_unSum_append, hitsL, fpr_unSum_map,
      fpr_unSum_const (6 * N) fil (by intro r hr; simp [fil] at hr; rw [hr.2, tpu_uRow_len])]
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · -- no items
    have hi : items = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hi' : its = [] := by simp [its, hi]
    have hf' : fil = [] := by simp [fil, hm0]
    constructor
    · intro _
      refine ⟨its ++ fil, uRow (21 * N + B), by rw [hc], by simp [hi', hf'], ?_, fun _ => 0,
        ?_, ?_⟩ <;> simp [hi', hf']
    · intro _
      refine ⟨items, Bv, hu, h3, hb, fun _ => 0, ?_, ?_⟩ <;> simp [hi]
  have hB0 : 0 < B := by
    have : items ≠ [] := by intro h; simp [h] at hL; omega
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil items this
    have := hb r hr; omega
  constructor
  · rintro ⟨items', Bv', hu', -, -, f, hf, hg⟩
    rw [hu] at hu'
    obtain ⟨rfl, hB'⟩ := List.append_inj' hu' rfl
    obtain rfl := List.singleton_inj.mp hB'
    rw [← hm] at hf hg
    let f' : ℕ → ℕ := fun i => if i < 3 * m then f i else i - 3 * m
    refine ⟨its ++ fil, uRow (21 * N + B), by rw [hc], ?_, ?_, f', ?_, ?_⟩
    · simp only [List.length_append, hitsL, hfilL]; omega
    · intro r hr
      simp only [List.mem_append, its, fil, List.mem_map, List.mem_replicate] at hr
      rw [tpu_uRow_len]
      rcases hr with ⟨x, hx, rfl⟩ | ⟨-, rfl⟩
      · have := hb x hx
        have : x.length ≤ (items.map List.length).sum :=
          List.le_sum_of_mem (List.mem_map_of_mem hx)
        rw [tpu_uRow_len]; omega
      · rw [tpu_uRow_len]; omega
    · intro i hi
      simp only [List.length_append, hitsL, hfilL] at hi ⊢
      simp only [f']
      split_ifs with h
      · have := hf i (by omega); omega
      · omega
    · intro g hg'
      simp only [List.length_append, hitsL, hfilL] at hg'
      have hg4 : g < m := by omega
      rw [hsum, fpr_unSum_congr items f' f g (fun i hi => by simp [f']; omega),
        fpr_cnt_congr items f' f g (fun i hi => by simp [f']; omega),
        fpr_cnt_congr fil _ (fun j => j + 0) g (fun j hj => by simp [f']),
        fpr_cnt_rep, hg g hg4, fpr_cnt_three B items hb hB0 f g (hg g hg4), tpu_uRow_len]
      rw [if_pos (by omega)]; ring
  · rintro ⟨items', Bv', hu', -, -, f, hf, hg⟩
    rw [hc] at hu'
    obtain ⟨rfl, hB'⟩ := List.append_inj' hu' rfl
    obtain rfl := List.singleton_inj.mp hB'
    have h4 : (its ++ fil).length / 4 = m := by
      simp only [List.length_append, hitsL, hfilL]; omega
    rw [h4] at hf hg
    refine ⟨items, Bv, hu, h3, hb, f, fun i hi => ?_, fun g hg' => ?_⟩
    · have := hf i (by simp only [List.length_append, hitsL, hfilL]; omega); omega
    · have e := hg g (by omega)
      rw [hsum, tpu_uRow_len] at e
      have hs := fpr_unSum_le items f g
      have := fpr_div (5 * fpr_cnt items f g + 6 * fpr_cnt fil (fun i => f (3 * m + i)) g)
        21 (unSum items f g) B N (by omega) hBN (by rw [← e]; ring)
      exact this.2

/-- **SAT reduces to unary 4-PARTITION** (correctness of `FPUI`). -/
theorem sat_iff_fpu (w : List SatSym) : SATLang w ↔ FPULang (FPUI w) := by
  rw [sat_iff_tpu]
  obtain ⟨hc, h3, hb⟩ := tpui_wf w
  refine fpr_tpu_iff (TPUI w) _ _ hc (by simpa using h3) ?_
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  simpa [tpu_uRow_len] using hb x hx

end Pnp.Karp.FourPartU
