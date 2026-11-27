import Pnp.Karp.Partition

/-!
# PARTITION: correctness of the reduction from SUBSET SUM

`ss_iff_part`: a SUBSET SUM instance `w` (target `t`, items `as`, sum `S`) is a yes-instance
iff its PARTITION instance `PI w` (items `as`, `S`, `2t`) is one.
-/

namespace Pnp.Karp.Partition

open Pnp.Relativize Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum

/-- The complementary selection. -/
def pr_cmpl : List (List SatSym) → List Bool → List Bool
  | [], _ => []
  | _ :: L, y => (!y.headD false) :: pr_cmpl L y.tail

theorem pr_sel_add_cmpl : ∀ (L : List (List SatSym)) (y : List Bool),
    selSum L y + selSum L (pr_cmpl L y) = totSum L
  | [], _ => rfl
  | r :: L, [] => by
    have ih := pr_sel_add_cmpl L []
    simp only [selSum, pr_cmpl, totSum, List.headD_nil, List.tail_nil] at ih ⊢
    simp; omega
  | r :: L, b :: y => by
    have ih := pr_sel_add_cmpl L y
    simp only [selSum, pr_cmpl, totSum, List.headD_cons, List.tail_cons] at ih ⊢
    cases b <;> simp <;> omega

theorem pr_sel_le (L : List (List SatSym)) (y : List Bool) : selSum L y ≤ totSum L := by
  have := pr_sel_add_cmpl L y; omega

theorem pr_sel_append : ∀ (L₁ L₂ : List (List SatSym)) (y : List Bool),
    selSum (L₁ ++ L₂) y = selSum L₁ y + selSum L₂ (y.drop L₁.length)
  | [], _, _ => by simp [selSum]
  | r :: L₁, L₂, y => by
    have ih := pr_sel_append L₁ L₂ y.tail
    simp only [List.cons_append, selSum, List.length_cons, ih, List.drop_tail]
    omega

theorem pr_tot_append : ∀ L₁ L₂ : List (List SatSym), totSum (L₁ ++ L₂) = totSum L₁ + totSum L₂
  | [], _ => by simp [totSum]
  | r :: L₁, L₂ => by simp only [List.cons_append, totSum, pr_tot_append L₁ L₂]; omega

/-- The selection `y` cut or padded to length `|L|`. -/
def pr_norm : List (List SatSym) → List Bool → List Bool
  | [], _ => []
  | _ :: L, y => y.headD false :: pr_norm L y.tail

theorem pr_length_norm : ∀ (L : List (List SatSym)) (y : List Bool), (pr_norm L y).length = L.length
  | [], _ => rfl
  | _ :: L, y => by simp [pr_norm, pr_length_norm L y.tail]

theorem pr_length_cmpl : ∀ (L : List (List SatSym)) (y : List Bool), (pr_cmpl L y).length = L.length
  | [], _ => rfl
  | _ :: L, y => by simp [pr_cmpl, pr_length_cmpl L y.tail]

theorem pr_sel_norm : ∀ (L : List (List SatSym)) (y z : List Bool),
    selSum L (pr_norm L y ++ z) = selSum L y
  | [], _, _ => by simp [selSum]
  | r :: L, y, z => by
    simp only [pr_norm, List.cons_append, selSum, List.headD_cons, List.tail_cons,
      pr_sel_norm L y.tail z]; rfl

theorem pr_sel_cmpl_app (L : List (List SatSym)) (y z : List Bool) :
    selSum L (pr_cmpl L y ++ z) = selSum L (pr_cmpl L y) := by
  have := pr_sel_norm L (pr_cmpl L y) z
  have e : pr_norm L (pr_cmpl L y) = pr_cmpl L y := by
    clear this
    induction L generalizing y with
    | nil => rfl
    | cons r L ih => simp [pr_norm, pr_cmpl, ih]
  rw [e] at this; exact this

theorem pr_bv_toRow : ∀ A : Str, bv (toRow A) = sv_bval A
  | [] => rfl
  | b :: A => by
    have ih := pr_bv_toRow A
    simp only [toRow, List.map_cons] at ih ⊢
    cases b <;> simp [bv, sv_bval, ih]

theorem pr_bval_acc : ∀ (A : Str) (L : List (List SatSym)),
    sv_bval (accRows A L) = sv_bval A + totSum L
  | A, [] => by simp [accRows, totSum]
  | A, r :: L => by
    rw [accRows, pr_bval_acc, sv_bval_addL, sv_bval_bits, totSum]; simp; omega

theorem pr_sep_toRow (A : Str) : sep ∉ toRow A := by
  simp only [toRow, List.mem_map, not_exists, not_and]
  intro b _; cases b <;> simp

/-- **Correctness of the reduction** SUBSET SUM → PARTITION. -/
theorem ss_iff_part (w : List SatSym) : SSLang w ↔ PartLang (PI w) := by
  unfold SSLang PartLang PI
  rcases hw : clauses w with _ | ⟨t, as⟩
  · constructor
    · rintro ⟨_, _, h, _⟩; exact absurd h (by simp)
    · rintro ⟨y, hy⟩
      change 2 * selSum [[pos]] y = totSum [[pos]] at hy
      simp only [selSum, totSum, bv] at hy
      split_ifs at hy <;> omega
  · have hsep : ∀ c ∈ as ++ [toRow (accRows [] as), zero :: toRow (sv_bits t)], sep ∉ c := by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | rfl | rfl
      · exact sep_not_mem_clauses w c (by rw [hw]; exact List.mem_cons_of_mem _ hc)
      · exact pr_sep_toRow _
      · simp only [List.mem_cons, reduceCtorEq, false_or]; exact pr_sep_toRow _
    rw [clauses_flatMap _ hsep]
    have hu : bv (toRow (accRows [] as)) = totSum as := by
      rw [pr_bv_toRow, pr_bval_acc]; simp [sv_bval]
    have hv : bv (zero :: toRow (sv_bits t)) = 2 * bv t := by
      simp [bv, pr_bv_toRow, sv_bval_bits]
    have htot : totSum (as ++ [toRow (accRows [] as), zero :: toRow (sv_bits t)]) =
        2 * totSum as + 2 * bv t := by
      rw [pr_tot_append]; simp only [totSum, hu, hv]; omega
    rw [htot]
    constructor
    · rintro ⟨t', as', h, y, hy⟩
      injection h with h1 h2; subst h1; subst h2
      refine ⟨pr_norm as y ++ [true, false], ?_⟩
      rw [pr_sel_append, pr_sel_norm, List.drop_left' (pr_length_norm as y)]
      simp only [selSum, List.headD_cons, List.tail_cons, if_true, hu, hv]
      simp; omega
    · rintro ⟨y, hy⟩
      refine ⟨t, as, rfl, ?_⟩
      rw [pr_sel_append] at hy
      have hle := pr_sel_le as y
      have hc := pr_sel_add_cmpl as y
      set A := selSum as y
      rcases hd : y.drop as.length with _ | ⟨bu, _ | ⟨bv', z⟩⟩
      all_goals rw [hd] at hy
      all_goals simp only [selSum, List.headD_nil, List.headD_cons, List.tail_cons, List.tail_nil,
        hu, hv, Bool.false_eq_true, if_false] at hy
      all_goals try (cases bu)
      all_goals try (cases bv')
      all_goals try simp only [Bool.false_eq_true, if_false, if_true] at hy
      all_goals first
        | exact ⟨y, by omega⟩
        | exact ⟨pr_cmpl as y, by omega⟩

end Pnp.Karp.Partition
