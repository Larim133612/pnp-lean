import Pnp.Karp.ThreePartUProgD

/-!
# Unary 3-PARTITION reduction program, part E: the constant stacks

`tpup_kC` builds, from `QQ = false^q` (stack `4`) and `false^K` (stack `6`), the constant
stacks `18`–`25` (`false^n` for the counts of `tpup_KH`, `23` holding `false^M`, `24`
`false^L`) and the power stacks `26 + j` (`R ^ j` printed `pos`).
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.ThreePartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.BinPacking Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

/-! ## Accumulating `false`s -/

/-- Append the stacks `srcs` onto `d`. -/
def tpup_acc (d : ℕ) : List ℕ → Cmd
  | [] => .skip
  | a :: l => .seq (copyVia a d 3) (tpup_acc d l)

/-- Push `k` times `false` onto `d`. -/
def tpup_pushN (d : ℕ) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (.push d false) (tpup_pushN d k)

/-- `d := false^(Σ |srcs| + k)`. -/
def tpup_stp (d : ℕ) (srcs : List ℕ) (k : ℕ) : Cmd := .seq (tpup_acc d srcs) (tpup_pushN d k)

theorem tpup_ex_acc {d : ℕ} (hd3 : d ≠ 3) (W : ℕ) : ∀ (l : List ℕ) (σ : ℕ → Str) (m : ℕ),
    σ 3 = [] → σ d = List.replicate m false →
    (∀ a ∈ l, a ≠ d ∧ a ≠ 3 ∧ σ a = List.replicate (σ a).length false ∧ (σ a).length ≤ W) →
    ExecLe (tpup_acc d l) σ
      (.norm (update σ d (List.replicate (m + (l.map fun a => (σ a).length).sum) false)))
      (l.length * (5 * W + 4) + 1)
  | [], σ, m, _, hd, _ => (ExecLe.skip σ).cast (by congr 1; simp [← hd]) (by simp)
  | a :: l, σ, m, h3, hd, hs => by
    obtain ⟨had, ha3, hae, haW⟩ := hs a List.mem_cons_self
    have p1 := ExecLe.of (exec_copyVia had ha3 hd3 σ h3)
    have ih := tpup_ex_acc hd3 W l (update σ d (σ a ++ σ d)) ((σ a).length + m)
      (by rw [update_of_ne (by omega), h3])
      (by rw [update_self, hd, hae, List.length_replicate, List.replicate_add])
      (fun b hb => by
        obtain ⟨h1, h2, h3, h4⟩ := hs b (List.mem_cons_of_mem _ hb)
        rw [update_of_ne h1]; exact ⟨h1, h2, h3, h4⟩)
    refine (p1.seq_norm ih).cast ?_ ?_
    · congr 1; rw [update_idem]; congr 2
      have : (l.map fun b => (update σ d (σ a ++ σ d) b).length) =
          l.map fun b => (σ b).length := List.map_congr_left (fun b hb => by
        rw [update_of_ne (hs b (List.mem_cons_of_mem _ hb)).1])
      rw [this]; simp; omega
    · simp only [List.length_cons]; nlinarith

theorem tpup_ex_pushN (d : ℕ) : ∀ (k : ℕ) (σ : ℕ → Str) (m : ℕ), σ d = List.replicate m false →
    ExecLe (tpup_pushN d k) σ (.norm (update σ d (List.replicate (m + k) false))) (k + 1)
  | 0, σ, m, hd => (ExecLe.skip σ).cast (by congr 1; simp [← hd]) (by simp)
  | k + 1, σ, m, hd => by
    have p1 := ExecLe.push d false σ
    have ih := tpup_ex_pushN d k (update σ d (false :: σ d)) (m + 1)
      (by rw [update_self, hd, List.replicate_succ])
    refine (p1.seq_norm ih).cast ?_ (by omega)
    congr 1; rw [update_idem]; congr 2; omega

theorem tpup_ex_stp {d : ℕ} (hd3 : d ≠ 3) (W : ℕ) (l : List ℕ) (k : ℕ) (σ : ℕ → Str)
    (h3 : σ 3 = []) (hd : σ d = [])
    (hs : ∀ a ∈ l, a ≠ d ∧ a ≠ 3 ∧ σ a = List.replicate (σ a).length false ∧ (σ a).length ≤ W) :
    ExecLe (tpup_stp d l k) σ
      (.norm (update σ d (List.replicate ((l.map fun a => (σ a).length).sum + k) false)))
      (l.length * (5 * W + 4) + k + 2) := by
  have p1 := tpup_ex_acc hd3 W l σ 0 h3 (by rw [hd]; rfl) hs
  have p2 := tpup_ex_pushN d k _ (0 + (l.map fun a => (σ a).length).sum) (update_self d _ σ)
  refine (p1.seq_norm p2).cast ?_ (by omega)
  congr 1; rw [update_idem]; congr 2; omega

/-! ## The power stacks -/

theorem tpup_pow_le' (R : ℕ) (hR : 1 ≤ R) (j : ℕ) (hj : j ≤ 8) : R ^ j ≤ R ^ 8 :=
  Nat.pow_le_pow_right hR hj

def tpup_powC : ℕ → Cmd
  | 0 => .skip
  | j + 1 => .seq (tpup_powC j) (tpup_rep 25 (26 + j) (27 + j))

def tpup_powT (R : ℕ) : ℕ := 5 * R + 4 + (R * (5 * (2 * R ^ 8) + 5) + 2)

theorem tpup_ex_powC (R : ℕ) (hR : 1 ≤ R) (σ : ℕ → Str) (h3 : σ 3 = []) (h7 : σ 7 = [])
    (h25 : (σ 25).length = R) (h26 : σ 26 = rv [pos])
    (hz : ∀ i, 1 ≤ i → i ≤ 8 → σ (26 + i) = []) : ∀ j ≤ 8, ∃ σ',
    ExecLe (tpup_powC j) σ (.norm σ') (j * tpup_powT R + 1) ∧
    (∀ i ≤ j, σ' (26 + i) = rv (List.replicate (R ^ i) pos)) ∧
    (∀ x, (x < 27 ∨ 26 + j < x) → σ' x = σ x) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨σ, (ExecLe.skip σ).cast rfl (by simp), fun i hi => ?_, fun _ _ => rfl⟩
    obtain rfl : i = 0 := by omega
    simpa using h26
  | succ j ih =>
    intro hj
    obtain ⟨σ', p1, hp, hf⟩ := ih (by omega)
    have e7 : σ' 7 = [] := by rw [hf 7 (by omega), h7]
    have e3 : σ' 3 = [] := by rw [hf 3 (by omega), h3]
    have p2 := tpup_ex_rep (c := 25) (p := 26 + j) (d := 27 + j) (by norm_num) (by norm_num)
      (by omega) (by omega) (by omega) (by omega) (by omega) σ' e7 e3
    have e25 : (σ' 25).length = R := by rw [hf 25 (by omega), h25]
    have e27 : σ' (27 + j) = [] := by
      rw [hf _ (by omega), show 27 + j = 26 + (j + 1) by omega, hz _ (by omega) hj]
    rw [e25, hp j le_rfl, e27] at p2
    have ev : (List.replicate R (rv (List.replicate (R ^ j) pos))).flatten ++ [] =
        rv (List.replicate (R ^ (j + 1)) pos) := by
      have := tpup_rv_rep [] (R ^ j) R
      simp only [rv, List.flatMap_nil, List.reverse_nil, List.nil_append] at this ⊢
      rw [this, pow_succ', ]
    rw [ev] at p2
    refine ⟨_, p1.seq_norm p2 |>.mono ?_, fun i hi => ?_, fun x hx => ?_⟩
    · have hl : (rv (List.replicate (R ^ j) pos)).length = 2 * R ^ j := by
        simp [rv, length_flatMap_ic, ic]; ring
      rw [hl]
      have := tpup_pow_le' R hR j (by omega)
      unfold tpup_powT
      nlinarith
    · rcases Nat.lt_or_ge i (j + 1) with h | h
      · rw [update_of_ne (by omega)]; exact hp i (by omega)
      · obtain rfl : i = j + 1 := by omega
        rw [show 26 + (j + 1) = 27 + j by omega, update_self]
    · rw [update_of_ne (by omega)]; exact hf x (by omega)

/-! ## The constants -/

theorem tpup_ex_stp' {d : ℕ} (hd3 : d ≠ 3) (W : ℕ) (l : List ℕ) (k v : ℕ) (σ : ℕ → Str)
    (h3 : σ 3 = []) (hd : σ d = [])
    (hs : ∀ a ∈ l, a ≠ d ∧ a ≠ 3 ∧ σ a = List.replicate (σ a).length false ∧ (σ a).length ≤ W)
    (hv : (l.map fun a => (σ a).length).sum + k = v) :
    ExecLe (tpup_stp d l k) σ (.norm (update σ d (List.replicate v false)))
      (l.length * (5 * W + 4) + k + 2) := by
  rw [← hv]; exact tpup_ex_stp hd3 W l k σ h3 hd hs

def tpup_kC : Cmd :=
  .seq (tpup_stp 23 [6, 4, 4, 4] 0) (.seq (tpup_stp 20 [23, 23, 23, 23, 23] 2)
  (.seq (tpup_stp 19 [20, 6, 4, 4] 0) (.seq (tpup_stp 24 [23, 23, 23] 1)
  (.seq (tpup_stp 18 [24] 1) (.seq (tpup_stp 21 [24, 24, 24] 0) (.seq (tpup_stp 22 [] 1)
  (.seq (tpup_stp 25 [24, 24, 24, 24, 24, 24, 24, 24, 24] 1)
  (.seq (pushList 26 (rv [pos])) (tpup_powC 8)))))))))

def tpup_kT (R : ℕ) : ℕ := 29 * (5 * R + 4) + 30 + 8 * tpup_powT R

theorem tpup_ex_kC (q K : ℕ) (σ : ℕ → Str) (h3 : σ 3 = []) (h7 : σ 7 = [])
    (h4 : σ 4 = List.replicate q false) (h6 : σ 6 = List.replicate K false)
    (hz : ∀ j, 18 ≤ j → j ≤ 34 → σ j = []) :
    ∃ σ', ExecLe tpup_kC σ (.norm σ') (tpup_kT (uR (K + 3 * q))) ∧ (∀ j < 18, σ' j = σ j) ∧
      tpup_KH σ' q (K + 3 * q) := by
  set M := K + 3 * q with hM
  set R := uR M with hR
  have hLR : 3 * uL M + 1 ≤ R := tpup_uL_le M
  have hL : uL M = 3 * M + 1 := rfl
  have hRL : R = 9 * uL M + 1 := rfl
  set σ1 := update σ 23 (List.replicate M false)
  have p1 := tpup_ex_stp' (d := 23) (by norm_num) R [6, 4, 4, 4] 0 M σ h3 (hz _ (by omega) (by omega))
    (by intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [h4, h6] <;> omega)
    (by simp [h4, h6]; omega)
  set σ2 := update σ1 20 (List.replicate (2 * uL M - M) false)
  have p2 := tpup_ex_stp' (d := 20) (by norm_num) R [23, 23, 23, 23, 23] 2 (2 * uL M - M) σ1
    (by simp [σ1, h3]) (by simp [σ1, hz]) (by intro a ha; simp at ha; subst ha; simp [σ1]; omega)
    (by simp [σ1]; omega)
  set σ3 := update σ2 19 (List.replicate (2 * uL M - q) false)
  have p3 := tpup_ex_stp' (d := 19) (by norm_num) R [20, 6, 4, 4] 0 (2 * uL M - q) σ2
    (by simp [σ2, σ1, h3]) (by simp [σ2, σ1, hz])
    (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> simp [σ2, σ1, h4, h6] <;> omega)
    (by simp [σ2, σ1, h4, h6]; omega)
  set σ4 := update σ3 24 (List.replicate (uL M) false)
  have p4 := tpup_ex_stp' (d := 24) (by norm_num) R [23, 23, 23] 1 (uL M) σ3
    (by simp [σ3, σ2, σ1, h3]) (by simp [σ3, σ2, σ1, hz])
    (by intro a ha; simp at ha; subst ha; simp [σ3, σ2, σ1]; omega)
    (by simp [σ3, σ2, σ1]; omega)
  set σ5 := update σ4 18 (List.replicate (uL M + 1) false)
  have p5 := tpup_ex_stp' (d := 18) (by norm_num) R [24] 1 (uL M + 1) σ4
    (by simp [σ4, σ3, σ2, σ1, h3]) (by simp [σ4, σ3, σ2, σ1, hz])
    (by intro a ha; simp at ha; subst ha; simp [σ4]; omega)
    (by simp [σ4])
  set σ6 := update σ5 21 (List.replicate (3 * uL M) false)
  have p6 := tpup_ex_stp' (d := 21) (by norm_num) R [24, 24, 24] 0 (3 * uL M) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, h3]) (by simp [σ5, σ4, σ3, σ2, σ1, hz])
    (by intro a ha; simp at ha; subst ha; simp [σ5, σ4]; omega)
    (by simp [σ5, σ4]; omega)
  set σ7 := update σ6 22 (List.replicate 1 false)
  have p7 := tpup_ex_stp' (d := 22) (by norm_num) R [] 1 1 σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, h3]) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hz])
    (by simp) (by simp)
  set σ8 := update σ7 25 (List.replicate R false)
  have p8 := tpup_ex_stp' (d := 25) (by norm_num) R [24, 24, 24, 24, 24, 24, 24, 24, 24] 1 R σ7
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h3]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hz])
    (by intro a ha; simp at ha; subst ha; simp [σ7, σ6, σ5, σ4]; omega)
    (by simp [σ7, σ6, σ5, σ4]; omega)
  have p9 := ExecLe.of (exec_pushList 26 (rv [pos]) σ8)
  have e26 : σ8 26 = [] := by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hz]
  rw [e26, List.append_nil] at p9
  set σ9 := update σ8 26 (rv [pos])
  obtain ⟨σ', p10, hp, hf⟩ := tpup_ex_powC R (tpup_R_pos M) σ9
    (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, h3])
    (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, h7])
    (by simp [σ9, σ8]) (by simp [σ9])
    (fun i h1 h2 => by
      simp only [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, update_apply]
      repeat rw [if_neg (by omega)]
      exact hz (26 + i) (by omega) (by omega)) 8 le_rfl
  refine ⟨σ', (p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm (p5.seq_norm (p6.seq_norm
    (p7.seq_norm (p8.seq_norm (p9.seq_norm p10))))))))).mono ?_, fun j hj => ?_, ?_⟩
  · have : (rv [pos]).length = 2 := by simp [rv, ic]
    rw [this]; simp only [List.length_cons, List.length_nil]; unfold tpup_kT; omega
  · rw [hf j (by omega)]
    simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, show j ≠ 26 by omega, show j ≠ 25 by omega,
      show j ≠ 24 by omega, show j ≠ 23 by omega, show j ≠ 22 by omega, show j ≠ 21 by omega,
      show j ≠ 20 by omega, show j ≠ 19 by omega, show j ≠ 18 by omega]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => hp j (by omega)⟩ <;> rw [hf _ (by omega)] <;>
      simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]

end Pnp.Karp.ThreePartU
