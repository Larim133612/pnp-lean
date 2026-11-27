import Pnp.Karp.Knapsack

/-!
# KNAPSACK ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(rows `W :: V :: items`, `Pnp/Karp/Knapsack.lean`) and a certificate `y : List Bool` (bit `i`
says whether item `i`, i.e. the rows `2i`, `2i+1` of `items`, is selected; missing bits are
`false`).  Numbers are bit stacks, least significant bit on top.  It reuses the ripple-carry
adder of the SUBSET SUM verifier (`Pnp/Karp/SubVer.lean`).  Stack layout of the main phase
(`kv_st`):

* `0`: the unread certificate bits `R`;  `3`: the internal code of the remaining rows `Q`;
* `4`: the capacity `W`;  `5`: the weight accumulator `AW`;  `9`: the value accumulator `AV`;
  `10`: the value goal `V`;  `6`, `7`: sum bits and carry of the adder;  `11`: the flag of the
  final comparisons.

Two generic tools let the adder `sv_addLoop` (stacks `3`–`7`) run in this layout:
`kv_exec_mix` (a command that avoids the stacks in `F` leaves them alone) and `kv_exec_ren`
(renaming stacks by a permutation; `kv_addV` is `sv_addLoop` with stacks `5` and `9` swapped).

Program (`kv_ver`):
1. `phaseA`, `trimC 2`, `move 2 3` (as for SUBSET SUM); `sv_frLoop`: read `W` (halt `false`
   if there is no row), `move 8 4`; `sv_frLoop`: read `V` (halt `false` if there is no second
   row), `move 8 10`;
2. `kv_mainLoop`: per item: if no row is left, run the final test `kv_fin`; otherwise pop a
   certificate bit, add the weight row to `AW` (or skip it); if no row is left (an unpaired
   last row: value `0`), run `kv_fin`; otherwise add the value row to `AV` (or skip it);
3. `kv_fin`: `AW ≤ W` and `V ≤ AV` by `kv_cmpLoop` (flag "`≤` so far": where the bits differ
   it becomes `a < b`, missing bits are `0`; `kv_leF`).

`kv_exec_ver`: the program halts with `kv_vres (dec z).1 (dec z).2` on every input `z`, within
`kv_Tver |z| ≤ tb 8 |z|` steps.
-/

namespace Pnp.Karp.Knapsack

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

/-! ## Frames and renamings of stacks -/

/-- `c` does not touch the stacks in `F` (and makes no calls). -/
def kv_av (F : ℕ → Bool) : Cmd → Bool
  | .push k _ => !F k
  | .pop k cn cf ct => !F k && kv_av F cn && kv_av F cf && kv_av F ct
  | .seq c d => kv_av F c && kv_av F d
  | .skip => true
  | .halt _ => true
  | .loop c => kv_av F c
  | .brk => true
  | .call .. => false

/-- `c` makes no calls. -/
def kv_nc : Cmd → Bool
  | .pop _ cn cf ct => kv_nc cn && kv_nc cf && kv_nc ct
  | .seq c d => kv_nc c && kv_nc d
  | .loop c => kv_nc c
  | .call .. => false
  | _ => true

/-- `c` with stack `k` renamed to `π k`. -/
def kv_ren (π : Equiv.Perm ℕ) : Cmd → Cmd
  | .push k b => .push (π k) b
  | .pop k cn cf ct => .pop (π k) (kv_ren π cn) (kv_ren π cf) (kv_ren π ct)
  | .seq c d => .seq (kv_ren π c) (kv_ren π d)
  | .skip => .skip
  | .halt b => .halt b
  | .loop c => .loop (kv_ren π c)
  | .brk => .brk
  | .call q o cf ct => .call q o cf ct

/-- The stacks `σ` with the stacks in `F` taken from `ρ`. -/
def kv_mix (F : ℕ → Bool) (σ ρ : ℕ → Str) : ℕ → Str := fun j => if F j then ρ j else σ j

/-- Map the stacks of a result. -/
def kv_rmap (g : (ℕ → Str) → ℕ → Str) : Res → Res
  | .norm σ => .norm (g σ)
  | .brk σ => .brk (g σ)
  | .halt b => .halt b

theorem kv_mix_update {F : ℕ → Bool} {k : ℕ} (hk : F k = false) (σ ρ : ℕ → Str) (s : Str) :
    kv_mix F (update σ k s) ρ = update (kv_mix F σ ρ) k s := by
  funext j; simp only [kv_mix, update_apply]; split_ifs <;> simp_all

theorem kv_exec_mix {F : ℕ → Bool} (ρ : ℕ → Str) {c : Cmd} {σ : ℕ → Str} {r : Res} {t : ℕ}
    (h : Exec c σ r t) : kv_av F c = true →
    Exec c (kv_mix F σ ρ) (kv_rmap (kv_mix F · ρ) r) t := by
  induction h with
  | push k b σ =>
    intro hc
    simp only [kv_av, Bool.not_eq_true'] at hc
    have := Exec.push k b (kv_mix F σ ρ)
    rw [show kv_mix F σ ρ k = σ k by simp [kv_mix, hc]] at this
    rwa [kv_rmap, kv_mix_update hc]
  | pop_nil hk _ ih =>
    intro hc
    simp only [kv_av, Bool.and_eq_true, Bool.not_eq_true'] at hc
    exact .pop_nil (by simp [kv_mix, hc.1.1.1, hk]) (ih hc.1.1.2)
  | @pop_cons k cn cf ct σ b s r t hk _ ih =>
    intro hc
    simp only [kv_av, Bool.and_eq_true, Bool.not_eq_true'] at hc
    refine .pop_cons (b := b) (s := s) (by simp [kv_mix, hc.1.1.1, hk]) ?_
    rw [← kv_mix_update hc.1.1.1]
    exact ih (by cases b <;> simp [hc])
  | seq_norm _ _ ih1 ih2 =>
    intro hc; simp only [kv_av, Bool.and_eq_true] at hc
    exact .seq_norm (ih1 hc.1) (ih2 hc.2)
  | seq_brk _ ih => intro hc; simp only [kv_av, Bool.and_eq_true] at hc; exact .seq_brk (ih hc.1)
  | seq_halt _ ih => intro hc; simp only [kv_av, Bool.and_eq_true] at hc; exact .seq_halt (ih hc.1)
  | skip σ => intro _; exact .skip _
  | halt b σ => intro _; exact .halt b _
  | brk σ => intro _; exact .brk _
  | loop_norm _ _ ih1 ih2 => intro hc; exact .loop_norm (ih1 hc) (ih2 hc)
  | loop_brk _ ih => intro hc; exact .loop_brk (ih hc)
  | loop_halt _ ih => intro hc; exact .loop_halt (ih hc)
  | call => intro hc; simp [kv_av] at hc

theorem kv_mix_le {F : ℕ → Bool} (ρ : ℕ → Str) {c : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ}
    (h : ExecLe c σ r T) (hc : kv_av F c = true) :
    ExecLe c (kv_mix F σ ρ) (kv_rmap (kv_mix F · ρ) r) T := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, ht, kv_exec_mix ρ h hc⟩

theorem kv_exec_ren (π : Equiv.Perm ℕ) {c : Cmd} {σ : ℕ → Str} {r : Res} {t : ℕ}
    (h : Exec c σ r t) : kv_nc c = true →
    Exec (kv_ren π c) (σ ∘ π.symm) (kv_rmap (· ∘ π.symm) r) t := by
  induction h with
  | push k b σ =>
    intro _
    have := Exec.push (π k) b (σ ∘ π.symm)
    rw [show (σ ∘ π.symm) (π k) = σ k by simp] at this
    rwa [kv_rmap, update_comp_equiv, Equiv.symm_symm]
  | pop_nil hk _ ih =>
    intro hc
    simp only [kv_nc, Bool.and_eq_true] at hc
    exact .pop_nil (by simp [hk]) (ih hc.1.1)
  | @pop_cons k cn cf ct σ b s r t hk _ ih =>
    intro hc
    simp only [kv_nc, Bool.and_eq_true] at hc
    refine .pop_cons (b := b) (s := s) (by simp [hk]) ?_
    have e : update (σ ∘ π.symm) (π k) s = update σ k s ∘ π.symm := by
      rw [update_comp_equiv, Equiv.symm_symm]
    rw [e]
    have := ih (by cases b <;> simp [hc])
    cases b <;> exact this
  | seq_norm _ _ ih1 ih2 =>
    intro hc; simp only [kv_nc, Bool.and_eq_true] at hc
    exact .seq_norm (ih1 hc.1) (ih2 hc.2)
  | seq_brk _ ih => intro hc; simp only [kv_nc, Bool.and_eq_true] at hc; exact .seq_brk (ih hc.1)
  | seq_halt _ ih => intro hc; simp only [kv_nc, Bool.and_eq_true] at hc; exact .seq_halt (ih hc.1)
  | skip σ => intro _; exact .skip _
  | halt b σ => intro _; exact .halt b _
  | brk σ => intro _; exact .brk _
  | loop_norm _ _ ih1 ih2 => intro hc; exact .loop_norm (ih1 hc) (ih2 hc)
  | loop_brk _ ih => intro hc; exact .loop_brk (ih hc)
  | loop_halt _ ih => intro hc; exact .loop_halt (ih hc)
  | call => intro hc; simp [kv_nc] at hc

theorem kv_ren_le (π : Equiv.Perm ℕ) {c : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ}
    (h : ExecLe c σ r T) (hc : kv_nc c = true) :
    ExecLe (kv_ren π c) (σ ∘ π.symm) (kv_rmap (· ∘ π.symm) r) T := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, ht, kv_exec_ren π h hc⟩



/-! ## Comparison -/

/-- One step of the comparison: bits `x` of `A`, `y` of `B`, flag "`A ≤ B` so far". -/
def kv_stp (g x y : Bool) : Bool := if x = y then g else y

/-- The comparison as the program does it (`g`: the flag of the lower bits). -/
def kv_leF : Bool → Str → Str → Bool
  | g, [], [] => g
  | g, [], y :: B => kv_leF (kv_stp g false y) [] B
  | g, x :: A, [] => kv_leF (kv_stp g x false) A []
  | g, x :: A, y :: B => kv_leF (kv_stp g x y) A B

/-- Update the flag on stack `f` for bits `x`, `y`. -/
def kv_S (f : ℕ) (x y : Bool) : Cmd :=
  if x = y then .skip else if y then .seq (.pop f .skip .skip .skip) (.push f true)
  else .pop f .skip .skip .skip

def kv_cmpB (a b f : ℕ) : Cmd :=
  .pop a (.pop b .brk (kv_S f false false) (kv_S f false true))
    (.pop b (kv_S f false false) (kv_S f false false) (kv_S f false true))
    (.pop b (kv_S f true false) (kv_S f true false) (kv_S f true true))

def kv_cmpLoop (a b f : ℕ) : Cmd := .loop (kv_cmpB a b f)

theorem kv_ex_S (f : ℕ) (x y g : Bool) (σ : ℕ → Str) (hf : σ f = CookLevin.fl g) :
    ExecLe (kv_S f x y) σ (.norm (update σ f (CookLevin.fl (kv_stp g x y)))) 3 := by
  have hc : ExecLe (Cmd.pop f .skip .skip .skip) σ (.norm (update σ f [])) 2 := by
    cases g
    · exact (ExecLe.pop_nil hf (ExecLe.skip _)).cast (by
        rw [show ([] : Str) = σ f by simp [hf, CookLevin.fl], update_eq_self]) le_rfl
    · exact ExecLe.pop_cons (b := true) (s := []) hf (ExecLe.skip _)
  cases x <;> cases y
  · refine (ExecLe.skip σ).cast ?_ (by omega)
    simp [kv_stp, ← hf]
  · refine (hc.seq_norm (ExecLe.push f true _)).cast ?_ le_rfl
    simp [kv_stp, CookLevin.fl]
  · refine hc.cast ?_ (by omega)
    simp [kv_stp, CookLevin.fl]
  · refine (ExecLe.skip σ).cast ?_ (by omega)
    simp [kv_stp, ← hf]

section Cmp
variable {a b f : ℕ} (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f)
include hab haf hbf

theorem kv_ex_cmpB (A B : Str) (g : Bool) (σ : ℕ → Str) (ha : σ a = A) (hb : σ b = B)
    (hf : σ f = CookLevin.fl g) (hne : A ≠ [] ∨ B ≠ []) :
    ∃ σ₁, ExecLe (kv_cmpB a b f) σ (.norm σ₁) 5 ∧ σ₁ a = A.tail ∧ σ₁ b = B.tail ∧
      σ₁ f = CookLevin.fl (kv_stp g (A.headD false) (B.headD false)) ∧
      ∀ j, j ≠ a → j ≠ b → j ≠ f → σ₁ j = σ j := by
  refine ⟨update (update (update σ a A.tail) b B.tail) f
    (CookLevin.fl (kv_stp g (A.headD false) (B.headD false))), ?_, by simp [haf, hab],
    by simp [hbf], by simp, fun j h1 h2 h3 => by simp [h1, h2, h3]⟩
  have hf' : ∀ s s', update (update σ a s) b s' f = CookLevin.fl g := by
    intro s s'; simp [hf, haf.symm, hbf.symm]
  rcases A with _ | ⟨x, A⟩ <;> rcases B with _ | ⟨y, B⟩
  · simp at hne
  · have e : update σ a [] = σ := by rw [← ha, update_eq_self]
    have hb' : update σ a [] b = y :: B := by rw [e, hb]
    have hs := kv_ex_S f false y g _ (hf' [] B)
    refine ExecLe.pop_nil (by rw [← ha]) ?_
    rw [← e]
    refine ExecLe.pop_cons hb' ?_
    cases y <;> exact hs.cast (by simp) (by omega)
  · have hb' : update σ a A b = [] := by simp [hab.symm, hb]
    have hs := kv_ex_S f x false g _ (hf' A [])
    have e : update (update σ a A) b [] = update σ a A := by rw [← hb', update_eq_self]
    refine ExecLe.pop_cons ha ?_
    rw [e] at hs
    cases x <;> exact ExecLe.pop_nil hb' (hs.cast (by simp [e]) (by omega))
  · have hb' : update σ a A b = y :: B := by simp [hab.symm, hb]
    have hs := kv_ex_S f x y g _ (hf' A B)
    refine ExecLe.pop_cons ha ?_
    cases x <;> exact ExecLe.pop_cons hb' (by cases y <;> exact hs.cast (by simp) (by omega))

theorem kv_ex_cmp : ∀ (A B : Str) (g : Bool) (σ : ℕ → Str), σ a = A → σ b = B →
    σ f = CookLevin.fl g →
    ∃ σ', ExecLe (kv_cmpLoop a b f) σ (.norm σ') (5 * (A.length + B.length) + 3) ∧
      σ' f = CookLevin.fl (kv_leF g A B) ∧ ∀ j, j ≠ a → j ≠ b → j ≠ f → σ' j = σ j
  | [], [], g, σ, ha, hb, hf =>
    ⟨σ, (ExecLe.loop_brk (ExecLe.pop_nil ha (ExecLe.pop_nil hb (ExecLe.brk _)))).cast rfl
      (by simp), by simp [kv_leF, hf], fun _ _ _ _ => rfl⟩
  | [], y :: B, g, σ, ha, hb, hf => by
    obtain ⟨σ₁, h1, h1a, h1b, h1f, h1j⟩ := kv_ex_cmpB hab haf hbf [] (y :: B) g σ ha hb hf
      (by simp)
    obtain ⟨σ', h2, h2f, h2j⟩ := kv_ex_cmp [] B _ σ₁ h1a h1b h1f
    refine ⟨σ', (ExecLe.loop_norm h1 h2).cast rfl (by simp; omega), by simpa [kv_leF] using h2f,
      fun j j1 j2 j3 => by rw [h2j j j1 j2 j3, h1j j j1 j2 j3]⟩
  | x :: A, [], g, σ, ha, hb, hf => by
    obtain ⟨σ₁, h1, h1a, h1b, h1f, h1j⟩ := kv_ex_cmpB hab haf hbf (x :: A) [] g σ ha hb hf
      (by simp)
    obtain ⟨σ', h2, h2f, h2j⟩ := kv_ex_cmp A [] _ σ₁ h1a h1b h1f
    refine ⟨σ', (ExecLe.loop_norm h1 h2).cast rfl (by simp; omega), by simpa [kv_leF] using h2f,
      fun j j1 j2 j3 => by rw [h2j j j1 j2 j3, h1j j j1 j2 j3]⟩
  | x :: A, y :: B, g, σ, ha, hb, hf => by
    obtain ⟨σ₁, h1, h1a, h1b, h1f, h1j⟩ := kv_ex_cmpB hab haf hbf (x :: A) (y :: B) g σ ha hb
      hf (by simp)
    obtain ⟨σ', h2, h2f, h2j⟩ := kv_ex_cmp A B _ σ₁ h1a h1b h1f
    refine ⟨σ', (ExecLe.loop_norm h1 h2).cast rfl (by simp; omega), by simpa [kv_leF] using h2f,
      fun j j1 j2 j3 => by rw [h2j j j1 j2 j3, h1j j j1 j2 j3]⟩

end Cmp

/-- The final test: `AW ≤ W` (stacks `5`, `4`) and `V ≤ AV` (stacks `10`, `9`); flag on `11`. -/
def kv_fin : Cmd :=
  .seq (.push 11 true) (.seq (kv_cmpLoop 5 4 11) (.pop 11 (.halt false) (.halt false)
    (.seq (.push 11 true) (.seq (kv_cmpLoop 10 9 11) (.pop 11 (.halt false) (.halt false)
      (.halt true))))))

theorem kv_ex_fin (W V AW AV : Str) (σ : ℕ → Str) (h4 : σ 4 = W) (h5 : σ 5 = AW)
    (h9 : σ 9 = AV) (h10 : σ 10 = V) (h11 : σ 11 = []) :
    ExecLe kv_fin σ (.halt (kv_leF true AW W && kv_leF true V AV))
      (5 * (W.length + V.length + AW.length + AV.length) + 14) := by
  have hp := ExecLe.push 11 true σ
  rw [h11] at hp
  obtain ⟨σ', h1, h1f, h1j⟩ := kv_ex_cmp (a := 5) (b := 4) (f := 11) (by decide) (by decide)
    (by decide) AW W true (update σ 11 [true]) (by simp [h5]) (by simp [h4]) (by simp [CookLevin.fl])
  refine (hp.seq_norm (h1.seq_norm (T₂ := 5 * (V.length + AV.length) + 7) ?_)).cast rfl
    (by omega)
  cases hr : kv_leF true AW W
  · rw [hr] at h1f
    exact (ExecLe.pop_nil h1f (ExecLe.halt false _)).cast (by simp) (by omega)
  · rw [hr] at h1f
    refine ExecLe.pop_cons (b := true) (s := []) h1f ?_
    have hp2 := ExecLe.push 11 true (update σ' 11 [])
    rw [update_self, update_idem] at hp2
    obtain ⟨σ'', h2, h2f, -⟩ := kv_ex_cmp (a := 10) (b := 9) (f := 11) (by decide) (by decide)
      (by decide) V AV true (update σ' 11 [true]) (by simp [h1j 10, h10]) (by simp [h1j 9, h9])
      (by simp [CookLevin.fl])
    refine (hp2.seq_norm (h2.seq_norm (T₂ := 2) ?_)).cast rfl (by omega)
    cases hr2 : kv_leF true V AV
    · rw [hr2] at h2f
      exact (ExecLe.pop_nil h2f (ExecLe.halt false _)).cast (by simp) (by omega)
    · rw [hr2] at h2f
      exact (ExecLe.pop_cons (b := true) (s := []) h2f (ExecLe.halt true _)).cast (by simp)
        (by omega)


/-! ## The main loop -/

/-- What the main loop computes (`W`, `V`: capacity and goal, `R`: unread certificate bits,
`AW`, `AV`: the accumulators). -/
def kv_go (W V : Str) : List (List SatSym) → Str → Str → Str → Bool
  | [], _, AW, AV => kv_leF true AW W && kv_leF true V AV
  | [a], R, AW, AV =>
    kv_leF true (if R.headD false then sv_addL false AW (sv_bits a) else AW) W && kv_leF true V AV
  | a :: b :: rows, R, AW, AV =>
    if R.headD false then
      kv_go W V rows R.tail (sv_addL false AW (sv_bits a)) (sv_addL false AV (sv_bits b))
    else kv_go W V rows R.tail AW AV

/-- The stacks of the main phase. -/
def kv_st (R Q W V AW AV : Str) : ℕ → Str := fun j =>
  if j = 0 then R else if j = 3 then Q else if j = 4 then W else if j = 5 then AW else
  if j = 9 then AV else if j = 10 then V else []

/-- The stacks `≥ 8` (untouched by the adder of `SubVer.lean`). -/
def kv_F : ℕ → Bool := fun j => decide (8 ≤ j)

/-- The renaming for the value accumulator. -/
def kv_π : Equiv.Perm ℕ := Equiv.swap 5 9

theorem kv_av_add : kv_av kv_F sv_addLoop = true := by decide
theorem kv_av_skip : kv_av kv_F sv_skipLoop = true := by decide
theorem kv_nc_add : kv_nc sv_addLoop = true := by decide

theorem kv_u0 {R Q W V AW AV : Str} (R' : Str) :
    update (kv_st R Q W V AW AV) 0 R' = kv_st R' Q W V AW AV := by
  funext j; simp only [kv_st, update_apply]; split_ifs <;> simp_all

theorem kv_mix_st (R Q W V A R₂ Q₂ W₂ A₂ AV : Str) :
    kv_mix kv_F (sv_st R Q W A [] false) (kv_st R₂ Q₂ W₂ V A₂ AV) = kv_st R Q W V A AV := by
  funext j; simp only [kv_mix, kv_F, sv_st, kv_st, CookLevin.fl, decide_eq_true_eq]
  split_ifs <;> first | rfl | omega

theorem kv_ren_st (R Q W V X R₂ Q₂ W₂ Y Z : Str) :
    kv_mix kv_F (sv_st R Q W X [] false) (kv_st R₂ Q₂ W₂ V Y Z) ∘ kv_π.symm =
      kv_st R Q W V Z X := by
  funext j; simp only [comp_apply, kv_π, Equiv.symm_swap, Equiv.swap_apply_def]
  by_cases h5 : j = 5
  · subst h5; simp [kv_mix, kv_F, kv_st]
  by_cases h9 : j = 9
  · subst h9; simp [kv_mix, kv_F, sv_st, kv_st]
  simp only [h5, h9, if_false]
  simp only [kv_mix, kv_F, sv_st, kv_st, CookLevin.fl, decide_eq_true_eq]
  split_ifs <;> first | rfl | omega

/-- Test whether stack `3` is empty (run `kv_fin` then) and continue with `c` otherwise. -/
def kv_peek (c : Cmd) : Cmd := .pop 3 kv_fin (.seq (.push 3 false) c) (.seq (.push 3 true) c)

theorem kv_ex_peek {c : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ} {x : Bool} {Q' : Str}
    (h3 : σ 3 = x :: Q') (h : ExecLe c σ r T) : ExecLe (kv_peek c) σ r (T + 2) := by
  have e : update (update σ 3 Q') 3 (x :: update σ 3 Q' 3) = σ := by
    rw [update_self, update_idem, ← h3, update_eq_self]
  have hp := ExecLe.push 3 x (update σ 3 Q')
  rw [e] at hp
  refine ExecLe.pop_cons (T := T + 1) h3 ?_
  cases x
  · exact (hp.seq_norm h).cast rfl (by omega)
  · exact (hp.seq_norm h).cast rfl (by omega)

theorem kv_ex_peek_nil {c : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ} (h3 : σ 3 = [])
    (h : ExecLe kv_fin σ r T) : ExecLe (kv_peek c) σ r (T + 1) := ExecLe.pop_nil h3 h

/-- Add the row on stack `3` to the value accumulator (stack `9`). -/
def kv_addV : Cmd := kv_ren kv_π sv_addLoop

def kv_SK : Cmd := .seq sv_skipLoop (kv_peek sv_skipLoop)

def kv_AD : Cmd := .seq sv_addLoop (kv_peek kv_addV)

def kv_mainB : Cmd := kv_peek (.pop 0 kv_SK kv_SK kv_AD)

def kv_mainLoop : Cmd := .loop kv_mainB

section Rows
variable {R W V : Str}

theorem kv_ex_addW (N : ℕ) (Q' : Str) (r : List SatSym) (AW AV : Str) (hr : sep ∉ r)
    (hN : AW.length + r.length ≤ N) :
    ExecLe sv_addLoop (kv_st R (r.flatMap ic ++ false :: false :: Q') W V AW AV)
      (.norm (kv_st R Q' W V (sv_addL false AW (sv_bits r)) AV)) (7 * r.length + 8 * N + 20) := by
  have h := kv_mix_le (kv_st R (r.flatMap ic ++ false :: false :: Q') W V AW AV)
    (sv_ex_addRow (R := R) (T := W) N Q' r AW [] false hr (by simp; omega)) kv_av_add
  rw [kv_mix_st] at h
  refine h.cast ?_ le_rfl
  simp only [kv_rmap, List.reverse_nil, List.nil_append]
  rw [kv_mix_st]

theorem kv_ex_addV (N : ℕ) (Q' : Str) (r : List SatSym) (AW AV : Str) (hr : sep ∉ r)
    (hN : AV.length + r.length ≤ N) :
    ExecLe kv_addV (kv_st R (r.flatMap ic ++ false :: false :: Q') W V AW AV)
      (.norm (kv_st R Q' W V AW (sv_addL false AV (sv_bits r)))) (7 * r.length + 8 * N + 20) := by
  have h := kv_ren_le kv_π (kv_mix_le (kv_st R Q' W V AV AW)
    (sv_ex_addRow (R := R) (T := W) N Q' r AV [] false hr (by simp; omega)) kv_av_add) kv_nc_add
  rw [kv_ren_st] at h
  refine h.cast ?_ le_rfl
  simp only [kv_rmap, List.reverse_nil, List.nil_append]
  rw [kv_ren_st]

theorem kv_ex_skip (Q' : Str) (r : List SatSym) (AW AV : Str) (hr : sep ∉ r) :
    ExecLe sv_skipLoop (kv_st R (r.flatMap ic ++ false :: false :: Q') W V AW AV)
      (.norm (kv_st R Q' W V AW AV)) (3 * r.length + 3) := by
  have h := kv_mix_le (kv_st R (r.flatMap ic ++ false :: false :: Q') W V AW AV)
    (sv_ex_skipRow (R := R) (T := W) AW Q' r hr) kv_av_skip
  rw [kv_mix_st] at h
  refine h.cast ?_ le_rfl
  simp only [kv_rmap]
  rw [kv_mix_st]

theorem kv_enc_ne (r : List SatSym) (rows : List (List SatSym)) :
    ∃ x Q', enc (r :: rows) = x :: Q' := by
  rw [enc_cons]
  cases h : r.flatMap ic with
  | nil => exact ⟨false, _, rfl⟩
  | cons x Q' => exact ⟨x, _, rfl⟩

theorem kv_ex_fin' (N : ℕ) (R Q AW AV : Str) (hWV : W.length + V.length ≤ N)
    (hA : AW.length + AV.length ≤ N) :
    ExecLe kv_fin (kv_st R Q W V AW AV) (.halt (kv_leF true AW W && kv_leF true V AV))
      (10 * N + 14) :=
  (kv_ex_fin W V AW AV _ rfl rfl rfl rfl rfl).cast rfl (by omega)

/-- Cost of the main loop. -/
def kv_T (N : ℕ) (rows : List (List SatSym)) : ℕ := (rows.length + 1) * (30 * N + 60)

theorem kv_ex_rows (N : ℕ) (hWV : W.length + V.length ≤ N) : ∀ (rows : List (List SatSym))
    (R AW AV : Str), (∀ r ∈ rows, sep ∉ r) →
    AW.length + AV.length + (rows.map List.length).sum + rows.length ≤ N →
    ExecLe kv_mainLoop (kv_st R (enc rows) W V AW AV) (.halt (kv_go W V rows R AW AV))
      (kv_T N rows)
  | [], R, AW, AV, _, hN => by
    simp only [List.map_nil, List.sum_nil, List.length_nil] at hN
    exact (ExecLe.loop_halt (kv_ex_peek_nil rfl (kv_ex_fin' N R _ AW AV hWV (by omega)))).cast
      (by simp [kv_go]) (by simp [kv_T]; omega)
  | [a], R, AW, AV, hrows, hN => by
    have ha : sep ∉ a := hrows a (by simp)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at hN
    obtain ⟨x, Q', hQ⟩ := kv_enc_ne a []
    have hl := sv_addL_length false AW (sv_bits a)
    simp only [sv_bits, List.length_map] at hl
    have hsk := kv_ex_skip (R := R.tail) (W := W) (V := V) (enc []) a AW AV ha
    have hfin := fun A' : Str => fun h : A'.length + AV.length ≤ N =>
      kv_ex_fin' (W := W) (V := V) N R.tail (enc []) A' AV hWV h
    have hb : ExecLe (.pop 0 kv_SK kv_SK kv_AD) (kv_st R (enc [a]) W V AW AV)
        (.halt (kv_go W V [a] R AW AV)) (25 * N + 50) := by
      rw [enc_cons]
      rcases R with _ | ⟨_ | _, R'⟩
      · exact (ExecLe.pop_nil rfl (hsk.seq_norm (kv_ex_peek_nil rfl (hfin AW (by omega))))).cast
          (by simp [kv_go]) (by omega)
      · have h := hsk.seq_norm (kv_ex_peek_nil (c := sv_skipLoop) rfl (hfin AW (by omega)))
        exact (ExecLe.pop_cons (b := false) (s := R') rfl (by rw [kv_u0]; exact h)).cast
          (by simp [kv_go]) (by omega)
      · have h := (kv_ex_addW (R := R') (W := W) (V := V) N (enc []) a AW AV ha (by omega)).seq_norm
          (kv_ex_peek_nil (c := kv_addV) rfl (hfin _ (by simp only [sv_bits] at *; omega)))
        exact (ExecLe.pop_cons (b := true) (s := R') rfl (by rw [kv_u0]; exact h)).cast
          (by simp [kv_go]) (by omega)
    exact (ExecLe.loop_halt (kv_ex_peek hQ hb)).cast rfl (by simp [kv_T]; nlinarith)
  | a :: b :: rows, R, AW, AV, hrows, hN => by
    have ha : sep ∉ a := hrows a (by simp)
    have hb' : sep ∉ b := hrows b (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hN
    obtain ⟨x, Q', hQ⟩ := kv_enc_ne a (b :: rows)
    obtain ⟨x2, Q2, hQ2⟩ := kv_enc_ne b rows
    have hlw := sv_addL_length false AW (sv_bits a)
    have hlv := sv_addL_length false AV (sv_bits b)
    simp only [sv_bits, List.length_map] at hlw hlv
    rcases R with _ | ⟨_ | _, R'⟩
    · have ih := kv_ex_rows N hWV rows [] AW AV hrs (by omega)
      have hs1 := kv_ex_skip (R := []) (W := W) (V := V) (enc (b :: rows)) a AW AV ha
      have hs2 := kv_ex_skip (R := []) (W := W) (V := V) (enc rows) b AW AV hb'
      have hB : ExecLe (.pop 0 kv_SK kv_SK kv_AD) (kv_st [] (enc (a :: b :: rows)) W V AW AV)
          (.norm (kv_st [] (enc rows) W V AW AV)) (30 * N + 50) := by
        rw [enc_cons]
        have h := hs1.seq_norm (kv_ex_peek hQ2 (by rw [← enc_cons] at hs2; exact hs2))
        have h2 := ExecLe.pop_nil (k := 0) (cn := kv_SK) (cf := kv_SK) (ct := kv_AD)
          (σ := kv_st [] (a.flatMap ic ++ false :: false :: enc (b :: rows)) W V AW AV) rfl h
        exact h2.cast rfl (by omega)
      exact (ExecLe.loop_norm (kv_ex_peek hQ hB) ih).cast (by simp [kv_go])
        (by simp [kv_T]; nlinarith)
    · have ih := kv_ex_rows N hWV rows R' AW AV hrs (by omega)
      have hs1 := kv_ex_skip (R := R') (W := W) (V := V) (enc (b :: rows)) a AW AV ha
      have hs2 := kv_ex_skip (R := R') (W := W) (V := V) (enc rows) b AW AV hb'
      have hB : ExecLe (.pop 0 kv_SK kv_SK kv_AD) (kv_st (false :: R') (enc (a :: b :: rows)) W V
          AW AV) (.norm (kv_st R' (enc rows) W V AW AV)) (30 * N + 50) := by
        rw [enc_cons]
        have h := hs1.seq_norm (kv_ex_peek hQ2 (by rw [← enc_cons] at hs2; exact hs2))
        have h2 := ExecLe.pop_cons (k := 0) (cn := kv_SK) (cf := kv_SK) (ct := kv_AD) (b := false)
          (s := R') (σ := kv_st (false :: R') (a.flatMap ic ++ false :: false :: enc (b :: rows)) W V AW AV)
          rfl (by rw [kv_u0]; exact h)
        exact h2.cast rfl (by omega)
      exact (ExecLe.loop_norm (kv_ex_peek hQ hB) ih).cast (by simp [kv_go])
        (by simp [kv_T]; nlinarith)
    · have ih := kv_ex_rows N hWV rows R' (sv_addL false AW (sv_bits a))
        (sv_addL false AV (sv_bits b)) hrs (by simp only [sv_bits]; omega)
      have hs1 := kv_ex_addW (R := R') (W := W) (V := V) N (enc (b :: rows)) a AW AV ha
        (by omega)
      have hs2 := kv_ex_addV (R := R') (W := W) (V := V) N (enc rows) b
        (sv_addL false AW (sv_bits a)) AV hb' (by omega)
      have hB : ExecLe (.pop 0 kv_SK kv_SK kv_AD) (kv_st (true :: R') (enc (a :: b :: rows)) W V
          AW AV) (.norm (kv_st R' (enc rows) W V (sv_addL false AW (sv_bits a))
            (sv_addL false AV (sv_bits b)))) (30 * N + 50) := by
        rw [enc_cons]
        have h := hs1.seq_norm (kv_ex_peek hQ2 (by rw [← enc_cons] at hs2; exact hs2))
        have h2 := ExecLe.pop_cons (k := 0) (cn := kv_SK) (cf := kv_SK) (ct := kv_AD) (b := true)
          (s := R') (σ := kv_st (true :: R') (a.flatMap ic ++ false :: false :: enc (b :: rows)) W V AW AV)
          rfl (by rw [kv_u0]; exact h)
        exact h2.cast rfl (by omega)
      exact (ExecLe.loop_norm (kv_ex_peek hQ hB) ih).cast (by simp [kv_go])
        (by simp [kv_T]; nlinarith)

end Rows

/-! ## The whole verifier -/

theorem kv_av_fr : kv_av (fun j => decide (j = 4)) sv_frLoop = true := by decide

/-- The answer of the verifier on `(w, y)`. -/
def kv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | W :: V :: items => kv_go (sv_bits W) (sv_bits V) items y [] []
  | _ => false

def kv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 3) (.seq sv_frLoop (.seq (move 8 4)
    (.seq sv_frLoop (.seq (move 8 10) kv_mainLoop))))))

/-- Time bound of the verifier. -/
def kv_Tver (n : ℕ) : ℕ := 30 * n + 30 + (n + 1) * (30 * n + 60)

theorem kv_exec_ver (z : Str) :
    ExecLe kv_ver (init [z]).stk (.halt (kv_vres (dec z).1 (dec z).2)) (kv_Tver z.length) := by
  have hl := dec_length z
  set w := (dec z).1
  set y := (dec z).2
  have h0 : (init [z]).stk 0 = z := rfl
  have he : ∀ j, j ≠ 0 → (init [z]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have hA := exec_phaseA z (init [z]).stk h0
  set σ₁ := update (update (init [z]).stk 0 y) 2 ((w.flatMap ic).reverse ++ (init [z]).stk 2)
  have hT := exec_trimC_word 2 w σ₁ (by simp [σ₁, he 2 (by decide)])
  set σ₂ := update σ₁ 2 (((trunc w).flatMap ic).reverse)
  have hM := exec_move (a := 2) (b := 3) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 2 []) 3 ((σ₂ 2).reverse ++ σ₂ 3) = sv_st0 y (enc (clauses w)) [] := by
    funext j
    simp only [σ₂, σ₁, sv_st0, update_apply, enc, trunc]
    split_ifs <;> simp_all
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ), ExecLe c (sv_st0 y (enc (clauses w)) []) r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 3) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  unfold kv_vres kv_ver
  have hsep := sep_not_mem_clauses w
  rcases hcw : clauses w with _ | ⟨t, _ | ⟨v, items⟩⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq sv_frLoop (.seq (move 8 4) (.seq sv_frLoop (.seq (move 8 10)
        kv_mainLoop)))) (sv_st0 y (enc []) []) (.halt false) 2 :=
      ExecLe.seq_halt (ExecLe.loop_halt ((ExecLe.pop_nil rfl (ExecLe.halt false _)).cast rfl
        le_rfl))
    refine (hpre _ _ _ hf).cast rfl ?_
    simp only [htl, kv_Tver]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    have hF := sv_ex_fr y (enc []) t [] (hsep t (by simp))
    rw [List.append_nil] at hF
    have hM2 := sv_ex_move84 y (enc []) (sv_bits t)
    have hf : ExecLe sv_frLoop (sv_st y (enc []) (sv_bits t) [] [] false) (.halt false) 2 :=
      ExecLe.loop_halt ((ExecLe.pop_nil rfl (ExecLe.halt false _)).cast rfl le_rfl)
    refine (hpre _ _ _ (hF.seq_norm (hM2.seq_norm (ExecLe.seq_halt hf)))).cast rfl ?_
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.map_nil, List.sum_nil,
      List.length_nil] at hsum
    simp only [htl, kv_Tver, sv_bits, List.length_map]; nlinarith
  · rw [hcw] at hsum hsep hpre
    rw [enc_cons] at hpre
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum
    have hF := sv_ex_fr y (enc (v :: items)) t [] (hsep t (by simp))
    rw [List.append_nil] at hF
    have hM2 := sv_ex_move84 y (enc (v :: items)) (sv_bits t)
    have hF2 := kv_mix_le (sv_st y (enc (v :: items)) (sv_bits t) [] [] false)
      (sv_ex_fr y (enc items) v [] (hsep v (by simp))) kv_av_fr
    have e1 : ∀ Q, kv_mix (fun j => decide (j = 4)) (sv_st0 y Q [])
        (sv_st y (enc (v :: items)) (sv_bits t) [] [] false) =
        sv_st y Q (sv_bits t) [] [] false := by
      intro Q
      funext j; simp only [kv_mix, sv_st0, sv_st, CookLevin.fl, decide_eq_true_eq]
      split_ifs <;> first | rfl | omega
    simp only [kv_rmap, List.append_nil] at hF2
    rw [e1, ← enc_cons] at hF2
    set σ₃ := kv_mix (fun j => decide (j = 4)) (sv_st0 y (enc items) (sv_bits v).reverse)
        (sv_st y (enc (v :: items)) (sv_bits t) [] [] false)
    have hM3 := exec_move (a := 8) (b := 10) (by decide) _ σ₃ rfl
    have h8 : σ₃ 8 = (sv_bits v).reverse := rfl
    have h10 : σ₃ 10 = [] := rfl
    have e2 : update (update σ₃ 8 []) 10 ((σ₃ 8).reverse ++ σ₃ 10) =
        kv_st y (enc items) (sv_bits t) (sv_bits v) [] [] := by
      rw [h8, h10, List.reverse_reverse, List.append_nil]
      funext j
      by_cases j10 : j = 10
      · subst j10; rfl
      by_cases j8 : j = 8
      · subst j8; rfl
      rw [update_of_ne j10, update_of_ne j8]
      simp only [σ₃, kv_mix, sv_st0, sv_st, kv_st, CookLevin.fl, decide_eq_true_eq]
      split_ifs <;> first | rfl | omega
    rw [e2] at hM3
    have hR := kv_ex_rows (W := sv_bits t) (V := sv_bits v) z.length
      (by simp only [sv_bits, List.length_map]; omega) items y [] []
      (fun r hr => hsep r (by simp [hr])) (by simp; omega)
    refine (hpre _ _ _ (hF.seq_norm (hM2.seq_norm (hF2.seq_norm
      ((ExecLe.of hM3).seq_norm hR))))).cast rfl ?_
    rw [h8]
    simp only [htl, kv_Tver, kv_T, sv_bits, List.length_reverse, List.length_map]
    have h1 : (items.length + 1) * (30 * z.length + 60) ≤ (z.length + 1) * (30 * z.length + 60) :=
      Nat.mul_le_mul_right _ (by omega)
    generalize (items.length + 1) * (30 * z.length + 60) = X at h1 ⊢
    generalize (z.length + 1) * (30 * z.length + 60) = Y at h1 ⊢
    omega

theorem kv_Tver_le (n : ℕ) : kv_Tver n ≤ tb 8 n := by
  unfold kv_Tver tb
  have hm : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm2 : 2 ^ 4 ≤ (n + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have e : (n + 2) ^ 8 = (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 4 := by ring
  have : 16 * (n + 2) ^ 2 * (n + 2) ^ 2 ≤ (n + 2) ^ 2 * (n + 2) ^ 2 * (n + 2) ^ 4 := by
    have := Nat.mul_le_mul_left ((n + 2) ^ 2 * (n + 2) ^ 2) hm2
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num] at this; linarith
  nlinarith

end Pnp.Karp.Knapsack
