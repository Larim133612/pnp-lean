import Pnp.Oracle.Machine

/-!
# `P O ⊆ NP O`

A decider is turned into a verifier ignoring its certificate: stacks are renamed by
`k ↦ if k = 0 then 0 else k + 1`, so that the certificate on stack `1` is never touched,
and the renamed program simulates the original one step by step.
-/

namespace Pnp.Relativize

namespace PSubsetNP

/-- Stack renaming that skips stack `1`. -/
def ren (k : ℕ) : ℕ := if k = 0 then 0 else k + 1

theorem ren_injective : Function.Injective ren := by
  intro a b h
  unfold ren at h
  split_ifs at h <;> omega

theorem ren_ne_one (k : ℕ) : ren k ≠ 1 := by
  unfold ren; split_ifs <;> omega

/-- Rename the stacks of an instruction. -/
def renInstr : Instr → Instr
  | .push k b n => .push (ren k) b n
  | .pop k z f t => .pop (ren k) z f t
  | .query k y n => .query (ren k) y n
  | .halt b => .halt b

/-- Rename the stacks of a program. -/
def renProg (p : Prog) : Prog := p.map renInstr

/-- Simulation relation between configurations of `p` and of `renProg p`. -/
def CfgRel (c c' : Cfg) : Prop := c'.pc = c.pc ∧ ∀ k, c'.stk (ren k) = c.stk k

/-- Simulation relation between states. -/
def Rel : State → State → Prop
  | .run c, .run c' => CfgRel c c'
  | .done b, .done b' => b = b'
  | _, _ => False

theorem update_ren (s : ℕ → Str) (k j : ℕ) (v : Str) :
    Function.update s (ren k) v (ren j) = Function.update (fun i => s (ren i)) k v j := by
  by_cases h : j = k
  · subst h; simp
  · rw [Function.update_of_ne (fun e => h (ren_injective e)), Function.update_of_ne h]

theorem step_rel (O : Oracle) (p : Prog) {c c' : Cfg} (h : CfgRel c c') :
    Rel (step O p c) (step O (renProg p) c') := by
  obtain ⟨hpc, hstk⟩ := h
  have hfun : (fun i => c'.stk (ren i)) = c.stk := funext hstk
  unfold step
  rw [renProg, List.getElem?_map, hpc]
  rcases hp : p[c.pc]? with _ | ⟨i⟩
  · rfl
  · cases i with
    | halt b => rfl
    | push k b n =>
      refine ⟨rfl, fun j => ?_⟩
      dsimp only [Option.map, renInstr]
      rw [update_ren, hfun, hstk]
    | pop k z f t =>
      dsimp only [Option.map, renInstr]
      rw [hstk k]
      cases c.stk k with
      | nil => exact ⟨rfl, hstk⟩
      | cons b s =>
        refine ⟨rfl, fun j => ?_⟩
        dsimp only
        rw [update_ren, hfun]
    | query k y n =>
      dsimp only [Option.map, renInstr]
      rw [hstk k]
      exact ⟨rfl, hstk⟩

theorem runFor_rel (O : Oracle) (p : Prog) (t : ℕ) {s s' : State} (h : Rel s s') :
    Rel (runFor O p t s) (runFor O (renProg p) t s') := by
  induction t generalizing s s' with
  | zero => exact h
  | succ t ih =>
    cases s with
    | done b =>
      cases s' with
      | done b' => simpa using h
      | run c' => exact h.elim
    | run c =>
      cases s' with
      | done b' => exact h.elim
      | run c' =>
        rw [runFor_succ_run, runFor_succ_run]
        exact ih (step_rel O p h)

theorem init_rel (x w : Str) : Rel (.run (init [x])) (.run (init [x, w])) := by
  refine ⟨rfl, fun k => ?_⟩
  simp only [init]
  rcases k with _ | k
  · rfl
  · have h1 : ren (k + 1) = k + 2 := by simp [ren]
    rw [h1]
    simp

end PSubsetNP

open PSubsetNP in
theorem P_subset_NP (O : Oracle) : P O ⊆ NP O := by
  rintro L ⟨p, k, hp⟩
  refine ⟨renProg p, k, fun x => ?_⟩
  obtain ⟨b, hrun, hb⟩ := hp x
  have hsim : ∀ w : Str,
      runFor O (renProg p) (tb k x.length) (.run (init [x, w])) = .done b := by
    intro w
    have := runFor_rel O p (tb k x.length) (init_rel x w)
    rw [hrun] at this
    revert this
    cases runFor O (renProg p) (tb k x.length) (.run (init [x, w])) with
    | done b' => intro h; exact congrArg State.done h.symm
    | run c => intro h; exact h.elim
  constructor
  · intro hx
    refine ⟨[], by simp, ?_⟩
    rw [hsim, hb.2 hx]
  · rintro ⟨w, -, hw⟩
    rw [hsim] at hw
    exact hb.1 (State.done.inj hw)

end Pnp.Relativize
