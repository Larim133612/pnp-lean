import Pnp.Oracle.Combinators

/-!
# Relocating programs

`reloc b i` adds `b` to all jump targets of an instruction.  If a relocated copy of a
program `B` sits at address `b` of a program `p` (`CodeAt p b (B.map (reloc b))`), every run of
`B` that does not halt is also a run of `p`, shifted by `b` (`Reach.embed`).  This lets us
compose independently built programs.
-/

namespace Pnp.Relativize

open Function Comb

/-- Add `b` to all jump targets. -/
def reloc (b : ℕ) : Instr → Instr
  | .push k x n => .push k x (b + n)
  | .pop k z f t => .pop k (b + z) (b + f) (b + t)
  | .query k y n => .query k (b + y) (b + n)
  | .halt x => .halt x

/-- Shift the program counter of a state. -/
def State.shift (b : ℕ) : State → State
  | .run c => .run ⟨b + c.pc, c.stk⟩
  | .done x => .done x

theorem step_reloc {O : Oracle} {B p : Prog} {b pc : ℕ} {i : Instr} (σ : ℕ → Str)
    (hB : B[pc]? = some i) (hp : p[b + pc]? = some (reloc b i)) :
    step O p ⟨b + pc, σ⟩ = (step O B ⟨pc, σ⟩).shift b := by
  cases i with
  | push k x n => simp [step, hB, hp, reloc, State.shift]
  | pop k z f t =>
    simp only [step, hB, hp, reloc]
    cases σ k with
    | nil => simp [State.shift]
    | cons x s => cases x <;> simp [State.shift]
  | query k y n => simp only [step, hB, hp, reloc]; split_ifs <;> simp [State.shift]
  | halt x => simp [step, hB, hp, reloc, State.shift]

theorem runFor_done_ne_run {O : Oracle} {p : Prog} {t : ℕ} {x : Bool} {c : Cfg} :
    runFor O p t (.done x) ≠ .run c := by simp

/-- A non-halting run of `B` is a run of `p` at offset `b`. -/
theorem Reach.embed {O : Oracle} {B p : Prog} {b : ℕ}
    (hB : CodeAt p b (B.map (reloc b))) :
    ∀ {t pc pc' : ℕ} {σ σ' : ℕ → Str}, Reach O B pc σ pc' σ' t →
      Reach O p (b + pc) σ (b + pc') σ' t
  | 0, pc, pc', σ, σ', h => by
    unfold Reach at h ⊢
    simp only [runFor_zero, State.run.injEq, Cfg.mk.injEq] at h ⊢
    exact ⟨by rw [h.1], h.2⟩
  | t + 1, pc, pc', σ, σ', h => by
    unfold Reach at h
    rw [runFor_succ_run] at h
    cases hi : B[pc]? with
    | none =>
      simp [step, hi] at h
    | some i =>
      have hlt : pc < B.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; exact absurd hi (by simp)
      have hp : p[b + pc]? = some (reloc b i) := by
        rw [hB pc (by simpa using hlt)]; simp [hi]
      have hs := step_reloc (O := O) σ hi hp
      cases hst : step O B ⟨pc, σ⟩ with
      | done x => rw [hst] at h; exact absurd h runFor_done_ne_run
      | run c =>
        rw [hst] at h hs
        have ih := Reach.embed hB (t := t) (pc := c.pc) (σ := c.stk) h
        unfold Reach at ih ⊢
        rw [runFor_succ_run, hs]
        exact ih

/-- The relocated tail of a concatenation. -/
theorem codeAt_append_reloc (A B : Prog) :
    CodeAt (A ++ B.map (reloc A.length)) A.length (B.map (reloc A.length)) := by
  intro j hj
  rw [List.getElem?_append_right (by omega)]
  simp

theorem codeAt_append_left (A C : Prog) : CodeAt (A ++ C) 0 A := by
  intro j hj
  rw [Nat.zero_add, List.getElem?_append_left hj]

/-- A non-halting run of `A` (possibly ending just past `A`) is a run of `A ++ C`. -/
theorem Reach.prefix {O : Oracle} {A C : Prog} {t pc pc' : ℕ} {σ σ' : ℕ → Str}
    (h : Reach O A pc σ pc' σ' t) : Reach O (A ++ C) pc σ pc' σ' t := by
  have := Reach.embed (b := 0) (B := A) (p := A ++ C) (by
    intro j hj
    rw [Nat.zero_add, List.getElem?_append_left (by simpa using hj)]
    simp only [List.getElem?_map]
    cases A[j]? with
    | none => rfl
    | some i => cases i <;> simp [reloc]) h
  simpa using this

end Pnp.Relativize
