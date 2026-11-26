import Pnp.Oracle.Machine

/-!
# Locality of oracle computations

`queries O p t s` lists the oracle queries made while running `p` for `t` steps from
`s`.  There are at most `t` of them, and the run only depends on the oracle's answers
on these strings.
-/

namespace Pnp.Relativize

/-- The string queried by the next step of `p` from `c`, if that step is a query. -/
def stepQuery (p : Prog) (c : Cfg) : Option Str :=
  match p[c.pc]? with
  | some (.query k _ _) => some (c.stk k)
  | _ => none

/-- The oracle queries made during `runFor O p t s`, in order. -/
noncomputable def queries (O : Oracle) (p : Prog) : ℕ → State → List Str
  | 0, _ => []
  | _ + 1, .done _ => []
  | t + 1, .run c => (stepQuery p c).toList ++ queries O p t (step O p c)

@[simp] theorem queries_zero (O : Oracle) (p : Prog) (s : State) : queries O p 0 s = [] := rfl

@[simp] theorem queries_done (O : Oracle) (p : Prog) (t : ℕ) (b : Bool) :
    queries O p t (.done b) = [] := by
  cases t <;> rfl

theorem queries_succ_run (O : Oracle) (p : Prog) (t : ℕ) (c : Cfg) :
    queries O p (t + 1) (.run c) = (stepQuery p c).toList ++ queries O p t (step O p c) := rfl

/-- At most one query per step. -/
theorem queries_length_le (O : Oracle) (p : Prog) (t : ℕ) (s : State) :
    (queries O p t s).length ≤ t := by
  induction t generalizing s with
  | zero => simp
  | succ t ih =>
    cases s with
    | done b => simp
    | run c =>
      rw [queries_succ_run, List.length_append]
      have h1 : (stepQuery p c).toList.length ≤ 1 := by
        cases stepQuery p c <;> simp
      have h2 := ih (step O p c)
      omega

/-- One step only depends on the oracle's answer to the step's query (if any). -/
theorem step_congr {O O' : Oracle} (p : Prog) (c : Cfg)
    (h : ∀ q ∈ (stepQuery p c).toList, q ∈ O ↔ q ∈ O') : step O p c = step O' p c := by
  unfold step
  unfold stepQuery at h
  rcases hp : p[c.pc]? with _ | ⟨i⟩
  · rfl
  · rw [hp] at h
    cases i with
    | push k b n => rfl
    | pop k z f t => rfl
    | halt b => rfl
    | query k y n =>
      have hk : c.stk k ∈ O ↔ c.stk k ∈ O' := h _ (by simp)
      dsimp only
      by_cases hq : c.stk k ∈ O
      · rw [if_pos hq, if_pos (hk.1 hq)]
      · rw [if_neg hq, if_neg (mt hk.2 hq)]

/-- Locality: oracles agreeing on all queries made give the same run and the same
queries. -/
theorem runFor_congr {O O' : Oracle} (p : Prog) (t : ℕ) (s : State)
    (h : ∀ q ∈ queries O p t s, q ∈ O ↔ q ∈ O') :
    runFor O p t s = runFor O' p t s ∧ queries O p t s = queries O' p t s := by
  induction t generalizing s with
  | zero => simp
  | succ t ih =>
    cases s with
    | done b => simp
    | run c =>
      rw [queries_succ_run] at h
      have hs : step O p c = step O' p c :=
        step_congr p c (fun q hq => h q (List.mem_append_left _ hq))
      have ih' := ih (step O p c) (fun q hq => h q (List.mem_append_right _ hq))
      rw [runFor_succ_run, runFor_succ_run, queries_succ_run, queries_succ_run, ih'.1, ih'.2,
        hs]
      exact ⟨rfl, rfl⟩

theorem runFor_eq_of_agree {O O' : Oracle} (p : Prog) (t : ℕ) (s : State)
    (h : ∀ q ∈ queries O p t s, q ∈ O ↔ q ∈ O') : runFor O p t s = runFor O' p t s :=
  (runFor_congr p t s h).1

end Pnp.Relativize
