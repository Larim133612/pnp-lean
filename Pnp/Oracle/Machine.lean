import Mathlib

/-!
# Oracle stack machines

A small, concrete model of deterministic oracle machines, used to state and prove
the Baker–Gill–Solovay theorem (relativization barrier).

* Strings are `List Bool`; an oracle is any set of strings.
* A machine (`Prog`) is a finite list of instructions acting on unboundedly many
  stacks of bits (`stk : ℕ → Str`); two stacks already simulate a Turing tape.
* `query k yes no` asks whether the current content of stack `k` (top first) lies in
  the oracle and jumps accordingly; as usual a query costs one step, but writing the
  query string costs one step per bit.
* The input `x` is placed on stack `0` (a certificate `w`, for verifiers, on stack `1`);
  all other stacks start empty; execution starts at instruction `0`.  Jumping outside
  the program rejects.

`P O` and `NP O` are the relativized classes for oracle `O`, with running time
`(|x|+2)^k` (every polynomial is eventually bounded by such a bound).  This is our
own model: it is not (yet) proved equivalent to the unrelativized upstream classes.
-/

namespace Pnp.Relativize

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle: a set of binary strings. -/
abbrev Oracle := Set Str

/-- Instructions of an oracle stack machine. Jump targets are instruction indices. -/
inductive Instr
  | /-- push bit `b` on stack `k`, go to `next` -/
    push (k : ℕ) (b : Bool) (next : ℕ)
  | /-- pop stack `k`; go to `onNil` if empty, else to `onFalse`/`onTrue` by the bit -/
    pop (k : ℕ) (onNil onFalse onTrue : ℕ)
  | /-- oracle query on the content of stack `k` -/
    query (k : ℕ) (yes no : ℕ)
  | /-- halt with answer `b` -/
    halt (b : Bool)
  deriving DecidableEq, Countable

/-- A machine is a finite list of instructions. -/
abbrev Prog := List Instr

/-- A running configuration: program counter and stacks. -/
structure Cfg where
  pc : ℕ
  stk : ℕ → Str

/-- A machine state: running, or halted with an answer. -/
inductive State
  | run (c : Cfg)
  | done (b : Bool)

open Classical in
/-- One step of program `p` with oracle `O`. -/
noncomputable def step (O : Oracle) (p : Prog) (c : Cfg) : State :=
  match p[c.pc]? with
  | none => .done false
  | some (.halt b) => .done b
  | some (.push k b n) => .run ⟨n, Function.update c.stk k (b :: c.stk k)⟩
  | some (.pop k z f t) =>
      match c.stk k with
      | [] => .run ⟨z, c.stk⟩
      | b :: s => .run ⟨if b then t else f, Function.update c.stk k s⟩
  | some (.query k y n) => .run ⟨if c.stk k ∈ O then y else n, c.stk⟩

/-- Run for (at most) `t` steps. -/
noncomputable def runFor (O : Oracle) (p : Prog) : ℕ → State → State
  | 0, s => s
  | _ + 1, .done b => .done b
  | t + 1, .run c => runFor O p t (step O p c)

/-- Initial configuration with inputs `xs` on stacks `0, 1, …`. -/
def init (xs : List Str) : Cfg := ⟨0, fun k => xs.getD k []⟩

/-- Polynomial time bound used throughout. -/
def tb (k n : ℕ) : ℕ := (n + 2) ^ k

/-- `p` decides `L` with oracle `O` in time `(|x|+2)^k`. -/
def DecidesIn (O : Oracle) (p : Prog) (k : ℕ) (L : Set Str) : Prop :=
  ∀ x : Str, ∃ b : Bool,
    runFor O p (tb k x.length) (.run (init [x])) = .done b ∧ (b = true ↔ x ∈ L)

/-- Relativized `P`: languages decided in polynomial time with oracle `O`. -/
def P (O : Oracle) : Set (Set Str) := {L | ∃ p k, DecidesIn O p k L}

/-- `p` verifies `L` with oracle `O`: `x ∈ L` iff some certificate `w` of length
`≤ (|x|+2)^k` makes `p` accept `(x, w)` within `(|x|+2)^k` steps. -/
def VerifiesIn (O : Oracle) (p : Prog) (k : ℕ) (L : Set Str) : Prop :=
  ∀ x : Str, x ∈ L ↔ ∃ w : Str, w.length ≤ tb k x.length ∧
    runFor O p (tb k x.length) (.run (init [x, w])) = .done true

/-- Relativized `NP`. -/
def NP (O : Oracle) : Set (Set Str) := {L | ∃ p k, VerifiesIn O p k L}

@[simp] theorem runFor_zero (O : Oracle) (p : Prog) (s : State) : runFor O p 0 s = s := rfl

@[simp] theorem runFor_done (O : Oracle) (p : Prog) (t : ℕ) (b : Bool) :
    runFor O p t (.done b) = .done b := by
  cases t <;> rfl

theorem runFor_succ_run (O : Oracle) (p : Prog) (t : ℕ) (c : Cfg) :
    runFor O p (t + 1) (.run c) = runFor O p t (step O p c) := rfl

theorem runFor_add (O : Oracle) (p : Prog) (t u : ℕ) (s : State) :
    runFor O p (t + u) s = runFor O p u (runFor O p t s) := by
  induction t generalizing s with
  | zero => simp
  | succ t ih =>
    cases s with
    | done b => simp
    | run c => rw [Nat.add_right_comm, runFor_succ_run, runFor_succ_run, ih]

/-- Once halted within `t` steps, the answer stays the same for any larger budget. -/
theorem runFor_mono {O : Oracle} {p : Prog} {t t' : ℕ} {s : State} {b : Bool}
    (h : runFor O p t s = .done b) (ht : t ≤ t') : runFor O p t' s = .done b := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [runFor_add, h, runFor_done]

end Pnp.Relativize
