import Pnp.Oracle.Shift
import Pnp.Oracle.FromTM2
import Pnp.Oracle.Official

/-!
# A structured language for oracle stack machines

Writing raw instruction lists (`Prog`, see `Pnp/Oracle/Machine.lean`) with explicit address
arithmetic is painful.  This file defines a small structured language `Cmd` (pushes, pops with
three-way branching, sequencing, loops with `brk`, halting, and calls of arbitrary
sub-programs on shifted stacks), a big-step semantics `Exec` with *exact* step costs, and a
compiler `compile` / `toProg` into `Prog`, proved correct for the empty oracle `∅`:

* `compile_sound`: if `compile c base nxt brkT` sits at address `base` of `p` and
  `Exec c σ r t`, then `p` runs `t` steps from `(base, σ)` and reaches `(nxt, σ')` if
  `r = .norm σ'`, `(brkT, σ')` if `r = .brk σ'`, and halts with `b` if `r = .halt b`.
* `runFor_toProg`: a top-level halting execution is a run of `toProg c`.
* `Exec.det`: the semantics is deterministic (result and cost).

The compiled code of `call q o cf ct` is a copy of `q` with stack indices shifted by `o`,
relocated, every `halt b` replaced by a jump to the continuation for `b`, and every jump target
outside `q` (meaning "reject" in `q`) redirected to the `false` continuation (`embI`); running the
copy simulates `q` step by step, leaving stacks `< o` untouched (`reach_embed`).  The caller-side
lemma `Exec.call_of_runFor` only needs a halting run `runFor ∅ q T … = .done b` and also bounds
how `q` can change the stacks (only stacks `< nW q`, total length grows by at most one per
step).

Finally we provide utility commands with exact semantics and costs: `drain`, `move`,
`moveTwo`, `copyVia`, `pushList`, `cmdSeq`, and loop iteration rules.

Costs: `push`, `skip`, `halt`, `brk` cost 1; `pop` costs 1 plus its branch; `seq` and `loop`
add the costs of their parts (no extra jumps); `call` costs the number of steps of `q`
(including the halting step) plus that of the continuation.
-/

namespace Pnp.Relativize.Struct

open Function Pnp.Relativize.Comb

/-- A jump without stack effect (a query to the empty oracle with equal targets). -/
abbrev nop (t : ℕ) : Instr := FromTM2.nop t

/-- Structured commands. -/
inductive Cmd
  | /-- push bit `b` on stack `k` -/
    push (k : ℕ) (b : Bool)
  | /-- pop stack `k`: empty → `cn`, popped `false` → `cf`, popped `true` → `ct` -/
    pop (k : ℕ) (cn cf ct : Cmd)
  | /-- sequencing -/
    seq (c d : Cmd)
  | /-- do nothing (one step) -/
    skip
  | /-- halt with answer `b` -/
    halt (b : Bool)
  | /-- repeat `c` until a `brk` (not inside a nested loop) is executed -/
    loop (c : Cmd)
  | /-- exit the innermost enclosing loop -/
    brk
  | /-- run program `q` on the stacks shifted by `o`; continue with `ct`/`cf` by its answer -/
    call (q : Prog) (o : ℕ) (cf ct : Cmd)

/-- Results of executing a command. -/
inductive Res
  | /-- normal termination -/
    norm (σ : ℕ → Str)
  | /-- a `brk` was executed -/
    brk (σ : ℕ → Str)
  | /-- the machine halted -/
    halt (b : Bool)

/-- The stacks `σ` with stacks `≥ o` replaced by `τ` (shifted by `o`). -/
def lift (σ : ℕ → Str) (o : ℕ) (τ : ℕ → Str) : ℕ → Str :=
  fun j => if j < o then σ j else τ (j - o)

/-- The stacks seen by a call at offset `o`. -/
def view (σ : ℕ → Str) (o : ℕ) : ℕ → Str := fun j => σ (o + j)

/-- Big-step semantics with exact step cost. -/
inductive Exec : Cmd → (ℕ → Str) → Res → ℕ → Prop
  | push (k : ℕ) (b : Bool) (σ : ℕ → Str) :
      Exec (.push k b) σ (.norm (update σ k (b :: σ k))) 1
  | pop_nil {k : ℕ} {cn cf ct : Cmd} {σ : ℕ → Str} {r : Res} {t : ℕ} :
      σ k = [] → Exec cn σ r t → Exec (.pop k cn cf ct) σ r (t + 1)
  | pop_cons {k : ℕ} {cn cf ct : Cmd} {σ : ℕ → Str} {b : Bool} {s : Str} {r : Res} {t : ℕ} :
      σ k = b :: s → Exec (if b then ct else cf) (update σ k s) r t →
      Exec (.pop k cn cf ct) σ r (t + 1)
  | seq_norm {c d : Cmd} {σ σ' : ℕ → Str} {r : Res} {t₁ t₂ : ℕ} :
      Exec c σ (.norm σ') t₁ → Exec d σ' r t₂ → Exec (.seq c d) σ r (t₁ + t₂)
  | seq_brk {c d : Cmd} {σ σ' : ℕ → Str} {t : ℕ} :
      Exec c σ (.brk σ') t → Exec (.seq c d) σ (.brk σ') t
  | seq_halt {c d : Cmd} {σ : ℕ → Str} {b : Bool} {t : ℕ} :
      Exec c σ (.halt b) t → Exec (.seq c d) σ (.halt b) t
  | skip (σ : ℕ → Str) : Exec .skip σ (.norm σ) 1
  | halt (b : Bool) (σ : ℕ → Str) : Exec (.halt b) σ (.halt b) 1
  | brk (σ : ℕ → Str) : Exec .brk σ (.brk σ) 1
  | loop_norm {c : Cmd} {σ σ' : ℕ → Str} {r : Res} {t₁ t₂ : ℕ} :
      Exec c σ (.norm σ') t₁ → Exec (.loop c) σ' r t₂ → Exec (.loop c) σ r (t₁ + t₂)
  | loop_brk {c : Cmd} {σ σ' : ℕ → Str} {t : ℕ} :
      Exec c σ (.brk σ') t → Exec (.loop c) σ (.norm σ') t
  | loop_halt {c : Cmd} {σ : ℕ → Str} {b : Bool} {t : ℕ} :
      Exec c σ (.halt b) t → Exec (.loop c) σ (.halt b) t
  | call {q : Prog} {o : ℕ} {cf ct : Cmd} {σ : ℕ → Str} {t pc : ℕ} {τ : ℕ → Str} {b : Bool}
      {r : Res} {t' : ℕ} :
      runFor ∅ q t (.run ⟨0, view σ o⟩) = .run ⟨pc, τ⟩ → step ∅ q ⟨pc, τ⟩ = .done b →
      Exec (if b then ct else cf) (lift σ o τ) r t' → Exec (.call q o cf ct) σ r (t + 1 + t')

/-! ### Compilation -/

/-- Size of the compiled code. -/
def size : Cmd → ℕ
  | .push _ _ => 1
  | .pop _ cn cf ct => 1 + size cn + size cf + size ct
  | .seq c d => size c + size d
  | .skip => 1
  | .halt _ => 1
  | .loop c => size c
  | .brk => 1
  | .call q _ cf ct => q.length + 1 + size cf + size ct

/-- Jump target `n` of `q` embedded at `base`: out-of-range targets go to `base + |q|`. -/
def tgt (base L n : ℕ) : ℕ := if n < L then base + n else base + L

theorem tgt_zero (base L : ℕ) : tgt base L 0 = base := by
  unfold tgt; split <;> omega

/-- Embedded instruction of a called program (`L = |q|`, `F`/`T` the continuations). -/
def embI (o base L F T : ℕ) : Instr → Instr
  | .push k b n => .push (k + o) b (tgt base L n)
  | .pop k z f t => .pop (k + o) (tgt base L z) (tgt base L f) (tgt base L t)
  | .query k y n => .query (k + o) (tgt base L y) (tgt base L n)
  | .halt b => nop (if b then T else F)

/-- Compile `c` to sit at address `base`; normal end jumps to `nxt`, `brk` to `brkT`. -/
def compile : Cmd → ℕ → ℕ → ℕ → List Instr
  | .push k b, _, n, _ => [.push k b n]
  | .pop k cn cf ct, base, n, br =>
      .pop k (base + 1) (base + 1 + size cn) (base + 1 + size cn + size cf) ::
        (compile cn (base + 1) n br ++ compile cf (base + 1 + size cn) n br ++
          compile ct (base + 1 + size cn + size cf) n br)
  | .seq c d, base, n, br => compile c base (base + size c) br ++ compile d (base + size c) n br
  | .skip, _, n, _ => [nop n]
  | .halt b, _, _, _ => [.halt b]
  | .loop c, base, n, _ => compile c base base n
  | .brk, _, _, br => [nop br]
  | .call q o cf ct, base, n, br =>
      q.map (embI o base q.length (base + q.length + 1) (base + q.length + 1 + size cf)) ++
        (nop (base + q.length + 1) :: (compile cf (base + q.length + 1) n br ++
          compile ct (base + q.length + 1 + size cf) n br))

@[simp] theorem compile_length : ∀ (c : Cmd) (base n br : ℕ),
    (compile c base n br).length = size c
  | .push _ _, _, _, _ => rfl
  | .pop _ cn cf ct, base, n, br => by
    simp only [compile, size, List.length_cons, List.length_append, compile_length]; omega
  | .seq c d, base, n, br => by simp only [compile, size, List.length_append, compile_length]
  | .skip, _, _, _ => rfl
  | .halt _, _, _, _ => rfl
  | .loop c, base, n, br => by simp only [compile, size, compile_length]
  | .brk, _, _, _ => rfl
  | .call q o cf ct, base, n, br => by
    simp only [compile, size, List.length_append, List.length_map, List.length_cons,
      compile_length]; omega

/-- The program of a command, placed at address `0` (normal end rejects). -/
def toProg (c : Cmd) : Prog := compile c 0 (size c) (size c)

/-! ### Simulating an embedded program -/

theorem lift_view (σ : ℕ → Str) (o : ℕ) : lift σ o (view σ o) = σ := by
  funext j; unfold lift view; split
  · rfl
  · congr 1; omega

theorem lift_add (σ : ℕ → Str) (o : ℕ) (τ : ℕ → Str) (k : ℕ) : lift σ o τ (k + o) = τ k := by
  unfold lift; rw [if_neg (by omega)]; congr 1; omega

theorem lift_update (σ : ℕ → Str) (o : ℕ) (τ : ℕ → Str) (k : ℕ) (s : Str) :
    lift σ o (update τ k s) = update (lift σ o τ) (k + o) s := by
  funext j
  unfold lift
  by_cases hj : j < o
  · rw [if_pos hj, update_of_ne (by omega), if_pos hj]
  · rw [if_neg hj]
    by_cases hk : j = k + o
    · subst hk; rw [update_self, show k + o - o = k by omega, update_self]
    · rw [update_of_ne (by omega), update_of_ne hk, if_neg hj]

section Embed

variable {p q : Prog} {o base F T : ℕ}

theorem getElem_embed (hp : CodeAt p base (q.map (embI o base q.length F T))) {pc : ℕ}
    {i : Instr} (hi : q[pc]? = some i) :
    p[tgt base q.length pc]? = some (embI o base q.length F T i) := by
  have hlt : pc < q.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; exact absurd hi (by simp)
  have : tgt base q.length pc = base + pc := by unfold tgt; rw [if_pos hlt]
  rw [this, hp pc (by simpa using hlt)]; simp [hi]

/-- One non-halting step of `q` is one step of the embedded copy. -/
theorem step_embed (hp : CodeAt p base (q.map (embI o base q.length F T))) (σ : ℕ → Str)
    {pc pc' : ℕ} {τ τ' : ℕ → Str} (hs : step ∅ q ⟨pc, τ⟩ = .run ⟨pc', τ'⟩) :
    step ∅ p ⟨tgt base q.length pc, lift σ o τ⟩ =
      .run ⟨tgt base q.length pc', lift σ o τ'⟩ := by
  cases hi : q[pc]? with
  | none => simp [step, hi] at hs
  | some i =>
    have hq := getElem_embed hp hi
    cases i with
    | push k b n =>
      simp only [step, hi, State.run.injEq, Cfg.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [step, hq, embI, lift_update, lift_add]
    | pop k z f t =>
      simp only [step, hi] at hs
      cases hk : τ k with
      | nil =>
        rw [hk] at hs
        simp only [State.run.injEq, Cfg.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp only [step, hq, embI, lift_add, hk]
      | cons x s =>
        rw [hk] at hs
        simp only [State.run.injEq, Cfg.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        simp only [step, hq, embI, lift_add, hk, lift_update]
        cases x <;> rfl
    | query k y n =>
      simp only [step, hi, Set.mem_empty_iff_false, if_false, State.run.injEq,
        Cfg.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [step, hq, embI, Set.mem_empty_iff_false, if_false]
    | halt b => simp [step, hi] at hs

/-- A non-halting run of `q` is a run of the embedded copy. -/
theorem reach_embed (hp : CodeAt p base (q.map (embI o base q.length F T))) (σ : ℕ → Str) :
    ∀ {t pc pc' : ℕ} {τ τ' : ℕ → Str}, Reach ∅ q pc τ pc' τ' t →
      Reach ∅ p (tgt base q.length pc) (lift σ o τ) (tgt base q.length pc') (lift σ o τ') t
  | 0, pc, pc', τ, τ', h => by
    unfold Reach at h
    simp only [runFor_zero, State.run.injEq, Cfg.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Reach.refl
  | t + 1, pc, pc', τ, τ', h => by
    unfold Reach at h
    rw [runFor_succ_run] at h
    cases hst : step ∅ q ⟨pc, τ⟩ with
    | done x => rw [hst] at h; simp at h
    | run c =>
      rw [hst] at h
      have h1 := Reach.of_step (step_embed hp σ (o := o) (show step ∅ q ⟨pc, τ⟩ =
        .run ⟨c.pc, c.stk⟩ from hst))
      exact (h1.trans (reach_embed hp σ (t := t) h)).cast rfl rfl (by omega)

/-- The halting step of `q` becomes a jump to the continuation. -/
theorem reach_embed_halt (hp : CodeAt p base (q.map (embI o base q.length F T)))
    (hF : p[base + q.length]? = some (nop F)) (σ : ℕ → Str) {pc : ℕ} {τ : ℕ → Str} {b : Bool}
    (hs : step ∅ q ⟨pc, τ⟩ = .done b) :
    Reach ∅ p (tgt base q.length pc) (lift σ o τ) (if b then T else F) (lift σ o τ) 1 := by
  cases hi : q[pc]? with
  | none =>
    simp only [step, hi, State.done.injEq] at hs
    subst hs
    have hlt : ¬ pc < q.length := by
      intro hc; rw [List.getElem?_eq_getElem hc] at hi; exact absurd hi (by simp)
    have : tgt base q.length pc = base + q.length := by unfold tgt; rw [if_neg hlt]
    rw [this]
    exact FromTM2.reach_nop hF
  | some i =>
    have hq := getElem_embed hp hi
    cases i with
    | halt b' =>
      simp only [step, hi, State.done.injEq] at hs
      subst hs
      exact FromTM2.reach_nop hq
    | push k x n => simp [step, hi] at hs
    | pop k z f t =>
      simp only [step, hi] at hs
      split at hs <;> simp at hs
    | query k y n => simp [step, hi] at hs

end Embed

/-! ### Correctness of the compiler -/

/-- What a result means for a run of the compiled code at `base`. -/
def Sound (p : Prog) (base nxt brkT : ℕ) (σ : ℕ → Str) : Res → ℕ → Prop
  | .norm σ', t => Reach ∅ p base σ nxt σ' t
  | .brk σ', t => Reach ∅ p base σ brkT σ' t
  | .halt b, t => runFor ∅ p t (.run ⟨base, σ⟩) = .done b

theorem Sound.pre {p : Prog} {a b nxt brkT t u : ℕ} {σ σ' : ℕ → Str} {r : Res}
    (h1 : Reach ∅ p a σ b σ' t) (h2 : Sound p b nxt brkT σ' r u) :
    Sound p a nxt brkT σ r (t + u) := by
  cases r with
  | norm τ => exact h1.trans h2
  | brk τ => exact h1.trans h2
  | halt x =>
    show runFor ∅ p (t + u) _ = _
    rw [runFor_add]; unfold Reach at h1; rw [h1]; exact h2

theorem codeAt_pop_branch {p : Prog} {base n br k : ℕ} {cn cf ct : Cmd} (b : Bool)
    (h : CodeAt p base (compile (.pop k cn cf ct) base n br)) :
    CodeAt p (if b then base + 1 + size cn + size cf else base + 1 + size cn)
      (compile (if b then ct else cf)
        (if b then base + 1 + size cn + size cf else base + 1 + size cn) n br) := by
  have ht := h.tail
  cases b
  · simp only [Bool.false_eq_true, if_false]
    exact ht.left.right.rebase (by simp)
  · simp only [if_true]
    exact ht.right.rebase (by simp; omega)

theorem codeAt_call_branch {p : Prog} {base n br o : ℕ} {q : Prog} {cf ct : Cmd} (b : Bool)
    (h : CodeAt p base (compile (.call q o cf ct) base n br)) :
    CodeAt p (if b then base + q.length + 1 + size cf else base + q.length + 1)
      (compile (if b then ct else cf)
        (if b then base + q.length + 1 + size cf else base + q.length + 1) n br) := by
  have ht := h.right.tail
  cases b
  · simp only [Bool.false_eq_true, if_false]
    exact ht.left.rebase (by simp)
  · simp only [if_true]
    exact ht.right.rebase (by simp)

/-- **Compiler correctness.** -/
theorem compile_sound {p : Prog} {c : Cmd} {σ : ℕ → Str} {r : Res} {t : ℕ}
    (h : Exec c σ r t) : ∀ base nxt brkT, CodeAt p base (compile c base nxt brkT) →
      Sound p base nxt brkT σ r t := by
  induction h with
  | push k b σ =>
    intro base nxt brkT hc
    exact reach_push hc.head
  | @pop_nil k cn cf ct σ r t hk _ ih =>
    intro base nxt brkT hc
    rw [Nat.add_comm]
    exact Sound.pre (reach_pop_nil hc.head hk) (ih _ _ _ hc.tail.left.left)
  | @pop_cons k cn cf ct σ b s r t hk _ ih =>
    intro base nxt brkT hc
    rw [Nat.add_comm]
    exact Sound.pre (reach_pop_cons hc.head hk) (ih _ _ _ (codeAt_pop_branch b hc))
  | seq_norm _ _ ih1 ih2 =>
    intro base nxt brkT hc
    exact Sound.pre (ih1 _ _ _ hc.left) (ih2 _ _ _ (hc.right.rebase (by simp)))
  | @seq_brk c _ _ _ _ _ ih => intro base nxt brkT hc; exact ih base (base + size c) brkT hc.left
  | @seq_halt c _ _ _ _ _ ih => intro base nxt brkT hc; exact ih base (base + size c) brkT hc.left
  | skip σ => intro base nxt brkT hc; exact FromTM2.reach_nop hc.head
  | halt b σ =>
    intro base nxt brkT hc
    show runFor ∅ p 1 _ = _
    rw [runFor_succ_run]; simp [step, hc.head]
  | brk σ => intro base nxt brkT hc; exact FromTM2.reach_nop hc.head
  | loop_norm _ _ ih1 ih2 =>
    intro base nxt brkT hc
    exact Sound.pre (ih1 base base nxt hc) (ih2 base nxt brkT hc)
  | loop_brk _ ih => intro base nxt brkT hc; exact ih base base nxt hc
  | loop_halt _ ih => intro base nxt brkT hc; exact ih base base nxt hc
  | @call q o cf ct σ t pc τ b r t' hr hs _ ih =>
    intro base nxt brkT hc
    have hq := hc.left
    have hF : p[base + q.length]? = some (nop (base + q.length + 1)) :=
      (hc.right.rebase (by simp)).head
    have h1 := reach_embed hq σ (o := o) hr
    rw [tgt_zero, lift_view] at h1
    have h2 := reach_embed_halt hq hF σ hs
    exact Sound.pre (h1.trans h2) (ih _ _ _ (codeAt_call_branch b hc))

/-- **Top level**: a halting execution is a run of `toProg c`. -/
theorem runFor_toProg {c : Cmd} {σ : ℕ → Str} {b : Bool} {t : ℕ}
    (h : Exec c σ (.halt b) t) : runFor ∅ (toProg c) t (.run ⟨0, σ⟩) = .done b :=
  compile_sound h 0 (size c) (size c) (codeAt_self _)

/-- Any larger budget works as well. -/
theorem runFor_toProg_le {c : Cmd} {σ : ℕ → Str} {b : Bool} {t T : ℕ}
    (h : Exec c σ (.halt b) t) (hT : t ≤ T) :
    runFor ∅ (toProg c) T (.run ⟨0, σ⟩) = .done b :=
  runFor_mono (runFor_toProg h) hT

/-- A normally terminating top-level execution rejects one step later. -/
theorem runFor_toProg_norm {c : Cmd} {σ σ' : ℕ → Str} {t : ℕ}
    (h : Exec c σ (.norm σ') t) : runFor ∅ (toProg c) (t + 1) (.run ⟨0, σ⟩) = .done false := by
  have h1 : Reach ∅ (toProg c) 0 σ (size c) σ' t := compile_sound h 0 (size c) (size c)
    (codeAt_self _)
  rw [runFor_add]; unfold Reach at h1; rw [h1, runFor_succ_run]
  have : (toProg c)[size c]? = none := List.getElem?_eq_none (by simp [toProg])
  simp [step, this]

/-! ### Determinism -/

theorem runFor_done_of_halt_lt {O : Oracle} {q : Prog} {s : State} {t t' : ℕ} {c : Cfg}
    {b : Bool} (h : runFor O q t s = .run c) (hs : step O q c = .done b) (ht : t < t') :
    runFor O q t' s = .done b := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_lt ht
  rw [show t + u + 1 = t + (1 + u) by omega, runFor_add, h, runFor_add, runFor_succ_run,
    runFor_zero, hs, runFor_done]

/-- The halting time and configuration of a run are unique. -/
theorem halt_unique {O : Oracle} {q : Prog} {s : State} {t t' : ℕ} {c c' : Cfg} {b b' : Bool}
    (h : runFor O q t s = .run c) (hs : step O q c = .done b)
    (h' : runFor O q t' s = .run c') (hs' : step O q c' = .done b') :
    t = t' ∧ c = c' ∧ b = b' := by
  rcases lt_trichotomy t t' with hl | rfl | hl
  · rw [runFor_done_of_halt_lt h hs hl] at h'; simp at h'
  · rw [h] at h'; cases h'; rw [hs] at hs'; cases hs'; exact ⟨rfl, rfl, rfl⟩
  · rw [runFor_done_of_halt_lt h' hs' hl] at h; simp at h

/-- The semantics is deterministic, including the cost. -/
theorem Exec.det {c : Cmd} {σ : ℕ → Str} {r : Res} {t : ℕ} (h : Exec c σ r t) :
    ∀ {r' t'}, Exec c σ r' t' → r = r' ∧ t = t' := by
  induction h with
  | push => intro r' t' h'; cases h'; exact ⟨rfl, rfl⟩
  | pop_nil hk _ ih =>
    intro r' t' h'
    cases h' with
    | pop_nil _ h2 => obtain ⟨rfl, rfl⟩ := ih h2; exact ⟨rfl, rfl⟩
    | pop_cons hk' _ => rw [hk] at hk'; cases hk'
  | pop_cons hk _ ih =>
    intro r' t' h'
    cases h' with
    | pop_nil hk' _ => rw [hk] at hk'; cases hk'
    | pop_cons hk' h2 =>
      rw [hk] at hk'; cases hk'
      obtain ⟨rfl, rfl⟩ := ih h2; exact ⟨rfl, rfl⟩
  | seq_norm _ _ ih1 ih2 =>
    intro r' t' h'
    cases h' with
    | seq_norm h1 h2 =>
      obtain ⟨e, rfl⟩ := ih1 h1; cases e
      obtain ⟨rfl, rfl⟩ := ih2 h2; exact ⟨rfl, rfl⟩
    | seq_brk h1 => obtain ⟨e, _⟩ := ih1 h1; cases e
    | seq_halt h1 => obtain ⟨e, _⟩ := ih1 h1; cases e
  | seq_brk _ ih =>
    intro r' t' h'
    cases h' with
    | seq_norm h1 _ => obtain ⟨e, _⟩ := ih h1; cases e
    | seq_brk h1 => obtain ⟨e, rfl⟩ := ih h1; cases e; exact ⟨rfl, rfl⟩
    | seq_halt h1 => obtain ⟨e, _⟩ := ih h1; cases e
  | seq_halt _ ih =>
    intro r' t' h'
    cases h' with
    | seq_norm h1 _ => obtain ⟨e, _⟩ := ih h1; cases e
    | seq_brk h1 => obtain ⟨e, _⟩ := ih h1; cases e
    | seq_halt h1 => obtain ⟨e, rfl⟩ := ih h1; cases e; exact ⟨rfl, rfl⟩
  | skip => intro r' t' h'; cases h'; exact ⟨rfl, rfl⟩
  | halt => intro r' t' h'; cases h'; exact ⟨rfl, rfl⟩
  | brk => intro r' t' h'; cases h'; exact ⟨rfl, rfl⟩
  | loop_norm _ _ ih1 ih2 =>
    intro r' t' h'
    cases h' with
    | loop_norm h1 h2 =>
      obtain ⟨e, rfl⟩ := ih1 h1; cases e
      obtain ⟨rfl, rfl⟩ := ih2 h2; exact ⟨rfl, rfl⟩
    | loop_brk h1 => obtain ⟨e, _⟩ := ih1 h1; cases e
    | loop_halt h1 => obtain ⟨e, _⟩ := ih1 h1; cases e
  | loop_brk _ ih =>
    intro r' t' h'
    cases h' with
    | loop_norm h1 _ => obtain ⟨e, _⟩ := ih h1; cases e
    | loop_brk h1 => obtain ⟨e, rfl⟩ := ih h1; cases e; exact ⟨rfl, rfl⟩
    | loop_halt h1 => obtain ⟨e, _⟩ := ih h1; cases e
  | loop_halt _ ih =>
    intro r' t' h'
    cases h' with
    | loop_norm h1 _ => obtain ⟨e, _⟩ := ih h1; cases e
    | loop_brk h1 => obtain ⟨e, _⟩ := ih h1; cases e
    | loop_halt h1 => obtain ⟨e, rfl⟩ := ih h1; cases e; exact ⟨rfl, rfl⟩
  | call hr hs _ ih =>
    intro r' t' h'
    cases h' with
    | call hr' hs' h2 =>
      obtain ⟨rfl, e, rfl⟩ := halt_unique hr hs hr' hs'
      cases e
      obtain ⟨rfl, rfl⟩ := ih h2; exact ⟨rfl, rfl⟩

/-! ### Calls: the caller-side lemma -/

@[simp] theorem view_apply (σ : ℕ → Str) (o j : ℕ) : view σ o j = σ (o + j) := rfl

theorem lift_apply (σ : ℕ → Str) (o : ℕ) (τ : ℕ → Str) (j : ℕ) :
    lift σ o τ j = if j < o then σ j else τ (j - o) := rfl

/-- A halting run has a last non-halting configuration. -/
theorem exists_last_of_runFor {O : Oracle} {q : Prog} {b : Bool} :
    ∀ {T : ℕ} {c : Cfg}, runFor O q T (.run c) = .done b →
      ∃ t c', t < T ∧ runFor O q t (.run c) = .run c' ∧ step O q c' = .done b
  | 0, c, h => by simp at h
  | T + 1, c, h => by
    rw [runFor_succ_run] at h
    cases hs : step O q c with
    | done x =>
      rw [hs, runFor_done] at h
      exact ⟨0, c, by omega, rfl, h ▸ hs⟩
    | run c'' =>
      rw [hs] at h
      obtain ⟨t, c', ht, h1, h2⟩ := exists_last_of_runFor h
      exact ⟨t + 1, c', by omega, by rw [runFor_succ_run, hs]; exact h1, h2⟩

theorem sum_update_le (v : ℕ → Str) (k : ℕ) (s : Str) (hs : s.length ≤ (v k).length + 1)
    (N : ℕ) : ∑ j ∈ Finset.range N, (update v k s j).length ≤
      ∑ j ∈ Finset.range N, (v j).length + 1 := by
  calc ∑ j ∈ Finset.range N, (update v k s j).length
      ≤ ∑ j ∈ Finset.range N, ((v j).length + if k = j then 1 else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j = k
        · subst hj; simp only [update_self, if_true]; exact hs
        · rw [update_of_ne hj, if_neg (Ne.symm hj)]; omega
    _ = ∑ j ∈ Finset.range N, (v j).length + if k ∈ Finset.range N then 1 else 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    _ ≤ ∑ j ∈ Finset.range N, (v j).length + 1 := by split <;> omega

/-- One step of `q` only touches stacks `< nW q` and grows the total length by at most 1. -/
theorem step_inv {q : Prog} {pc pc' : ℕ} {v v' : ℕ → Str}
    (h : step ∅ q ⟨pc, v⟩ = .run ⟨pc', v'⟩) :
    (∀ j, Official.nW q ≤ j → v' j = v j) ∧
      ∀ N, ∑ j ∈ Finset.range N, (v' j).length ≤ ∑ j ∈ Finset.range N, (v j).length + 1 := by
  cases hi : q[pc]? with
  | none => simp [step, hi] at h
  | some i =>
    have hk := Official.stkIdx_lt q (List.mem_of_getElem? hi)
    cases i with
    | push k b n =>
      simp only [step, hi, State.run.injEq, Cfg.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [Official.stkIdx] at hk
      exact ⟨fun j hj => update_of_ne (by omega) _ _,
        sum_update_le v k _ (by simp)⟩
    | pop k z f t =>
      simp only [step, hi] at h
      simp only [Official.stkIdx] at hk
      cases hv : v k with
      | nil =>
        rw [hv] at h
        simp only [State.run.injEq, Cfg.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨fun _ _ => rfl, fun N => by omega⟩
      | cons x s =>
        rw [hv] at h
        simp only [State.run.injEq, Cfg.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨fun j hj => update_of_ne (by omega) _ _,
          sum_update_le v k _ (by simp [hv]; omega)⟩
    | query k y n =>
      simp only [step, hi, State.run.injEq, Cfg.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨fun _ _ => rfl, fun N => by omega⟩
    | halt b => simp [step, hi] at h

/-- Invariants of non-halting runs of `q`. -/
theorem reach_inv {q : Prog} : ∀ {t pc pc' : ℕ} {v v' : ℕ → Str},
    Reach ∅ q pc v pc' v' t →
    (∀ j, Official.nW q ≤ j → v' j = v j) ∧
      ∀ N, ∑ j ∈ Finset.range N, (v' j).length ≤ ∑ j ∈ Finset.range N, (v j).length + t
  | 0, pc, pc', v, v', h => by
    unfold Reach at h
    simp only [runFor_zero, State.run.injEq, Cfg.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨fun _ _ => rfl, fun N => by omega⟩
  | t + 1, pc, pc', v, v', h => by
    unfold Reach at h
    rw [runFor_succ_run] at h
    cases hst : step ∅ q ⟨pc, v⟩ with
    | done x => rw [hst] at h; simp at h
    | run c =>
      rw [hst] at h
      obtain ⟨a1, b1⟩ := step_inv (show step ∅ q ⟨pc, v⟩ = .run ⟨c.pc, c.stk⟩ from hst)
      obtain ⟨a2, b2⟩ := reach_inv (t := t) h
      exact ⟨fun j hj => (a2 j hj).trans (a1 j hj),
        fun N => (b2 N).trans (by have := b1 N; omega)⟩

/-- **Calls, caller side.**  If `q` halts with answer `b` within `T` steps on the shifted
stacks, the call takes `t + 1 ≤ T` steps (plus the continuation) and continues from
`lift σ o τ`, where `τ` agrees with the input view above `nW q` and has total length growing
by at most `t`. -/
theorem Exec.call_of_runFor {q : Prog} {o : ℕ} {cf ct : Cmd} {σ : ℕ → Str} {b : Bool} {T : ℕ}
    (h : runFor ∅ q T (.run ⟨0, view σ o⟩) = .done b) :
    ∃ t τ, t < T ∧ (∀ j, Official.nW q ≤ j → τ j = σ (o + j)) ∧
      (∀ N, ∑ j ∈ Finset.range N, (τ j).length ≤
        ∑ j ∈ Finset.range N, (σ (o + j)).length + t) ∧
      ∀ {r : Res} {t' : ℕ}, Exec (if b then ct else cf) (lift σ o τ) r t' →
        Exec (.call q o cf ct) σ r (t + 1 + t') := by
  obtain ⟨t, ⟨pc, τ⟩, ht, h1, h2⟩ := exists_last_of_runFor h
  obtain ⟨i1, i2⟩ := reach_inv (show Reach ∅ q 0 (view σ o) pc τ t from h1)
  exact ⟨t, τ, ht, i1, i2, fun h3 => Exec.call h1 h2 h3⟩

/-! ### Rules -/

theorem Exec.cast {c : Cmd} {σ : ℕ → Str} {r r' : Res} {t t' : ℕ} (h : Exec c σ r t)
    (hr : r = r') (ht : t = t') : Exec c σ r' t' := hr ▸ ht ▸ h

/-- Iterating a loop body `n` times normally, then running the loop from the last state. -/
theorem Exec.loop_iter {c : Cmd} {r : Res} {t : ℕ} :
    ∀ (n : ℕ) (f : ℕ → ℕ → Str) (g : ℕ → ℕ),
      (∀ i < n, Exec c (f i) (.norm (f (i + 1))) (g i)) →
      Exec (.loop c) (f n) r t →
      Exec (.loop c) (f 0) r (∑ i ∈ Finset.range n, g i + t)
  | 0, f, g, _, hend => hend.cast rfl (by simp)
  | n + 1, f, g, hs, hend => by
    have ih := Exec.loop_iter n (fun i => f (i + 1)) (fun i => g (i + 1))
      (fun i hi => hs (i + 1) (by omega)) hend
    exact (Exec.loop_norm (hs 0 (by omega)) ih).cast rfl
      (by rw [Finset.sum_range_succ']; omega)

/-- Iterate a loop body `n` times, then `brk` out. -/
theorem Exec.loop_iter_brk {c : Cmd} {σ' : ℕ → Str} {t : ℕ} (n : ℕ) (f : ℕ → ℕ → Str)
    (g : ℕ → ℕ) (hs : ∀ i < n, Exec c (f i) (.norm (f (i + 1))) (g i))
    (hend : Exec c (f n) (.brk σ') t) :
    Exec (.loop c) (f 0) (.norm σ') (∑ i ∈ Finset.range n, g i + t) :=
  Exec.loop_iter n f g hs (.loop_brk hend)

/-- Iterate a loop body `n` times, then halt inside it. -/
theorem Exec.loop_iter_halt {c : Cmd} {b : Bool} {t : ℕ} (n : ℕ) (f : ℕ → ℕ → Str)
    (g : ℕ → ℕ) (hs : ∀ i < n, Exec c (f i) (.norm (f (i + 1))) (g i))
    (hend : Exec c (f n) (.halt b) t) :
    Exec (.loop c) (f 0) (.halt b) (∑ i ∈ Finset.range n, g i + t) :=
  Exec.loop_iter n f g hs (.loop_halt hend)

/-- Pop rule with the branch written out. -/
theorem Exec.pop_false {k : ℕ} {cn cf ct : Cmd} {σ : ℕ → Str} {s : Str} {r : Res} {t : ℕ}
    (hk : σ k = false :: s) (h : Exec cf (update σ k s) r t) :
    Exec (.pop k cn cf ct) σ r (t + 1) := Exec.pop_cons hk h

theorem Exec.pop_true {k : ℕ} {cn cf ct : Cmd} {σ : ℕ → Str} {s : Str} {r : Res} {t : ℕ}
    (hk : σ k = true :: s) (h : Exec ct (update σ k s) r t) :
    Exec (.pop k cn cf ct) σ r (t + 1) := Exec.pop_cons hk h

/-- Folded sequencing (`cmdSeq [] = skip`). -/
def cmdSeq : List Cmd → Cmd
  | [] => .skip
  | c :: cs => .seq c (cmdSeq cs)

@[simp] theorem cmdSeq_nil : cmdSeq [] = .skip := rfl
@[simp] theorem cmdSeq_cons (c : Cmd) (cs : List Cmd) : cmdSeq (c :: cs) = .seq c (cmdSeq cs) :=
  rfl

theorem Exec.cmdSeq_nil (σ : ℕ → Str) : Exec (cmdSeq []) σ (.norm σ) 1 := .skip σ

theorem Exec.cmdSeq_cons {c : Cmd} {cs : List Cmd} {σ σ' : ℕ → Str} {r : Res} {t₁ t₂ : ℕ}
    (h1 : Exec c σ (.norm σ') t₁) (h2 : Exec (cmdSeq cs) σ' r t₂) :
    Exec (cmdSeq (c :: cs)) σ r (t₁ + t₂) := .seq_norm h1 h2

/-- A chain of normally terminating commands: `cmdSeq` ends in the last state, with cost the
sum of the costs plus one (for the final `skip`). -/
theorem Exec.cmdSeq_chain : ∀ (cs : List Cmd) (f : ℕ → ℕ → Str) (g : ℕ → ℕ),
    (∀ i (hi : i < cs.length), Exec cs[i] (f i) (.norm (f (i + 1))) (g i)) →
    Exec (cmdSeq cs) (f 0) (.norm (f cs.length)) (∑ i ∈ Finset.range cs.length, g i + 1)
  | [], f, g, _ => (Exec.skip _).cast rfl (by simp)
  | c :: cs, f, g, h => by
    have ih := Exec.cmdSeq_chain cs (fun i => f (i + 1)) (fun i => g (i + 1))
      (fun i hi => h (i + 1) (by simp; omega))
    exact (Exec.seq_norm (h 0 (by simp)) ih).cast rfl
      (by simp only [List.length_cons]; rw [Finset.sum_range_succ']; omega)

/-! ### Utility commands -/

/-- Empty stack `k`. -/
def drain (k : ℕ) : Cmd := .loop (.pop k .brk .skip .skip)

theorem exec_drain (k : ℕ) : ∀ (l : Str) (σ : ℕ → Str), σ k = l →
    Exec (drain k) σ (.norm (update σ k [])) (2 * l.length + 2)
  | [], σ, hk => (Exec.loop_brk (Exec.pop_nil hk (Exec.brk σ))).cast
      (by rw [← hk, update_eq_self]) rfl
  | x :: s, σ, hk => by
    have h1 : Exec (.pop k .brk .skip .skip) σ (.norm (update σ k s)) 2 :=
      Exec.pop_cons hk (by cases x <;> exact Exec.skip _)
    have h2 := exec_drain k s (update σ k s) (by simp)
    exact (Exec.loop_norm h1 h2).cast (by rw [update_idem]) (by simp; omega)

/-- Pop all bits of stack `a`, pushing each onto stack `b`. -/
def move (a b : ℕ) : Cmd := .loop (.pop a .brk (.push b false) (.push b true))

theorem exec_move {a b : ℕ} (hab : a ≠ b) : ∀ (l : Str) (σ : ℕ → Str), σ a = l →
    Exec (move a b) σ (.norm (update (update σ a []) b (l.reverse ++ σ b))) (2 * l.length + 2)
  | [], σ, hk => (Exec.loop_brk (Exec.pop_nil hk (Exec.brk σ))).cast
      (by
        congr 1; funext j
        by_cases hj : j = b
        · subst hj; simp
        · by_cases ha : j = a
          · subst ha; simp [hj, hk]
          · simp [hj, ha]) rfl
  | x :: s, σ, hk => by
    have h1 : Exec (.pop a .brk (.push b false) (.push b true)) σ
        (.norm (update (update σ a s) b (x :: σ b))) 2 := by
      have e : update σ a s b = σ b := update_of_ne (Ne.symm hab) _ _
      refine Exec.pop_cons hk ?_
      cases x
      · exact (Exec.push b false _).cast (by rw [e]) rfl
      · exact (Exec.push b true _).cast (by rw [e]) rfl
    have h2 := exec_move hab s (update (update σ a s) b (x :: σ b)) (by rw [update_of_ne hab, update_self])
    refine (Exec.loop_norm h1 h2).cast ?_ (by simp; omega)
    congr 1; funext j
    by_cases hj : j = b
    · subst hj; simp
    · by_cases ha : j = a
      · subst ha; simp [hj]
      · simp [hj, ha]

/-- Pop all bits of stack `s`, pushing each onto both `a` and `b`. -/
def moveTwo (s a b : ℕ) : Cmd :=
  .loop (.pop s .brk (.seq (.push a false) (.push b false)) (.seq (.push a true) (.push b true)))

theorem exec_moveTwo {s a b : ℕ} (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b) :
    ∀ (l : Str) (σ : ℕ → Str), σ s = l →
    Exec (moveTwo s a b) σ
      (.norm (update (update (update σ s []) a (l.reverse ++ σ a)) b (l.reverse ++ σ b)))
      (3 * l.length + 2)
  | [], σ, hk => (Exec.loop_brk (Exec.pop_nil hk (Exec.brk σ))).cast
      (by
        congr 1; funext j
        by_cases hj : j = b
        · subst hj; simp
        · by_cases ha : j = a
          · subst ha; simp [hj]
          · by_cases hs : j = s
            · subst hs; simp [hj, ha, hk]
            · simp [hj, ha, hs]) rfl
  | x :: l, σ, hk => by
    have h1 : Exec (.pop s .brk (.seq (.push a false) (.push b false))
        (.seq (.push a true) (.push b true))) σ
        (.norm (update (update (update σ s l) a (x :: σ a)) b (x :: σ b))) 3 := by
      have ea : update σ s l a = σ a := update_of_ne (Ne.symm hsa) _ _
      have eb : update (update σ s l) a (x :: σ a) b = σ b := by
        rw [update_of_ne (Ne.symm hab), update_of_ne (Ne.symm hsb)]
      refine Exec.pop_cons hk ?_
      cases x
      · exact (Exec.seq_norm (Exec.push a false _) (Exec.push b false _)).cast
          (by rw [ea, eb]) rfl
      · exact (Exec.seq_norm (Exec.push a true _) (Exec.push b true _)).cast
          (by rw [ea, eb]) rfl
    have h2 := exec_moveTwo hsa hsb hab l
      (update (update (update σ s l) a (x :: σ a)) b (x :: σ b))
      (by rw [update_of_ne hsb, update_of_ne hsa, update_self])
    refine (Exec.loop_norm h1 h2).cast ?_ (by simp; omega)
    congr 1; funext j
    by_cases hj : j = b
    · subst hj; simp
    · by_cases ha : j = a
      · subst ha; simp [hj]
      · by_cases hs : j = s
        · subst hs; simp [hj, ha]
        · simp [hj, ha, hs]

/-- Append a copy of stack `a` on top of stack `b`, using the empty temporary stack `t`. -/
def copyVia (a b t : ℕ) : Cmd := .seq (move a t) (moveTwo t a b)

theorem exec_copyVia {a b t : ℕ} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (σ : ℕ → Str)
    (ht : σ t = []) :
    Exec (copyVia a b t) σ (.norm (update σ b (σ a ++ σ b))) (5 * (σ a).length + 4) := by
  have h1 := exec_move hat (σ a) σ rfl
  set σ1 := update (update σ a []) t ((σ a).reverse ++ σ t) with hσ1
  have e1 : σ1 t = (σ a).reverse := by simp [σ1, ht]
  have h2 := exec_moveTwo (Ne.symm hat) (Ne.symm hbt) hab _ σ1 e1
  refine (Exec.seq_norm h1 h2).cast ?_ (by simp; omega)
  congr 1; funext j
  by_cases hj : j = b
  · subst hj; simp [σ1, hab.symm, hbt]
  · by_cases ha : j = a
    · subst ha; simp [σ1, hj, hat]
    · by_cases hs : j = t
      · subst hs; simp [σ1, hj, ha, ht]
      · simp [σ1, hj, ha, hs]

/-- Straight-line pushes: stack `k` becomes `s ++ σ k` (`s` read top first). -/
def pushList (k : ℕ) : Str → Cmd
  | [] => .skip
  | x :: s => .seq (pushList k s) (.push k x)

theorem exec_pushList (k : ℕ) : ∀ (s : Str) (σ : ℕ → Str),
    Exec (pushList k s) σ (.norm (update σ k (s ++ σ k))) (s.length + 1)
  | [], σ => (Exec.skip σ).cast (by simp) (by simp)
  | x :: s, σ => (Exec.seq_norm (exec_pushList k s σ) (Exec.push k x _)).cast
      (by simp) (by simp)

/-! ### Upper-bound style -/

/-- `c` produces `r` from `σ` within `T` steps. -/
def ExecLe (c : Cmd) (σ : ℕ → Str) (r : Res) (T : ℕ) : Prop := ∃ t ≤ T, Exec c σ r t

theorem ExecLe.of {c : Cmd} {σ : ℕ → Str} {r : Res} {t : ℕ} (h : Exec c σ r t) :
    ExecLe c σ r t := ⟨t, le_rfl, h⟩

theorem ExecLe.mono {c : Cmd} {σ : ℕ → Str} {r : Res} {T T' : ℕ} (h : ExecLe c σ r T)
    (hT : T ≤ T') : ExecLe c σ r T' := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, ht.trans hT, h⟩

theorem ExecLe.seq_norm {c d : Cmd} {σ σ' : ℕ → Str} {r : Res} {T₁ T₂ : ℕ}
    (h1 : ExecLe c σ (.norm σ') T₁) (h2 : ExecLe d σ' r T₂) :
    ExecLe (.seq c d) σ r (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, h1⟩ := h1; obtain ⟨t₂, ht₂, h2⟩ := h2
  exact ⟨t₁ + t₂, by omega, .seq_norm h1 h2⟩

theorem ExecLe.seq_halt {c d : Cmd} {σ : ℕ → Str} {b : Bool} {T : ℕ}
    (h : ExecLe c σ (.halt b) T) : ExecLe (.seq c d) σ (.halt b) T := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, ht, .seq_halt h⟩

theorem ExecLe.seq_brk {c d : Cmd} {σ σ' : ℕ → Str} {T : ℕ}
    (h : ExecLe c σ (.brk σ') T) : ExecLe (.seq c d) σ (.brk σ') T := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, ht, .seq_brk h⟩

theorem ExecLe.runFor_toProg {c : Cmd} {σ : ℕ → Str} {b : Bool} {T : ℕ}
    (h : ExecLe c σ (.halt b) T) : runFor ∅ (toProg c) T (.run ⟨0, σ⟩) = .done b := by
  obtain ⟨t, ht, h⟩ := h; exact runFor_toProg_le h ht

end Pnp.Relativize.Struct

