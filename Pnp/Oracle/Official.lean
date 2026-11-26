import Pnp.Oracle.Machine
import Pnp.Upstream.Millennium

/-!
# The empty-oracle class `P ∅` is contained in the official class `P`

Our own oracle stack machines (`Pnp.Relativize`, see `Pnp/Oracle/Machine.lean`) were so far
unconnected to the official, Mathlib-based definition of `P` used by the Clay statement
(`Millennium.InPolynomialTime`, defined with Mathlib's multi-stack machines `FinTM2`).

Here we prove

* `inPolynomialTime_of_mem_P_empty`: every language decided by one of our machines with the
  empty oracle in time `(|x|+2)^k` lies in the official class `P` (over the alphabet `Bool`).

The proof compiles a program `p : Prog` into a Mathlib `FinTM2`:

* stacks `0, …, w-1` simulate the (finitely many) stacks used by `p`, stack `w` is the output;
* labels `inl i` (`i ≤ |p|`) simulate instruction `i` (label `|p|` = "jumped outside": reject),
  labels `inr j` empty work stack `j` (Mathlib's halting configuration requires all non-output
  stacks to be empty);
* one instruction of `p` is one `TM2` step; a query to the empty oracle always answers "no".

The running time is `T + w·(|x| + T + 1)` with `T = (|x|+2)^k`, a polynomial.
-/

namespace Pnp.Relativize.Official

open Turing Turing.TM2 Polynomial

/-- The stack an instruction acts on (`0` for `halt`). -/
def stkIdx : Instr → ℕ
  | .push k _ _ => k
  | .pop k _ _ _ => k
  | .query k _ _ => k
  | .halt _ => 0

variable (p : Prog)

/-- Number of work stacks: larger than every stack index used by `p`. -/
def nW : ℕ := (p.map (fun i => stkIdx i + 1)).sum + 1

theorem one_le_nW : 1 ≤ nW p := by simp [nW]

theorem stkIdx_lt {i : Instr} (h : i ∈ p) : stkIdx i < nW p := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun i => stkIdx i + 1) h)
  simp only [nW]; omega

/-- Stack indices of the compiled machine. -/
abbrev K := Fin (nW p + 1)

/-- Labels: instruction labels and cleanup labels. -/
abbrev Lab := Fin (p.length + 1) ⊕ Fin (nW p)

/-- The compiled machine's stack for stack `k` of `p` (truncated, never the output stack). -/
def toK (k : ℕ) : K p := ⟨min k (nW p - 1), by have := one_le_nW p; omega⟩

/-- The output stack. -/
def outK : K p := Fin.last _

/-- Label of program counter `n` (out-of-range counters all go to label `|p|`). -/
def lab (n : ℕ) : Lab p := .inl ⟨min n p.length, by omega⟩

/-- First cleanup label. -/
def clean0 : Lab p := .inr ⟨0, one_le_nW p⟩

/-- Jump target of a `pop` after reading the popped value. -/
def jmp (z f t : ℕ) : Option Bool → Lab p
  | none => lab p z
  | some false => lab p f
  | some true => lab p t

/-- Statement type of the compiled machine. -/
abbrev St := Stmt (fun _ : K p => Bool) (Lab p) (Option Bool)

/-- Cleanup of work stack `j`: pop until empty, then continue with `j+1` or halt. -/
def cleanStep (j : Fin (nW p)) : St p :=
  .pop (toK p j) (fun _ o => o)
    (.branch (fun v => v.isSome) (.goto fun _ => .inr j)
      (if h : j.val + 1 < nW p then .goto fun _ => .inr ⟨j.val + 1, h⟩
       else .load (fun _ => none) .halt))

/-- Translation of one instruction (or of "no instruction": reject). -/
def instrStmt : Option Instr → St p
  | none => .push (outK p) (fun _ => false) (.goto fun _ => clean0 p)
  | some (.halt b) => .push (outK p) (fun _ => b) (.goto fun _ => clean0 p)
  | some (.push k b n) => .push (toK p k) (fun _ => b) (.goto fun _ => lab p n)
  | some (.pop k z f t) => .pop (toK p k) (fun _ o => o) (.goto (jmp p z f t))
  | some (.query _ _ n) => .goto fun _ => lab p n

/-- The compiled program. -/
def M : Lab p → St p
  | .inl i => instrStmt p p[i.val]?
  | .inr j => cleanStep p j

/-- The compiled `FinTM2`. -/
def tm : FinTM2 where
  K := K p
  k₀ := toK p 0
  k₁ := outK p
  Γ := fun _ => Bool
  Λ := Lab p
  main := lab p 0
  σ := Option Bool
  initialState := none
  m := M p

/-- Configurations of the compiled machine. -/
abbrev Cf := Turing.TM2.Cfg (fun _ : K p => Bool) (Lab p) (Option Bool)

/-- `n` steps of the compiled machine. -/
def it (n : ℕ) (c : Cf p) : Option (Cf p) := (flip bind (TM2.step (M p)))^[n] (some c)

theorem it_zero (c : Cf p) : it p 0 c = some c := rfl

theorem it_succ {c c' : Cf p} (h : TM2.step (M p) c = some c') (n : ℕ) :
    it p (n + 1) c = it p n c' := by
  simp only [it, Function.iterate_succ_apply]
  simp [flip, h]

theorem it_add {c c' : Cf p} {a : ℕ} (h : it p a c = some c') (b : ℕ) :
    it p (b + a) c = it p b c' := by
  simp only [it] at h ⊢
  rw [Function.iterate_add_apply, h]

/-! ### Basic facts about indices -/

theorem toK_val {k : ℕ} (hk : k < nW p) : (toK p k).val = k := by
  simp [toK]; omega

theorem toK_ne_outK (k : ℕ) : toK p k ≠ outK p := by
  intro h
  have := congrArg Fin.val h
  simp [toK, outK] at this
  have := one_le_nW p
  omega

theorem val_lt_of_ne_outK {i : K p} (h : i ≠ outK p) : i.val < nW p := by
  have := i.isLt
  rcases Nat.lt_or_ge i.val (nW p) with h' | h'
  · exact h'
  · exact absurd (Fin.ext (by simp [outK]; omega)) h

theorem eq_toK_iff {i : K p} {k : ℕ} (hk : k < nW p) : i = toK p k ↔ i.val = k := by
  constructor
  · rintro rfl; exact toK_val p hk
  · intro h; exact Fin.ext (by rw [toK_val p hk, h])

theorem getElem?_min (n : ℕ) : p[min n p.length]? = p[n]? := by
  rcases Nat.lt_or_ge n p.length with h | h
  · rw [Nat.min_eq_left h.le]
  · rw [Nat.min_eq_right h]; simp [List.getElem?_eq_none h]

theorem M_lab (n : ℕ) : M p (lab p n) = instrStmt p p[n]? := by
  simp [M, lab, getElem?_min]

/-! ### Simulation of one step -/

/-- The compiled stacks `S` represent the stacks of `c`, and the output stack is empty. -/
def Sim (c : Relativize.Cfg) (S : ∀ _ : K p, List Bool) : Prop :=
  (∀ j : K p, j.val < nW p → S j = c.stk j.val) ∧ S (outK p) = []

theorem upd_apply (S : ∀ _ : K p, List Bool) (k j : K p) (l : List Bool) :
    Function.update S k l j = if j = k then l else S j := by
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem sim_update {c : Relativize.Cfg} {S : ∀ _ : K p, List Bool} (hs : Sim p c S) {k : ℕ}
    (hk : k < nW p) (l : List Bool) (pc : ℕ) :
    Sim p ⟨pc, Function.update c.stk k l⟩ (Function.update S (toK p k) l) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [upd_apply]
    by_cases h : j.val = k
    · rw [if_pos ((eq_toK_iff p hk).2 h), h]; simp
    · rw [if_neg (fun h' => h ((eq_toK_iff p hk).1 h')), hs.1 j hj]
      simp [h]
  · rw [upd_apply, if_neg (fun h => toK_ne_outK p k h.symm), hs.2]

theorem len_update_le (S : ∀ _ : K p, List Bool) (k : K p) (l : List Bool)
    (hl : l.length ≤ (S k).length + 1) (j : K p) :
    (Function.update S k l j).length ≤ (S j).length + 1 := by
  rw [upd_apply]; split_ifs with h
  · subst h; exact hl
  · omega

theorem step_run {c c2 : Relativize.Cfg} {S : ∀ _ : K p, List Bool} (v : Option Bool)
    (hs : Sim p c S) (h : step ∅ p c = .run c2) :
    ∃ v2 S2, TM2.step (M p) ⟨some (lab p c.pc), v, S⟩ = some ⟨some (lab p c2.pc), v2, S2⟩ ∧
      Sim p c2 S2 ∧ ∀ j : K p, (S2 j).length ≤ (S j).length + 1 := by
  unfold step at h
  rcases hp : p[c.pc]? with _ | ins
  · simp [hp] at h
  have hmem : ins ∈ p := List.mem_of_getElem? hp
  have hk := stkIdx_lt p hmem
  rw [hp] at h
  cases ins with
  | halt b => simp at h
  | push k b n =>
    simp only [State.run.injEq] at h
    subst h
    simp only [stkIdx] at hk
    refine ⟨v, Function.update S (toK p k) (b :: S (toK p k)), ?_, ?_, ?_⟩
    · simp [TM2.step, M_lab, hp, instrStmt]
    · have := sim_update p hs hk (b :: c.stk k) n
      rwa [hs.1 _ (by rw [toK_val p hk]; exact hk), toK_val p hk]
    · exact len_update_le p S _ _ (by simp)
  | query k y n =>
    simp only [Set.mem_empty_iff_false, if_false, State.run.injEq] at h
    subst h
    refine ⟨v, S, ?_, hs, fun j => by omega⟩
    simp [TM2.step, M_lab, hp, instrStmt]
  | pop k z f t =>
    simp only [stkIdx] at hk
    have hSk : S (toK p k) = c.stk k := by rw [hs.1 _ (by rw [toK_val p hk]; exact hk), toK_val p hk]
    rcases hck : c.stk k with _ | ⟨b, s⟩
    · simp only [hck, State.run.injEq] at h
      subst h
      refine ⟨none, S, ?_, hs, fun j => by omega⟩
      simp [TM2.step, M_lab, hp, instrStmt, hSk, hck, jmp, Function.update_eq_self_iff]
    · simp only [hck, State.run.injEq] at h
      subst h
      refine ⟨some b, Function.update S (toK p k) s, ?_, ?_, ?_⟩
      · simp only [TM2.step, M_lab, hp, instrStmt, stepAux, hSk, hck, List.head?_cons,
          List.tail_cons, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, and_true]
        cases b <;> rfl
      · exact sim_update p hs hk s _
      · exact len_update_le p S _ _ (by rw [hSk, hck]; simp; omega)

theorem step_done {c : Relativize.Cfg} {S : ∀ _ : K p, List Bool} {b : Bool} (v : Option Bool)
    (hs : Sim p c S) (h : step ∅ p c = .done b) :
    TM2.step (M p) ⟨some (lab p c.pc), v, S⟩ =
      some ⟨some (clean0 p), v, Function.update S (outK p) [b]⟩ := by
  unfold step at h
  rcases hp : p[c.pc]? with _ | ins
  · simp only [hp, State.done.injEq] at h
    subst h
    simp [TM2.step, M_lab, hp, instrStmt, hs.2]
  rw [hp] at h
  cases ins with
  | halt b' =>
    simp only [State.done.injEq] at h
    subst h
    simp [TM2.step, M_lab, hp, instrStmt, hs.2]
  | push k b n => simp at h
  | query k y n => simp at h
  | pop k z f t =>
    rcases hck : c.stk k with _ | ⟨b, s⟩ <;> simp [hck] at h

/-- Simulation of a whole halting run: the compiled machine reaches the first cleanup label
with the answer on the output stack, within the same number of steps. -/
theorem run_sim {b : Bool} (t : ℕ) : ∀ (c : Relativize.Cfg) (S : ∀ _ : K p, List Bool)
    (v : Option Bool) (B : ℕ), Sim p c S → (∀ j, (S j).length ≤ B) →
    runFor ∅ p t (.run c) = .done b →
    ∃ n ≤ t, ∃ v' S', it p n ⟨some (lab p c.pc), v, S⟩ = some ⟨some (clean0 p), v', S'⟩ ∧
      S' (outK p) = [b] ∧ ∀ j : K p, j ≠ outK p → (S' j).length ≤ B + n := by
  induction t with
  | zero => intro c S v B _ _ h; simp at h
  | succ t ih =>
    intro c S v B hs hB h
    rw [runFor_succ_run] at h
    rcases hst : step ∅ p c with c2 | b'
    · rw [hst] at h
      obtain ⟨v2, S2, hstep, hs2, hlen⟩ := step_run p v hs hst
      obtain ⟨n, hn, v', S', hit, hout, hlen'⟩ :=
        ih c2 S2 v2 (B + 1) hs2 (fun j => by have := hB j; have := hlen j; omega) h
      refine ⟨n + 1, by omega, v', S', ?_, hout, fun j hj => ?_⟩
      · rw [it_succ p hstep, hit]
      · have := hlen' j hj; omega
    · rw [hst, runFor_done, State.done.injEq] at h
      subst h
      refine ⟨1, by omega, v, Function.update S (outK p) [b'], ?_, by simp, fun j hj => ?_⟩
      · rw [it_succ p (step_done p v hs hst), it_zero]
      · rw [Function.update_of_ne hj]; have := hB j; omega

/-! ### Cleanup -/

theorem cleanup_inner (j : Fin (nW p)) : ∀ (l : List Bool) (S : ∀ _ : K p, List Bool)
    (v : Option Bool), S (toK p j) = l →
    ∃ v', it p l.length ⟨some (.inr j), v, S⟩ =
      some ⟨some (.inr j), v', Function.update S (toK p j) []⟩ := by
  intro l
  induction l with
  | nil =>
    intro S v hS
    refine ⟨v, ?_⟩
    rw [List.length_nil, it_zero, ← hS, Function.update_eq_self]
  | cons a l ih =>
    intro S v hS
    have hstep : TM2.step (M p) ⟨some (.inr j), v, S⟩ =
        some ⟨some (.inr j), some a, Function.update S (toK p j) l⟩ := by
      simp [TM2.step, M, cleanStep, hS]
    obtain ⟨v', hit⟩ := ih (Function.update S (toK p j) l) (some a) (by simp)
    refine ⟨v', ?_⟩
    rw [List.length_cons, it_succ p hstep, hit, Function.update_idem]

theorem haltList_stk (b : Bool) (i : K p) :
    ((haltList (tm p) [b]).stk i : List Bool) = if i = outK p then [b] else [] := by
  by_cases h : i = outK p
  · subst h; simp [haltList, tm]
  · simp [haltList, tm, h]

theorem cleanup (b : Bool) (B : ℕ) : ∀ (d : ℕ) (j : Fin (nW p)), nW p - j.val = d →
    ∀ (S : ∀ _ : K p, List Bool) (v : Option Bool),
    (∀ i : K p, i ≠ outK p → (S i).length ≤ B) → S (outK p) = [b] →
    (∀ i : K p, i.val < j.val → S i = []) →
    ∃ n ≤ d * (B + 1), it p n ⟨some (.inr j), v, S⟩ = some (haltList (tm p) [b]) := by
  intro d
  induction d with
  | zero => intro j hj; have := j.isLt; omega
  | succ d ih =>
    intro j hj S v hB hout hlow
    have hjK : (toK p j).val = j.val := toK_val p j.isLt
    obtain ⟨v1, hit1⟩ := cleanup_inner p j (S (toK p j)) S v rfl
    have hl : (S (toK p j)).length ≤ B := hB _ (toK_ne_outK p _)
    set S1 := Function.update S (toK p j) [] with hS1
    have hS1j : S1 (toK p j) = [] := by simp [S1]
    have hS1o : S1 (outK p) = [b] := by
      rw [hS1, Function.update_of_ne (toK_ne_outK p _).symm, hout]
    have hlow1 : ∀ i : K p, i.val < j.val + 1 → S1 i = [] := by
      intro i hi
      by_cases h : i = toK p j
      · rw [h, hS1j]
      · rw [hS1, Function.update_of_ne h]
        apply hlow
        have : i.val ≠ j.val := fun h' => h (Fin.ext (by rw [hjK, h']))
        omega
    by_cases hnext : j.val + 1 < nW p
    · have hstep : TM2.step (M p) ⟨some (.inr j), v1, S1⟩ =
          some ⟨some (.inr ⟨j.val + 1, hnext⟩), none, S1⟩ := by
        simp [TM2.step, M, cleanStep, hS1j, hnext, Function.update_eq_self_iff]
      obtain ⟨n, hn, hit⟩ := ih ⟨j.val + 1, hnext⟩ (by simp; omega) S1 none
        (fun i hi => by
          rw [hS1, upd_apply]; split_ifs
          · simp
          · exact hB i hi) hS1o hlow1
      refine ⟨n + 1 + (S (toK p j)).length, ?_, ?_⟩
      · have : (d + 1) * (B + 1) = d * (B + 1) + B + 1 := by ring
        omega
      · rw [it_add p hit1, it_succ p hstep, hit]
    · have hstep : TM2.step (M p) ⟨some (.inr j), v1, S1⟩ = some (haltList (tm p) [b]) := by
        have hS1eq : S1 = (haltList (tm p) [b]).stk := by
          funext i
          rw [haltList_stk]
          split_ifs with h
          · rw [h, hS1o]
          · apply hlow1
            have := val_lt_of_ne_outK p h
            omega
        simp only [TM2.step, M, cleanStep, hnext, dite_false, stepAux, hS1j, List.head?_nil,
          Option.isSome_none, cond_false, List.tail_nil]
        rw [show Function.update S1 (toK p j) [] = S1 by rw [← hS1j, Function.update_eq_self], hS1eq]
        rfl
      refine ⟨1 + (S (toK p j)).length, ?_, ?_⟩
      · have : (d + 1) * (B + 1) = d * (B + 1) + B + 1 := by ring
        omega
      · rw [it_add p hit1, it_succ p hstep, it_zero]
        rfl

/-! ### Main theorem -/

theorem initList_stk (x : List Bool) (i : K p) :
    ((initList (tm p) x).stk i : List Bool) = if i = toK p 0 then x else [] := by
  by_cases h : i = toK p 0
  · subst h; simp [initList, tm]
  · simp [initList, tm, h]

/-- **`P ∅ ⊆ P`.** Every language decided by one of our oracle stack machines with the empty
oracle in time `(|x|+2)^k` is in the official class `P` of the Clay formalization
(`Millennium.InPolynomialTime`, multi-stack Turing machines of Mathlib, alphabet `Bool`). -/
theorem inPolynomialTime_of_mem_P_empty {L : Set Str} (hL : L ∈ P ∅) :
    Millennium.InPolynomialTime (Millennium.fin_encoding_string Bool) (fun x => x ∈ L) := by
  classical
  obtain ⟨p, k, hp⟩ := hL
  refine ⟨fun x => decide (x ∈ L), ?_, fun x => by simp⟩
  refine
    { tm := tm p
      inputAlphabet := Equiv.refl Bool
      outputAlphabet := Equiv.refl Bool
      time := (X + 2) ^ k + C (nW p) * (X + (X + 2) ^ k + 1)
      outputsFun := fun x => ?_ }
  set b := decide (x ∈ L) with hbdef
  have hrun : runFor ∅ p (tb k x.length) (.run (init [x])) = .done b := by
    obtain ⟨b', hrun, hb'⟩ := hp x
    have : b' = b := by cases b' <;> simp_all
    rw [← this]; exact hrun
  have hx : List.map (Equiv.refl Bool).invFun ((Millennium.fin_encoding_string Bool).encode x)
      = x := by simp
  have hout : List.map (Equiv.refl Bool).invFun (Computability.finEncodingBoolBool.encode b) = [b] := by
    simp [Computability.finEncodingBoolBool, Computability.encodeBool]
  -- the initial configuration simulates `init [x]`
  set S0 : ∀ _ : K p, List Bool := fun i => if i = toK p 0 then x else [] with hS0
  have h0 : (0 : ℕ) < nW p := one_le_nW p
  have hsim : Sim p (init [x]) S0 := by
    refine ⟨fun j hj => ?_, ?_⟩
    · simp only [hS0, eq_toK_iff p h0, init]
      rcases j with ⟨_ | j, hj'⟩ <;> simp
    · simp only [hS0, if_neg (fun h : outK p = toK p 0 => toK_ne_outK p 0 h.symm)]
  have hB : ∀ j, (S0 j).length ≤ x.length := by
    intro j; simp only [hS0]; split_ifs <;> simp
  have hinit : (initList (tm p) (List.map (Equiv.refl Bool).invFun
      ((Millennium.fin_encoding_string Bool).encode x)) : Cf p) =
      ⟨some (lab p (init [x]).pc), none, S0⟩ := by
    show (⟨_, _, _⟩ : Cf p) = _
    congr 1
    funext i
    refine (initList_stk p _ i).trans ?_
    simp only [hS0]
    split_ifs
    · exact hx
    · rfl
  have hmain : ∃ n, n ≤ (x.length + 2) ^ k + nW p * (x.length + (x.length + 2) ^ k + 1) ∧
      it p n ⟨some (lab p (init [x]).pc), none, S0⟩ = some (haltList (tm p) [b]) := by
    obtain ⟨n1, hn1, v', S', hit1, hout', hlen⟩ :=
      run_sim p _ (init [x]) S0 none x.length hsim hB hrun
    obtain ⟨n2, hn2, hit2⟩ := cleanup p b (x.length + n1) (nW p) ⟨0, h0⟩ (by simp) S' v' hlen
      hout' (fun i hi => by simp at hi)
    have hit2' : it p n2 ⟨some (clean0 p), v', S'⟩ = some (haltList (tm p) [b]) := hit2
    refine ⟨n2 + n1, ?_, by rw [it_add p hit1, hit2']⟩
    simp only [tb] at hn1
    have : nW p * (x.length + n1 + 1) ≤ nW p * (x.length + (x.length + 2) ^ k + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨⟨Classical.choose hmain, ?_⟩, ?_⟩
  · change _ = some (haltList (tm p) [b])
    have h2 : it p (Classical.choose hmain) (initList (tm p) (List.map (Equiv.refl Bool).invFun
        ((Millennium.fin_encoding_string Bool).encode x)) : Cf p) = some (haltList (tm p) [b]) := by
      rw [hinit]; exact (Classical.choose_spec hmain).2
    exact h2
  · simp only [Millennium.fin_encoding_string_encode, eval_add, eval_pow, eval_X, eval_ofNat,
      eval_mul, eval_C, eval_one]
    exact (Classical.choose_spec hmain).1

end Pnp.Relativize.Official
