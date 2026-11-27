import Pnp.CookLevin.SAT

/-!
# Structured stack programs computing functions → official `TM2ComputableInPolyTime` (M33a)

If a structured program `c : Cmd` (see `Pnp/Oracle/Struct.lean`), started on input `x`, terminates
normally within `(|x|+2)^K` steps, having pushed the 2-bit codes `ic` of the symbols of `g x` onto
stack `kOut` (so that this stack ends up as `((g x).flatMap ic).reverse`), then `g` is computable in
polynomial time in Mathlib's official sense (`Turing.TM2ComputableInPolyTime`).

The proof composes (`Pnp.TM2Comp.comp`) two machines:

* **Machine A** (`Bool → Bool`), a variant of `Pnp/Oracle/Official.lean`: it simulates
  `toProg c` on work stacks; when the program jumps outside (or halts), it pops stack `kOut`
  onto the output stack bit by bit (this reverses it, so the output is `(g x).flatMap ic`), and
  then empties all work stacks.  For the simulated stacks we reuse `Official.K q`,
  `Official.Sim q`, … for the auxiliary program `q = toProg c ++ [push kOut false 0]`, whose
  `nW` exceeds both every stack index of `toProg c` and `kOut`.
* **Machine B** (`Bool → SatSym`): decodes a bit string two bits at a time (`dec2`), with
  `dec2 (l.flatMap ic) = l`.

* `computable_of_cmd`, `computable_of_cmd_code`: the main results.
-/

namespace Pnp.CookLevin.FunBridge

open Turing Polynomial Pnp.Relativize

/-! ## Machine A: simulate the program, then output stack `kOut` -/

section MachineA

variable (p q : Prog) (kOut : ℕ)

/-- Labels: instruction labels, the transfer label (`none`), cleanup labels. -/
abbrev Lab := Fin (p.length + 1) ⊕ Option (Fin (Official.nW q))

/-- Label of program counter `n` (out-of-range counters all go to label `|p|`). -/
def lab (n : ℕ) : Lab p q := .inl ⟨min n p.length, by omega⟩

/-- The transfer label. -/
def xfer : Lab p q := .inr none

/-- First cleanup label. -/
def clean0 : Lab p q := .inr (some ⟨0, Official.one_le_nW q⟩)

/-- Jump target of a `pop` after reading the popped value. -/
def jmp (z f t : ℕ) : Option Bool → Lab p q
  | none => lab p q z
  | some false => lab p q f
  | some true => lab p q t

/-- Statement type of machine A. -/
abbrev St := TM2.Stmt (fun _ : Official.K q => Bool) (Lab p q) (Option Bool)

/-- Cleanup of work stack `j`: pop until empty, then continue with `j+1` or halt. -/
def cleanStep (j : Fin (Official.nW q)) : St p q :=
  .pop (Official.toK q j) (fun _ o => o)
    (.branch (fun v => v.isSome) (.goto fun _ => .inr (some j))
      (if h : j.val + 1 < Official.nW q then .goto fun _ => .inr (some ⟨j.val + 1, h⟩)
       else .load (fun _ => none) .halt))

/-- Transfer: pop stack `kOut`, push the bit on the output stack; when empty, clean up. -/
def xferStmt : St p q :=
  .pop (Official.toK q kOut) (fun _ o => o)
    (.branch (fun v => v.isSome)
      (.push (Official.outK q) (fun v => v.getD false) (.goto fun _ => xfer p q))
      (.goto fun _ => clean0 p q))

/-- Translation of one instruction (or of "no instruction": start the transfer). -/
def instrStmt : Option Instr → St p q
  | none => .goto fun _ => xfer p q
  | some (.halt _) => .goto fun _ => xfer p q
  | some (.push k b n) => .push (Official.toK q k) (fun _ => b) (.goto fun _ => lab p q n)
  | some (.pop k z f t) => .pop (Official.toK q k) (fun _ o => o) (.goto (jmp p q z f t))
  | some (.query _ _ n) => .goto fun _ => lab p q n

/-- The program of machine A. -/
def M : Lab p q → St p q
  | .inl i => instrStmt p q p[i.val]?
  | .inr none => xferStmt p q kOut
  | .inr (some j) => cleanStep p q j

/-- Machine A as a `FinTM2`. -/
def tm : FinTM2 where
  K := Official.K q
  k₀ := Official.toK q 0
  k₁ := Official.outK q
  Γ := fun _ => Bool
  Λ := Lab p q
  main := lab p q 0
  σ := Option Bool
  initialState := none
  m := M p q kOut

/-- Configurations of machine A. -/
abbrev Cf := Turing.TM2.Cfg (fun _ : Official.K q => Bool) (Lab p q) (Option Bool)

/-- `n` steps of machine A. -/
def it (n : ℕ) (c : Cf p q) : Option (Cf p q) := (flip bind (TM2.step (M p q kOut)))^[n] (some c)

theorem it_zero (c : Cf p q) : it p q kOut 0 c = some c := rfl

theorem it_succ {c c' : Cf p q} (h : TM2.step (M p q kOut) c = some c') (n : ℕ) :
    it p q kOut (n + 1) c = it p q kOut n c' := by
  simp only [it, Function.iterate_succ_apply]
  simp [flip, h]

theorem it_add {c c' : Cf p q} {a : ℕ} (h : it p q kOut a c = some c') (b : ℕ) :
    it p q kOut (b + a) c = it p q kOut b c' := by
  simp only [it] at h ⊢
  rw [Function.iterate_add_apply, h]

theorem M_lab (n : ℕ) : M p q kOut (lab p q n) = instrStmt p q p[n]? := by
  simp [M, lab, Official.getElem?_min]

/-! ### Simulation of the program -/

theorem step_run (hq : ∀ i ∈ p, Official.stkIdx i < Official.nW q) {c c2 : Relativize.Cfg}
    {S : ∀ _ : Official.K q, List Bool} (v : Option Bool)
    (hs : Official.Sim q c S) (h : step ∅ p c = .run c2) :
    ∃ v2 S2, TM2.step (M p q kOut) ⟨some (lab p q c.pc), v, S⟩ =
        some ⟨some (lab p q c2.pc), v2, S2⟩ ∧
      Official.Sim q c2 S2 ∧ ∀ j : Official.K q, (S2 j).length ≤ (S j).length + 1 := by
  unfold step at h
  rcases hp : p[c.pc]? with _ | ins
  · simp [hp] at h
  have hmem : ins ∈ p := List.mem_of_getElem? hp
  have hk := hq _ hmem
  rw [hp] at h
  cases ins with
  | halt b => simp at h
  | push k b n =>
    simp only [State.run.injEq] at h
    subst h
    simp only [Official.stkIdx] at hk
    refine ⟨v, Function.update S (Official.toK q k) (b :: S (Official.toK q k)), ?_, ?_, ?_⟩
    · simp [TM2.step, M_lab, hp, instrStmt]
    · have := Official.sim_update q hs hk (b :: c.stk k) n
      rwa [hs.1 _ (by rw [Official.toK_val q hk]; exact hk), Official.toK_val q hk]
    · exact Official.len_update_le q S _ _ (by simp)
  | query k y n =>
    simp only [Set.mem_empty_iff_false, if_false, State.run.injEq] at h
    subst h
    refine ⟨v, S, ?_, hs, fun j => by omega⟩
    simp [TM2.step, M_lab, hp, instrStmt]
  | pop k z f t =>
    simp only [Official.stkIdx] at hk
    have hSk : S (Official.toK q k) = c.stk k := by
      rw [hs.1 _ (by rw [Official.toK_val q hk]; exact hk), Official.toK_val q hk]
    rcases hck : c.stk k with _ | ⟨b, s⟩
    · simp only [hck, State.run.injEq] at h
      subst h
      refine ⟨none, S, ?_, hs, fun j => by omega⟩
      simp [TM2.step, M_lab, hp, instrStmt, hSk, hck, jmp, Function.update_eq_self_iff]
    · simp only [hck, State.run.injEq] at h
      subst h
      refine ⟨some b, Function.update S (Official.toK q k) s, ?_, ?_, ?_⟩
      · simp only [TM2.step, M_lab, hp, instrStmt, TM2.stepAux, hSk, hck, List.head?_cons,
          List.tail_cons, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, and_true]
        cases b <;> rfl
      · exact Official.sim_update q hs hk s _
      · exact Official.len_update_le q S _ _ (by rw [hSk, hck]; simp; omega)

/-- Simulation of a non-halting run. -/
theorem run_reach (hq : ∀ i ∈ p, Official.stkIdx i < Official.nW q) (t : ℕ) :
    ∀ (c : Relativize.Cfg) (S : ∀ _ : Official.K q, List Bool) (v : Option Bool) (B : ℕ)
      (pc' : ℕ) (σ' : ℕ → Str), Official.Sim q c S → (∀ j, (S j).length ≤ B) →
    runFor ∅ p t (.run c) = .run ⟨pc', σ'⟩ →
    ∃ v' S', it p q kOut t ⟨some (lab p q c.pc), v, S⟩ = some ⟨some (lab p q pc'), v', S'⟩ ∧
      Official.Sim q ⟨pc', σ'⟩ S' ∧ ∀ j, (S' j).length ≤ B + t := by
  induction t with
  | zero =>
    intro c S v B pc' σ' hs hB h
    rw [runFor_zero, State.run.injEq] at h
    subst h
    exact ⟨v, S, it_zero p q kOut _, hs, fun j => by simpa using hB j⟩
  | succ t ih =>
    intro c S v B pc' σ' hs hB h
    rw [runFor_succ_run] at h
    rcases hst : step ∅ p c with c2 | b'
    · rw [hst] at h
      obtain ⟨v2, S2, hstep, hs2, hlen⟩ := step_run p q kOut hq v hs hst
      obtain ⟨v', S', hit, hs', hlen'⟩ :=
        ih c2 S2 v2 (B + 1) pc' σ' hs2 (fun j => by have := hB j; have := hlen j; omega) h
      refine ⟨v', S', ?_, hs', fun j => ?_⟩
      · rw [it_succ p q kOut hstep, hit]
      · have := hlen' j; omega
    · rw [hst, runFor_done] at h
      cases h

/-! ### Transfer -/

theorem toK_ne (k : ℕ) : Official.outK q ≠ Official.toK q k :=
  fun h => Official.toK_ne_outK q k h.symm

theorem xfer_run : ∀ (l acc : List Bool) (S : ∀ _ : Official.K q, List Bool) (v : Option Bool),
    S (Official.toK q kOut) = l → S (Official.outK q) = acc →
    ∃ S', it p q kOut (l.length + 1) ⟨some (xfer p q), v, S⟩ =
        some ⟨some (clean0 p q), none, S'⟩ ∧
      S' (Official.outK q) = l.reverse ++ acc ∧
      ∀ j, j ≠ Official.outK q → (S' j).length ≤ (S j).length := by
  intro l
  induction l with
  | nil =>
    intro acc S v hS hacc
    refine ⟨Function.update S (Official.toK q kOut) [], ?_, ?_, ?_⟩
    · rw [List.length_nil, it_succ p q kOut (c' := ⟨some (clean0 p q), none,
        Function.update S (Official.toK q kOut) []⟩) ?_, it_zero]
      simp [TM2.step, M, xfer, xferStmt, hS, TM2.stepAux]
    · rw [Function.update_of_ne (toK_ne q kOut), hacc]; simp
    · intro j _
      rw [Official.upd_apply]; split_ifs <;> simp
  | cons a l ih =>
    intro acc S v hS hacc
    have hstep : TM2.step (M p q kOut) ⟨some (xfer p q), v, S⟩ =
        some ⟨some (xfer p q), some a, Function.update (Function.update S
          (Official.toK q kOut) l) (Official.outK q) (a :: acc)⟩ := by
      simp [TM2.step, M, xfer, xferStmt, hS, TM2.stepAux, Function.update_of_ne (toK_ne q kOut),
        hacc]
    obtain ⟨S', hit, hout, hlen⟩ := ih (a :: acc) (Function.update (Function.update S
          (Official.toK q kOut) l) (Official.outK q) (a :: acc)) (some a)
      (by rw [Function.update_of_ne (toK_ne q kOut).symm]; simp)
      (by simp)
    refine ⟨S', ?_, by rw [hout]; simp, fun j hj => ?_⟩
    · rw [List.length_cons, it_succ p q kOut hstep, hit]
    · refine (hlen j hj).trans ?_
      rw [Function.update_of_ne hj, Official.upd_apply]
      split_ifs with h
      · subst h; rw [hS]; simp
      · exact le_rfl

/-! ### Cleanup -/

theorem cleanup_inner (j : Fin (Official.nW q)) : ∀ (l : List Bool)
    (S : ∀ _ : Official.K q, List Bool) (v : Option Bool), S (Official.toK q j) = l →
    ∃ v', it p q kOut l.length ⟨some (.inr (some j)), v, S⟩ =
      some ⟨some (.inr (some j)), v', Function.update S (Official.toK q j) []⟩ := by
  intro l
  induction l with
  | nil =>
    intro S v hS
    refine ⟨v, ?_⟩
    rw [List.length_nil, it_zero, ← hS, Function.update_eq_self]
  | cons a l ih =>
    intro S v hS
    have hstep : TM2.step (M p q kOut) ⟨some (.inr (some j)), v, S⟩ =
        some ⟨some (.inr (some j)), some a, Function.update S (Official.toK q j) l⟩ := by
      simp [TM2.step, M, cleanStep, hS]
    obtain ⟨v', hit⟩ := ih (Function.update S (Official.toK q j) l) (some a) (by simp)
    refine ⟨v', ?_⟩
    rw [List.length_cons, it_succ p q kOut hstep, hit, Function.update_idem]

theorem haltList_stk (o : List Bool) (i : Official.K q) :
    ((haltList (tm p q kOut) o).stk i : List Bool) = if i = Official.outK q then o else [] := by
  by_cases h : i = Official.outK q
  · subst h; simp [haltList, tm]
  · simp [haltList, tm, h]

theorem cleanup (o : List Bool) (B : ℕ) : ∀ (d : ℕ) (j : Fin (Official.nW q)),
    Official.nW q - j.val = d →
    ∀ (S : ∀ _ : Official.K q, List Bool) (v : Option Bool),
    (∀ i : Official.K q, i ≠ Official.outK q → (S i).length ≤ B) → S (Official.outK q) = o →
    (∀ i : Official.K q, i.val < j.val → S i = []) →
    ∃ n ≤ d * (B + 1), it p q kOut n ⟨some (.inr (some j)), v, S⟩ =
      some (haltList (tm p q kOut) o) := by
  intro d
  induction d with
  | zero => intro j hj; have := j.isLt; omega
  | succ d ih =>
    intro j hj S v hB hout hlow
    have hjK : (Official.toK q j).val = j.val := Official.toK_val q j.isLt
    obtain ⟨v1, hit1⟩ := cleanup_inner p q kOut j (S (Official.toK q j)) S v rfl
    have hl : (S (Official.toK q j)).length ≤ B := hB _ (Official.toK_ne_outK q _)
    set S1 := Function.update S (Official.toK q j) [] with hS1
    have hS1j : S1 (Official.toK q j) = [] := by simp [S1]
    have hS1o : S1 (Official.outK q) = o := by
      rw [hS1, Function.update_of_ne (Official.toK_ne_outK q _).symm, hout]
    have hlow1 : ∀ i : Official.K q, i.val < j.val + 1 → S1 i = [] := by
      intro i hi
      by_cases h : i = Official.toK q j
      · rw [h, hS1j]
      · rw [hS1, Function.update_of_ne h]
        apply hlow
        have : i.val ≠ j.val := fun h' => h (Fin.ext (by rw [hjK, h']))
        omega
    by_cases hnext : j.val + 1 < Official.nW q
    · have hstep : TM2.step (M p q kOut) ⟨some (.inr (some j)), v1, S1⟩ =
          some ⟨some (.inr (some ⟨j.val + 1, hnext⟩)), none, S1⟩ := by
        simp [TM2.step, M, cleanStep, hS1j, hnext, Function.update_eq_self_iff]
      obtain ⟨n, hn, hit⟩ := ih ⟨j.val + 1, hnext⟩ (by simp; omega) S1 none
        (fun i hi => by
          rw [hS1, Official.upd_apply]; split_ifs
          · simp
          · exact hB i hi) hS1o hlow1
      refine ⟨n + 1 + (S (Official.toK q j)).length, ?_, ?_⟩
      · have : (d + 1) * (B + 1) = d * (B + 1) + B + 1 := by ring
        omega
      · rw [it_add p q kOut hit1, it_succ p q kOut hstep, hit]
    · have hstep : TM2.step (M p q kOut) ⟨some (.inr (some j)), v1, S1⟩ =
          some (haltList (tm p q kOut) o) := by
        have hS1eq : S1 = (haltList (tm p q kOut) o).stk := by
          funext i
          rw [haltList_stk]
          split_ifs with h
          · rw [h, hS1o]
          · apply hlow1
            have := Official.val_lt_of_ne_outK q h
            omega
        simp only [TM2.step, M, cleanStep, hnext, dite_false, TM2.stepAux, hS1j, List.head?_nil,
          Option.isSome_none, cond_false, List.tail_nil]
        rw [show Function.update S1 (Official.toK q j) [] = S1 by
          rw [← hS1j, Function.update_eq_self], hS1eq]
        rfl
      refine ⟨1 + (S (Official.toK q j)).length, ?_, ?_⟩
      · have : (d + 1) * (B + 1) = d * (B + 1) + B + 1 := by ring
        omega
      · rw [it_add p q kOut hit1, it_succ p q kOut hstep, it_zero]
        rfl

/-! ### Main theorem for machine A -/

/-- The auxiliary program fixing the number of work stacks (larger than `kOut`). -/
def pe (p : Prog) (kOut : ℕ) : Prog := p ++ [.push kOut false 0]

theorem nW_pe (p : Prog) (kOut : ℕ) : Official.nW (pe p kOut) = Official.nW p + kOut + 1 := by
  simp [Official.nW, pe, Official.stkIdx]; omega

theorem hq_pe (p : Prog) (kOut : ℕ) :
    ∀ i ∈ p, Official.stkIdx i < Official.nW (pe p kOut) := fun i hi => by
  have := Official.stkIdx_lt p hi; rw [nW_pe]; omega

theorem initList_stk (x : List Bool) (i : Official.K q) :
    ((initList (tm p q kOut) x).stk i : List Bool) = if i = Official.toK q 0 then x else [] := by
  by_cases h : i = Official.toK q 0
  · subst h; simp [initList, tm]
  · simp [initList, tm, h]

open Pnp.CookLevin in
/-- Machine A runs within the polynomial bound and outputs `(g x).flatMap ic`. -/
theorem mainA (c : Struct.Cmd) (kOut K : ℕ) (g : Str → List SatSym)
    (h : ∀ x : Str, ∃ σ', Struct.ExecLe c (init [x]).stk (.norm σ') (tb K x.length) ∧
      σ' kOut = ((g x).flatMap ic).reverse) (x : Str) :
    ∃ n, n ≤ (x.length + 2) ^ K + 1 + (x.length + (x.length + 2) ^ K + 1) +
        Official.nW (pe (Struct.toProg c) kOut) * (x.length + (x.length + 2) ^ K + 1) ∧
      it (Struct.toProg c) (pe (Struct.toProg c) kOut) kOut n
        (initList (tm (Struct.toProg c) (pe (Struct.toProg c) kOut) kOut) x) =
        some (haltList (tm (Struct.toProg c) (pe (Struct.toProg c) kOut) kOut)
          ((g x).flatMap ic)) := by
  set p := Struct.toProg c with hpdef
  set q := pe p kOut with hqdef
  have hq : ∀ i ∈ p, Official.stkIdx i < Official.nW q := hq_pe p kOut
  have hkq : kOut < Official.nW q := by rw [hqdef, nW_pe]; omega
  obtain ⟨σ', ⟨t, ht, hex⟩, hσ'⟩ := h x
  have hreach : runFor ∅ p t (.run (init [x])) = .run ⟨Struct.size c, σ'⟩ :=
    Struct.compile_sound hex 0 (Struct.size c) (Struct.size c) (Comb.codeAt_self _)
  have hsize : Struct.size c = p.length := by simp [hpdef, Struct.toProg]
  -- the initial configuration
  set S0 : ∀ _ : Official.K q, List Bool := fun i => if i = Official.toK q 0 then x else []
    with hS0
  have h0 : (0 : ℕ) < Official.nW q := Official.one_le_nW q
  have hsim : Official.Sim q (init [x]) S0 := by
    refine ⟨fun j hj => ?_, ?_⟩
    · simp only [hS0, Official.eq_toK_iff q h0, init]
      rcases j with ⟨_ | j, hj'⟩ <;> simp
    · simp only [hS0, if_neg (toK_ne q 0)]
  have hB : ∀ j, (S0 j).length ≤ x.length := by
    intro j; simp only [hS0]; split_ifs <;> simp
  have hinit : (initList (tm p q kOut) x : Cf p q) = ⟨some (lab p q (init [x]).pc), none, S0⟩ := by
    show (⟨_, _, _⟩ : Cf p q) = _
    congr 1
  -- phase 1: simulation
  obtain ⟨v1, S1, hit1, hs1, hlen1⟩ :=
    run_reach p q kOut hq t (init [x]) S0 none x.length _ _ hsim hB hreach
  have hstepX : TM2.step (M p q kOut) ⟨some (lab p q (Struct.size c)), v1, S1⟩ =
      some ⟨some (xfer p q), v1, S1⟩ := by
    simp [TM2.step, M_lab, hsize, instrStmt, TM2.stepAux]
  -- phase 2: transfer
  set l := ((g x).flatMap ic).reverse with hl
  have hS1k : S1 (Official.toK q kOut) = l := by
    rw [hs1.1 _ (by rw [Official.toK_val q hkq]; exact hkq), Official.toK_val q hkq]
    exact hσ'
  obtain ⟨S2, hit2, hout2, hlen2⟩ := xfer_run p q kOut l [] S1 v1 hS1k hs1.2
  have hll : l.length ≤ x.length + t := by rw [← hS1k]; exact hlen1 _
  -- phase 3: cleanup
  obtain ⟨n3, hn3, hit3⟩ := cleanup p q kOut ((g x).flatMap ic) (x.length + t) (Official.nW q)
    ⟨0, h0⟩ (by simp) S2 none (fun i hi => (hlen2 i hi).trans (hlen1 i))
    (by rw [hout2, hl]; simp) (fun i hi => by simp at hi)
  have hit3' : it p q kOut n3 ⟨some (clean0 p q), none, S2⟩ =
      some (haltList (tm p q kOut) ((g x).flatMap ic)) := hit3
  refine ⟨n3 + (l.length + 1) + 1 + t, ?_, ?_⟩
  · simp only [tb] at ht
    have : Official.nW q * (x.length + t + 1) ≤
        Official.nW q * (x.length + (x.length + 2) ^ K + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [hinit]
    refine (it_add p q kOut hit1 _).trans ?_
    rw [it_succ p q kOut hstepX, it_add p q kOut hit2, hit3']

open Pnp.CookLevin in
/-- Machine A as an official polynomial-time computation of `x ↦ (g x).flatMap ic`. -/
theorem computableA (c : Struct.Cmd) (kOut K : ℕ) (g : Str → List SatSym)
    (h : ∀ x : Str, ∃ σ', Struct.ExecLe c (init [x]).stk (.norm σ') (tb K x.length) ∧
      σ' kOut = ((g x).flatMap ic).reverse) :
    Nonempty (TM2ComputableInPolyTime (Millennium.fin_encoding_string Bool).encode
      (Millennium.fin_encoding_string Bool).encode (fun x => (g x).flatMap ic)) := by
  classical
  refine ⟨
    { tm := tm (Struct.toProg c) (pe (Struct.toProg c) kOut) kOut
      inputAlphabet := Equiv.refl Bool
      outputAlphabet := Equiv.refl Bool
      time := (X + 2) ^ K + 1 + (X + (X + 2) ^ K + 1) +
        C (Official.nW (pe (Struct.toProg c) kOut)) * (X + (X + 2) ^ K + 1)
      outputsFun := fun x => ?_ }⟩
  have hmain := mainA c kOut K g h x
  refine ⟨⟨Classical.choose hmain, ?_⟩, ?_⟩
  · change _ = some (haltList (tm (Struct.toProg c) (pe (Struct.toProg c) kOut) kOut) _)
    simp only [Millennium.fin_encoding_string_encode, Equiv.refl]
    erw [List.map_id, List.map_id]
    exact (Classical.choose_spec hmain).2
  · simp only [Millennium.fin_encoding_string_encode, eval_add, eval_pow, eval_X, eval_ofNat,
      eval_mul, eval_C, eval_one]
    exact (Classical.choose_spec hmain).1

end MachineA

/-! ## Machine B: decode bit pairs into `SatSym` -/

section MachineB

open Pnp.CookLevin Pnp.TM2Proj

/-- Decoding of one bit pair (inverse of `ic`). -/
def sym : Bool → Bool → SatSym
  | false, false => .sep
  | false, true => .zero
  | true, false => .pos
  | true, true => .neg

/-- Decoding of a bit string, two bits at a time (a trailing odd bit is dropped). -/
def dec2 : List Bool → List SatSym
  | a :: b :: r => sym a b :: dec2 r
  | _ => []

theorem dec2_flatMap_ic : ∀ l : List SatSym, dec2 (l.flatMap ic) = l
  | [] => rfl
  | s :: l => by
    cases s <;> simp [ic, dec2, sym, dec2_flatMap_ic l]

theorem length_dec2_le : ∀ w : List Bool, (dec2 w).length ≤ w.length
  | [] => le_refl _
  | [_] => Nat.zero_le _
  | a :: b :: r => by
    have := length_dec2_le r
    simp only [dec2, List.length_cons]; omega

/-- The three stacks of machine B. -/
inductive BS
  | inp
  | aux
  | out
  deriving DecidableEq, Fintype

/-- Stack alphabets of machine B. -/
abbrev BΓ : BS → Type
  | .inp => Bool
  | .aux => SatSym
  | .out => SatSym

/-- Stack contents of machine B from the three lists. -/
def bstk (a : List Bool) (b o : List SatSym) : ∀ k : BS, List (BΓ k)
  | .inp => a
  | .aux => b
  | .out => o

theorem bupdate_inp (a : List Bool) (b o : List SatSym) (l : List Bool) :
    Function.update (bstk a b o) BS.inp l = bstk l b o := by
  funext j; cases j <;> rfl

theorem bupdate_aux (a : List Bool) (b o : List SatSym) (l : List SatSym) :
    Function.update (bstk a b o) BS.aux l = bstk a l o := by
  funext j; cases j <;> rfl

theorem bupdate_out (a : List Bool) (b o : List SatSym) (l : List SatSym) :
    Function.update (bstk a b o) BS.out l = bstk a b l := by
  funext j; cases j <;> rfl

/-- Labels of machine B: read the first bit, read the second bit, output. -/
inductive BL
  | l0
  | l1
  | l2
  deriving DecidableEq, Fintype

/-- States of machine B: the first bit read, the decoded symbol. -/
abbrev Bσ := Option Bool × Option SatSym

/-- The program of machine B. -/
def bprog : BL → TM2.Stmt BΓ BL Bσ
  | .l0 =>
    .pop BS.inp (fun _ o => (o, none))
      (.branch (fun s => s.1.isSome) (.goto fun _ => .l1) (.goto fun _ => .l2))
  | .l1 =>
    .pop BS.inp (fun s o => (s.1, o.map (sym (s.1.getD false))))
      (.branch (fun s => s.2.isSome)
        (.push BS.aux (fun s => s.2.getD .sep) (.goto fun _ => .l0))
        (.goto fun _ => .l2))
  | .l2 =>
    .pop BS.aux (fun _ o => (none, o))
      (.branch (fun s => s.2.isSome)
        (.push BS.out (fun s => s.2.getD .sep) (.goto fun _ => .l2))
        .halt)

/-- The step function of machine B. -/
abbrev bstep : TM2.Cfg BΓ BL Bσ → Option (TM2.Cfg BΓ BL Bσ) := TM2.step bprog

/-- Phase 1: decode the input onto the scratch stack (reversed). -/
theorem bphase1 : ∀ (w : List Bool) (acc o : List SatSym) (s : Bσ), ∃ n s', n ≤ w.length + 1 ∧
    runF bstep n (some ⟨some .l0, s, bstk w acc o⟩) =
      some ⟨some .l2, s', bstk [] ((dec2 w).reverse ++ acc) o⟩
  | [], acc, o, s => by
    refine ⟨1, (none, none), le_refl _, ?_⟩
    rw [runF_succ]
    show runF bstep 0 (some (TM2.stepAux (bprog .l0) s (bstk [] acc o))) = _
    simp only [bprog, TM2.stepAux]
    rw [show bstk [] acc o BS.inp = [] from rfl, bupdate_inp]
    simp [runF, dec2]
  | [a], acc, o, s => by
    refine ⟨2, (some a, none), le_refl _, ?_⟩
    rw [runF_succ]
    show runF bstep 1 (some (TM2.stepAux (bprog .l0) s (bstk [a] acc o))) = _
    simp only [bprog, TM2.stepAux]
    rw [show bstk [a] acc o BS.inp = [a] from rfl, bupdate_inp]
    change runF bstep 1 (some ⟨some .l1, (some a, none), bstk [] acc o⟩) = _
    rw [runF_succ]
    show runF bstep 0 (some (TM2.stepAux (bprog .l1) (some a, none) (bstk [] acc o))) = _
    simp only [bprog, TM2.stepAux]
    rw [show bstk [] acc o BS.inp = [] from rfl, bupdate_inp]
    simp [runF, dec2]
  | a :: b :: r, acc, o, s => by
    obtain ⟨n, s', hn, hrun⟩ := bphase1 r (sym a b :: acc) o (some a, some (sym a b))
    refine ⟨n + 1 + 1, s', by simp; omega, ?_⟩
    rw [runF_succ]
    show runF bstep (n + 1) (some (TM2.stepAux (bprog .l0) s (bstk (a :: b :: r) acc o))) = _
    simp only [bprog, TM2.stepAux]
    rw [show bstk (a :: b :: r) acc o BS.inp = a :: b :: r from rfl, bupdate_inp]
    change runF bstep (n + 1) (some ⟨some .l1, (some a, none), bstk (b :: r) acc o⟩) = _
    rw [runF_succ]
    show runF bstep n (some (TM2.stepAux (bprog .l1) (some a, none) (bstk (b :: r) acc o))) = _
    simp only [bprog, TM2.stepAux]
    rw [show bstk (b :: r) acc o BS.inp = b :: r from rfl, bupdate_inp]
    change runF bstep n (some (TM2.stepAux (.push BS.aux (fun s : Bσ => s.2.getD .sep)
      (.goto fun _ => .l0)) (some a, some (sym a b)) (bstk r acc o))) = _
    simp only [TM2.stepAux]
    rw [show bstk r acc o BS.aux = acc from rfl, bupdate_aux]
    change runF bstep n (some ⟨some .l0, (some a, some (sym a b)), bstk r (sym a b :: acc) o⟩) = _
    rw [hrun]
    simp [dec2]

/-- Phase 2: pop the scratch stack onto the output stack, then halt. -/
theorem bphase2 : ∀ (u o : List SatSym) (s : Bσ),
    runF bstep (u.length + 1) (some ⟨some .l2, s, bstk [] u o⟩) =
      some ⟨none, (none, none), bstk [] [] (u.reverse ++ o)⟩
  | [], o, s => by
    rw [List.length_nil, runF_succ]
    show runF bstep 0 (some (TM2.stepAux (bprog .l2) s (bstk [] [] o))) = _
    simp only [bprog, TM2.stepAux]
    rw [show bstk [] [] o BS.aux = [] from rfl, bupdate_aux]
    simp [runF]
  | y :: u, o, s => by
    rw [List.length_cons, runF_succ]
    show runF bstep (u.length + 1) (some (TM2.stepAux (bprog .l2) s (bstk [] (y :: u) o))) = _
    simp only [bprog, TM2.stepAux]
    rw [show bstk [] (y :: u) o BS.aux = y :: u from rfl, bupdate_aux]
    change runF bstep (u.length + 1) (some (TM2.stepAux (.push BS.out
      (fun s : Bσ => s.2.getD .sep) (.goto fun _ => .l2)) (none, some y) (bstk [] u o))) = _
    simp only [TM2.stepAux]
    rw [show bstk [] u o BS.out = o from rfl, bupdate_out]
    change runF bstep (u.length + 1) (some ⟨some .l2, (none, some y), bstk [] u (y :: o)⟩) = _
    rw [bphase2 u (y :: o)]
    simp

/-- Machine B. -/
def btm : FinTM2 :=
  { K := BS
    k₀ := BS.inp
    k₁ := BS.out
    Γ := BΓ
    Λ := BL
    main := .l0
    σ := Bσ
    initialState := (none, none)
    Γk₀Fin := (inferInstance : Fintype Bool)
    m := bprog }

theorem bmain (w : List Bool) : ∃ n, n ≤ 2 * w.length + 2 ∧
    runF bstep n (some ⟨some .l0, (none, none), bstk w [] []⟩) =
      some ⟨none, (none, none), bstk [] [] (dec2 w)⟩ := by
  obtain ⟨n, s', hn, hrun⟩ := bphase1 w [] [] (none, none)
  refine ⟨((dec2 w).reverse.length + 1) + n, ?_, ?_⟩
  · have := length_dec2_le w
    simp only [List.length_reverse]; omega
  · rw [runF_add, hrun, List.append_nil, bphase2, List.reverse_reverse, List.append_nil]

/-- Machine B computes `dec2` in linear time. -/
noncomputable def computableB : TM2ComputableInPolyTime (Millennium.fin_encoding_string Bool).encode
    (Millennium.fin_encoding_string SatSym).encode dec2 :=
  { tm := btm
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl SatSym
    time := 2 * X + 2
    outputsFun := fun w => by
      have hinit : initList btm w = (⟨some .l0, (none, none), bstk w [] []⟩ :
          TM2.Cfg BΓ BL Bσ) := by
        show (⟨some .l0, (none, none), _⟩ : TM2.Cfg BΓ BL Bσ) = _
        congr 1
        funext k; cases k <;> rfl
      have hhalt : haltList btm (dec2 w) = (⟨none, (none, none), bstk [] [] (dec2 w)⟩ :
          TM2.Cfg BΓ BL Bσ) := by
        show (⟨none, (none, none), _⟩ : TM2.Cfg BΓ BL Bσ) = _
        congr 1
        funext k; cases k <;> rfl
      have hm := bmain w
      refine ⟨⟨Classical.choose hm, ?_⟩, ?_⟩
      · change runF bstep _ (some (initList btm (List.map id w))) =
          some (haltList btm (List.map id (dec2 w)))
        rw [List.map_id, List.map_id, hinit, hhalt]
        exact (Classical.choose_spec hm).2
      · simp only [Millennium.fin_encoding_string_encode, eval_add, eval_mul, eval_X,
          eval_ofNat]
        exact (Classical.choose_spec hm).1 }

end MachineB

/-! ## Main results -/

open Pnp.Relativize.Struct Pnp.CookLevin in
/-- **Structured programs computing functions are official polynomial-time computations.**
If `c` started with `x` on stack 0 terminates normally within `(|x|+2)^K` steps, leaving the
`ic` codes of the symbols of `g x` (pushed in order) on stack `kOut`, then `g` is in Mathlib's
`TM2ComputableInPolyTime`. -/
theorem computable_of_cmd (c : Cmd) (kOut K : ℕ) (g : Str → List SatSym)
    (h : ∀ x : Str, ∃ σ', ExecLe c (init [x]).stk (.norm σ') (tb K x.length) ∧
      σ' kOut = ((g x).flatMap ic).reverse) :
    Nonempty (Turing.TM2ComputableInPolyTime (Millennium.fin_encoding_string Bool).encode
      (Millennium.fin_encoding_string SatSym).encode g) := by
  obtain ⟨hA⟩ := computableA c kOut K g h
  have e : dec2 ∘ (fun x => (g x).flatMap ic) = g := funext fun x => dec2_flatMap_ic (g x)
  rw [← e]
  exact ⟨Pnp.TM2Comp.comp hA computableB⟩

open Pnp.Relativize.Struct Pnp.CookLevin in
/-- The same for inputs given by any finite encoding `e`, read through a bit code `cd`. -/
theorem computable_of_cmd_code {T : Type} (e : Computability.FinEncoding T) (cd : e.Γ → List Bool)
    (c : Cmd) (kOut K : ℕ) (g : Str → List SatSym)
    (h : ∀ x : Str, ∃ σ', ExecLe c (init [x]).stk (.norm σ') (tb K x.length) ∧
      σ' kOut = ((g x).flatMap ic).reverse)
    (F : T → List SatSym) (hF : ∀ t, F t = g ((e.encode t).flatMap cd)) :
    Nonempty (Turing.TM2ComputableInPolyTime e.encode
      (Millennium.fin_encoding_string SatSym).encode F) := by
  obtain ⟨hg⟩ := computable_of_cmd c kOut K g h
  have e' : g ∘ (fun t => (e.encode t).flatMap cd) = F := funext fun t => (hF t).symm
  rw [← e']
  exact ⟨Pnp.TM2Comp.comp (Pnp.TM2Hom.homComp e cd) hg⟩

end Pnp.CookLevin.FunBridge
