import Pnp.Oracle.Official
import Pnp.Oracle.Combinators
import Pnp.Oracle.Truncate

/-!
# `NP ∅` is contained in the official class `NP`

* `inNP_of_mem_NP_empty`: every language verified by one of our machines with the empty oracle
  (`Pnp.Relativize.NP ∅`) is in the official class `NP` of the Clay formalization
  (`Millennium.InNondeterministicPolynomialTime`, alphabet `Bool`).

The official definition asks for a checking relation `R x y`, decided by a Mathlib `FinTM2` in
polynomial time on the pair encoding `x#y`, with `x ∈ L ↔ ∃ y, |y| ≤ |x|^k' ∧ R x y`.  We take
`R x y` = "the verifier accepts `(x, y)` within `(|x|+2)^k` steps" for `|x| ≥ 2`, and hard-wire
the answers for the three inputs of length `≤ 1` (for them the official certificates have
length `≤ 1`).  The compiled machine

1. splits `x#y` into the verifier's stacks `0` and `1` (two passes over the input) and puts
   `|x|` marks on `k` counter stacks; it also records whether `|x| ≤ 1`;
2. runs the nested counting loops `Comb.pad k` (as our own program, on a separate group of
   stacks) to write a clock of exactly `(|x|+2)^k` marks;
3. runs the verifier, popping one clock mark before every instruction and rejecting when the
   clock is empty, so it halts within the time bound on *every* certificate;
4. empties all work stacks, as Mathlib's halting configuration requires.

Certificates longer than the time bound are handled by `runFor_take` (`Truncate.lean`).
-/

namespace Pnp.Relativize.OfficialNP

open Turing Turing.TM2 Polynomial Pnp.Relativize.Official

/-- Symbols of the pair encoding `x#y` over `Bool`: `inl b` (input), `inr none` (separator),
`inr (some b)` (certificate). -/
abbrev G := Bool ⊕ Option Bool

/-- The bit carried by a symbol (`false` for the separator). -/
def bitOf : G → Bool
  | .inl b => b
  | .inr (some b) => b
  | .inr none => false

/-- A bound on the stack indices used by a program. -/
def bnd (q : Prog) : ℕ := (q.map (fun i => stkIdx i + 1)).sum

theorem stkIdx_lt_bnd {q : Prog} {i : Instr} (h : i ∈ q) : stkIdx i < bnd q := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun i => stkIdx i + 1) h)
  simp only [bnd]; omega

/-- The data of the compiled machine: verifier `p`, exponent `k`, answers `sm` on the inputs
of length `≤ 1` (`sm none` for the empty input, `sm (some b)` for `[b]`). -/
structure Data where
  p : Prog
  k : ℕ
  sm : Option Bool → Bool

variable (D : Data)

/-- The clock program: nested counting loops writing `m^k` marks on its stack `1`. -/
def pr : Prog := Comb.pad D.k 0

/-- Number of verifier stacks. -/
def nW : ℕ := bnd D.p + 2

/-- Number of clock-program stacks. -/
def Wp : ℕ := bnd (pr D) + 2 * D.k + 2

/-- Offset of the clock-program stacks. -/
def oP : ℕ := nW D + 1

/-- Number of work stacks: verifier stacks, one buffer, clock-program stacks. -/
def nS : ℕ := nW D + 1 + Wp D

theorem nS_pos : 0 < nS D := by simp [nS]

/-- Stack indices: the output stack `inl ()` and the work stacks. -/
abbrev KK := Unit ⊕ Fin (nS D)

/-- Stack alphabets: `Bool` for the output stack, `G` for the work stacks. -/
abbrev Γ' (i : KK D) : Type := Sum.casesOn (motive := fun _ => Type) i (fun _ => Bool) (fun _ => G)

instance (i : KK D) : Fintype (Γ' D i) := by
  rcases i with _ | _ <;> dsimp [Γ'] <;> infer_instance

/-- Work stack number `i` (truncated). -/
abbrev wk (i : ℕ) : KK D := .inr ⟨min i (nS D - 1), by have := nS_pos D; omega⟩

/-- The output stack. -/
abbrev OUT : KK D := .inl ()

/-- The buffer stack used to split the input. -/
abbrev A : KK D := wk D (nW D)

/-- The clock (stack `1` of the clock program). -/
abbrev CLK : KK D := wk D (oP D + 1)

/-- Counter `j` of the clock program. -/
abbrev cntK (j : ℕ) : KK D := wk D (oP D + Comb.cnt j)

/-- What the first pass has seen of `x`: `some none` = nothing, `some (some b)` = exactly
`[b]`, `none` = at least two bits. -/
abbrev Small := Option (Option Bool)

/-- Labels: verifier instructions, clock-program instructions, cleanup of each work stack,
first pass (with the `Small` record), second pass (`false`) and counter completion (`true`). -/
abbrev Lab := (Fin (D.p.length + 1) ⊕ Fin ((pr D).length + 1)) ⊕ (Fin (nS D) ⊕ (Small ⊕ Bool))

def labP (n : ℕ) : Lab D := .inl (.inl ⟨min n D.p.length, by omega⟩)
def labQ (n : ℕ) : Lab D := .inl (.inr ⟨min n (pr D).length, by omega⟩)
def clean (j : Fin (nS D)) : Lab D := .inr (.inl j)
def clean0 : Lab D := clean D ⟨0, nS_pos D⟩
def P1 (s : Small) : Lab D := .inr (.inr (.inl s))
def P2 : Lab D := .inr (.inr (.inr false))
def BUMP : Lab D := .inr (.inr (.inr true))

/-- Statements of the compiled machine. -/
abbrev St := Stmt (Γ' D) (Lab D) (Option G)

/-- Write answer `b` on the output stack and start the cleanup. -/
def haltOut (b : Bool) : St D := .push (OUT D) (fun _ => b) (.goto fun _ => clean0 D)

/-- Translation of one instruction of a program whose stacks live at offset `o`; `h b` is
executed when the program halts with answer `b` (or jumps outside, `b = false`). -/
def instrG (o : ℕ) (lab : ℕ → Lab D) (h : Bool → St D) : Option Instr → St D
  | none => h false
  | some (.halt b) => h b
  | some (.push k b n) => .push (wk D (o + k)) (fun _ => (.inl b : G)) (.goto fun _ => lab n)
  | some (.pop k z f t) => .pop (wk D (o + k)) (fun _ g => g)
      (.goto fun v => match v with
        | none => lab z
        | some g => if bitOf g then lab t else lab f)
  | some (.query _ _ n) => .goto fun _ => lab n

/-- Push one mark on each of the first `j` counters. -/
def pushCnt : ℕ → St D → St D
  | 0, q => q
  | j + 1, q => .push (cntK D j) (fun _ => (.inl true : G)) (pushCnt j q)

/-- Record a symbol in the first pass. -/
def upd : Small → Option G → Small
  | some none, some (.inl b) => some (some b)
  | some (some _), some (.inl _) => none
  | s, _ => s

def isInl : Option G → Bool
  | some (.inl _) => true
  | _ => false

def isCert : Option G → Bool
  | some (.inr (some _)) => true
  | _ => false

def bitO : Option G → Bool
  | some g => bitOf g
  | none => false

/-- End of the first pass. -/
def end1 : Small → St D
  | none => .goto fun _ => P2 D
  | some o => .push (OUT D) (fun _ => D.sm o) (.goto fun _ => clean0 D)

/-- The compiled program. -/
def M : Lab D → St D
  | .inl (.inl i) => .pop (CLK D) (fun _ g => g)
      (.branch (fun v => v.isSome) (instrG D 0 (labP D) (haltOut D) D.p[i.val]?)
        (haltOut D false))
  | .inl (.inr i) => instrG D (oP D) (labQ D) (fun _ => .goto fun _ => labP D 0) (pr D)[i.val]?
  | .inr (.inl j) => .pop (.inr j) (fun _ g => g)
      (.branch (fun v => v.isSome) (.goto fun _ => clean D j)
        (if h : j.val + 1 < nS D then .goto fun _ => clean D ⟨j.val + 1, h⟩
         else .load (fun _ => none) .halt))
  | .inr (.inr (.inl s)) => .pop (wk D 0) (fun _ g => g)
      (.branch (fun v => v.isSome)
        (.push (A D) (fun v => v.getD (.inr none)) (.goto fun v => P1 D (upd s v)))
        (end1 D s))
  | .inr (.inr (.inr false)) => .pop (A D) (fun _ g => g)
      (.branch (fun v => v.isSome)
        (.branch isInl
          (.push (wk D 0) (fun v => (.inl (bitO v) : G)) (pushCnt D D.k (.goto fun _ => P2 D)))
          (.branch isCert (.push (wk D 1) (fun v => (.inl (bitO v) : G)) (.goto fun _ => P2 D))
            (.goto fun _ => P2 D)))
        (.goto fun _ => BUMP D))
  | .inr (.inr (.inr true)) => pushCnt D D.k (pushCnt D D.k (.goto fun _ => labQ D 0))

/-- The compiled `FinTM2`. -/
@[reducible] def tm : FinTM2 where
  K := KK D
  k₀ := wk D 0
  k₁ := OUT D
  Γ := Γ' D
  Λ := Lab D
  main := P1 D (some none)
  σ := Option G
  initialState := none
  m := M D

/-- Configurations. -/
abbrev Cf := Turing.TM2.Cfg (Γ' D) (Lab D) (Option G)

/-- Stack contents. -/
abbrev Stk := ∀ i : KK D, List (Γ' D i)

/-- `n` steps of the compiled machine. -/
def it (n : ℕ) (c : Cf D) : Option (Cf D) := (flip bind (TM2.step (M D)))^[n] (some c)

theorem it_zero (c : Cf D) : it D 0 c = some c := rfl

theorem it_succ {c c' : Cf D} (h : TM2.step (M D) c = some c') (n : ℕ) :
    it D (n + 1) c = it D n c' := by
  simp only [it, Function.iterate_succ_apply]
  simp [flip, h]

theorem it_add {c c' : Cf D} {a : ℕ} (h : it D a c = some c') (b : ℕ) :
    it D (b + a) c = it D b c' := by
  simp only [it] at h ⊢
  rw [Function.iterate_add_apply, h]

/-! ### Indices -/

theorem two_le_nW : 2 ≤ nW D := by simp [nW]

theorem wk_eq {i : ℕ} (hi : i < nS D) : wk D i = .inr ⟨i, hi⟩ := by
  simp only [wk, Sum.inr.injEq, Fin.mk.injEq]; omega

theorem wk_inj {i j : ℕ} (hi : i < nS D) (hj : j < nS D) : wk D i = wk D j ↔ i = j := by
  rw [wk_eq D hi, wk_eq D hj]; simp

theorem wk_ne {i j : ℕ} (hi : i < nS D) (hj : j < nS D) (h : i ≠ j) : wk D i ≠ wk D j :=
  fun e => h ((wk_inj D hi hj).1 e)

theorem wk_ne_OUT (i : ℕ) : wk D i ≠ OUT D := by simp [wk, OUT]

theorem OUT_ne_wk (i : ℕ) : OUT D ≠ wk D i := (wk_ne_OUT D i).symm

theorem nW_lt_nS : nW D < nS D := by simp [nS]; omega

theorem oP_add_lt {i : ℕ} (hi : i < Wp D) : oP D + i < nS D := by simp [oP, nS]; omega

theorem cnt_lt_Wp {j : ℕ} (hj : j < D.k) : Comb.cnt j < Wp D := by
  simp [Comb.cnt, Wp]; omega

theorem aux_lt_Wp {j : ℕ} (hj : j < D.k) : Comb.aux j < Wp D := by
  simp [Comb.aux, Wp]; omega

theorem one_lt_Wp : 1 < Wp D := by simp [Wp]

theorem pr_stk {i : Instr} (h : i ∈ pr D) : stkIdx i < Wp D := by
  have := stkIdx_lt_bnd h; simp [Wp]; omega

theorem p_stk {i : Instr} (h : i ∈ D.p) : stkIdx i < nW D := by
  have := stkIdx_lt_bnd h; simp [nW]; omega

/-! ### Simulating one instruction -/

/-- The work stacks `o, …, o+W-1` hold the stacks `0, …, W-1` of `c` (bits as `inl`). -/
def SimW (o W : ℕ) (c : Relativize.Cfg) (S : Stk D) : Prop :=
  ∀ i < W, S (wk D (o + i)) = (c.stk i).map Sum.inl

/-- `S'` agrees with `S` outside the window `o, …, o+W-1`. -/
def Fr (o W : ℕ) (S S' : Stk D) : Prop :=
  ∀ j : KK D, (∀ i < W, j ≠ wk D (o + i)) → S' j = S j

theorem Fr.refl (o W : ℕ) (S : Stk D) : Fr D o W S S := fun _ _ => rfl

theorem Fr.trans {o W : ℕ} {S S' S'' : Stk D} (h : Fr D o W S S') (h' : Fr D o W S' S'') :
    Fr D o W S S'' := fun j hj => (h' j hj).trans (h j hj)

theorem M_labP (n : ℕ) : M D (labP D n) = .pop (CLK D) (fun _ g => g)
    (.branch (fun v => v.isSome) (instrG D 0 (labP D) (haltOut D) D.p[n]?) (haltOut D false)) := by
  simp [M, labP, getElem?_min]

theorem M_labQ (n : ℕ) : M D (labQ D n) =
    instrG D (oP D) (labQ D) (fun _ => .goto fun _ => labP D 0) (pr D)[n]? := by
  simp [M, labQ, getElem?_min]

section Window

variable {o W : ℕ} (hoW : o + W ≤ nS D)
include hoW

theorem wk_win_iff {i k : ℕ} (hi : i < W) (hk : k < W) : wk D (o + i) = wk D (o + k) ↔ i = k := by
  rw [wk_inj D (by omega) (by omega)]; omega

theorem simW_update {c : Relativize.Cfg} {S : Stk D} (hs : SimW D o W c S) {k : ℕ} (hk : k < W)
    (l : Str) (pc : ℕ) :
    SimW D o W ⟨pc, Function.update c.stk k l⟩
      (Function.update S (wk D (o + k)) (l.map Sum.inl)) := by
  intro i hi
  by_cases h : i = k
  · subst h; simp
  · rw [Function.update_of_ne (fun h' => h ((wk_win_iff D hoW hi hk).1 h')), hs i hi]
    simp [Function.update_of_ne h]

omit hoW in
theorem fr_update (S : Stk D) {k : ℕ} (hk : k < W) (l : List G) :
    Fr D o W S (Function.update S (wk D (o + k)) l) := fun _ hj =>
  Function.update_of_ne (hj k hk) _ _

omit hoW in
theorem len_update_le' (S : Stk D) (kk : KK D) (l : List (Γ' D kk))
    (hl : l.length ≤ (S kk).length + 1) (j : KK D) :
    (Function.update S kk l j).length ≤ (S j).length + 1 := by
  by_cases h : j = kk
  · subst h; simpa using hl
  · rw [Function.update_of_ne h]; omega

theorem instrG_run (q : Prog) (hq : ∀ ins ∈ q, stkIdx ins < W) {c c2 : Relativize.Cfg}
    {S : Stk D} (hs : SimW D o W c S) (h : step ∅ q c = .run c2) (lab : ℕ → Lab D)
    (hh : Bool → St D) (v : Option G) :
    ∃ v2 S2, stepAux (instrG D o lab hh q[c.pc]?) v S = ⟨some (lab c2.pc), v2, S2⟩ ∧
      SimW D o W c2 S2 ∧ Fr D o W S S2 ∧ ∀ j, (S2 j).length ≤ (S j).length + 1 := by
  unfold step at h
  rcases hp : q[c.pc]? with _ | ins
  · simp [hp] at h
  have hk := hq ins (List.mem_of_getElem? hp)
  rw [hp] at h
  cases ins with
  | halt b => simp at h
  | push k b n =>
    simp only [State.run.injEq] at h
    subst h
    simp only [stkIdx] at hk
    refine ⟨v, Function.update S (wk D (o + k)) ((b :: c.stk k).map Sum.inl), ?_,
      simW_update D hoW hs hk _ n, fr_update D S hk _, len_update_le' D S _ _ ?_⟩
    · simp [instrG, stepAux, hs k hk]
    · simp [hs k hk]
  | query k y n =>
    simp only [Set.mem_empty_iff_false, if_false, State.run.injEq] at h
    subst h
    exact ⟨v, S, by simp [instrG, stepAux], hs, Fr.refl D o W S, fun j => by omega⟩
  | pop k z f t =>
    simp only [stkIdx] at hk
    have hSk := hs k hk
    rcases hck : c.stk k with _ | ⟨b, s⟩
    · simp only [hck, State.run.injEq] at h
      subst h
      rw [hck] at hSk
      refine ⟨none, S, ?_, hs, Fr.refl D o W S, fun j => by omega⟩
      simp only [instrG, stepAux, hSk, List.map_nil, List.head?_nil, List.tail_nil]
      rw [show Function.update S (wk D (o + k)) [] = S by
        rw [← Function.update_eq_self (wk D (o + k)) S, hSk]; simp]
    · simp only [hck, State.run.injEq] at h
      subst h
      rw [hck] at hSk
      refine ⟨some (.inl b), Function.update S (wk D (o + k)) (s.map Sum.inl), ?_,
        simW_update D hoW hs hk _ _, fr_update D S hk _, len_update_le' D S _ _ ?_⟩
      · simp only [instrG, stepAux, hSk, List.map_cons, List.head?_cons, List.tail_cons]
        cases b <;> rfl
      · rw [hSk]; simp; omega

omit hoW in
theorem instrG_done (q : Prog) {c : Relativize.Cfg} {b : Bool} (h : step ∅ q c = .done b)
    (lab : ℕ → Lab D) (hh : Bool → St D) : instrG D o lab hh q[c.pc]? = hh b := by
  unfold step at h
  rcases hp : q[c.pc]? with _ | ins
  · simp only [hp, State.done.injEq] at h; subst h; rfl
  rw [hp] at h
  cases ins with
  | halt b' => simp only [State.done.injEq] at h; subst h; rfl
  | push k b n => simp at h
  | query k y n => simp at h
  | pop k z f t => rcases hck : c.stk k with _ | ⟨a, s⟩ <;> simp [hck] at h

end Window

theorem hoQ : oP D + Wp D ≤ nS D := by simp [oP, nS]
theorem hoP : 0 + nW D ≤ nS D := by simp [nS]; omega

/-! ### Running the clock program -/

theorem runQ (t : ℕ) : ∀ (c c' : Relativize.Cfg) (S : Stk D) (v : Option G),
    SimW D (oP D) (Wp D) c S → runFor ∅ (pr D) t (.run c) = .run c' →
    ∃ v' S', it D t ⟨some (labQ D c.pc), v, S⟩ = some ⟨some (labQ D c'.pc), v', S'⟩ ∧
      SimW D (oP D) (Wp D) c' S' ∧ Fr D (oP D) (Wp D) S S' := by
  induction t with
  | zero =>
    intro c c' S v hs h
    simp only [runFor_zero, State.run.injEq] at h
    subst h
    exact ⟨v, S, rfl, hs, Fr.refl D _ _ S⟩
  | succ t ih =>
    intro c c' S v hs h
    rw [runFor_succ_run] at h
    rcases hst : step ∅ (pr D) c with c2 | b
    · rw [hst] at h
      obtain ⟨v2, S2, hstep, hs2, hfr, -⟩ := instrG_run D (hoQ D) (pr D) (fun _ h => pr_stk D h)
        hs hst (labQ D) (fun _ => .goto fun _ => labP D 0) v
      obtain ⟨v', S', hit, hs', hfr'⟩ := ih c2 c' S2 v2 hs2 h
      refine ⟨v', S', ?_, hs', hfr.trans D hfr'⟩
      rw [it_succ D (c' := ⟨some (labQ D c2.pc), v2, S2⟩) (by
        simp only [TM2.step, M_labQ, hstep]), hit]
    · rw [hst, runFor_done] at h; cases h

/-! ### Running the verifier against the clock -/

theorem CLK_notin_P (i : ℕ) (hi : i < nW D) : CLK D ≠ wk D (0 + i) := by
  rw [CLK, Ne, wk_inj D (oP_add_lt D (one_lt_Wp D)) (by have := nW_lt_nS D; omega)]
  simp [oP]; omega

/-- The answer of a state: `b` if halted with `b`, `false` if still running. -/
def accOf : State → Bool
  | .done b => b
  | .run _ => false

theorem accOf_eq_true {s : State} : accOf s = true ↔ s = .done true := by
  cases s with
  | run c => simp [accOf]
  | done b => cases b <;> simp [accOf]

theorem runP (r : ℕ) : ∀ (c : Relativize.Cfg) (S : Stk D) (v : Option G) (B : ℕ),
    SimW D 0 (nW D) c S → S (CLK D) = List.replicate r (.inl true) → S (OUT D) = [] →
    (∀ j, j ≠ OUT D → (S j).length ≤ B) →
    ∃ n ≤ r + 1, ∃ v' S', it D n ⟨some (labP D c.pc), v, S⟩ = some ⟨some (clean0 D), v', S'⟩ ∧
      S' (OUT D) = [accOf (runFor ∅ D.p r (.run c))] ∧
      ∀ j, j ≠ OUT D → (S' j).length ≤ B + n := by
  induction r with
  | zero =>
    intro c S v B hs hclk hout hB
    refine ⟨1, le_rfl, none, Function.update (Function.update S (CLK D) []) (OUT D) [false],
      ?_, ?_, fun j hj => ?_⟩
    · rw [it_succ D (c' := ⟨some (clean0 D), none, Function.update (Function.update S (CLK D) [])
        (OUT D) [false]⟩), it_zero]
      simp only [TM2.step, M_labP, stepAux, hclk, List.replicate_zero, List.head?_nil,
        Option.isSome_none, cond_false, haltOut, List.tail_nil]
      rw [Function.update_of_ne (OUT_ne_wk D _), hout]
    · simp; rfl
    · rw [Function.update_of_ne hj]
      by_cases h : j = CLK D
      · subst h; simp
      · rw [Function.update_of_ne h]; have := hB j hj; omega
  | succ r ih =>
    intro c S v B hs hclk hout hB
    set S1 := Function.update S (CLK D) (List.replicate r (.inl true)) with hS1
    have hs1 : SimW D 0 (nW D) c S1 := by
      intro i hi; rw [hS1, Function.update_of_ne ((CLK_notin_P D i hi).symm), hs i hi]
    have hout1 : S1 (OUT D) = [] := by rw [hS1, Function.update_of_ne (OUT_ne_wk D _), hout]
    have hB1 : ∀ j, j ≠ OUT D → (S1 j).length ≤ B := by
      intro j hj
      by_cases h : j = CLK D
      · subst h; have := hB _ hj; rw [hclk] at this; simp at this; simp [hS1]; omega
      · rw [hS1, Function.update_of_ne h]; exact hB j hj
    have htick : ∀ q₁ q₂ : St D, stepAux (.pop (CLK D) (fun _ g => g)
        (.branch (fun v => v.isSome) q₁ q₂)) v S = stepAux q₁ (some (.inl true)) S1 := by
      intro q₁ q₂
      simp only [stepAux, hclk, List.replicate_succ, List.head?_cons, Option.isSome_some,
        cond_true, List.tail_cons, hS1]
    rcases hst : step ∅ D.p c with c2 | b
    · obtain ⟨v2, S2, hstep, hs2, hfr, hlen⟩ := instrG_run D (hoP D) D.p (fun _ h => p_stk D h)
        hs1 hst (labP D) (haltOut D) (some (.inl true))
      have hclk2 : S2 (CLK D) = List.replicate r (.inl true) := by
        rw [hfr _ (fun i hi => CLK_notin_P D i hi), hS1]; simp
      have hout2 : S2 (OUT D) = [] := by
        rw [hfr _ (fun i _ => OUT_ne_wk D _), hout1]
      obtain ⟨n, hn, v', S', hit, hS'out, hlen'⟩ := ih c2 S2 v2 (B + 1) hs2 hclk2 hout2
        (fun j hj => by have := hB1 j hj; have := hlen j; omega)
      refine ⟨n + 1, by omega, v', S', ?_, ?_, fun j hj => ?_⟩
      · rw [it_succ D (c' := ⟨some (labP D c2.pc), v2, S2⟩) (by
          simp only [TM2.step, M_labP, htick, hstep]), hit]
      · rw [hS'out, runFor_succ_run, hst]
      · have := hlen' j hj; omega
    · refine ⟨1, by omega, some (.inl true), Function.update S1 (OUT D) [b], ?_, ?_,
        fun j hj => ?_⟩
      · rw [it_succ D (c' := ⟨some (clean0 D), some (.inl true), Function.update S1 (OUT D) [b]⟩)
          (by simp only [TM2.step, M_labP, htick, instrG_done D D.p hst, haltOut, stepAux,
            hout1]), it_zero]
      · simp [runFor_succ_run, hst, accOf]
      · rw [Function.update_of_ne hj]; have := hB1 j hj; omega

/-! ### Cleanup -/

theorem cleanup_inner (j : Fin (nS D)) : ∀ (l : List G) (S : Stk D)
    (v : Option G), S (.inr j) = l →
    ∃ v', it D l.length ⟨some (clean D j), v, S⟩ =
      some ⟨some (clean D j), v', Function.update S (.inr j) []⟩ := by
  intro l
  induction l with
  | nil =>
    intro S v hS
    refine ⟨v, ?_⟩
    rw [List.length_nil, it_zero, Function.update_eq_self_iff.2 hS.symm]
  | cons a l ih =>
    intro S v hS
    have hstep : TM2.step (M D) ⟨some (clean D j), v, S⟩ =
        some ⟨some (clean D j), some a, Function.update S (.inr j) l⟩ := by
      simp only [TM2.step, clean, M, stepAux, hS, List.head?_cons, Option.isSome_some,
        cond_true, List.tail_cons]
    obtain ⟨v', hit⟩ := ih (Function.update S (.inr j) l) (some a) (by simp)
    refine ⟨v', ?_⟩
    rw [List.length_cons, it_succ D hstep, hit, Function.update_idem]

theorem haltList_eq (b : Bool) (S : Stk D) (hout : S (OUT D) = [b])
    (hw : ∀ j : Fin (nS D), S (.inr j) = []) :
    (⟨none, none, S⟩ : Cf D) = haltList (tm D) [b] := by
  unfold haltList
  congr 1
  funext i
  rcases i with ⟨⟩ | j
  · exact hout
  · exact hw j

theorem cleanup (b : Bool) (B : ℕ) : ∀ (d : ℕ) (j : Fin (nS D)), nS D - j.val = d →
    ∀ (S : Stk D) (v : Option G),
    (∀ i, i ≠ OUT D → (S i).length ≤ B) → S (OUT D) = [b] →
    (∀ i : Fin (nS D), i.val < j.val → S (.inr i) = []) →
    ∃ n ≤ d * (B + 1), it D n ⟨some (clean D j), v, S⟩ = some (haltList (tm D) [b]) := by
  intro d
  induction d with
  | zero => intro j hj; have := j.isLt; omega
  | succ d ih =>
    intro j hj S v hB hout hlow
    obtain ⟨v1, hit1⟩ := cleanup_inner D j (S (.inr j)) S v rfl
    have hl : (S (.inr j)).length ≤ B := hB _ (by simp [OUT])
    set S1 := Function.update S (Sum.inr j : KK D) [] with hS1
    have hS1j : S1 (.inr j) = [] := by simp [S1]
    have hS1o : S1 (OUT D) = [b] := by
      rw [hS1, Function.update_of_ne (by simp [OUT]), hout]
    have hlow1 : ∀ i : Fin (nS D), i.val < j.val + 1 → S1 (.inr i) = [] := by
      intro i hi
      by_cases h : i = j
      · rw [h, hS1j]
      · rw [hS1, Function.update_of_ne (by simpa using h)]
        apply hlow
        have : i.val ≠ j.val := fun h' => h (Fin.ext h')
        omega
    have hupd : Function.update S1 (Sum.inr j : KK D) [] = S1 := by
      rw [← hS1j, Function.update_eq_self]
    by_cases hnext : j.val + 1 < nS D
    · have hstep : TM2.step (M D) ⟨some (clean D j), v1, S1⟩ =
          some ⟨some (clean D ⟨j.val + 1, hnext⟩), none, S1⟩ := by
        simp only [TM2.step, clean, M, stepAux, hS1j, List.head?_nil, Option.isSome_none,
          cond_false, hnext, dite_true, List.tail_nil, hupd]
      obtain ⟨n, hn, hit⟩ := ih ⟨j.val + 1, hnext⟩ (by simp; omega) S1 none
        (fun i hi => by
          by_cases h : i = .inr j
          · subst h; rw [hS1j]; simp
          · rw [hS1, Function.update_of_ne h]; exact hB i hi) hS1o hlow1
      refine ⟨n + 1 + (S (.inr j)).length, ?_, ?_⟩
      · have : (d + 1) * (B + 1) = d * (B + 1) + B + 1 := by ring
        omega
      · rw [it_add D hit1, it_succ D hstep, hit]
    · have hstep : TM2.step (M D) ⟨some (clean D j), v1, S1⟩ = some (haltList (tm D) [b]) := by
        rw [← haltList_eq D b S1 hS1o (fun i => hlow1 i (by have := i.isLt; omega))]
        simp only [TM2.step, clean, M, stepAux, hS1j, List.head?_nil, Option.isSome_none,
          cond_false, hnext, dite_false, List.tail_nil, hupd]
        rfl
      refine ⟨1 + (S (.inr j)).length, ?_, ?_⟩
      · have : (d + 1) * (B + 1) = d * (B + 1) + B + 1 := by ring
        omega
      · rw [it_add D hit1, it_succ D hstep, it_zero]
        rfl

/-! ### Counters -/

/-- The effect of `pushCnt n` on the stacks. -/
def addCnt : ℕ → Stk D → Stk D
  | 0, S => S
  | n + 1, S => addCnt n (Function.update S (cntK D n) (.inl true :: S (cntK D n)))

theorem stepAux_pushCnt (n : ℕ) (q : St D) (v : Option G) (S : Stk D) :
    stepAux (pushCnt D n q) v S = stepAux q v (addCnt D n S) := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih => simp only [pushCnt, stepAux, ih, addCnt]

theorem cntK_inj {i j : ℕ} (hi : i < D.k) (hj : j < D.k) : cntK D i = cntK D j ↔ i = j := by
  rw [cntK, cntK, wk_inj D (oP_add_lt D (cnt_lt_Wp D hi)) (oP_add_lt D (cnt_lt_Wp D hj))]
  simp [Comb.cnt]

theorem addCnt_other' {n : ℕ} (hn : n ≤ D.k) : ∀ (S : Stk D) {i : KK D},
    (∀ j < n, i ≠ cntK D j) → addCnt D n S i = S i := by
  induction n with
  | zero => intro S i _; rfl
  | succ n ih =>
    intro S i hi
    simp only [addCnt]
    rw [ih (by omega) _ (fun j hj => hi j (by omega)), Function.update_of_ne (hi n (by omega))]

theorem addCnt_cnt {n : ℕ} (hn : n ≤ D.k) : ∀ (S : Stk D) {j : ℕ}, j < n →
    addCnt D n S (cntK D j) = .inl true :: S (cntK D j) := by
  induction n with
  | zero => intro S j hj; omega
  | succ n ih =>
    intro S j hj
    simp only [addCnt]
    rcases Nat.lt_or_ge j n with h | h
    · rw [ih (by omega) _ h, Function.update_of_ne ((cntK_inj D (by omega) (by omega)).not.2
        (by omega))]
    · have hjn : j = n := by omega
      subst hjn
      rw [addCnt_other' D (by omega) _ (fun i hi => (cntK_inj D (by omega) (by omega)).not.2
        (by omega))]
      simp

/-! ### First pass: move the input to the buffer, recording `|x| ≤ 1` -/

theorem A_ne_wk0 : A D ≠ wk D 0 := by
  rw [A, Ne, wk_inj D (nW_lt_nS D) (nS_pos D)]; have := two_le_nW D; omega

theorem pass1 (l : List G) : ∀ (s : Small) (S : Stk D) (v : Option G), S (wk D 0) = l →
    ∃ v', it D l.length ⟨some (P1 D s), v, S⟩ = some ⟨some (P1 D (l.foldl
      (fun s g => upd s (some g)) s)), v', Function.update (Function.update S (wk D 0) [])
        (A D) (l.reverse ++ S (A D))⟩ := by
  induction l with
  | nil =>
    intro s S v hS
    refine ⟨v, ?_⟩
    rw [List.length_nil, it_zero, List.reverse_nil, List.nil_append,
      show Function.update S (wk D 0) [] = S from Function.update_eq_self_iff.2 hS.symm,
      Function.update_eq_self]
    rfl
  | cons g l ih =>
    intro s S v hS
    set S2 := Function.update (Function.update S (wk D 0) l) (A D) (g :: S (A D)) with hS2
    have hstep : TM2.step (M D) ⟨some (P1 D s), v, S⟩ =
        some ⟨some (P1 D (upd s (some g))), some g, S2⟩ := by
      simp only [TM2.step, P1, M, stepAux, hS, List.head?_cons, Option.isSome_some, cond_true,
        List.tail_cons, Option.getD_some, hS2, Function.update_of_ne (A_ne_wk0 D)]
    obtain ⟨v', hit⟩ := ih (upd s (some g)) S2 (some g) (by
      rw [hS2, Function.update_of_ne (A_ne_wk0 D).symm]; simp)
    refine ⟨v', ?_⟩
    rw [List.length_cons, it_succ D hstep, hit, List.foldl_cons]
    congr 2
    funext j
    by_cases hA : j = A D
    · subst hA
      simp [hS2]
    · rw [Function.update_of_ne hA, Function.update_of_ne hA]
      by_cases h0 : j = wk D 0
      · subst h0; simp
      · rw [Function.update_of_ne h0, Function.update_of_ne h0, hS2, Function.update_of_ne hA,
          Function.update_of_ne h0]

theorem end1_step (s : Small) (S : Stk D) (v : Option G) (hS : S (wk D 0) = []) :
    TM2.step (M D) ⟨some (P1 D s), v, S⟩ = some (stepAux (end1 D s) none S) := by
  simp only [TM2.step, P1, M, stepAux, hS, List.head?_nil, Option.isSome_none, cond_false,
    List.tail_nil]
  rw [Function.update_eq_self_iff.2 hS.symm]

/-! ### Second pass: split the buffer into `x` (stack `0`) and `y` (stack `1`) -/

/-- Input bits of a list of symbols. -/
def xsOf (l : List G) : List Bool := l.filterMap fun g => match g with
  | .inl b => some b
  | .inr _ => none

/-- Certificate bits of a list of symbols. -/
def ysOf (l : List G) : List Bool := l.filterMap fun g => match g with
  | .inr (some b) => some b
  | _ => none

theorem wk1_ne_wk0 : wk D 1 ≠ wk D 0 := by
  rw [Ne, wk_inj D (by have := nW_lt_nS D; have := two_le_nW D; omega) (nS_pos D)]; omega

theorem A_ne_wk1 : A D ≠ wk D 1 := by
  rw [A, Ne, wk_inj D (nW_lt_nS D) (by have := nW_lt_nS D; have := two_le_nW D; omega)]
  have := two_le_nW D; omega

theorem cntK_ne_wk {j i : ℕ} (hj : j < D.k) (hi : i ≤ nW D) : cntK D j ≠ wk D i := by
  rw [cntK, Ne, wk_inj D (oP_add_lt D (cnt_lt_Wp D hj)) (by have := nW_lt_nS D; omega)]
  simp [oP]; omega

/-- The stacks touched by the second pass. -/
def Touched2 (i : KK D) : Prop := i = A D ∨ i = wk D 0 ∨ i = wk D 1 ∨ ∃ j < D.k, i = cntK D j

theorem pass2 (l : List G) : ∀ (S : Stk D) (v : Option G), S (A D) = l →
    ∃ v' S', it D l.length ⟨some (P2 D), v, S⟩ = some ⟨some (P2 D), v', S'⟩ ∧
      S' (A D) = [] ∧ S' (wk D 0) = (xsOf l).reverse.map Sum.inl ++ S (wk D 0) ∧
      S' (wk D 1) = (ysOf l).reverse.map Sum.inl ++ S (wk D 1) ∧
      (∀ j < D.k, S' (cntK D j) = List.replicate (xsOf l).length (.inl true) ++ S (cntK D j)) ∧
      (∀ i, ¬ Touched2 D i → S' i = S i) := by
  induction l with
  | nil =>
    intro S v hS
    exact ⟨v, S, rfl, hS, by simp [xsOf], by simp [ysOf], fun j _ => by simp [xsOf],
      fun _ _ => rfl⟩
  | cons g l ih =>
    intro S v hS
    set S1 := Function.update S (A D) l with hS1
    have hS1A : S1 (A D) = l := by simp [S1]
    have h1 : ∀ i, i ≠ A D → S1 i = S i := fun i h => by rw [hS1, Function.update_of_ne h]
    rcases g with b | (_ | b)
    · -- an input bit: push it on stack 0 and count it
      set S2 := addCnt D D.k (Function.update S1 (wk D 0) (.inl b :: S1 (wk D 0))) with hS2
      have hstep : TM2.step (M D) ⟨some (P2 D), v, S⟩ = some ⟨some (P2 D), some (.inl b), S2⟩ := by
        simp only [TM2.step, P2, M, stepAux, hS, List.head?_cons, Option.isSome_some,
          cond_true, isInl, List.tail_cons, stepAux_pushCnt, hS2, hS1, bitO, bitOf]
      have nc : ∀ i : ℕ, i ≤ nW D → ∀ j < D.k, wk D i ≠ cntK D j :=
        fun i hi j hj => (cntK_ne_wk D hj hi).symm
      have hS2A : S2 (A D) = l := by
        rw [hS2, addCnt_other' D le_rfl _ (fun j hj => nc _ le_rfl j hj),
          Function.update_of_ne (A_ne_wk0 D), hS1A]
      obtain ⟨v', S', hit, hA', h0', h1', hc', hfr'⟩ := ih S2 (some (.inl b)) hS2A
      refine ⟨v', S', by rw [List.length_cons, it_succ D hstep, hit], hA', ?_, ?_, ?_, ?_⟩
      · rw [h0', hS2, addCnt_other' D le_rfl _ (fun j hj => nc 0 (by omega) j hj)]
        simp [xsOf, h1 _ (A_ne_wk0 D).symm]
      · rw [h1', hS2, addCnt_other' D le_rfl _ (fun j hj => nc 1 (by have := two_le_nW D; omega)
          j hj), Function.update_of_ne (wk1_ne_wk0 D), h1 _ (A_ne_wk1 D).symm]
        simp [ysOf]
      · intro j hj
        rw [hc' j hj, hS2, addCnt_cnt D le_rfl _ hj,
          Function.update_of_ne (cntK_ne_wk D hj (by omega)),
          h1 _ (cntK_ne_wk D hj le_rfl)]
        simp [xsOf, List.replicate_succ']
      · intro i hi
        have hT : ¬ Touched2 D i := hi
        simp only [Touched2, not_or, not_exists, not_and] at hT
        rw [hfr' i hi, hS2, addCnt_other' D le_rfl _ (fun j hj => hT.2.2.2 j hj),
          Function.update_of_ne hT.2.1, h1 _ hT.1]
    · -- the separator: skip it
      have hstep : TM2.step (M D) ⟨some (P2 D), v, S⟩ = some ⟨some (P2 D), some (.inr none), S1⟩ := by
        simp only [TM2.step, P2, M, stepAux, hS, List.head?_cons, Option.isSome_some,
          cond_true, isInl, isCert, cond_false, List.tail_cons, hS1]
      obtain ⟨v', S', hit, hA', h0', h1', hc', hfr'⟩ := ih S1 (some (.inr none)) hS1A
      refine ⟨v', S', by rw [List.length_cons, it_succ D hstep, hit], hA', ?_, ?_, ?_, ?_⟩
      · rw [h0', h1 _ (A_ne_wk0 D).symm]; simp [xsOf]
      · rw [h1', h1 _ (A_ne_wk1 D).symm]; simp [ysOf]
      · intro j hj
        rw [hc' j hj, h1 _ (cntK_ne_wk D hj le_rfl)]; simp [xsOf]
      · intro i hi
        rw [hfr' i hi, h1 i (fun h => hi (Or.inl h))]
    · -- a certificate bit: push it on stack 1
      set S2 := Function.update S1 (wk D 1) (.inl b :: S1 (wk D 1)) with hS2
      have hstep : TM2.step (M D) ⟨some (P2 D), v, S⟩ =
          some ⟨some (P2 D), some (.inr (some b)), S2⟩ := by
        simp only [TM2.step, P2, M, stepAux, hS, List.head?_cons, Option.isSome_some,
          cond_true, isInl, isCert, cond_false, List.tail_cons, hS2, hS1, bitO, bitOf]
      have hS2A : S2 (A D) = l := by rw [hS2, Function.update_of_ne (A_ne_wk1 D), hS1A]
      obtain ⟨v', S', hit, hA', h0', h1', hc', hfr'⟩ := ih S2 (some (.inr (some b))) hS2A
      refine ⟨v', S', by rw [List.length_cons, it_succ D hstep, hit], hA', ?_, ?_, ?_, ?_⟩
      · rw [h0', hS2, Function.update_of_ne (wk1_ne_wk0 D).symm, h1 _ (A_ne_wk0 D).symm]
        simp [xsOf]
      · rw [h1', hS2, h1 _ (A_ne_wk1 D).symm]; simp [ysOf]
      · intro j hj
        rw [hc' j hj, hS2, Function.update_of_ne (cntK_ne_wk D hj (by
          have := two_le_nW D; omega)), h1 _ (cntK_ne_wk D hj le_rfl)]
        simp [xsOf]
      · intro i hi
        have hT : ¬ Touched2 D i := hi
        simp only [Touched2, not_or, not_exists, not_and] at hT
        rw [hfr' i hi, hS2, Function.update_of_ne hT.2.2.1, h1 _ hT.1]

theorem end2_step (S : Stk D) (v : Option G) (hS : S (A D) = []) :
    TM2.step (M D) ⟨some (P2 D), v, S⟩ = some ⟨some (BUMP D), none, S⟩ := by
  simp only [TM2.step, P2, M, stepAux, hS, List.head?_nil, Option.isSome_none, cond_false,
    List.tail_nil]
  rw [Function.update_eq_self_iff.2 hS.symm]

theorem bump_step (S : Stk D) (v : Option G) :
    TM2.step (M D) ⟨some (BUMP D), v, S⟩ =
      some ⟨some (labQ D 0), v, addCnt D D.k (addCnt D D.k S)⟩ := by
  simp only [TM2.step, BUMP, M, stepAux_pushCnt, stepAux]

/-! ### The whole run -/

theorem it_trans {c c' c'' : Cf D} {a b : ℕ} (h : it D a c = some c') (h' : it D b c' = some c'') :
    it D (b + a) c = some c'' := by rw [it_add D h, h']

theorem it_one {c c' : Cf D} (h : TM2.step (M D) c = some c') : it D 1 c = some c' := by
  rw [it_succ D h, it_zero]

/-- The pair encoding `x#y`. -/
def inp (x y : Str) : List G := x.map .inl ++ .inr none :: y.map (fun b => .inr (some b))

/-- The record of the first pass. -/
def cls : Str → Small
  | [] => some none
  | [b] => some (some b)
  | _ => none

theorem foldl_upd_inr (y : Str) : ∀ s : Small,
    (y.map (fun b => (Sum.inr (some b) : G))).foldl (fun s g => upd s (some g)) s = s := by
  induction y with
  | nil => intro s; rfl
  | cons b y ih =>
    intro s
    rw [List.map_cons, List.foldl_cons, show upd s (some (.inr (some b))) = s by
      rcases s with _ | _ | _ <;> rfl, ih]

theorem foldl_upd_none (l : List G) : l.foldl (fun s g => upd s (some g)) none = none := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [List.foldl_cons, show upd none (some g) = none by rfl, ih]

theorem foldl_inp (x y : Str) :
    (inp x y).foldl (fun s g => upd s (some g)) (some none) = cls x := by
  have hsep : ∀ s : Small, upd s (some (.inr none)) = s := by
    intro s; rcases s with _ | _ | _ <;> rfl
  unfold inp
  rw [List.foldl_append, List.foldl_cons, hsep, foldl_upd_inr]
  rcases x with _ | ⟨b, _ | ⟨b', x⟩⟩
  · rfl
  · rfl
  · simp only [List.map_cons, List.foldl_cons]
    rw [show upd (some none) (some (.inl b)) = some (some b) by rfl,
      show upd (some (some b)) (some (.inl b')) = none by rfl, foldl_upd_none]
    rfl

theorem xsOf_inp_reverse (x y : Str) : xsOf (inp x y).reverse = x.reverse := by
  simp [xsOf, inp, List.filterMap_reverse, List.filterMap_append, List.filterMap_map]

theorem ysOf_inp_reverse (x y : Str) : ysOf (inp x y).reverse = y.reverse := by
  simp [ysOf, inp, List.filterMap_reverse, List.filterMap_append, List.filterMap_map]

theorem length_inp (x y : Str) : (inp x y).length = x.length + 1 + y.length := by
  simp [inp]; omega

theorem initList_w0 (l : List G) : (initList (tm D) l).stk (wk D 0) = l := by
  simp [initList, tm]

theorem initList_ne (l : List G) {i : KK D} (h : i ≠ wk D 0) : (initList (tm D) l).stk i = [] := by
  simp [initList, tm, h]

/-- The initial stacks of the clock program: `m` marks on each counter. -/
def σ0 (m : ℕ) : ℕ → Str := fun i =>
  if 2 ≤ i ∧ i % 2 = 0 ∧ i < 2 * D.k + 2 then List.replicate m true else []

theorem full_σ0 (m : ℕ) : Comb.Full D.k m (σ0 D m) := by
  intro j hj
  constructor
  · simp [σ0, Comb.cnt]; omega
  · simp only [σ0, Comb.aux]; rw [if_neg (by omega)]

theorem M_exitQ (v : Option G) (S : Stk D) :
    TM2.step (M D) ⟨some (labQ D (0 + (4 * D.k + 1))), v, S⟩ = some ⟨some (labP D 0), v, S⟩ := by
  have : (pr D)[0 + (4 * D.k + 1)]? = none := by
    rw [List.getElem?_eq_none]; simp [pr]
  simp only [TM2.step, M_labQ, this, instrG, stepAux]

/-- The short input coded by `sm`'s argument. -/
def strOf : Option Bool → Str
  | none => []
  | some b => [b]

/-- The argument of `sm` for a short input. -/
def sOf : Str → Option Bool
  | [b] => some b
  | _ => none

theorem strOf_sOf {x : Str} (hx : x.length ≤ 1) : strOf (sOf x) = x := by
  rcases x with _ | ⟨b, _ | ⟨b', x⟩⟩
  · rfl
  · rfl
  · simp at hx

theorem cls_of_le {x : Str} (hx : x.length ≤ 1) : cls x = some (sOf x) := by
  rcases x with _ | ⟨b, _ | ⟨b', x⟩⟩
  · rfl
  · rfl
  · simp at hx

theorem cls_of_gt {x : Str} (hx : ¬ x.length ≤ 1) : cls x = none := by
  rcases x with _ | ⟨b, _ | ⟨b', x⟩⟩
  · simp at hx
  · simp at hx
  · rfl

/-- The answer computed by the compiled machine on `x#y`. -/
noncomputable def out (x y : Str) : Bool :=
  if x.length ≤ 1 then D.sm (sOf x)
  else accOf (runFor ∅ D.p ((x.length + 2) ^ D.k) (.run (init [x, y])))

theorem main_run (x y : Str) :
    ∃ n ≤ 2 * (inp x y).length + 5 + Comb.Tpad (x.length + 2) D.k + (x.length + 2) ^ D.k +
      nS D * ((inp x y).length + 2 * (x.length + 2) ^ D.k + 4),
      it D n (initList (tm D) (inp x y)) = some (haltList (tm D) [out D x y]) := by
  set N := (inp x y).length with hN
  set S0 : Stk D := (initList (tm D) (inp x y)).stk with hS0def
  have hc0 : (initList (tm D) (inp x y) : Cf D) = ⟨some (P1 D (some none)), none, S0⟩ := rfl
  have hS0w : S0 (wk D 0) = inp x y := initList_w0 D _
  have hS0n : ∀ i, i ≠ wk D 0 → S0 i = [] := fun i h => initList_ne D _ h
  obtain ⟨v1, h1⟩ := pass1 D (inp x y) (some none) S0 none hS0w
  rw [foldl_inp, ← hN] at h1
  set S1 : Stk D := Function.update (Function.update S0 (wk D 0) []) (A D)
    ((inp x y).reverse ++ S0 (A D)) with hS1
  have hS1w : S1 (wk D 0) = [] := by
    rw [hS1, Function.update_of_ne (A_ne_wk0 D).symm]; simp
  have hS1A : S1 (A D) = (inp x y).reverse := by
    rw [hS1, hS0n _ (A_ne_wk0 D)]; simp
  have hS1n : ∀ i, i ≠ wk D 0 → i ≠ A D → S1 i = [] := by
    intro i h0 hA
    rw [hS1, Function.update_of_ne hA, Function.update_of_ne h0, hS0n i h0]
  have h2 := end1_step D (cls x) S1 v1 hS1w
  show ∃ n ≤ _, it D n ⟨some (P1 D (some none)), none, S0⟩ = _
  by_cases hx : x.length ≤ 1
  · -- short input: hard-wired answer
    rw [cls_of_le hx] at h1 h2
    set S2 := Function.update S1 (OUT D) [D.sm (sOf x)] with hS2
    have hstep : TM2.step (M D) ⟨some (P1 D (some (sOf x))), v1, S1⟩ =
        some ⟨some (clean0 D), none, S2⟩ := by
      rw [h2]
      simp only [end1, stepAux, hS2, hS1n _ (OUT_ne_wk D 0) (OUT_ne_wk D _)]
    obtain ⟨nc, hnc, hc⟩ := cleanup D (D.sm (sOf x)) N (nS D) ⟨0, nS_pos D⟩ (by simp) S2 none
      (fun i hi => by
        rw [hS2, Function.update_of_ne hi]
        by_cases hA : i = A D
        · rw [hA, hS1A]; simp [hN]
        · by_cases h0 : i = wk D 0
          · rw [h0, hS1w]; simp
          · rw [hS1n i h0 hA]; simp)
      (by simp [hS2]) (fun i hi => by simp at hi)
    refine ⟨nc + (1 + N), ?_, ?_⟩
    · have : nS D * (N + 1) ≤ nS D * (N + 2 * (x.length + 2) ^ D.k + 4) :=
        Nat.mul_le_mul_left _ (by omega)
      have : nc ≤ nS D * (N + 1) := hnc
      omega
    · rw [it_trans D (it_trans D h1 (it_one D hstep)) hc]
      exact congrArg (fun b => some (haltList (tm D) [b])) (if_pos hx).symm
  · -- long input: split, build the clock, run the verifier
    rw [cls_of_gt hx] at h1 h2
    have hstep2 : TM2.step (M D) ⟨some (P1 D none), v1, S1⟩ = some ⟨some (P2 D), none, S1⟩ := by
      rw [h2]; rfl
    obtain ⟨v2, S2, h3, hS2A, hS2w0, hS2w1, hS2c, hS2fr⟩ := pass2 D _ S1 none hS1A
    rw [xsOf_inp_reverse, List.reverse_reverse, hS1w, List.append_nil] at hS2w0
    rw [ysOf_inp_reverse, List.reverse_reverse, hS1n _ (wk1_ne_wk0 D) (A_ne_wk1 D).symm,
      List.append_nil] at hS2w1
    have h4 := end2_step D S2 v2 hS2A
    have h5 := bump_step D S2 none
    set S3 := addCnt D D.k (addCnt D D.k S2) with hS3
    set m := x.length + 2 with hm
    have hS3c : ∀ j < D.k, S3 (cntK D j) = List.replicate m (.inl true) := by
      intro j hj
      rw [hS3, addCnt_cnt D le_rfl _ hj, addCnt_cnt D le_rfl _ hj, hS2c j hj,
        hS1n _ (cntK_ne_wk D hj (by omega)) (cntK_ne_wk D hj le_rfl)]
      simp [xsOf_inp_reverse, hm, List.replicate_succ]
    have hS3o : ∀ i, ¬ Touched2 D i → S3 i = S1 i := by
      intro i hi
      have hT : ¬ Touched2 D i := hi
      simp only [Touched2, not_or, not_exists, not_and] at hT
      rw [hS3, addCnt_other' D le_rfl _ hT.2.2.2, addCnt_other' D le_rfl _ hT.2.2.2, hS2fr i hi]
    -- the clock program
    have hsimQ : SimW D (oP D) (Wp D) ⟨0, σ0 D m⟩ S3 := by
      intro i hi
      simp only [σ0]
      split_ifs with hc
      · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j + 2 := ⟨(i - 2) / 2, by omega⟩
        have hj : j < D.k := by omega
        show S3 (cntK D j) = _
        rw [hS3c j hj]
        simp
      · have hT : ¬ Touched2 D (wk D (oP D + i)) := by
          simp only [Touched2, not_or, not_exists, not_and]
          have hlt := oP_add_lt D hi
          refine ⟨?_, ?_, ?_, fun j hj h => ?_⟩
          · exact wk_ne D hlt (nW_lt_nS D) (by simp [oP]; omega)
          · exact wk_ne D hlt (nS_pos D) (by simp [oP])
          · exact wk_ne D hlt (by have := nW_lt_nS D; have := two_le_nW D; omega)
              (by simp [oP]; have := two_le_nW D; omega)
          · rw [wk_inj D hlt (oP_add_lt D (cnt_lt_Wp D hj))] at h
            simp [Comb.cnt] at h; omega
        rw [hS3o _ hT, hS1n]
        · simp
        · exact wk_ne D (oP_add_lt D hi) (nS_pos D) (by simp [oP])
        · exact wk_ne D (oP_add_lt D hi) (nW_lt_nS D) (by simp [oP]; omega)
    have hpad := Comb.reach_pad (O := ∅) (p := pr D) m D.k 0 (σ0 D m) (Comb.codeAt_self _)
      (full_σ0 D m)
    obtain ⟨v4, S4, h6, hsim4, hfr4⟩ := runQ D _ ⟨0, σ0 D m⟩ _ S3 none hsimQ hpad
    have h7 := M_exitQ D v4 S4
    -- the verifier
    set T := m ^ D.k with hT
    have hP : ∀ i < nW D, S4 (wk D i) = S3 (wk D i) := by
      intro i hi
      refine hfr4 _ (fun i' hi' => ?_)
      rw [Ne, wk_inj D (by have := nW_lt_nS D; omega) (oP_add_lt D hi')]; simp [oP]; omega
    have hS3c' : ∀ i, (∀ j < D.k, i ≠ cntK D j) → S3 i = S2 i := by
      intro i hi
      rw [hS3, addCnt_other' D le_rfl _ hi, addCnt_other' D le_rfl _ hi]
    have nc : ∀ i ≤ nW D, ∀ j < D.k, wk D i ≠ cntK D j :=
      fun i hi j hj => (cntK_ne_wk D hj hi).symm
    have hsimP : SimW D 0 (nW D) (init [x, y]) S4 := by
      intro i hi
      rw [Nat.zero_add, hP i hi]
      rcases i with _ | _ | i
      · rw [hS3c' _ (nc 0 (by omega)), hS2w0]; rfl
      · rw [hS3c' _ (nc 1 (by omega)), hS2w1]; rfl
      · have hlt : i + 1 + 1 < nS D := by have := nW_lt_nS D; omega
        have hT : ¬ Touched2 D (wk D (i + 1 + 1)) := by
          simp only [Touched2, not_or, not_exists, not_and]
          refine ⟨?_, ?_, ?_, fun j hj => nc _ (by omega) j hj⟩
          · exact wk_ne D hlt (nW_lt_nS D) (by omega)
          · exact wk_ne D hlt (nS_pos D) (by omega)
          · exact wk_ne D hlt (by omega) (by omega)
        rw [hS3o _ hT, hS1n]
        · simp [init]
        · exact wk_ne D hlt (nS_pos D) (by omega)
        · exact wk_ne D hlt (nW_lt_nS D) (by omega)
    have hclk : S4 (CLK D) = List.replicate T (.inl true) := by
      show S4 (wk D (oP D + 1)) = _
      rw [hsim4 1 (one_lt_Wp D)]
      simp [σ0, hT]
    have hout4 : S4 (OUT D) = [] := by
      rw [hfr4 _ (fun i _ => OUT_ne_wk D _), hS3o]
      · exact hS1n _ (OUT_ne_wk D 0) (OUT_ne_wk D _)
      · simp only [Touched2, not_or, not_exists, not_and]
        exact ⟨OUT_ne_wk D _, OUT_ne_wk D _, OUT_ne_wk D _, fun j _ => OUT_ne_wk D _⟩
    have hlenN : x.length ≤ N ∧ y.length ≤ N := by
      rw [hN, length_inp]; omega
    have hlen4 : ∀ j, j ≠ OUT D → (S4 j).length ≤ N + T + 2 := by
      intro j hj
      rcases j with ⟨⟩ | ⟨i, hi⟩
      · exact absurd rfl hj
      · have hwi : (Sum.inr ⟨i, hi⟩ : KK D) = wk D i := (wk_eq D hi).symm
        rw [hwi]
        rcases Nat.lt_or_ge i (nW D) with h | h
        · have := hsimP i h
          rw [Nat.zero_add] at this
          rw [this, List.length_map]
          rcases i with _ | _ | i <;> simp [init] <;> omega
        · rcases Nat.eq_or_lt_of_le h with h | h
          · subst h
            rw [hfr4 _ (fun i' hi' => wk_ne D (nW_lt_nS D) (oP_add_lt D hi') (by simp [oP]; omega))]
            rw [hS3c' _ (nc _ le_rfl)]
            exact (congrArg List.length hS2A).le.trans (by simp)
          · have hi' : i - oP D < Wp D := by simp [oP, nS] at hi ⊢; omega
            have e : wk D i = wk D (oP D + (i - oP D)) := by congr 1; simp [oP] at h ⊢; omega
            rw [e, hsim4 _ hi', List.length_map]
            simp only [Function.update_apply]
            split_ifs
            · simp [σ0]; omega
            · simp only [σ0]; split_ifs <;> simp <;> omega
    obtain ⟨np, hnp, v5, S5, h8, hS5o, hlen5⟩ :=
      runP D T (init [x, y]) S4 v4 (N + T + 2) hsimP hclk hout4 hlen4
    obtain ⟨ncl, hncl, h9⟩ := cleanup D _ (N + 2 * T + 3) (nS D) ⟨0, nS_pos D⟩ (by simp) S5 v5
      (fun j hj => by have := hlen5 j hj; omega) hS5o (fun i hi => by simp at hi)
    refine ⟨ncl + (np + (1 + (Comb.Tpad m D.k + (1 + (1 + (N + (1 + N))))))), ?_, ?_⟩
    · have : ncl ≤ nS D * (N + 2 * T + 4) := hncl
      omega
    · have e := it_trans D (it_trans D (it_trans D (it_trans D (it_trans D (it_trans D
        (it_trans D (it_trans D h1 (it_one D hstep2)) h3) (it_one D h4)) (it_one D h5)) h6)
        (it_one D h7)) h8) h9
      rw [hN] at e ⊢
      rw [List.length_reverse] at e
      rw [e]
      exact congrArg (fun b => some (haltList (tm D) [b])) (by simp [out, hx, hT, hm])

/-! ### Main theorem -/

theorem le_sq_of_two_le {n : ℕ} (h : 2 ≤ n) : n + 2 ≤ n ^ 2 := by nlinarith

/-- **`NP ∅ ⊆ NP`.** Every language verified by one of our oracle stack machines with the empty
oracle in time `(|x|+2)^k` is in the official class `NP` of the Clay formalization
(`Millennium.InNondeterministicPolynomialTime`, alphabet `Bool`). -/
theorem inNP_of_mem_NP_empty {L : Set Str} (hL : L ∈ NP ∅) :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Bool)
      (fun x => x ∈ L) := by
  classical
  obtain ⟨p, k, hp⟩ := hL
  let D : Data := ⟨p, k, fun o => decide (strOf o ∈ L)⟩
  refine ⟨Bool, inferInstance, fun x y => out D x y = true, 2 * k, ?_, ?_⟩
  · refine ⟨fun q => out D q.1 q.2, ?_, fun q => Iff.rfl⟩
    refine
      { tm := tm D
        inputAlphabet := Equiv.refl _
        outputAlphabet := Equiv.refl Bool
        time := 2 * X + 5 + (X + 2) ^ (3 * k + 1) + (X + 2) ^ k +
          C (nS D) * (X + 2 * (X + 2) ^ k + 4)
        outputsFun := fun q => ?_ }
    obtain ⟨x, y⟩ := q
    have hx' : List.map (Equiv.refl G).invFun ((Millennium.pair_encoding
        (Millennium.fin_encoding_string Bool) (Millennium.fin_encoding_string Bool)).encode (x, y))
        = inp x y := by
      rw [Millennium.pair_encoding.encode_eq]; simp [inp]; rfl
    have hlen : ((Millennium.pair_encoding (Millennium.fin_encoding_string Bool)
        (Millennium.fin_encoding_string Bool)).encode (x, y)).length = (inp x y).length := by
      rw [← hx', List.length_map]; rfl
    have hmain := main_run D x y
    refine ⟨⟨Classical.choose hmain, ?_⟩, ?_⟩
    · change _ = some (haltList (tm D) [out D x y])
      have h2 : it D (Classical.choose hmain) (initList (tm D) (List.map (Equiv.refl G).invFun
          ((Millennium.pair_encoding (Millennium.fin_encoding_string Bool)
            (Millennium.fin_encoding_string Bool)).encode (x, y))) : Cf D) =
            some (haltList (tm D) [out D x y]) := by
        rw [hx']; exact (Classical.choose_spec hmain).2
      exact h2
    · have hb := (Classical.choose_spec hmain).1
      show Classical.choose hmain ≤ _
      rw [hlen]
      simp only [eval_add, eval_pow, eval_X, eval_ofNat, eval_mul, eval_C]
      have hxN : x.length + 2 ≤ (inp x y).length + 2 := by simp [length_inp]; omega
      have t1 : Comb.Tpad (x.length + 2) k ≤ ((inp x y).length + 2) ^ (3 * k + 1) :=
        (Tpad_le (by omega) k).trans (Nat.pow_le_pow_left hxN _)
      have t2 : (x.length + 2) ^ k ≤ ((inp x y).length + 2) ^ k := Nat.pow_le_pow_left hxN _
      have t3 : nS D * ((inp x y).length + 2 * (x.length + 2) ^ k + 4) ≤
          nS D * ((inp x y).length + 2 * ((inp x y).length + 2) ^ k + 4) :=
        Nat.mul_le_mul_left _ (by omega)
      change Classical.choose hmain ≤ 2 * (inp x y).length + 5 + Comb.Tpad (x.length + 2) k +
        (x.length + 2) ^ k + nS D * ((inp x y).length + 2 * (x.length + 2) ^ k + 4) at hb
      omega
  · intro x
    simp only [Millennium.fin_encoding_string_encode]
    constructor
    · intro hx
      by_cases hx1 : x.length ≤ 1
      · exact ⟨[], by simp, by simp [out, hx1, D, strOf_sOf hx1, hx]⟩
      · obtain ⟨w, hw, hrun⟩ := (hp x).1 hx
        refine ⟨w, ?_, ?_⟩
        · calc w.length ≤ (x.length + 2) ^ k := hw
            _ ≤ (x.length ^ 2) ^ k := Nat.pow_le_pow_left (le_sq_of_two_le (by omega)) _
            _ = x.length ^ (2 * k) := by rw [← pow_mul]
        · simp only [out, if_neg hx1]
          exact accOf_eq_true.2 hrun
    · rintro ⟨y, -, hy⟩
      by_cases hx1 : x.length ≤ 1
      · simp only [out, if_pos hx1, D, strOf_sOf hx1, decide_eq_true_eq] at hy
        exact hy
      · simp only [out, if_neg hx1] at hy
        exact (hp x).2 ⟨y.take _, List.length_take_le _ _, runFor_take (accOf_eq_true.1 hy)⟩

end Pnp.Relativize.OfficialNP
