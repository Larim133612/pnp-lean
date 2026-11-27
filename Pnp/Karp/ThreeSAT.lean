import Pnp.Karp.Basic

/-!
# 3-SAT: the language and the reduction from SAT (combinatorial part)

## The language

`SAT3Lang w := Is3 w ∧ SATLang w`: `w` is a satisfiable dense CNF formula (format of
`Pnp/CookLevin/SAT.lean`) **every clause of which has at most three literals**
(`Is3`: at most three non-`zero` symbols in every finished clause; as in `SATLang`, symbols
after the last `sep` are not a clause and are ignored).  `is3_iff_chk` characterizes `Is3` by
the one-pass counter `chk` that the verifier program of `Pnp/Karp/ThreeSATNP.lean` runs.

## The reduction (`red`)

A "prefix-OR chain" construction, local in the input position.  The original variable `x_j`
becomes variable `2j`; for every input position `p` there is a chain variable `y_p` (variable
`2p+1`) meaning "some literal of the current clause before position `p` is true".  Reading the
input left to right with `j` = position inside the current clause and `d = p - j`:

* start: the clause `¬y_0`;
* a symbol `s ≠ sep` at position `p`: the clause `ℓ_j ∨ y_p ∨ ¬y_{p+1}` (where `ℓ_j` is the
  literal described by `s` at variable `2j`; nothing for `s = zero`);
* `sep` at position `p`: the clauses `y_p` and `¬y_{p+1}`.

Each output clause has at most three literals and the output has no unfinished tail.
`red_iff : SAT3Lang (red w) ↔ SATLang w`.
-/

namespace Pnp.Karp.ThreeSAT

open Pnp.CookLevin SatSym

/-! ## The language -/

/-- Every finished clause of the dense formula `w` has at most three literals
(non-`zero` symbols). -/
def Is3 (w : List SatSym) : Prop := ∀ c ∈ clauses w, (c.filter (· ≠ zero)).length ≤ 3

/-- **3-SAT**: satisfiable dense CNF formulas with at most three literals per clause
(`Is3`; symbols after the last `sep` are ignored, as in `SATLang`). -/
def SAT3Lang : Millennium.Language (List SatSym) := fun w => Is3 w ∧ SATLang w

/-- One-pass check of `Is3`: `k` counts the literals of the current clause. -/
def chk : List SatSym → ℕ → Bool
  | [], _ => true
  | sep :: w, k => decide (k ≤ 3) && chk w 0
  | zero :: w, k => chk w k
  | pos :: w, k => chk w (k + 1)
  | neg :: w, k => chk w (k + 1)

theorem chk_iff : ∀ (w cur : List SatSym),
    chk w (cur.filter (· ≠ zero)).length = true ↔
      ∀ c ∈ clausesAux w cur, (c.filter (· ≠ zero)).length ≤ 3
  | [], cur => by simp [chk, clausesAux]
  | sep :: w, cur => by
    have ih := chk_iff w []
    simp only [List.filter_nil, List.length_nil] at ih
    simp only [chk, clausesAux, Bool.and_eq_true, decide_eq_true_eq, ih, List.mem_cons,
      forall_eq_or_imp, List.filter_reverse, List.length_reverse]
  | zero :: w, cur => by
    have ih := chk_iff w (zero :: cur)
    simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false] at ih
    simpa [chk, clausesAux] using ih
  | pos :: w, cur => by
    have ih := chk_iff w (pos :: cur)
    simp only [List.filter_cons, ne_eq, reduceCtorEq, not_false_eq_true, decide_true,
      if_true, List.length_cons] at ih
    simpa [chk, clausesAux] using ih
  | neg :: w, cur => by
    have ih := chk_iff w (neg :: cur)
    simp only [List.filter_cons, ne_eq, reduceCtorEq, not_false_eq_true, decide_true,
      if_true, List.length_cons] at ih
    simpa [chk, clausesAux] using ih

theorem is3_iff_chk (w : List SatSym) : Is3 w ↔ chk w 0 = true := by
  have := chk_iff w []
  simp only [List.filter_nil, List.length_nil] at this
  rw [this]; rfl

/-! ## Clause-level lemmas -/

/-- `m` copies of `zero`. -/
abbrev zs (m : ℕ) : List SatSym := List.replicate m zero

theorem clausesAux_block (rest : List SatSym) : ∀ (c cur : List SatSym), sep ∉ c →
    clausesAux (c ++ sep :: rest) cur = (cur.reverse ++ c) :: clausesAux rest []
  | [], cur, _ => by simp [clausesAux]
  | s :: c, cur, h => by
    have hs : s ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have hc : sep ∉ c := fun e => h (List.mem_cons_of_mem _ e)
    have ih := clausesAux_block rest c (s :: cur) hc
    cases s <;> simp_all [clausesAux]

theorem clauses_flatMap : ∀ L : List (List SatSym), (∀ c ∈ L, sep ∉ c) →
    clauses (L.flatMap (· ++ [sep])) = L
  | [], _ => rfl
  | c :: L, h => by
    have ih := clauses_flatMap L (fun c hc => h c (List.mem_cons_of_mem _ hc))
    simp only [clauses] at ih ⊢
    rw [List.flatMap_cons, List.append_assoc, List.singleton_append,
      clausesAux_block _ c [] (h c (List.mem_cons_self ..)), ih]
    simp

theorem clauseSat_iff_exists (a : ℕ → Bool) (c : List SatSym) :
    ClauseSat a c ↔ ∃ j, litTrue a j (c.getD j zero) := by
  constructor
  · rintro ⟨j, -, h⟩; exact ⟨j, h⟩
  · rintro ⟨j, h⟩
    refine ⟨j, ?_, h⟩
    by_contra hj
    rw [List.getD_eq_default _ _ (by omega)] at h
    exact h

theorem clauseSat_nil (a : ℕ → Bool) : ¬ ClauseSat a [] := by
  rintro ⟨j, hj, -⟩; simp at hj

theorem litTrue_succ (a : ℕ → Bool) (k : ℕ) (s : SatSym) :
    litTrue a (k + 1) s ↔ litTrue (fun i => a (i + 1)) k s := by
  cases s <;> rfl

theorem clauseSat_cons (a : ℕ → Bool) (s : SatSym) (c : List SatSym) :
    ClauseSat a (s :: c) ↔ litTrue a 0 s ∨ ClauseSat (fun i => a (i + 1)) c := by
  rw [clauseSat_iff_exists, clauseSat_iff_exists]
  constructor
  · rintro ⟨j, h⟩
    cases j with
    | zero => exact Or.inl h
    | succ k => exact Or.inr ⟨k, by simpa [litTrue_succ] using h⟩
  · rintro (h | ⟨k, h⟩)
    · exact ⟨0, h⟩
    · exact ⟨k + 1, by simpa [litTrue_succ] using h⟩

theorem clauseSat_zs (m : ℕ) : ∀ (a : ℕ → Bool) (c : List SatSym),
    ClauseSat a (zs m ++ c) ↔ ClauseSat (fun i => a (i + m)) c := by
  induction m with
  | zero => intro a c; simp
  | succ m ih =>
    intro a c
    show ClauseSat a (List.replicate (m + 1) zero ++ c) ↔ _
    rw [List.replicate_succ, List.cons_append, clauseSat_cons, ih]
    simp only [litTrue, false_or]
    have : (fun i => a (i + m + 1)) = fun i => a (i + (m + 1)) := by
      funext i; congr 1
    rw [this]

theorem litTrue_zero_shift (a : ℕ → Bool) (m : ℕ) (s : SatSym) :
    litTrue (fun i => a (i + m)) 0 s ↔ litTrue a m s := by
  cases s <;> simp [litTrue]

/-- The step clause `ℓ_j ∨ y_p ∨ ¬y_{p+1}` (`p = j + d`). -/
def stp (s : SatSym) (j d : ℕ) : List SatSym := zs (2 * j) ++ [s] ++ zs (2 * d) ++ [pos, zero, neg]

/-- The clause `y_p` (`p = j + d`). -/
def uPos (j d : ℕ) : List SatSym := zs (2 * j) ++ zs (2 * d) ++ [zero, pos]

/-- The clause `¬y_{p+1}` (`p = j + d`). -/
def uNeg (j d : ℕ) : List SatSym := zs (2 * j) ++ zs (2 * d) ++ [zero, zero, zero, neg]

theorem clauseSat_stp (a : ℕ → Bool) (s : SatSym) (j d : ℕ) :
    ClauseSat a (stp s j d) ↔
      litTrue a (2 * j) s ∨ a (2 * (j + d) + 1) = true ∨ a (2 * (j + d) + 3) = false := by
  simp only [stp, List.append_assoc, clauseSat_zs, clauseSat_cons,
    List.cons_append, List.nil_append, litTrue_zero_shift]
  simp only [litTrue, false_or, clauseSat_nil, or_false]
  have e1 : 0 + 2 * d + 1 + 2 * j = 2 * (j + d) + 1 := by ring
  have e2 : 0 + 1 + 1 + 2 * d + 1 + 2 * j = 2 * (j + d) + 3 := by ring
  rw [e1, e2]

theorem clauseSat_uPos (a : ℕ → Bool) (j d : ℕ) :
    ClauseSat a (uPos j d) ↔ a (2 * (j + d) + 1) = true := by
  simp only [uPos, List.append_assoc, clauseSat_zs, clauseSat_cons, litTrue, false_or,
    clauseSat_nil, or_false]
  have e1 : 0 + 1 + 2 * d + 2 * j = 2 * (j + d) + 1 := by ring
  rw [e1]

theorem clauseSat_uNeg (a : ℕ → Bool) (j d : ℕ) :
    ClauseSat a (uNeg j d) ↔ a (2 * (j + d) + 3) = false := by
  simp only [uNeg, List.append_assoc, clauseSat_zs, clauseSat_cons, litTrue, false_or,
    clauseSat_nil, or_false]
  have e1 : 0 + 1 + 1 + 1 + 2 * d + 2 * j = 2 * (j + d) + 3 := by ring
  rw [e1]

/-! ## The reduction -/

/-- The clauses produced from the input suffix `w`, with `j` the position inside the current
clause and `d = p - j` (`p` the global input position). -/
def goC : List SatSym → ℕ → ℕ → List (List SatSym)
  | [], _, _ => []
  | s :: w, j, d =>
    if s = sep then uPos j d :: uNeg j d :: goC w 0 (j + d + 1)
    else stp s j d :: goC w (j + 1) d

/-- All clauses of the output: `¬y_0`, then `goC`. -/
def TC (w : List SatSym) : List (List SatSym) := [zero, neg] :: goC w 0 0

/-- **The reduction SAT → 3-SAT** (as a dense formula: every clause followed by `sep`). -/
def red (w : List SatSym) : List SatSym := (TC w).flatMap (· ++ [sep])

theorem goC_shape : ∀ (w : List SatSym) (j d : ℕ), ∀ c ∈ goC w j d,
    sep ∉ c ∧ (c.filter (· ≠ zero)).length ≤ 3
  | [], _, _ => by simp [goC]
  | s :: w, j, d => by
    intro c hc
    have ih := goC_shape w
    by_cases hs : s = sep
    · subst hs
      simp only [goC, if_true, List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · simp [uPos, ]
      · simp [uNeg, ]
      · exact ih _ _ c hc
    · simp only [goC, hs, if_false, List.mem_cons] at hc
      rcases hc with rfl | hc
      · refine ⟨by simp [stp, Ne.symm hs], ?_⟩
        cases s <;> simp_all [stp, ]
      · exact ih _ _ c hc

theorem TC_shape (w : List SatSym) : ∀ c ∈ TC w, sep ∉ c ∧ (c.filter (· ≠ zero)).length ≤ 3 := by
  intro c hc
  simp only [TC, List.mem_cons] at hc
  rcases hc with rfl | hc
  · simp
  · exact goC_shape w 0 0 c hc

theorem clauses_red (w : List SatSym) : clauses (red w) = TC w :=
  clauses_flatMap _ fun c hc => (TC_shape w c hc).1

theorem is3_red (w : List SatSym) : Is3 (red w) := by
  intro c hc
  rw [clauses_red] at hc
  exact (TC_shape w c hc).2

/-! ## Correctness -/

/-- Truth value of the literal described by `s` at clause position `j`. -/
def litB (a : ℕ → Bool) (j : ℕ) : SatSym → Bool
  | pos => a j
  | neg => !a j
  | _ => false

theorem evalF_cons_ne (a : ℕ → Bool) {s : SatSym} (hs : s ≠ sep) (w : List SatSym) (j : ℕ)
    (F : Bool) : evalF a (s :: w) j F = evalF a w (j + 1) (F || litB a j s) := by
  cases s <;> simp_all [evalF, litB]

/-- The chain values: `yAux a w j F q` is the value of `y` at `q` positions after the start of
`w` (`F`: some literal of the current clause seen so far is true). -/
def yAux (a : ℕ → Bool) : List SatSym → ℕ → Bool → ℕ → Bool
  | _, _, F, 0 => F
  | [], _, F, _ + 1 => F
  | s :: w, j, F, q + 1 =>
    if s = sep then yAux a w 0 false q else yAux a w (j + 1) (F || litB a j s) q

theorem litTrue_iff_litB {a b : ℕ → Bool} (hb : ∀ i, b (2 * i) = a i) (j : ℕ) (s : SatSym) :
    litTrue b (2 * j) s ↔ litB a j s = true := by
  cases s <;> simp [litTrue, litB, hb]

theorem fwd (a b : ℕ → Bool) (hb : ∀ i, b (2 * i) = a i) : ∀ (w : List SatSym) (j d : ℕ)
    (F : Bool), (∀ q, b (2 * (j + d + q) + 1) = yAux a w j F q) → evalF a w j F = true →
      ∀ c ∈ goC w j d, ClauseSat b c
  | [], _, _, _, _, _ => by simp [goC]
  | s :: w, j, d, F, H, he => by
    intro c hc
    have H0 := H 0
    have H1 := H 1
    have Hs : ∀ q, b (2 * (j + d + (q + 1)) + 1) = yAux a (s :: w) j F (q + 1) := fun q => H _
    simp only [yAux, Nat.add_zero] at H0 H1 Hs
    by_cases hs : s = sep
    · subst hs
      simp only [evalF, Bool.and_eq_true] at he
      simp only [goC, if_true, List.mem_cons] at hc
      simp only [if_true] at H1 Hs
      rcases hc with rfl | rfl | hc
      · rw [clauseSat_uPos, H0, he.1]
      · rw [clauseSat_uNeg]; rw [← H1]; congr 1
      · refine fwd a b hb w 0 (j + d + 1) false (fun q => ?_) he.2 c hc
        rw [← Hs q]; congr 1; ring
    · rw [evalF_cons_ne a hs] at he
      simp only [goC, hs, if_false, List.mem_cons] at hc
      simp only [hs, if_false] at H1 Hs
      rcases hc with rfl | hc
      · rw [clauseSat_stp, litTrue_iff_litB hb]
        have e : 2 * (j + d) + 3 = 2 * (j + d + 1) + 1 := by ring
        rw [e, H1, H0]
        cases F <;> cases litB a j s <;> simp
      · refine fwd a b hb w (j + 1) d _ (fun q => ?_) he c hc
        rw [← Hs q]; congr 1; ring

theorem bwd (b : ℕ → Bool) : ∀ (w : List SatSym) (j d : ℕ) (F : Bool),
    (b (2 * (j + d) + 1) = true → F = true) → (∀ c ∈ goC w j d, ClauseSat b c) →
      evalF (fun i => b (2 * i)) w j F = true
  | [], _, _, _, _, _ => rfl
  | s :: w, j, d, F, hF, hc => by
    by_cases hs : s = sep
    · subst hs
      simp only [goC, if_true, List.mem_cons, forall_eq_or_imp] at hc
      obtain ⟨h1, h2, h3⟩ := hc
      rw [clauseSat_uPos] at h1
      rw [clauseSat_uNeg] at h2
      simp only [evalF, Bool.and_eq_true]
      refine ⟨hF h1, bwd b w 0 (j + d + 1) false (fun h => ?_) h3⟩
      rw [show 2 * (0 + (j + d + 1)) + 1 = 2 * (j + d) + 3 by ring, h2] at h
      exact absurd h (by simp)
    · simp only [goC, hs, if_false, List.mem_cons, forall_eq_or_imp] at hc
      obtain ⟨h1, h3⟩ := hc
      rw [clauseSat_stp, litTrue_iff_litB (a := fun i => b (2 * i)) (fun _ => rfl)] at h1
      rw [evalF_cons_ne _ hs]
      refine bwd b w (j + 1) d _ (fun h => ?_) h3
      rw [show 2 * (j + 1 + d) + 1 = 2 * (j + d) + 3 by ring] at h
      rw [h] at h1
      simp only [Bool.or_eq_true]
      rcases h1 with h1 | h1 | h1
      · exact Or.inr h1
      · exact Or.inl (hF h1)
      · exact absurd h1 (by simp)

theorem sat_red_iff (w : List SatSym) : SATLang (red w) ↔ SATLang w := by
  rw [clauses_sat_iff, clauses_red]
  constructor
  · rintro ⟨b, hb⟩
    simp only [TC, List.mem_cons, forall_eq_or_imp] at hb
    obtain ⟨h0, hb⟩ := hb
    have h1 : b 1 = false := by
      have := (clauseSat_cons b zero [neg]).1 h0
      simp only [litTrue, false_or, clauseSat_cons, clauseSat_nil, or_false] at this
      simpa using this
    exact ⟨_, bwd b w 0 0 false (fun h => by rw [h1] at h; exact absurd h (by simp)) hb⟩
  · rintro ⟨a, ha⟩
    let b : ℕ → Bool := fun i => if i % 2 = 0 then a (i / 2) else yAux a w 0 false (i / 2)
    have hb : ∀ i, b (2 * i) = a i := fun i => by simp [b]
    have hy : ∀ q, b (2 * (0 + 0 + q) + 1) = yAux a w 0 false q := fun q => by
      simp only [b, zero_add]
      rw [if_neg (by omega)]; congr 1; omega
    refine ⟨b, ?_⟩
    simp only [TC, List.mem_cons, forall_eq_or_imp]
    refine ⟨?_, fwd a b hb w 0 0 false hy ha⟩
    rw [clauseSat_cons]
    right
    rw [clauseSat_cons]
    left
    have := hy 0
    simp only [yAux] at this
    simpa [litTrue] using this

/-- **Correctness of the reduction**: `red w ∈ 3-SAT ↔ w ∈ SAT`. -/
theorem red_iff (w : List SatSym) : SAT3Lang (red w) ↔ SATLang w :=
  ⟨fun h => (sat_red_iff w).1 h.2, fun h => ⟨is3_red w, (sat_red_iff w).2 h⟩⟩

end Pnp.Karp.ThreeSAT
