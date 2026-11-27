import Pnp.CookLevin.SAT
import Pnp.Circuits.Basic

/-!
# Circuit satisfiability reduces to SAT: the Tseitin transformation (M28)

For a B₂ circuit `C : Circuit n s` (`Pnp/Circuits/Basic.lean`) we build a dense CNF formula
`tseitin C : List SatSym` (in the format of `Pnp/CookLevin/SAT.lean`) with one variable per wire
(`x_j` for `j < n` is input `j`, `x_{n+i}` is the output of gate `i`) such that

* `tseitin_sat_iff : SATLang (tseitin C) ↔ ∃ x, C.eval x = true`,
* `length_tseitin_le : (tseitin C).length ≤ (4 * s + 1) * (n + s + 1)`.

For gate `i = (op, p, q)` and each pair `(u, v)` of Boolean values the formula contains the clause
`x_p ≠ u ∨ x_q ≠ v ∨ x_{n+i} = op u v` (omitted when `p = q` and `u ≠ v`, where it is a tautology
that the dense format, with one symbol per variable, cannot write).  Finally the unit clause
`x_out` asks for output `true`.

This is the purely combinatorial part of the Cook–Levin NP-hardness proof; that the map
`C ↦ tseitin C` is computable in polynomial time by a Turing machine (uniformity), and the
tableau construction turning an NP verifier into circuits, are not done here.

## General CNF encoding

A clause is a partial map `L : ℕ → Option Bool` (`L j = some b`: the literal “`x_j = b`”).
`denseClause N L` writes it densely for variables `< N`; `encodeCNF N cs` concatenates clauses.
`evalF_encodeCNF` characterises its value: every clause has a true literal below `N`.
-/

namespace Pnp.CookLevin

open Pnp.Circuits SatSym

/-! ## Dense encoding of a list of clauses -/

/-- The dense symbol of a literal slot. -/
def litSym : Option Bool → SatSym
  | none => zero
  | some true => pos
  | some false => neg

/-- A clause as a dense word over variables `< N`, terminated by `sep`. -/
def denseClause (N : ℕ) (L : ℕ → Option Bool) : List SatSym :=
  (List.range' 0 N).map (fun k => litSym (L k)) ++ [sep]

/-- A list of clauses as a dense formula. -/
def encodeCNF (N : ℕ) (cs : List (ℕ → Option Bool)) : List SatSym :=
  cs.flatMap (denseClause N)

/-- `L` has a true literal (below `N`) under `a`. -/
def ClauseHolds (N : ℕ) (a : ℕ → Bool) (L : ℕ → Option Bool) : Prop :=
  ∃ j < N, L j = some (a j)

theorem evalF_range' (a : ℕ → Bool) (L : ℕ → Option Bool) (w : List SatSym) :
    ∀ (m j : ℕ) (F : Bool),
      evalF a ((List.range' j m).map (fun k => litSym (L k)) ++ sep :: w) j F = true ↔
        ((F = true ∨ ∃ k, j ≤ k ∧ k < j + m ∧ L k = some (a k)) ∧ evalF a w 0 false = true)
  | 0, j, F => by
    simp only [List.range'_zero, List.map_nil, List.nil_append, evalF, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
    · rintro ⟨h1 | ⟨k, h3, h4, -⟩, h2⟩
      · exact ⟨h1, h2⟩
      · omega
  | m + 1, j, F => by
    rw [List.range'_succ, List.map_cons, List.cons_append]
    have ih := evalF_range' a L w m (j + 1)
    have key : ∀ F' : Bool, (F' = true ↔ F = true ∨ L j = some (a j)) →
        ((F' = true ∨ ∃ k, j + 1 ≤ k ∧ k < j + 1 + m ∧ L k = some (a k)) ↔
          (F = true ∨ ∃ k, j ≤ k ∧ k < j + (m + 1) ∧ L k = some (a k))) := by
      intro F' hF'
      rw [hF']
      constructor
      · rintro ((h | h) | ⟨k, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, le_rfl, by omega, h⟩
        · exact Or.inr ⟨k, by omega, by omega, h3⟩
      · rintro (h | ⟨k, h1, h2, h3⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
          · exact Or.inl (Or.inr h3)
          · exact Or.inr ⟨k, by omega, by omega, h3⟩
    rcases hL : L j with _ | _ | _
    · simp only [show litSym none = zero from rfl, evalF]
      rw [ih]; exact and_congr_left' (key _ (by simp [hL]))
    · simp only [show litSym (some false) = neg from rfl, evalF]
      rw [ih]; exact and_congr_left' (key _ (by cases a j <;> simp [hL]))
    · simp only [show litSym (some true) = pos from rfl, evalF]
      rw [ih]; exact and_congr_left' (key _ (by cases a j <;> simp [hL]))

theorem evalF_denseClause (N : ℕ) (a : ℕ → Bool) (L : ℕ → Option Bool) (w : List SatSym) :
    evalF a (denseClause N L ++ w) 0 false = true ↔
      (ClauseHolds N a L ∧ evalF a w 0 false = true) := by
  unfold denseClause
  rw [List.append_assoc, List.singleton_append, evalF_range']
  simp [ClauseHolds]

/-- **Semantics of the encoding.** -/
theorem evalF_encodeCNF (N : ℕ) (a : ℕ → Bool) (cs : List (ℕ → Option Bool)) :
    evalF a (encodeCNF N cs) 0 false = true ↔ ∀ L ∈ cs, ClauseHolds N a L := by
  induction cs with
  | nil => simp [encodeCNF, evalF]
  | cons L cs ih =>
    have e : encodeCNF N (L :: cs) = denseClause N L ++ encodeCNF N cs := by
      simp [encodeCNF]
    rw [e, evalF_denseClause, ih]
    simp

theorem length_denseClause (N : ℕ) (L : ℕ → Option Bool) :
    (denseClause N L).length = N + 1 := by
  simp [denseClause]

theorem length_encodeCNF (N : ℕ) (cs : List (ℕ → Option Bool)) :
    (encodeCNF N cs).length = cs.length * (N + 1) := by
  induction cs with
  | nil => simp [encodeCNF]
  | cons L cs ih =>
    rw [encodeCNF, List.flatMap_cons, List.length_append, ← encodeCNF, ih, length_denseClause,
      List.length_cons]
    ring

/-! ## Wires of a circuit -/

section Wires

variable {n : ℕ} (x : Fin n → Bool)

theorem wires_castSucc (s : ℕ) (g : Gates n (s + 1)) (k : Fin (n + s)) :
    wires x (s + 1) g (Fin.castSucc k) = wires x s (fun i => g i.castSucc) k := by
  simp only [wires]
  exact Fin.snoc_castSucc (α := fun _ => Bool) _ _ _

theorem wires_last (s : ℕ) (g : Gates n (s + 1)) :
    wires x (s + 1) g (Fin.last (n + s)) =
      (g (Fin.last s)).1 (wires x s (fun i => g i.castSucc) (g (Fin.last s)).2.1)
        (wires x s (fun i => g i.castSucc) (g (Fin.last s)).2.2) := by
  simp only [wires]
  exact Fin.snoc_last (α := fun _ => Bool) _ _

/-- Input wires carry the input. -/
theorem wires_input : ∀ (s : ℕ) (g : Gates n s) (j : ℕ) (hj : j < n),
    wires x s g ⟨j, by omega⟩ = x ⟨j, hj⟩
  | 0, g, j, hj => rfl
  | s + 1, g, j, hj => by
    have := wires_castSucc x s g ⟨j, by omega⟩
    simp only [Fin.castSucc_mk] at this
    rw [this, wires_input s _ j hj]

/-- Gate wires carry the gate value. -/
theorem wires_gate : ∀ (s : ℕ) (g : Gates n s) (i : Fin s),
    wires x s g ⟨n + i.val, by omega⟩ =
      (g i).1 (wires x s g (Fin.castLE (by omega) (g i).2.1))
        (wires x s g (Fin.castLE (by omega) (g i).2.2))
  | 0, g, i => i.elim0
  | s + 1, g, i => by
    induction i using Fin.lastCases with
    | last =>
      have h := wires_last x s g
      have e : (⟨n + (Fin.last s).val, by omega⟩ : Fin (n + (s + 1))) = Fin.last (n + s) := by
        ext; simp
      rw [e, h]
      exact congrArg₂ _ (wires_castSucc x s g _).symm (wires_castSucc x s g _).symm
    | cast i =>
      have e : (⟨n + (Fin.castSucc i).val, by omega⟩ : Fin (n + (s + 1))) =
          Fin.castSucc (⟨n + i.val, by have := i.isLt; omega⟩ : Fin (n + s)) := by ext; simp
      rw [e, wires_castSucc, wires_gate s _ i]
      exact congrArg₂ _ (wires_castSucc x s g _).symm (wires_castSucc x s g _).symm

end Wires

/-! ## The Tseitin formula -/

section Tseitin

variable {n s : ℕ}

/-- An assignment to wire variables respects every gate. -/
def Consistent (g : Gates n s) (a : ℕ → Bool) : Prop :=
  ∀ i : Fin s, a (n + i.val) = (g i).1 (a (g i).2.1) (a (g i).2.2)

/-- A consistent assignment equals the wire values on its own inputs. -/
theorem consistent_eq_wires {g : Gates n s} {a : ℕ → Bool} (h : Consistent g a) :
    ∀ (m : ℕ) (hm : m < n + s), a m = wires (fun j : Fin n => a j) s g ⟨m, hm⟩ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hmn : m < n
    · rw [wires_input _ s g m hmn]
    · obtain ⟨i, rfl⟩ : ∃ i, m = n + i := ⟨m - n, by omega⟩
      have hi : i < s := by omega
      have hw := wires_gate (fun j : Fin n => a ↑j) s g ⟨i, hi⟩
      simp only at hw
      rw [hw, h ⟨i, hi⟩]
      exact congrArg₂ _
        (ih _ (by have := (g ⟨i, hi⟩).2.1.isLt; simp only at this; omega) _)
        (ih _ (by have := (g ⟨i, hi⟩).2.2.isLt; simp only at this; omega) _)

/-- The clause `x_p ≠ u ∨ x_q ≠ v ∨ x_o = op u v`. -/
def gateClause (op : Bool → Bool → Bool) (p q o : ℕ) (u v : Bool) : ℕ → Option Bool :=
  fun j => if j = p then some (!u) else if j = q then some (!v) else
    if j = o then some (op u v) else none

/-- All four pairs of input values. -/
def boolPairs : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

theorem mem_boolPairs (uv : Bool × Bool) : uv ∈ boolPairs := by
  rcases uv with ⟨_ | _, _ | _⟩ <;> decide

/-- The clauses of one gate (tautologies for `p = q` omitted). -/
def gateClauses (op : Bool → Bool → Bool) (p q o : ℕ) : List (ℕ → Option Bool) :=
  (boolPairs.filter (fun uv => !decide (p = q ∧ uv.1 ≠ uv.2))).map
    (fun uv => gateClause op p q o uv.1 uv.2)

theorem length_gateClauses_le (op : Bool → Bool → Bool) (p q o : ℕ) :
    (gateClauses op p q o).length ≤ 4 := by
  unfold gateClauses
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp [boolPairs])

theorem gateClause_holds {N : ℕ} {a : ℕ → Bool} {op : Bool → Bool → Bool} {p q o : ℕ}
    {u v : Bool} (hp : p < o) (hq : q < o) (ho : o < N) (hpq : ¬(p = q ∧ u ≠ v)) :
    ClauseHolds N a (gateClause op p q o u v) ↔ (a p ≠ u ∨ a q ≠ v ∨ a o = op u v) := by
  constructor
  · rintro ⟨j, -, hj⟩
    unfold gateClause at hj
    split_ifs at hj with h1 h2 h3
    · subst h1; left; cases u <;> cases h : a j <;> simp_all
    · subst h2; right; left; cases v <;> cases h : a j <;> simp_all
    · subst h3; right; right; simp_all
  · rintro (h | h | h)
    · refine ⟨p, by omega, ?_⟩
      simp only [gateClause, if_true]
      cases u <;> cases h' : a p <;> simp_all
    · refine ⟨q, by omega, ?_⟩
      by_cases e : q = p
      · subst e
        have : u = v := by by_contra c; exact hpq ⟨rfl, c⟩
        subst this
        simp only [gateClause, if_true]
        cases u <;> cases h' : a q <;> simp_all
      · simp only [gateClause, e, if_false, if_true]
        cases v <;> cases h' : a q <;> simp_all
    · refine ⟨o, ho, ?_⟩
      simp only [gateClause, show o ≠ p by omega, show o ≠ q by omega, if_false, if_true, h]

theorem gateClauses_holds {N : ℕ} {a : ℕ → Bool} {op : Bool → Bool → Bool} {p q o : ℕ}
    (hp : p < o) (hq : q < o) (ho : o < N) :
    (∀ L ∈ gateClauses op p q o, ClauseHolds N a L) ↔ a o = op (a p) (a q) := by
  constructor
  · intro h
    have hpq : ¬(p = q ∧ a p ≠ a q) := by rintro ⟨rfl, c⟩; exact c rfl
    have hmem : gateClause op p q o (a p) (a q) ∈ gateClauses op p q o := by
      unfold gateClauses
      refine List.mem_map.2 ⟨(a p, a q), ?_, rfl⟩
      simp only [List.mem_filter, mem_boolPairs, true_and]
      by_cases e : p = q <;> simp_all
    rcases (gateClause_holds hp hq ho hpq).1 (h _ hmem) with c | c | c
    · exact absurd rfl c
    · exact absurd rfl c
    · exact c
  · intro h L hL
    unfold gateClauses at hL
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := List.mem_map.1 hL
    have hpq : ¬(p = q ∧ u ≠ v) := by
      have := (List.mem_filter.1 huv).2; by_cases e : p = q <;> simp_all
    refine (gateClause_holds hp hq ho hpq).2 ?_
    by_cases hu : a p = u
    · by_cases hv : a q = v
      · subst hu hv; exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl hv)
    · exact Or.inl hu

/-- The unit clause `x_o`. -/
def unitClause (o : ℕ) : ℕ → Option Bool := fun j => if j = o then some true else none

theorem unitClause_holds {N : ℕ} {a : ℕ → Bool} {o : ℕ} (ho : o < N) :
    ClauseHolds N a (unitClause o) ↔ a o = true := by
  constructor
  · rintro ⟨j, -, hj⟩
    unfold unitClause at hj
    split_ifs at hj with h
    · subst h; simp_all
  · intro h
    exact ⟨o, ho, by simp [unitClause, h]⟩

/-- The Tseitin clauses of a circuit (variables `0, …, n + s - 1`). -/
def tseitinCNF (C : Circuit n s) : List (ℕ → Option Bool) :=
  (List.finRange s).flatMap (fun i => gateClauses (C.1 i).1 (C.1 i).2.1 (C.1 i).2.2 (n + i.val))
    ++ [unitClause C.2]

/-- **The Tseitin formula** of a circuit, as a dense CNF word. -/
def tseitin (C : Circuit n s) : List SatSym := encodeCNF (n + s) (tseitinCNF C)

theorem length_tseitinCNF_le (C : Circuit n s) : (tseitinCNF C).length ≤ 4 * s + 1 := by
  unfold tseitinCNF
  rw [List.length_append, List.length_flatMap, List.length_singleton]
  have : (List.map (fun i : Fin s =>
      (gateClauses (C.1 i).1 (C.1 i).2.1 (C.1 i).2.2 (n + i.val)).length)
      (List.finRange s)).sum ≤ (List.finRange s).length * 4 := by
    have := List.sum_le_card_nsmul (List.map (fun i : Fin s =>
      (gateClauses (C.1 i).1 (C.1 i).2.1 (C.1 i).2.2 (n + i.val)).length)
      (List.finRange s)) 4 (by
        intro y hy
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
        exact length_gateClauses_le _ _ _ _)
    simpa using this
  rw [List.length_finRange] at this
  omega

/-- **Size bound**: the formula has length `O((n + s) · s)`. -/
theorem length_tseitin_le (C : Circuit n s) :
    (tseitin C).length ≤ (4 * s + 1) * (n + s + 1) := by
  rw [tseitin, length_encodeCNF]
  exact Nat.mul_le_mul_right _ (length_tseitinCNF_le C)

theorem tseitinCNF_holds (C : Circuit n s) (a : ℕ → Bool) :
    (∀ L ∈ tseitinCNF C, ClauseHolds (n + s) a L) ↔ Consistent C.1 a ∧ a C.2 = true := by
  have hb : ∀ i : Fin s, (C.1 i).2.1.val < n + i.val ∧ (C.1 i).2.2.val < n + i.val ∧
      n + i.val < n + s := fun i => ⟨(C.1 i).2.1.isLt, (C.1 i).2.2.isLt, by omega⟩
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · refine (gateClauses_holds (hb i).1 (hb i).2.1 (hb i).2.2).1 (fun L hL => h L ?_)
      exact List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_finRange i, hL⟩)
    · exact (unitClause_holds C.2.isLt).1 (h _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · rintro ⟨hc, ho⟩ L hL
    rcases List.mem_append.1 hL with hL | hL
    · obtain ⟨i, -, hL⟩ := List.mem_flatMap.1 hL
      exact (gateClauses_holds (hb i).1 (hb i).2.1 (hb i).2.2).2 (hc i) L hL
    · rw [List.mem_singleton.1 hL]
      exact (unitClause_holds C.2.isLt).2 ho

/-- **Tseitin's theorem**: the formula is satisfiable iff the circuit is. -/
theorem tseitin_sat_iff (C : Circuit n s) :
    SATLang (tseitin C) ↔ ∃ x : Fin n → Bool, C.eval x = true := by
  unfold SATLang tseitin
  simp only [evalF_encodeCNF, tseitinCNF_holds]
  constructor
  · rintro ⟨a, hc, ho⟩
    refine ⟨fun j => a j, ?_⟩
    rw [Circuit.eval, ← ho]
    exact (consistent_eq_wires hc C.2 C.2.isLt).symm
  · rintro ⟨x, hx⟩
    let a : ℕ → Bool := fun j => if h : j < n + s then wires x s C.1 ⟨j, h⟩ else false
    have ha : ∀ k : Fin (n + s), a k = wires x s C.1 k := fun k => by simp [a, k.isLt]
    refine ⟨a, fun i => ?_, ?_⟩
    · have hw := wires_gate x s C.1 i
      have e1 : a (n + i.val) = wires x s C.1 ⟨n + i.val, by omega⟩ := by
        simp [a, show n + i.val < n + s by omega]
      rw [e1, hw, ← ha, ← ha]
      rfl
    · rw [ha]; exact hx

/-- Circuit satisfiability, as a predicate on circuits. -/
def CircuitSat (C : Circuit n s) : Prop := ∃ x : Fin n → Bool, C.eval x = true

theorem circuitSat_iff_tseitin (C : Circuit n s) : CircuitSat C ↔ SATLang (tseitin C) :=
  (tseitin_sat_iff C).symm

end Tseitin

end Pnp.CookLevin
