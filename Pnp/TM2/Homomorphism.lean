import Pnp.TM2.Compose
import Pnp.Oracle.Official

/-!
# Symbol-wise homomorphisms in the official two-stack machine model

For a finite alphabet `Γ` and a code `c : Γ → List Bool`, the map `w ↦ w.flatMap c` (replace
every symbol `g` of `w` by the bit string `c g`) is computed in linear time by a hand-built Mathlib
`FinTM2` machine `homTM c`. It has three stacks (`inp`: the input, `aux`: scratch, `out`: the
output), state type `Option Γ` and two labels:

1. label `false`: pop the input symbol by symbol and push each onto `aux` (this reverses it);
2. label `true`: pop `aux` (last input symbol first); for a popped symbol `g`, push the bits of
   `c g` onto `out` in reverse order, all within *one* step (the statement contains `B` guarded
   pushes, `B` the maximal code length); when `aux` is empty, halt.

Each phase takes `|w| + 1` steps, so the machine runs in time `2|w| + 2`.

* `homTM_outputs`: the machine outputs `w.flatMap c` on input `w` in `2|w| + 2` steps.
* `homCompOf`: for any `enc : α → List Γ`, a `TM2ComputableInPolyTime` for
  `fun a => (enc a).flatMap c`; special cases `homCompList` (identity encoding) and `homComp`
  (an arbitrary `FinEncoding`).
* `inPolynomialTime_of_code`: if `L t ↔ (e.encode t).flatMap c ∈ S` with `S ∈ P ∅` (our own
  machine model), then `L` is in the official class `P` for the encoding `e`.
-/

namespace Pnp.TM2Hom

open Turing Millennium Computability Pnp.TM2Proj

noncomputable section

/-- The three stacks of the homomorphism machine. -/
inductive Stk
  | inp
  | aux
  | out
  deriving DecidableEq, Fintype

variable {Γ : Type}

/-- Stack alphabets: input symbols, (optional) input symbols on the scratch stack, bits. -/
abbrev Γ' (Γ : Type) : Stk → Type
  | .inp => Γ
  | .aux => Option Γ
  | .out => Bool

/-- Stack contents from the three lists. -/
def stk (a : List Γ) (b : List (Option Γ)) (o : List Bool) : ∀ k : Stk, List (Γ' Γ k)
  | .inp => a
  | .aux => b
  | .out => o

theorem update_inp (a : List Γ) (b : List (Option Γ)) (o : List Bool) (l : List Γ) :
    Function.update (stk a b o) Stk.inp l = stk l b o := by
  funext j; cases j <;> rfl

theorem update_aux (a : List Γ) (b : List (Option Γ)) (o : List Bool) (l : List (Option Γ)) :
    Function.update (stk a b o) Stk.aux l = stk a l o := by
  funext j; cases j <;> rfl

theorem update_out (a : List Γ) (b : List (Option Γ)) (o : List Bool) (l : List Bool) :
    Function.update (stk a b o) Stk.out l = stk a b l := by
  funext j; cases j <;> rfl

variable (c : Γ → List Bool)

/-- The code of the symbol held in the state (empty for `none`). -/
def code (s : Option Γ) : List Bool := s.elim [] c

/-- Guarded pushes: push the bits `i, i+1, …, i+n-1` of `(code s).reverse` (those that exist)
onto the output stack, then continue with `q`. -/
def pushesFrom : ℕ → ℕ → TM2.Stmt (Γ' Γ) Bool (Option Γ) → TM2.Stmt (Γ' Γ) Bool (Option Γ)
  | _, 0, q => q
  | i, n + 1, q =>
    .branch (fun s => decide (i < (code c s).length))
      (.push Stk.out (fun s => (code c s).reverse.getD i false) (pushesFrom (i + 1) n q)) q

theorem stepAux_pushesFrom (i n : ℕ) (q : TM2.Stmt (Γ' Γ) Bool (Option Γ)) (s : Option Γ)
    (a : List Γ) (b : List (Option Γ)) (o : List Bool) :
    TM2.stepAux (pushesFrom c i n q) s (stk a b o) =
      TM2.stepAux q s (stk a b ((((code c s).reverse.drop i).take n).reverse ++ o)) := by
  induction n generalizing i o with
  | zero => simp [pushesFrom]
  | succ n ih =>
    by_cases hi : i < (code c s).length
    · simp only [pushesFrom, TM2.stepAux, hi, decide_true, cond_true]
      rw [show stk a b o Stk.out = o from rfl, update_out, ih]
      have hi' : i < (code c s).reverse.length := by simpa using hi
      rw [List.drop_eq_getElem_cons hi', List.take_succ_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.getD_eq_getElem _ _ hi']
    · simp only [pushesFrom, TM2.stepAux, hi, decide_false, cond_false]
      rw [List.drop_eq_nil_of_le (by simpa using hi)]
      simp

/-- A bound on the code lengths. -/
def B [Fintype Γ] : ℕ := Finset.univ.sup fun g => (c g).length

theorem code_length_le [Fintype Γ] (s : Option Γ) : (code c s).length ≤ B c := by
  rcases s with _ | g
  · exact Nat.zero_le _
  · exact Finset.le_sup (f := fun g => (c g).length) (Finset.mem_univ g)

/-- The program of the homomorphism machine. -/
def prog [Fintype Γ] : Bool → TM2.Stmt (Γ' Γ) Bool (Option Γ)
  | false =>
    .pop Stk.inp (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push Stk.aux (fun s => s) (.goto fun _ => false))
        (.goto fun _ => true))
  | true =>
    .pop Stk.aux (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (pushesFrom c 0 (B c) (.goto fun _ => true))
        .halt)

/-- The step function of the homomorphism machine. -/
abbrev step' [Fintype Γ] : TM2.Cfg (Γ' Γ) Bool (Option Γ) → Option (TM2.Cfg (Γ' Γ) Bool (Option Γ)) :=
  TM2.step (prog c)

variable [Fintype Γ]

/-- Phase 1: move the input, reversed, onto the scratch stack. -/
theorem run_phase1 (rest : List Γ) (aux : List (Option Γ)) (x : Option Γ) :
    runF (step' c) (rest.length + 1) (some ⟨some false, x, stk rest aux []⟩) =
      some ⟨some true, none, stk [] ((rest.map some).reverse ++ aux) []⟩ := by
  induction rest generalizing aux x with
  | nil =>
    rw [List.length_nil, runF_succ]
    show runF (step' c) 0 (some (TM2.stepAux (prog c false) x (stk [] aux []))) = _
    simp only [prog, TM2.stepAux]
    rw [show stk ([] : List Γ) aux [] Stk.inp = [] from rfl, update_inp]
    simp [runF]
  | cons g rest ih =>
    rw [List.length_cons, runF_succ]
    show runF (step' c) (rest.length + 1)
      (some (TM2.stepAux (prog c false) x (stk (g :: rest) aux []))) = _
    simp only [prog, TM2.stepAux]
    rw [show stk (g :: rest) aux [] Stk.inp = g :: rest from rfl, update_inp]
    change runF (step' c) (rest.length + 1)
      (some (TM2.stepAux (.goto fun _ => false) (some g)
        (Function.update (stk rest aux []) Stk.aux (some g :: aux)))) = _
    rw [update_aux]
    change runF (step' c) (rest.length + 1)
      (some ⟨some false, some g, stk rest (some g :: aux) []⟩) = _
    rw [ih]
    simp

/-- Phase 2: pop the scratch stack, pushing the codes onto the output stack, then halt. -/
theorem run_phase2 (u : List Γ) (o : List Bool) (x : Option Γ) :
    runF (step' c) (u.length + 1) (some ⟨some true, x, stk [] (u.map some) o⟩) =
      some ⟨none, none, stk [] [] (u.reverse.flatMap c ++ o)⟩ := by
  induction u generalizing o x with
  | nil =>
    rw [List.length_nil, runF_succ]
    show runF (step' c) 0 (some (TM2.stepAux (prog c true) x (stk [] [] o))) = _
    simp only [prog, TM2.stepAux]
    rw [show stk ([] : List Γ) [] o Stk.aux = [] from rfl, update_aux]
    simp [runF]
  | cons g u ih =>
    rw [List.length_cons, runF_succ]
    show runF (step' c) (u.length + 1)
      (some (TM2.stepAux (prog c true) x (stk [] (some g :: u.map some) o))) = _
    simp only [prog, TM2.stepAux]
    rw [show stk [] (some g :: u.map some) o Stk.aux = some g :: u.map some from rfl, update_aux]
    change runF (step' c) (u.length + 1)
      (some (TM2.stepAux (pushesFrom c 0 (B c) (.goto fun _ => true)) (some g)
        (stk [] (u.map some) o))) = _
    rw [stepAux_pushesFrom]
    have hB : (code c (some g)).length ≤ B c := code_length_le c _
    rw [List.drop_zero, List.take_of_length_le (by simpa using hB), List.reverse_reverse]
    change runF (step' c) (u.length + 1)
      (some ⟨some true, some g, stk [] (u.map some) (c g ++ o)⟩) = _
    rw [ih]
    simp

/-- The homomorphism machine. -/
def homTM : FinTM2 :=
  { K := Stk
    k₀ := Stk.inp
    k₁ := Stk.out
    Γ := Γ' Γ
    Λ := Bool
    main := false
    σ := Option Γ
    initialState := none
    Γk₀Fin := (inferInstance : Fintype Γ)
    m := prog c }

/-- **The homomorphism machine** outputs `w.flatMap c` on input `w` in `2|w| + 2` steps. -/
def homTM_outputs (w : List Γ) :
    TM2OutputsInTime (homTM c) w (some (w.flatMap c)) (2 * w.length + 2) := by
  refine { steps := (w.length + 1) + (w.length + 1), evals_in_steps := ?_, steps_le_m := by omega }
  have hinit : initList (homTM c) w = (⟨some false, none, stk w [] []⟩ :
      TM2.Cfg (Γ' Γ) Bool (Option Γ)) := by
    show (⟨some false, none, _⟩ : TM2.Cfg (Γ' Γ) Bool (Option Γ)) = _
    congr 1
    funext k; cases k <;> rfl
  have hhalt : haltList (homTM c) (w.flatMap c) = (⟨none, none, stk [] [] (w.flatMap c)⟩ :
      TM2.Cfg (Γ' Γ) Bool (Option Γ)) := by
    show (⟨none, none, _⟩ : TM2.Cfg (Γ' Γ) Bool (Option Γ)) = _
    congr 1
    funext k; cases k <;> rfl
  change runF (step' c) ((w.length + 1) + (w.length + 1)) (some (initList (homTM c) w)) =
    some (haltList (homTM c) (w.flatMap c))
  rw [hinit, hhalt, runF_add, run_phase1, List.append_nil, ← List.map_reverse,
    show w.length = w.reverse.length from (List.length_reverse).symm, run_phase2,
    List.reverse_reverse, List.append_nil]
  rfl

/-- The homomorphism `fun a => (enc a).flatMap c` is polynomial-time computable, for any map
`enc : α → List Γ` used as input encoding (the machine only sees the list `enc a`). -/
def homCompOf {α : Type} (enc : α → List Γ) :
    TM2ComputableInPolyTime enc (fin_encoding_string Bool).encode (fun a => (enc a).flatMap c) :=
  { tm := homTM c
    inputAlphabet := Equiv.refl Γ
    outputAlphabet := Equiv.refl Bool
    time := 2 * Polynomial.X + 2
    outputsFun := fun a => by
      have h := homTM_outputs c (enc a)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      show TM2OutputsInTime (homTM c) (List.map id (enc a))
        (some (List.map id (List.flatMap c (enc a)))) _
      rw [List.map_id, List.map_id]
      exact h }

/-- `List.flatMap c` on strings over `Γ` (identity encoding), in linear time. -/
def homCompList : TM2ComputableInPolyTime (fin_encoding_string Γ).encode
    (fin_encoding_string Bool).encode (List.flatMap c) :=
  homCompOf c (fin_encoding_string Γ).encode

end

/-- **Symbol-wise homomorphisms** of an encoding are polynomial-time computable. -/
noncomputable def homComp {T : Type} (e : FinEncoding T) (c : e.Γ → List Bool) :
    TM2ComputableInPolyTime e.encode (fin_encoding_string Bool).encode
      (fun t => (e.encode t).flatMap c) :=
  letI := e.ΓFin
  homCompOf c e.encode

/-- If membership in `L` is membership of the code `(e.encode t).flatMap c` in a language of our
own `P ∅`, then `L` is in the official class `P` for the encoding `e`. -/
theorem inPolynomialTime_of_code {T : Type} (e : FinEncoding T) (c : e.Γ → List Bool)
    (S : Set Pnp.Relativize.Str) (hS : S ∈ Pnp.Relativize.P ∅) (L : Millennium.Language T)
    (hL : ∀ t, L t ↔ (e.encode t).flatMap c ∈ S) : InPolynomialTime e L :=
  Pnp.TM2Comp.reducible_source_in_p e (fin_encoding_string Bool) L (fun x => x ∈ S)
    ⟨_, homComp e c, hL⟩ (Pnp.Relativize.Official.inPolynomialTime_of_mem_P_empty hS)

end Pnp.TM2Hom
