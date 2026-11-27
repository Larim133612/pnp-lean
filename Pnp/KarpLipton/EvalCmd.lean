import Pnp.Oracle.StructLib
import Pnp.Circuits.Multi

/-!
# Evaluating dense circuits with our structured stack programs (M32b)

To put the Karp–Lipton collapse into the official class `Σ₂ᴾ` we need a polynomial-time
program that evaluates a circuit given as data.  Random access to wire values is awkward on
stacks, so we use a **dense** circuit format, in the spirit of the dense CNF formulas of
`Pnp.CookLevin.SAT`: a gate lists *one token per earlier wire*, saying whether that wire is its
first and/or second input, so a gate is evaluated by one sequential scan of the wire values.

## The bit format

The circuit is a bit string `G` (stack `g`, top first), read token by token:

* `false, a, b`: a **wire token** for the next unscanned wire `x`: the first input flag `u` becomes
  `u || (a && x)`, the second `v` becomes `v || (b && x)`, and `x` moves to the scanned part;
* `true, t₀, t₁, t₂, t₃`: a **gate end** with truth table `t`: the value `r = t[2u + v]` is
  inserted right after the scanned wires (for an honest gate: appended at the end), the scan
  restarts at wire `0` and the flags are reset.

Missing bits read as `false`; a wire token with no wire left is skipped.  `evalD G V S u v` is the
resulting list of wire values (`V` the unscanned wires, `S` the scanned ones in reverse order).

## The program

`evalCmd g v s u w` (stacks: code `g`, wires `v` (top = wire `0`), scratch `s`, flags `u`, `w`,
a flag being `[]` or `[true]`) runs in time `≤ (|G| + 1)(2(|V| + |G|) + 40) + 2(|V| + |G|) + 20`
and leaves `evalD G V [] false false` on `v`, all other used stacks empty and all other stacks
unchanged (`exec_evalCmd`).

## Honest circuits

`denseGate op sels` is the code of a gate with operation `op` and input selection `sels`;
`evalD_denseGate`: on wires `V` with `|sels| = |V|` and exactly one first/second input selected,
it appends `op (V_a) (V_b)`.  `mcDense` encodes a multi-output circuit followed by one copy gate per
output, so that the outputs are the last wires (`evalD_mcDense`).
-/

namespace Pnp.Relativize.Struct

open Function

/-! ## Semantics on bits -/

/-- Truth table lookup: `t[2u + v]`. -/
def ttb (t₀ t₁ t₂ t₃ u v : Bool) : Bool := if u then (if v then t₃ else t₂) else (if v then t₁ else t₀)

/-- Dense circuit evaluation on raw bits. -/
def evalD : Str → Str → Str → Bool → Bool → Str
  | [], V, S, _, _ => S.reverse ++ V
  | false :: G, V, S, u, v =>
    match V with
    | [] => evalD (G.drop 2) [] S u v
    | x :: V => evalD (G.drop 2) V (x :: S) (u || (G.getD 0 false && x)) (v || (G.getD 1 false && x))
  | true :: G, V, S, u, v =>
    evalD (G.drop 4) (S.reverse ++ ttb (G.getD 0 false) (G.getD 1 false) (G.getD 2 false)
      (G.getD 3 false) u v :: V) [] false false
termination_by G => G.length
decreasing_by all_goals simp

theorem evalD_nil (V S : Str) (u v : Bool) : evalD [] V S u v = S.reverse ++ V := by
  rw [evalD]

theorem evalD_wire_nil (a b : Bool) (G S : Str) (u v : Bool) :
    evalD (false :: a :: b :: G) [] S u v = evalD G [] S u v := by
  rw [evalD]; simp

theorem evalD_wire (a b x : Bool) (G V S : Str) (u v : Bool) :
    evalD (false :: a :: b :: G) (x :: V) S u v = evalD G V (x :: S) (u || (a && x)) (v || (b && x)) := by
  rw [evalD]; simp

theorem evalD_gate (t₀ t₁ t₂ t₃ : Bool) (G V S : Str) (u v : Bool) :
    evalD (true :: t₀ :: t₁ :: t₂ :: t₃ :: G) V S u v =
      evalD G (S.reverse ++ ttb t₀ t₁ t₂ t₃ u v :: V) [] false false := by
  rw [evalD]; simp

theorem length_evalD_le : ∀ (G V S : Str) (u v : Bool),
    (evalD G V S u v).length ≤ V.length + S.length + G.length
  | [], V, S, u, v => by rw [evalD_nil]; simp; omega
  | false :: G, V, S, u, v => by
    cases V with
    | nil =>
      rw [evalD]
      have := length_evalD_le (G.drop 2) [] S u v
      simp only [List.length_drop, List.length_nil, List.length_cons] at this ⊢; omega
    | cons x V =>
      rw [evalD]
      have := length_evalD_le (G.drop 2) V (x :: S) (u || (G.getD 0 false && x))
        (v || (G.getD 1 false && x))
      simp only [List.length_drop, List.length_cons] at this ⊢; omega
  | true :: G, V, S, u, v => by
    rw [evalD]
    have := length_evalD_le (G.drop 4) (S.reverse ++ ttb (G.getD 0 false) (G.getD 1 false)
      (G.getD 2 false) (G.getD 3 false) u v :: V) [] false false
    simp only [List.length_drop, List.length_append, List.length_reverse, List.length_cons,
      List.length_nil] at this ⊢; omega
termination_by G => G.length
decreasing_by all_goals simp

/-! ## The program -/

section Prog

variable (g v s u w : ℕ)

/-- Set a flag (`[]` or `[true]`) to `[true]`. -/
def setF (k : ℕ) : Cmd := .pop k (.push k true) (.push k true) (.push k true)

/-- Scan wire value `x` with selection bits `a`, `b`. -/
def scC (a b x : Bool) : Cmd :=
  .seq (.push s x) (.seq (if a && x then setF u else .skip) (if b && x then setF w else .skip))

/-- Wire token, after reading `a`, `b`: scan the next wire if there is one. -/
def wB (a b : Bool) : Cmd := .pop v .skip (scC s u w a b false) (scC s u w a b true)

/-- Wire token, after reading `a`. -/
def wA (a : Bool) : Cmd := .pop g (wB v s u w a false) (wB v s u w a false) (wB v s u w a true)

/-- Wire token. -/
def wireT : Cmd := .pop g (wA g v s u w false) (wA g v s u w false) (wA g v s u w true)

/-- Pop `j` bits of `g`. -/
def dropN : ℕ → Cmd
  | 0 => .skip
  | j + 1 => .pop g (dropN j) (dropN j) (dropN j)

/-- Pop `j` bits of `g` and push the one at offset `k` (`false` if missing) onto `s`. -/
def pk : ℕ → ℕ → Cmd
  | 0, _ => .push s false
  | j + 1, 0 => .pop g (.seq (.push s false) (dropN g j)) (.seq (.push s false) (dropN g j))
      (.seq (.push s true) (dropN g j))
  | j + 1, k + 1 => .pop g (pk j k) (pk j k) (pk j k)

/-- Gate end, after reading the flags. -/
def gF (x y : Bool) : Cmd := .seq (pk g s 4 ((if x then 2 else 0) + (if y then 1 else 0))) (move s v)

/-- Gate end, after reading the first flag. -/
def gW (x : Bool) : Cmd := .pop w (gF g v s x false) (gF g v s x true) (gF g v s x true)

/-- Gate end. -/
def gateT : Cmd := .pop u (gW g v s w false) (gW g v s w true) (gW g v s w true)

/-- One token. -/
def evBody : Cmd := .pop g .brk (wireT g v s u w) (gateT g v s u w)

/-- **The dense circuit evaluator.** -/
def evalCmd : Cmd :=
  .seq (.loop (evBody g v s u w)) (.seq (move s v) (.seq (drain u) (drain w)))

end Prog

/-! ## Correctness -/

/-- A flag stack. -/
def fl (b : Bool) : Str := if b then [true] else []

section Correct

variable {g v s u w : ℕ} (hgv : g ≠ v) (hgs : g ≠ s) (hgu : g ≠ u) (hgw : g ≠ w) (hvs : v ≠ s)
  (hvu : v ≠ u) (hvw : v ≠ w) (hsu : s ≠ u) (hsw : s ≠ w) (huw : u ≠ w)

/-- `σ'` agrees with `σ` outside the stacks `g, v, s, u, w`. -/
def Frame (g v s u w : ℕ) (σ σ' : ℕ → Str) : Prop :=
  ∀ j, j ≠ g → j ≠ v → j ≠ s → j ≠ u → j ≠ w → σ' j = σ j

theorem Frame.refl (σ : ℕ → Str) : Frame g v s u w σ σ := fun _ _ _ _ _ _ => rfl

theorem Frame.trans {σ₁ σ₂ σ₃ : ℕ → Str} (h₁ : Frame g v s u w σ₁ σ₂)
    (h₂ : Frame g v s u w σ₂ σ₃) : Frame g v s u w σ₁ σ₃ :=
  fun j a b c d e => (h₂ j a b c d e).trans (h₁ j a b c d e)

theorem Frame.update {σ σ' : ℕ → Str} (h : Frame g v s u w σ σ') {k : ℕ}
    (hk : k = g ∨ k = v ∨ k = s ∨ k = u ∨ k = w) (l : Str) :
    Frame g v s u w σ (Function.update σ' k l) := by
  intro j a b c d e
  rw [update_of_ne (by rcases hk with rfl | rfl | rfl | rfl | rfl <;> assumption)]
  exact h j a b c d e

theorem exec_setF {k : ℕ} (σ : ℕ → Str) (b : Bool) (hk : σ k = fl b) :
    Exec (setF k) σ (.norm (update σ k [true])) 2 := by
  cases b
  · exact (Exec.pop_nil hk ((Exec.push k true σ).cast (by rw [hk]; rfl) rfl))
  · have hk' : σ k = true :: [] := hk
    refine (Exec.pop_cons hk' ?_).cast rfl rfl
    simp only [if_true]
    exact (Exec.push k true _).cast (by simp) rfl

include hgv hgs hgu hgw hvs hvu hvw hsu hsw huw in
/-- Scanning one wire value. -/
theorem exec_scC (a b x : Bool) (σ : ℕ → Str) (u₀ w₀ : Bool) (hu : σ u = fl u₀)
    (hw : σ w = fl w₀) :
    ∃ σ', ExecLe (scC s u w a b x) σ (.norm σ') 5 ∧ σ' s = x :: σ s ∧
      σ' u = fl (u₀ || (a && x)) ∧ σ' w = fl (w₀ || (b && x)) ∧ σ' g = σ g ∧ σ' v = σ v ∧
      Frame g v s u w σ σ' := by
  set σ1 := update σ s (x :: σ s)
  have h1 : σ1 u = fl u₀ := by simp [σ1, Ne.symm hsu, hu]
  have h1w : σ1 w = fl w₀ := by simp [σ1, Ne.symm hsw, hw]
  -- the first flag
  obtain ⟨σ2, h2, h2u, h2fr, h2w⟩ : ∃ σ2, ExecLe (if a && x then setF u else .skip) σ1 (.norm σ2) 2 ∧
      σ2 u = fl (u₀ || (a && x)) ∧ (∀ j, j ≠ u → σ2 j = σ1 j) ∧ σ2 w = fl w₀ := by
    by_cases hax : (a && x) = true
    · refine ⟨_, ExecLe.of (by rw [if_pos hax]; exact exec_setF σ1 u₀ h1), ?_, ?_, ?_⟩
      · simp [hax, fl]
      · intro j hj; simp [hj]
      · simp [Ne.symm huw, h1w]
    · refine ⟨σ1, (ExecLe.of (by rw [if_neg hax]; exact Exec.skip σ1)).mono (by omega), ?_,
        fun _ _ => rfl, h1w⟩
      simp only [Bool.not_eq_true] at hax; simp [hax, h1]
  obtain ⟨σ3, h3, h3w, h3fr⟩ : ∃ σ3, ExecLe (if b && x then setF w else .skip) σ2 (.norm σ3) 2 ∧
      σ3 w = fl (w₀ || (b && x)) ∧ (∀ j, j ≠ w → σ3 j = σ2 j) := by
    by_cases hbx : (b && x) = true
    · refine ⟨_, ExecLe.of (by rw [if_pos hbx]; exact exec_setF σ2 w₀ h2w), ?_, ?_⟩
      · simp [hbx, fl]
      · intro j hj; simp [hj]
    · refine ⟨σ2, (ExecLe.of (by rw [if_neg hbx]; exact Exec.skip σ2)).mono (by omega), ?_,
        fun _ _ => rfl⟩
      simp only [Bool.not_eq_true] at hbx; simp [hbx, h2w]
  refine ⟨σ3, ((ExecLe.of (Exec.push s x σ)).seq_norm (h2.seq_norm h3)).mono (by omega), ?_, ?_,
    h3w, ?_, ?_, ?_⟩
  · rw [h3fr s hsw, h2fr s hsu]; simp [σ1]
  · rw [h3fr u huw, h2u]
  · rw [h3fr g hgw, h2fr g hgu]; simp [σ1, hgs]
  · rw [h3fr v hvw, h2fr v hvu]; simp [σ1, hvs]
  · intro j a1 a2 a3 a4 a5
    rw [h3fr j a5, h2fr j a4]; simp [σ1, a3]

/-- Pop with default `false` on an empty stack. -/
theorem ExecLe.popD {k : ℕ} {C : Bool → Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ}
    (h : ExecLe (C ((σ k).getD 0 false)) (update σ k ((σ k).drop 1)) r T) :
    ExecLe (.pop k (C false) (C false) (C true)) σ r (T + 1) := by
  cases hk : σ k with
  | nil =>
    rw [hk] at h
    simp only [List.getD_nil, List.drop_nil] at h
    rw [← hk, update_eq_self] at h
    exact ExecLe.pop_nil hk h
  | cons b l =>
    rw [hk] at h
    simp only [List.getD_cons_zero, List.drop_succ_cons, List.drop_zero] at h
    refine ExecLe.pop_cons hk ?_
    cases b <;> simpa using h

theorem exec_dropN (k : ℕ) : ∀ (j : ℕ) (σ : ℕ → Str),
    ExecLe (dropN k j) σ (.norm (update σ k ((σ k).drop j))) (j + 1)
  | 0, σ => (ExecLe.of (Exec.skip σ)).cast (by simp) (by omega)
  | j + 1, σ => by
    have h := exec_dropN k j (update σ k ((σ k).drop 1))
    simp only [update_self, update_idem, List.drop_drop] at h
    have h' := ExecLe.popD (C := fun _ => dropN k j) (σ := σ) (by
      simpa [Nat.add_comm] using h)
    exact h'

theorem getD_drop_one (l : Str) (k : ℕ) : (l.drop 1).getD k false = l.getD (k + 1) false := by
  cases l <;> simp

theorem getD_drop_two (l : Str) (k : ℕ) : (l.drop 2).getD k false = l.getD (k + 2) false := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp

theorem exec_pk (hgs : g ≠ s) : ∀ (j k : ℕ), k < j → ∀ σ : ℕ → Str,
    ExecLe (pk g s j k) σ
      (.norm (update (update σ g ((σ g).drop j)) s ((σ g).getD k false :: σ s))) (j + 3)
  | 0, k, hk, _ => absurd hk (by omega)
  | j + 1, 0, _, σ => by
    refine (ExecLe.popD (C := fun b => .seq (.push s b) (dropN g j)) (σ := σ) (T := j + 2) ?_).cast
      rfl (by omega)
    set σ1 := update σ g ((σ g).drop 1)
    have h1 := ExecLe.of (Exec.push s ((σ g).getD 0 false) σ1)
    have h2 := exec_dropN g j (update σ1 s ((σ g).getD 0 false :: σ1 s))
    refine (h1.seq_norm h2).cast ?_ (by omega)
    congr 1; funext i
    simp only [σ1, update_apply]
    split_ifs <;> simp_all [List.drop_drop, Nat.add_comm]
  | j + 1, k + 1, hk, σ => by
    refine (ExecLe.popD (C := fun _ => pk g s j k) (σ := σ) (T := j + 3) ?_).cast rfl (by omega)
    have h := exec_pk hgs j k (by omega) (update σ g ((σ g).drop 1))
    refine h.cast ?_ le_rfl
    congr 1; funext i
    simp only [update_apply]
    split_ifs <;> simp_all [List.drop_drop, Nat.add_comm, getD_drop_one]

/-- Index of the truth-table entry. -/
def tix (x y : Bool) : ℕ := (if x then 2 else 0) + (if y then 1 else 0)

theorem ttb_eq (G : Str) (x y : Bool) :
    ttb (G.getD 0 false) (G.getD 1 false) (G.getD 2 false) (G.getD 3 false) x y =
      G.getD (tix x y) false := by
  cases x <;> cases y <;> rfl

include hgs hvs hgv in
theorem exec_gF (x y : Bool) (σ : ℕ → Str) :
    ∃ σ', ExecLe (gF g v s x y) σ (.norm σ') (2 * (σ s).length + 11) ∧
      σ' g = (σ g).drop 4 ∧ σ' v = (σ s).reverse ++ (σ g).getD (tix x y) false :: σ v ∧
      σ' s = [] ∧ ∀ j, j ≠ g → j ≠ v → j ≠ s → σ' j = σ j := by
  have h1 := exec_pk hgs 4 (tix x y) (by cases x <;> cases y <;> simp [tix]) σ
  set σ1 := update (update σ g ((σ g).drop 4)) s ((σ g).getD (tix x y) false :: σ s)
  have e1 : σ1 s = (σ g).getD (tix x y) false :: σ s := by simp [σ1]
  have h2 := ExecLe.of (exec_move hvs.symm _ σ1 e1)
  refine ⟨_, (h1.seq_norm h2).mono (by simp; omega), ?_, ?_, ?_, ?_⟩
  · simp [σ1, hgv, hgs, update_apply]
  · simp [σ1, hvs, hvs.symm, hgv, hgv.symm, update_apply]
  · simp [σ1, hvs, hvs.symm, update_apply]
  · intro j a b c; simp [σ1, a, b, c, update_apply]

include hgs hvs hgv hgw hvw hsw in
theorem exec_gW (x : Bool) (σ : ℕ → Str) (w₀ : Bool) (hw : σ w = fl w₀) :
    ∃ σ', ExecLe (gW g v s w x) σ (.norm σ') (2 * (σ s).length + 12) ∧
      σ' g = (σ g).drop 4 ∧ σ' v = (σ s).reverse ++ (σ g).getD (tix x w₀) false :: σ v ∧
      σ' s = [] ∧ σ' w = [] ∧ ∀ j, j ≠ g → j ≠ v → j ≠ s → j ≠ w → σ' j = σ j := by
  cases w₀
  · obtain ⟨σ', h, h1, h2, h3, h4⟩ := exec_gF hgv hgs hvs x false σ
    refine ⟨σ', ExecLe.pop_nil hw h, h1, h2, h3, ?_, fun j a b c _ => h4 j a b c⟩
    rw [h4 w hgw.symm hvw.symm hsw.symm, hw]; rfl
  · have hw' : σ w = true :: [] := hw
    set σ1 := update σ w []
    obtain ⟨σ', h, h1, h2, h3, h4⟩ := exec_gF hgv hgs hvs x true σ1
    have e : ∀ j, j ≠ w → σ1 j = σ j := fun j hj => update_of_ne hj _ _
    refine ⟨σ', ExecLe.pop_cons hw' (by simpa using h.cast rfl (by rw [e s hsw])), ?_, ?_, h3,
      ?_, ?_⟩
    · rw [h1, e g hgw]
    · rw [h2, e g hgw, e s hsw, e v hvw]
    · rw [h4 w hgw.symm hvw.symm hsw.symm]; simp [σ1]
    · intro j a b c d; rw [h4 j a b c, e j d]

include hgs hvs hgv hgw hvw hsw hgu hvu hsu huw in
theorem exec_gateT (σ : ℕ → Str) (u₀ w₀ : Bool) (hu : σ u = fl u₀) (hw : σ w = fl w₀) :
    ∃ σ', ExecLe (gateT g v s u w) σ (.norm σ') (2 * (σ s).length + 13) ∧
      σ' g = (σ g).drop 4 ∧ σ' v = (σ s).reverse ++ (σ g).getD (tix u₀ w₀) false :: σ v ∧
      σ' s = [] ∧ σ' u = [] ∧ σ' w = [] ∧ Frame g v s u w σ σ' := by
  cases u₀
  · obtain ⟨σ', h, h1, h2, h3, h4, h5⟩ := exec_gW hgv hgs hgw hvs hvw hsw false σ w₀ hw
    refine ⟨σ', ExecLe.pop_nil hu h, h1, h2, h3, ?_, h4, fun j a b c _ d => h5 j a b c d⟩
    rw [h5 u hgu.symm hvu.symm hsu.symm huw, hu]; rfl
  · have hu' : σ u = true :: [] := hu
    set σ1 := update σ u []
    have e : ∀ j, j ≠ u → σ1 j = σ j := fun j hj => update_of_ne hj _ _
    obtain ⟨σ', h, h1, h2, h3, h4, h5⟩ := exec_gW hgv hgs hgw hvs hvw hsw true σ1 w₀
      (by rw [e w huw.symm, hw])
    refine ⟨σ', ExecLe.pop_cons hu' (by simpa using h.cast rfl (by rw [e s hsu])), ?_, ?_, h3,
      ?_, h4, ?_⟩
    · rw [h1, e g hgu]
    · rw [h2, e g hgu, e s hsu, e v hvu]
    · rw [h5 u hgu.symm hvu.symm hsu.symm huw]; simp [σ1]
    · intro j a b c d f; rw [h5 j a b c f, e j d]

/-- The machine state for the evaluator. -/
def St (g v s u w : ℕ) (σ : ℕ → Str) (G V S : Str) (u₀ w₀ : Bool) : Prop :=
  σ g = G ∧ σ v = V ∧ σ s = S ∧ σ u = fl u₀ ∧ σ w = fl w₀

include hgs hvs hgv hgw hvw hsw hgu hvu hsu huw in
/-- One gate end. -/
theorem step_gate (σ : ℕ → Str) (G V S : Str) (u₀ w₀ : Bool)
    (h : St g v s u w σ (true :: G) V S u₀ w₀) :
    ∃ σ', ExecLe (evBody g v s u w) σ (.norm σ') (2 * S.length + 14) ∧ Frame g v s u w σ σ' ∧
      St g v s u w σ' (G.drop 4) (S.reverse ++ ttb (G.getD 0 false) (G.getD 1 false)
        (G.getD 2 false) (G.getD 3 false) u₀ w₀ :: V) [] false false := by
  obtain ⟨hG, hV, hS, hu, hw⟩ := h
  set σ1 := update σ g G
  have e : ∀ j, j ≠ g → σ1 j = σ j := fun j hj => update_of_ne hj _ _
  obtain ⟨σ', h, h1, h2, h3, h4, h5, h6⟩ := exec_gateT hgv hgs hgu hgw hvs hvu hvw hsu hsw huw σ1
    u₀ w₀ (by rw [e u hgu.symm, hu]) (by rw [e w hgw.symm, hw])
  refine ⟨σ', ExecLe.pop_cons hG (by simpa using h.cast rfl (by rw [e s hgs.symm, hS])),
    ?_, ?_, ?_, h3, ?_, ?_⟩
  · intro j a b c d f; rw [h6 j a b c d f, e j a]
  · rw [h1]; simp [σ1]
  · rw [h2, e s hgs.symm, e v hgv.symm, hS, hV, ttb_eq]; simp [σ1]
  · rw [h4]; rfl
  · rw [h5]; rfl

include hgs hvs hgv hgw hvw hsw hgu hvu hsu huw in
/-- One wire token, no wire left. -/
theorem step_wire_nil (σ : ℕ → Str) (G S : Str) (u₀ w₀ : Bool)
    (h : St g v s u w σ (false :: G) [] S u₀ w₀) :
    ∃ σ', ExecLe (evBody g v s u w) σ (.norm σ') 9 ∧ Frame g v s u w σ σ' ∧
      St g v s u w σ' (G.drop 2) [] S u₀ w₀ := by
  obtain ⟨hG, hV, hS, hu, hw⟩ := h
  refine ⟨update σ g (G.drop 2), ?_, ?_, ?_⟩
  · refine (ExecLe.pop_cons hG ?_).mono (show 5 + 1 ≤ 9 by omega)
    simp only [Bool.false_eq_true, if_false]
    refine (ExecLe.popD (C := fun a => wA g v s u w a) ?_)
    simp only [update_self, update_idem]
    unfold wA
    refine (ExecLe.popD (C := fun b => wB v s u w (G.getD 0 false) b) (T := 3) ?_)
    simp only [update_self, update_idem, List.drop_drop]
    refine (ExecLe.pop_nil (by simp [hgv.symm, hV]) (ExecLe.of (Exec.skip _))).cast ?_ (by omega)
    rfl
  · exact (Frame.refl σ).update (Or.inl rfl) _
  · refine ⟨by simp, ?_, ?_, ?_, ?_⟩ <;> simp [hgv.symm, hgs.symm, hgu.symm, hgw.symm, hV, hS, hu, hw]

include hgs hvs hgv hgw hvw hsw hgu hvu hsu huw in
/-- One wire token scanning wire `x`. -/
theorem step_wire_cons (σ : ℕ → Str) (G V S : Str) (x : Bool) (u₀ w₀ : Bool)
    (h : St g v s u w σ (false :: G) (x :: V) S u₀ w₀) :
    ∃ σ', ExecLe (evBody g v s u w) σ (.norm σ') 9 ∧ Frame g v s u w σ σ' ∧
      St g v s u w σ' (G.drop 2) V (x :: S) (u₀ || (G.getD 0 false && x))
        (w₀ || (G.getD 1 false && x)) := by
  obtain ⟨hG, hV, hS, hu, hw⟩ := h
  set σ1 := update (update σ g (G.drop 2)) v V
  have e : ∀ j, j ≠ g → j ≠ v → σ1 j = σ j := fun j a b => by simp [σ1, a, b]
  obtain ⟨σ', h, h1, h2, h3, h4, h5, h6⟩ := exec_scC hgv hgs hgu hgw hvs hvu hvw hsu hsw huw
    (G.getD 0 false) (G.getD 1 false) x σ1 u₀ w₀ (by rw [e u hgu.symm hvu.symm, hu])
    (by rw [e w hgw.symm hvw.symm, hw])
  refine ⟨σ', ?_, ?_, ?_⟩
  · refine (ExecLe.pop_cons hG ?_).mono (show 8 + 1 ≤ 9 by omega)
    simp only [Bool.false_eq_true, if_false]
    refine (ExecLe.popD (C := fun a => wA g v s u w a) ?_)
    simp only [update_self, update_idem]
    unfold wA
    refine (ExecLe.popD (C := fun b => wB v s u w (G.getD 0 false) b) (T := 6) ?_)
    simp only [update_self, update_idem, List.drop_drop, getD_drop_one]
    have hv : update σ g (List.drop (1 + 1) G) v = x :: V := by simp [hgv.symm, hV]
    refine ExecLe.pop_cons hv ?_
    have : update (update σ g (List.drop (1 + 1) G)) v V = σ1 := rfl
    cases x <;> simpa [this] using h
  · intro j a b c d f; rw [h6 j a b c d f, e j a b]
  · refine ⟨?_, ?_, ?_, h2, h3⟩
    · rw [h4]; simp [σ1, hgv, update_apply]
    · rw [h5]; simp [σ1]
    · rw [h1, e s hgs.symm hvs.symm, hS]

/-- Time bound of the evaluation loop. -/
def evBnd (G V S : Str) : ℕ := (G.length + 1) * (2 * (V.length + S.length + G.length) + 40)

theorem evBnd_step {a a' m m' : ℕ} (ha : a' < a) (hm : m' ≤ m + 1) (hmc : m' + a' ≤ m + a)
    (c : ℕ) (hc : c ≤ 2 * m + 14) :
    c + (a' + 1) * (2 * (m' + a') + 40) ≤ (a + 1) * (2 * (m + a) + 40) := by
  have h1 : (a' + 1) * (2 * (m' + a') + 40) ≤ a * (2 * (m + a) + 40) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

include hgs hvs hgv hgw hvw hsw hgu hvu hsu huw in
/-- **The evaluation loop.** -/
theorem exec_evLoop : ∀ (n : ℕ) (G : Str), G.length = n → ∀ (V S : Str) (u₀ w₀ : Bool)
    (σ : ℕ → Str), St g v s u w σ G V S u₀ w₀ →
    ∃ σ', ExecLe (.loop (evBody g v s u w)) σ (.norm σ') (evBnd G V S) ∧
      Frame g v s u w σ σ' ∧ σ' g = [] ∧ (σ' s).reverse ++ σ' v = evalD G V S u₀ w₀ ∧
      (∃ b, σ' u = fl b) ∧ (∃ b, σ' w = fl b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn V S u₀ w₀ σ hst
  match G, hst with
  | [], hst =>
    obtain ⟨hG, hV, hS, hu, hw⟩ := hst
    refine ⟨σ, ?_, Frame.refl σ, hG, by rw [hS, hV, evalD_nil], ⟨u₀, hu⟩, ⟨w₀, hw⟩⟩
    exact ((ExecLe.pop_nil hG (ExecLe.of (Exec.brk σ))).loop_brk).mono
      (by simp [evBnd] <;> omega)
  | false :: G, hst =>
    cases V with
    | nil =>
      obtain ⟨σ1, h1, f1, s1⟩ := step_wire_nil hgv hgs hgu hgw hvs hvu hvw hsu hsw huw σ G S u₀ w₀ hst
      obtain ⟨σ2, h2, f2, e2, e3, e4, e5⟩ := ih (G.drop 2).length (by simp at hn ⊢ <;> omega) _ rfl
        [] S u₀ w₀ σ1 s1
      refine ⟨σ2, (ExecLe.loop_norm h1 h2).mono ?_, f1.trans f2, e2, ?_, e4, e5⟩
      · unfold evBnd
        exact evBnd_step (by simp) (by simp) (by simp <;> omega) 9 (by omega)
      · rw [e3, evalD]
    | cons x V =>
      obtain ⟨σ1, h1, f1, s1⟩ := step_wire_cons hgv hgs hgu hgw hvs hvu hvw hsu hsw huw σ G V S x
        u₀ w₀ hst
      obtain ⟨σ2, h2, f2, e2, e3, e4, e5⟩ := ih (G.drop 2).length (by simp at hn ⊢ <;> omega) _ rfl
        V (x :: S) _ _ σ1 s1
      refine ⟨σ2, (ExecLe.loop_norm h1 h2).mono ?_, f1.trans f2, e2, ?_, e4, e5⟩
      · unfold evBnd
        exact evBnd_step (by simp) (by simp <;> omega) (by simp <;> omega) 9 (by omega)
      · rw [e3, evalD]
  | true :: G, hst =>
    obtain ⟨σ1, h1, f1, s1⟩ := step_gate hgv hgs hgu hgw hvs hvu hvw hsu hsw huw σ G V S u₀ w₀ hst
    obtain ⟨σ2, h2, f2, e2, e3, e4, e5⟩ := ih (G.drop 4).length (by simp at hn ⊢ <;> omega) _ rfl
      _ [] false false σ1 s1
    refine ⟨σ2, (ExecLe.loop_norm h1 h2).mono ?_, f1.trans f2, e2, ?_, e4, e5⟩
    · unfold evBnd
      exact evBnd_step (by simp) (by simp <;> omega) (by simp <;> omega) _ (by omega)
    · rw [e3, evalD]

theorem fl_length (b : Bool) : (fl b).length ≤ 1 := by cases b <;> simp [fl]

include hgs hvs hgv hgw hvw hsw hgu hvu hsu huw in
/-- **The dense circuit evaluator**: from empty scratch stacks, `evalCmd` leaves
`evalD G V [] false false` on `v`. -/
theorem exec_evalCmd (σ : ℕ → Str) (G V : Str) (hG : σ g = G) (hV : σ v = V) (hs : σ s = [])
    (hu : σ u = []) (hw : σ w = []) :
    ∃ σ', ExecLe (evalCmd g v s u w) σ (.norm σ')
        ((G.length + 1) * (2 * (V.length + G.length) + 40) + 2 * (V.length + G.length) + 20) ∧
      σ' v = evalD G V [] false false ∧ σ' g = [] ∧ σ' s = [] ∧ σ' u = [] ∧ σ' w = [] ∧
      Frame g v s u w σ σ' := by
  obtain ⟨σ1, h1, f1, e1, e2, ⟨b1, e3⟩, ⟨b2, e4⟩⟩ := exec_evLoop hgv hgs hgu hgw hvs hvu hvw hsu
    hsw huw _ G rfl V [] false false σ ⟨hG, hV, hs, hu, hw⟩
  have hlen : (σ1 s).length ≤ V.length + G.length := by
    have := length_evalD_le G V [] false false
    rw [← e2] at this; simp at this; omega
  have hm := exec_move hvs.symm (σ1 s) σ1 rfl
  set σ2 := update (update σ1 s []) v ((σ1 s).reverse ++ σ1 v)
  have hd1 := exec_drain u (σ2 u) σ2 rfl
  set σ3 := update σ2 u []
  have hd2 := exec_drain w (σ3 w) σ3 rfl
  have hu2 : σ2 u = fl b1 := by simp [σ2, hsu.symm, hvu.symm, e3]
  have hw3 : σ3 w = fl b2 := by simp [σ3, σ2, huw.symm, hsw.symm, hvw.symm, e4]
  refine ⟨update σ3 w [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (h1.seq_norm ((ExecLe.of hm).seq_norm ((ExecLe.of hd1).seq_norm (ExecLe.of hd2)))).mono ?_
    have := fl_length b1; have := fl_length b2
    rw [hu2, hw3]; simp only [evBnd, List.length_nil, add_zero] at *; omega
  · simp [σ3, σ2, hvw, hvu, e2]
  · simp [σ3, σ2, hgw, hgu, hgv, hgs, e1]
  · simp [σ3, σ2, hsw, hsu, hvs.symm]
  · simp [σ3, huw]
  · simp
  · intro j a b c d f
    simp [σ3, σ2, a, b, c, d, f]
    exact f1 j a b c d f

end Correct

end Pnp.Relativize.Struct

/-! ## Honest dense circuits -/

namespace Pnp.Relativize.Struct

open Pnp.Circuits Function

/-- A wire token. -/
def wtok (p : Bool × Bool) : Str := [false, p.1, p.2]

/-- The truth table of an operation. -/
def ttOf (op : Bool → Bool → Bool) : Str := [op false false, op false true, op true false, op true true]

/-- The code of a gate: one wire token per available wire, then the gate end. -/
def denseGate (op : Bool → Bool → Bool) (sels : List (Bool × Bool)) : Str :=
  sels.flatMap wtok ++ true :: ttOf op

/-- “Some selected wire is true” (first or second selection). -/
def anyS (f : Bool × Bool → Bool) (sels : List (Bool × Bool)) (V : Str) : Bool :=
  (sels.zip V).any (fun p => f p.1 && p.2)

theorem evalD_scan (G : Str) : ∀ (sels : List (Bool × Bool)) (V₁ V₂ S : Str) (u v : Bool),
    sels.length = V₁.length →
    evalD (sels.flatMap wtok ++ G) (V₁ ++ V₂) S u v =
      evalD G V₂ (V₁.reverse ++ S) (u || anyS Prod.fst sels V₁) (v || anyS Prod.snd sels V₁)
  | [], [], V₂, S, u, v, _ => by simp [anyS]
  | p :: sels, x :: V₁, V₂, S, u, v, h => by
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append, wtok, List.nil_append,
      List.cons_append]
    rw [evalD_wire, evalD_scan G sels V₁ V₂ (x :: S) _ _ (by simpa using h)]
    simp [anyS, Bool.or_assoc]
  | [], _ :: _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h

theorem ttb_ttOf (op : Bool → Bool → Bool) (x y : Bool) :
    ttb (op false false) (op false true) (op true false) (op true true) x y = op x y := by
  cases x <;> cases y <;> rfl

/-- **An honest gate** appends its value. -/
theorem evalD_denseGate (op : Bool → Bool → Bool) (sels : List (Bool × Bool)) (V G : Str)
    (h : sels.length = V.length) :
    evalD (denseGate op sels ++ G) V [] false false =
      evalD G (V ++ [op (anyS Prod.fst sels V) (anyS Prod.snd sels V)]) [] false false := by
  unfold denseGate ttOf
  have := evalD_scan (true :: op false false :: op false true :: op true false :: op true true :: G)
    sels V [] [] false false h
  rw [List.append_nil] at this
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [this, evalD_gate, ttb_ttOf]
  simp

/-- Selection of wires `a` and `b` among the wires `j, …, j + m - 1`. -/
def selsFrom (j m a b : ℕ) : List (Bool × Bool) :=
  (List.range' j m).map fun i => (decide (i = a), decide (i = b))

theorem length_selsFrom (j m a b : ℕ) : (selsFrom j m a b).length = m := by simp [selsFrom]

theorem anyS_selsFrom_fst_lt {a b : ℕ} : ∀ (V : Str) (j m : ℕ), a < j →
    anyS Prod.fst (selsFrom j m a b) V = false
  | [], j, m, _ => by simp [anyS]
  | _ :: _, _, 0, _ => by simp [anyS, selsFrom]
  | x :: V, j, m + 1, h => by
    have := anyS_selsFrom_fst_lt (a := a) (b := b) V (j + 1) m (by omega)
    simp only [anyS, selsFrom, List.range'_succ, List.map_cons, List.zip_cons_cons,
      List.any_cons] at this ⊢
    rw [this]; simp; omega

theorem anyS_selsFrom_snd_lt {a b : ℕ} : ∀ (V : Str) (j m : ℕ), b < j →
    anyS Prod.snd (selsFrom j m a b) V = false
  | [], j, m, _ => by simp [anyS]
  | _ :: _, _, 0, _ => by simp [anyS, selsFrom]
  | x :: V, j, m + 1, h => by
    have := anyS_selsFrom_snd_lt (a := a) (b := b) V (j + 1) m (by omega)
    simp only [anyS, selsFrom, List.range'_succ, List.map_cons, List.zip_cons_cons,
      List.any_cons] at this ⊢
    rw [this]; simp; omega

theorem anyS_selsFrom_fst {a b : ℕ} : ∀ (V : Str) (j : ℕ), j ≤ a → a < j + V.length →
    anyS Prod.fst (selsFrom j V.length a b) V = V.getD (a - j) false
  | [], j, h1, h2 => by simp at h2; omega
  | x :: V, j, h1, h2 => by
    have e : anyS Prod.fst (selsFrom j (x :: V).length a b) (x :: V) =
        ((decide (j = a)) && x || anyS Prod.fst (selsFrom (j + 1) V.length a b) V) := by
      simp [anyS, selsFrom, List.range'_succ]
    rw [e]
    by_cases hj : j = a
    · subst hj
      rw [anyS_selsFrom_fst_lt V (j + 1) V.length (by omega)]
      simp
    · rw [anyS_selsFrom_fst V (j + 1) (by omega) (by simp at h2; omega)]
      obtain ⟨t, rfl⟩ : ∃ t, a = j + 1 + t := ⟨a - j - 1, by omega⟩
      simp [hj, show j + 1 + t - j = t + 1 by omega]

theorem anyS_selsFrom_snd {a b : ℕ} : ∀ (V : Str) (j : ℕ), j ≤ b → b < j + V.length →
    anyS Prod.snd (selsFrom j V.length a b) V = V.getD (b - j) false
  | [], j, h1, h2 => by simp at h2; omega
  | x :: V, j, h1, h2 => by
    have e : anyS Prod.snd (selsFrom j (x :: V).length a b) (x :: V) =
        ((decide (j = b)) && x || anyS Prod.snd (selsFrom (j + 1) V.length a b) V) := by
      simp [anyS, selsFrom, List.range'_succ]
    rw [e]
    by_cases hj : j = b
    · subst hj
      rw [anyS_selsFrom_snd_lt V (j + 1) V.length (by omega)]
      simp
    · rw [anyS_selsFrom_snd V (j + 1) (by omega) (by simp at h2; omega)]
      obtain ⟨t, rfl⟩ : ∃ t, b = j + 1 + t := ⟨b - j - 1, by omega⟩
      simp [hj, show j + 1 + t - j = t + 1 by omega]

/-- An honest gate reading wires `a, b < |V|`. -/
theorem evalD_gate_ab (op : Bool → Bool → Bool) (a b : ℕ) (V G : Str) (ha : a < V.length)
    (hb : b < V.length) :
    evalD (denseGate op (selsFrom 0 V.length a b) ++ G) V [] false false =
      evalD G (V ++ [op (V.getD a false) (V.getD b false)]) [] false false := by
  rw [evalD_denseGate _ _ _ _ (length_selsFrom _ _ _ _), anyS_selsFrom_fst V 0 (by omega)
    (by omega), anyS_selsFrom_snd V 0 (by omega) (by omega)]
  simp

/-- The gates `0, …, k - 1` of `g` in dense form. -/
def gatesCode {n s : ℕ} (g : Gates n s) (k : ℕ) : Str :=
  (List.range k).flatMap fun i => denseGate (opOf g i) (selsFrom 0 (n + i) (inA g i) (inB g i))

theorem getD_range_map {f : ℕ → Bool} {N i : ℕ} (hi : i < N) :
    ((List.range N).map f).getD i false = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

theorem evalD_gatesCode {n s : ℕ} (x : Fin n → Bool) (g : Gates n s) :
    ∀ k ≤ s, ∀ G : Str, evalD (gatesCode g k ++ G) (List.ofFn x) [] false false =
      evalD G ((List.range (n + k)).map (wv x s g)) [] false false
  | 0, _, G => by
    simp only [gatesCode, List.range_zero, List.flatMap_nil, List.nil_append, Nat.add_zero]
    congr 1
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    simp at h₁
    exact (wv_input x s g h₁).symm
  | k + 1, hk, G => by
    have e : gatesCode g (k + 1) = gatesCode g k ++
        denseGate (opOf g k) (selsFrom 0 (n + k) (inA g k) (inB g k)) := by
      simp [gatesCode, List.range_succ, List.flatMap_append]
    rw [e, List.append_assoc, evalD_gatesCode x g k (by omega)]
    have hlen : ((List.range (n + k)).map (wv x s g)).length = n + k := by simp
    have ha := inA_lt g (show k < s by omega)
    have hb := inB_lt g (show k < s by omega)
    have := evalD_gate_ab (opOf g k) (inA g k) (inB g k) ((List.range (n + k)).map (wv x s g)) G
      (by omega) (by omega)
    rw [hlen] at this
    rw [this, getD_range_map ha, getD_range_map hb, ← wv_gate' x g (show k < s by omega),
      show n + (k + 1) = n + k + 1 by omega, List.range_succ, List.map_append]
    rfl

/-- Output wire `j` (junk beyond `m`). -/
def outW {n s m : ℕ} (o : Fin m → Fin (n + s)) (j : ℕ) : ℕ := if h : j < m then (o ⟨j, h⟩).val else 0

/-- Copy gates for the outputs `0, …, k - 1`. -/
def outCode {n s m : ℕ} (o : Fin m → Fin (n + s)) (k : ℕ) : Str :=
  (List.range k).flatMap fun t => denseGate (fun a _ => a) (selsFrom 0 (n + s + t) (outW o t) (outW o t))

theorem outW_lt {n s m : ℕ} (o : Fin m → Fin (n + s)) (j : ℕ) (hn : 0 < n + s) : outW o j < n + s := by
  unfold outW; split_ifs <;> simp [hn]

theorem evalD_outCode {n s m : ℕ} (o : Fin m → Fin (n + s)) (hn : 0 < n + s) (W : Str)
    (hW : W.length = n + s) :
    ∀ k ≤ m, ∀ G : Str, evalD (outCode o k ++ G) W [] false false =
      evalD G (W ++ (List.range k).map (fun t => W.getD (outW o t) false)) [] false false
  | 0, _, G => by simp [outCode]
  | k + 1, hk, G => by
    have e : outCode o (k + 1) = outCode o k ++
        denseGate (fun a _ => a) (selsFrom 0 (n + s + k) (outW o k) (outW o k)) := by
      simp [outCode, List.range_succ, List.flatMap_append]
    rw [e, List.append_assoc, evalD_outCode o hn W hW k (by omega)]
    set V := W ++ (List.range k).map (fun t => W.getD (outW o t) false)
    have hV : V.length = n + s + k := by simp [V, hW]
    have hlt := outW_lt o k hn
    have := evalD_gate_ab (fun a _ => a) (outW o k) (outW o k) V G (by omega) (by omega)
    rw [hV] at this
    rw [this]
    have hg : V.getD (outW o k) false = W.getD (outW o k) false := by
      simp only [V, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : outW o k < W.length)]
    rw [hg, List.range_succ, List.map_append, List.append_assoc]
    rfl

/-- **Dense code of a multi-output circuit**: the gates, then one copy gate per output. -/
def mcDense {n m s : ℕ} (C : MCircuit n m s) : Str := gatesCode C.1 s ++ outCode C.2 m

/-- An honest dense circuit leaves all wire values followed by the outputs. -/
theorem evalD_mcDense {n m s : ℕ} (C : MCircuit n m s) (hn : 0 < n) (x : Fin n → Bool) :
    evalD (mcDense C) (List.ofFn x) [] false false =
      (List.range (n + s)).map (wv x s C.1) ++
        (List.range m).map (fun t => if h : t < m then C.eval x ⟨t, h⟩ else false) := by
  unfold mcDense
  rw [evalD_gatesCode x C.1 s le_rfl, ← List.append_nil (outCode C.2 m),
    evalD_outCode C.2 (by omega) _ (by simp) m le_rfl, evalD_nil]
  simp only [List.reverse_nil, List.nil_append, List.append_nil]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [List.mem_range] at ht
  rw [getD_range_map (outW_lt C.2 t (by omega)), dif_pos ht]
  simp [outW, ht, MCircuit.eval, wires_eq_wv]

theorem length_denseGate (op : Bool → Bool → Bool) (sels : List (Bool × Bool)) :
    (denseGate op sels).length = 3 * sels.length + 5 := by
  have : ∀ l : List (Bool × Bool), (l.flatMap wtok).length = 3 * l.length := by
    intro l; induction l with
    | nil => simp
    | cons p l ih => simp [List.flatMap_cons, wtok, ih]; ring
  simp [denseGate, ttOf, this]

theorem length_gatesCode_le {n s : ℕ} (g : Gates n s) :
    ∀ k, (gatesCode g k).length ≤ k * (3 * (n + k) + 5)
  | 0 => by simp [gatesCode]
  | k + 1 => by
    have e : gatesCode g (k + 1) = gatesCode g k ++
        denseGate (opOf g k) (selsFrom 0 (n + k) (inA g k) (inB g k)) := by
      simp [gatesCode, List.range_succ, List.flatMap_append]
    rw [e, List.length_append, length_denseGate, length_selsFrom]
    have := length_gatesCode_le g k
    nlinarith

theorem length_outCode_le {n s m : ℕ} (o : Fin m → Fin (n + s)) :
    ∀ k, (outCode o k).length ≤ k * (3 * (n + s + k) + 5)
  | 0 => by simp [outCode]
  | k + 1 => by
    have e : outCode o (k + 1) = outCode o k ++
        denseGate (fun a _ => a) (selsFrom 0 (n + s + k) (outW o k) (outW o k)) := by
      simp [outCode, List.range_succ, List.flatMap_append]
    rw [e, List.length_append, length_denseGate, length_selsFrom]
    have := length_outCode_le o k
    nlinarith

theorem length_mcDense_le {n m s : ℕ} (C : MCircuit n m s) :
    (mcDense C).length ≤ (s + m) * (3 * (n + s + m) + 5) := by
  unfold mcDense
  rw [List.length_append]
  have h1 := length_gatesCode_le C.1 s
  have h2 := length_outCode_le C.2 m
  nlinarith

end Pnp.Relativize.Struct
