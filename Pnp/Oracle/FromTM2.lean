import Pnp.Oracle.Combinators
import Pnp.PPoly.TM2Local

/-!
# Simulating Mathlib's `FinTM2` machines by our stack machines

This file is the first half of `official P ⊆ P ∅`: an arbitrary Mathlib multi-stack machine
`tm : FinTM2` (with input alphabet `≃ Bool`) is compiled into one of our programs `Prog`
(`Pnp/Oracle/Machine.lean`), and one step of `tm` is simulated by a bounded number of steps of
the compiled program.

* **Symbols.**  Only finitely many symbols can ever appear on stack `k` (`Pnp.PPoly.A`): the
  pushable ones, plus the input alphabet.  We list them (`L k`) and write the symbol with index
  `i` as the *truncated unary* word `tu (N k) i = false^i true` (or `false^i` for the last index
  `N k - 1`).  For the input stack the list starts with the two input symbols, `N = 2`, and the
  codes are just `[true]` / `[false]`: the raw input already *is* the encoded input stack.
* **Stacks.**  Stack `k` of `tm` lives on our stack `sk k` (the input stack on stack `0`).
* **Control.**  The compiled program has one instruction for every state of a finite automaton
  `Q`: "execute statement `q` with variable `v`", "push a code", "read a code", "read the output".
  Jumps without stack effect use a query to the (empty) oracle with both targets equal.

Main result: `sim_step'`.  One step of `tm` (as the total step `Pnp.PPoly.step'`) takes at most
`Dm * B` steps of the program, preserving the encoding relation `Enc`.
-/

namespace Pnp.Relativize.FromTM2

open Turing Turing.TM2 Function Pnp.Relativize.Comb
open Pnp.PPoly (A A_finite StkInA step' pushSet pushable)

/-! ### Statements: subterms and size -/

section Generic

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- All subterms of a statement (including itself). -/
def subs : Stmt Γ Λ σ → List (Stmt Γ Λ σ)
  | s@(.push _ _ q) => s :: subs q
  | s@(.peek _ _ q) => s :: subs q
  | s@(.pop _ _ q) => s :: subs q
  | s@(.load _ q) => s :: subs q
  | s@(.branch _ q₁ q₂) => s :: (subs q₁ ++ subs q₂)
  | s@(.goto _) => [s]
  | .halt => [.halt]

theorem mem_subs_self (q : Stmt Γ Λ σ) : q ∈ subs q := by
  cases q <;> simp [subs]

/-- Length of the longest path through a statement (all node kinds count, `halt` is free). -/
def sz : Stmt Γ Λ σ → ℕ
  | .push _ _ q => sz q + 1
  | .peek _ _ q => sz q + 1
  | .pop _ _ q => sz q + 1
  | .load _ q => sz q + 1
  | .branch _ q₁ q₂ => max (sz q₁) (sz q₂) + 1
  | .goto _ => 1
  | .halt => 0

end Generic

/-! ### Truncated unary codes -/

/-- The truncated unary code of index `i` among `n` symbols. -/
def tu (n i : ℕ) : Str := List.replicate i false ++ (if i + 1 < n then [true] else [])

/-! ### Generic reading and pushing loops -/

section Loops

variable {p : Prog}

/-- A jump without effect on the stacks (a query to the empty oracle with equal targets). -/
def nop (t : ℕ) : Instr := .query 0 t t

theorem reach_nop {pc t : ℕ} {stk : ℕ → Str} (h : p[pc]? = some (nop t)) :
    Reach ∅ p pc stk t stk 1 :=
  Reach.of_step (by simp [step, h, nop])

/-- Reading a truncated unary code from stack `j`: `R c` is the reading state after `c` zeros,
`T i` the continuation for index `i`, `z` the continuation for an empty stack. -/
theorem reach_read {j n z : ℕ} {R T : ℕ → ℕ}
    (hR : ∀ c, c + 1 < n →
      p[R c]? = some (.pop j z (if c + 2 = n then T (c + 1) else R (c + 1)) (T c))) :
    ∀ d c i, i = c + d → i < n → c + 1 < n → ∀ (stk : ℕ → Str) (rest : Str),
      stk j = List.replicate d false ++ (if i + 1 < n then [true] else []) ++ rest →
      ∃ t ≤ d + 1, Reach ∅ p (R c) stk (T i) (update stk j rest) t := by
  intro d
  induction d with
  | zero =>
    intro c i hi hin hc stk rest hs
    have hic : c = i := by omega
    subst hic
    have hs' : stk j = true :: rest := by simp [hs, hc]
    refine ⟨1, le_rfl, ?_⟩
    simpa using reach_pop_cons (O := ∅) (σ := stk) (hR c hc) hs'
  | succ d ih =>
    intro c i hi hin hc stk rest hs
    have hs' : stk j = false :: (List.replicate d false ++
        (if i + 1 < n then [true] else []) ++ rest) := by
      rw [hs]; simp [List.replicate_succ]
    have h1 := reach_pop_cons (O := ∅) (σ := stk) (hR c hc) hs'
    simp only [Bool.false_eq_true, if_false] at h1
    by_cases hc2 : c + 2 = n
    · -- the last (unterminated) code: `i = n - 1`, nothing more to read
      rw [if_pos hc2] at h1
      have hd : d = 0 := by omega
      subst hd
      have hi1 : ¬ i + 1 < n := by omega
      refine ⟨1, by omega, ?_⟩
      refine h1.cast (by rw [hi]) ?_ rfl
      simp [hi1]
    · rw [if_neg hc2] at h1
      obtain ⟨t, ht, h2⟩ := ih (c + 1) i (by omega) hin (by omega)
        (update stk j (List.replicate d false ++ (if i + 1 < n then [true] else []) ++ rest))
        rest (by simp)
      refine ⟨1 + t, by omega, ?_⟩
      exact (h1.trans h2).cast rfl (by simp) rfl

/-- Pushing `i` zeros on stack `j` via the states `PU i, …, PU 0`, then continuing at `E`. -/
theorem reach_pushU {j E : ℕ} {PU : ℕ → ℕ} (m : ℕ)
    (h0 : p[PU 0]? = some (nop E))
    (hs : ∀ i, i < m → p[PU (i + 1)]? = some (.push j false (PU i))) :
    ∀ i, i ≤ m → ∀ (stk : ℕ → Str),
      Reach ∅ p (PU i) stk E (update stk j (List.replicate i false ++ stk j)) (i + 1) := by
  intro i
  induction i with
  | zero => intro _ stk; simpa using reach_nop (stk := stk) h0
  | succ i ih =>
    intro hi stk
    have h1 := reach_push (O := ∅) (σ := stk) (hs i (by omega))
    refine (h1.trans (ih (by omega) _)).cast rfl ?_ (by omega)
    simp [List.replicate_succ']

end Loops

/-! ### The compiled machine -/

section Compile

variable (tm : FinTM2)

attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin FinTM2.kFin FinTM2.kDecidableEq

open scoped Classical

/-- Statements of `tm`. -/
abbrev St := Stmt tm.Γ tm.Λ tm.σ

/-- Layout parameters of the compilation: a preferred order of the input symbols (they get the
first indices) and an offset for our stack numbers of the non-input stacks. -/
structure Layout where
  ℓ₀ : List (tm.Γ tm.k₀)
  o : ℕ

variable (ly : Layout tm) (e₁ : tm.Γ tm.k₁ ≃ Bool)

/-- A list of the reachable symbols of stack `k` (the input stack starts with the two input
symbols). -/
noncomputable def L : ∀ k, List (tm.Γ k) :=
  update (fun k => (A_finite tm k).toFinset.toList) tm.k₀
    (ly.ℓ₀ ++ (Finset.univ.toList : List (tm.Γ tm.k₀)).filter (· ∉ ly.ℓ₀))

/-- Number of codes used on stack `k`. -/
noncomputable def N (k : tm.K) : ℕ := max 2 (L tm ly k).length

/-- Index of a symbol. -/
noncomputable def ix (k : tm.K) (g : tm.Γ k) : ℕ := (L tm ly k).idxOf g

/-- Symbol with a given index. -/
noncomputable def sy (k : tm.K) (i : ℕ) : Option (tm.Γ k) := (L tm ly k)[i]?

/-- The code of a symbol. -/
noncomputable def code (k : tm.K) (g : tm.Γ k) : Str := tu (N tm ly k) (ix tm ly k g)

/-- The encoding of a whole stack (top first). -/
noncomputable def enc (k : tm.K) (s : List (tm.Γ k)) : Str := s.flatMap (code tm ly k)

theorem mem_L {k : tm.K} {g : tm.Γ k} (hg : g ∈ A tm k) : g ∈ L tm ly k := by
  by_cases hk : k = tm.k₀
  · subst hk
    simp only [L, update_self, List.mem_append, List.mem_filter, Finset.mem_toList,
      Finset.mem_univ, true_and, decide_eq_true_eq]
    tauto
  · simp only [L, update_of_ne hk, Finset.mem_toList, Set.Finite.mem_toFinset]
    exact hg

theorem ix_lt {k : tm.K} {g : tm.Γ k} (hg : g ∈ A tm k) : ix tm ly k g < N tm ly k :=
  lt_of_lt_of_le (List.idxOf_lt_length_iff.2 (mem_L tm ly hg)) (le_max_right _ _)

theorem sy_ix {k : tm.K} {g : tm.Γ k} (hg : g ∈ A tm k) : sy tm ly k (ix tm ly k g) = some g :=
  List.getElem?_idxOf (mem_L tm ly hg)

theorem two_le_N (k : tm.K) : 2 ≤ N tm ly k := le_max_left _ _

/-- Our stack holding stack `k` of `tm`. -/
noncomputable def sk (k : tm.K) : ℕ :=
  if k = tm.k₀ then 0 else ly.o + (Fintype.equivFin tm.K k : ℕ) + 1

theorem sk_injective : Injective (sk tm ly) := by
  intro a b h
  unfold sk at h
  by_cases ha : a = tm.k₀ <;> by_cases hb : b = tm.k₀
  · rw [ha, hb]
  · simp [ha, hb] at h
  · simp [ha, hb] at h
  · simp only [ha, hb, if_false, add_left_inj, add_right_inj] at h
    exact (Fintype.equivFin tm.K).injective (Fin.ext h)

theorem sk_k₀ : sk tm ly tm.k₀ = 0 := by simp [sk]

theorem sk_ne_zero {k : tm.K} (hk : k ≠ tm.k₀) : sk tm ly k ≠ 0 := by simp [sk, hk]

theorem o_lt_sk {k : tm.K} (hk : k ≠ tm.k₀) : ly.o < sk tm ly k := by simp [sk, hk]

/-- The encoding relation between the stacks of `tm` and our stacks. -/
def Enc (S : ∀ k, List (tm.Γ k)) (stk : ℕ → Str) : Prop :=
  ∀ k, stk (sk tm ly k) = enc tm ly k (S k)

theorem Enc.update {S : ∀ k, List (tm.Γ k)} {stk : ℕ → Str} (h : Enc tm ly S stk) (k : tm.K)
    (s : List (tm.Γ k)) :
    Enc tm ly (Function.update S k s) (Function.update stk (sk tm ly k) (enc tm ly k s)) := by
  intro k'
  by_cases hk : k' = k
  · subst hk; simp
  · rw [update_of_ne hk, update_of_ne ((sk_injective tm ly).ne hk)]
    exact h k'

/-- States of the finite control. -/
inductive Q
  | /-- execute statement `q` with variable `v` -/
    exec (q : St tm) (v : tm.σ)
  | /-- push the code of index `i` on stack `k`, then execute `q` with `v` -/
    pushC (k : tm.K) (i : ℕ) (q : St tm) (v : tm.σ)
  | /-- push `i` zeros on stack `k`, then execute `q` with `v` -/
    pushU (k : tm.K) (i : ℕ) (q : St tm) (v : tm.σ)
  | /-- reading a code for the `pop`/`peek` statement `q`, `c` zeros read so far -/
    rd (q : St tm) (v : tm.σ) (c : ℕ)
  | /-- reading the code of the output symbol -/
    out (c : ℕ)
  | /-- halt with answer `b` -/
    fin (b : Bool)

/-- All statements that can occur. -/
noncomputable def SL : List (St tm) :=
  .halt :: (Finset.univ.toList : List tm.Λ).flatMap fun l => subs (tm.m l)

/-- Bound on all code counts. -/
noncomputable def Nm : ℕ := Finset.univ.sup (N tm ly)

theorem N_le_Nm (k : tm.K) : N tm ly k ≤ Nm tm ly :=
  Finset.le_sup (f := N tm ly) (Finset.mem_univ k)

/-- All states of the finite control (the initial one first). -/
noncomputable def states : List (Q tm) :=
  .exec (tm.m tm.main) tm.initialState ::
    (((SL tm).flatMap fun q => (Finset.univ.toList : List tm.σ).map fun v => Q.exec q v) ++
      ((Finset.univ.toList : List tm.K).flatMap fun k => (List.range (Nm tm ly + 1)).flatMap
        fun i => (SL tm).flatMap fun q => (Finset.univ.toList : List tm.σ).flatMap fun v =>
          [Q.pushC k i q v, Q.pushU k i q v]) ++
      ((SL tm).flatMap fun q => (Finset.univ.toList : List tm.σ).flatMap fun v =>
        (List.range (Nm tm ly + 1)).map fun c => Q.rd q v c) ++
      ((List.range (Nm tm ly + 1)).map Q.out) ++ [Q.fin false, Q.fin true])

theorem exec_mem {q : St tm} (hq : q ∈ SL tm) (v : tm.σ) : Q.exec q v ∈ states tm ly := by
  simp only [states, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨q, hq, v, by simp, rfl⟩))))

theorem pushC_mem {q : St tm} (hq : q ∈ SL tm) (k : tm.K) {i : ℕ} (hi : i ≤ Nm tm ly)
    (v : tm.σ) : Q.pushC k i q v ∈ states tm ly := by
  simp only [states, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
  refine Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, by simp, i, by simp; omega, q, hq, v,
    by simp, by simp⟩))))

theorem pushU_mem {q : St tm} (hq : q ∈ SL tm) (k : tm.K) {i : ℕ} (hi : i ≤ Nm tm ly)
    (v : tm.σ) : Q.pushU k i q v ∈ states tm ly := by
  simp only [states, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
  refine Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, by simp, i, by simp; omega, q, hq, v,
    by simp, by simp⟩))))

theorem rd_mem {q : St tm} (hq : q ∈ SL tm) (v : tm.σ) {c : ℕ} (hc : c ≤ Nm tm ly) :
    Q.rd q v c ∈ states tm ly := by
  simp only [states, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr (Or.inl (Or.inl (Or.inr ⟨q, hq, v, by simp, c, by simp; omega, rfl⟩)))

theorem out_mem {c : ℕ} (hc : c ≤ Nm tm ly) : Q.out c ∈ states tm ly := by
  simp only [states, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr (Or.inl (Or.inr ⟨c, by simp; omega, rfl⟩))

theorem fin_mem (b : Bool) : Q.fin b ∈ states tm ly := by
  simp only [states, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
  cases b <;> simp

theorem m_mem (l : tm.Λ) : tm.m l ∈ SL tm := by
  simp only [SL, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨l, by simp, mem_subs_self _⟩

theorem halt_mem : (Stmt.halt : St tm) ∈ SL tm := by simp [SL]

theorem subs_subset_SL (l : tm.Λ) : ∀ r ∈ subs (tm.m l), r ∈ SL tm := by
  intro r hr
  simp only [SL, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨l, by simp, hr⟩

/-- Program counter of a state. -/
noncomputable def idx (s : Q tm) : ℕ := (states tm ly).idxOf s

/-- The answer for output index `i`. -/
noncomputable def ans (i : ℕ) : Bool :=
  match sy tm ly tm.k₁ i with
  | some g => e₁ g
  | none => false

/-- The instruction of a state. -/
noncomputable def act : Q tm → Instr
  | .exec (.push k f q) v => nop (idx tm ly (.pushC k (ix tm ly k (f v)) q v))
  | .exec (.peek k f q) v => nop (idx tm ly (.rd (.peek k f q) v 0))
  | .exec (.pop k f q) v => nop (idx tm ly (.rd (.pop k f q) v 0))
  | .exec (.load a q) v => nop (idx tm ly (.exec q (a v)))
  | .exec (.branch f q₁ q₂) v => nop (idx tm ly (.exec (cond (f v) q₁ q₂) v))
  | .exec (.goto f) v => nop (idx tm ly (.exec (tm.m (f v)) v))
  | .exec .halt _ => nop (idx tm ly (.out 0))
  | .pushC k i q v =>
      if i + 1 < N tm ly k then .push (sk tm ly k) true (idx tm ly (.pushU k i q v))
      else nop (idx tm ly (.pushU k i q v))
  | .pushU _ 0 q v => nop (idx tm ly (.exec q v))
  | .pushU k (i + 1) q v => .push (sk tm ly k) false (idx tm ly (.pushU k i q v))
  | .rd (.pop k f q) v c =>
      .pop (sk tm ly k) (idx tm ly (.exec q (f v none)))
        (if c + 2 = N tm ly k then idx tm ly (.exec q (f v (sy tm ly k (c + 1))))
          else idx tm ly (.rd (.pop k f q) v (c + 1)))
        (idx tm ly (.exec q (f v (sy tm ly k c))))
  | .rd (.peek k f q) v c =>
      .pop (sk tm ly k) (idx tm ly (.exec q (f v none)))
        (if c + 2 = N tm ly k then idx tm ly (.pushC k (c + 1) q (f v (sy tm ly k (c + 1))))
          else idx tm ly (.rd (.peek k f q) v (c + 1)))
        (idx tm ly (.pushC k c q (f v (sy tm ly k c))))
  | .rd _ _ _ => .halt false
  | .out c =>
      .pop (sk tm ly tm.k₁) (idx tm ly (.fin false))
        (if c + 2 = N tm ly tm.k₁ then idx tm ly (.fin (ans tm ly e₁ (c + 1)))
          else idx tm ly (.out (c + 1)))
        (idx tm ly (.fin (ans tm ly e₁ c)))
  | .fin b => .halt b

/-- The compiled program. -/
noncomputable def prog : Prog := (states tm ly).map (act tm ly e₁)

theorem prog_idx {s : Q tm} (hs : s ∈ states tm ly) :
    (prog tm ly e₁)[idx tm ly s]? = some (act tm ly e₁ s) := by
  simp [prog, idx, List.getElem?_idxOf hs]

theorem idx_init : idx tm ly (.exec (tm.m tm.main) tm.initialState) = 0 := by
  simp [idx, states]

/-! ### Pushing and reading codes -/

theorem reach_pushC {q : St tm} (hq : q ∈ SL tm) (k : tm.K) {i : ℕ} (hi : i < N tm ly k)
    (v : tm.σ) (stk : ℕ → Str) :
    ∃ t ≤ i + 2, Reach ∅ (prog tm ly e₁) (idx tm ly (.pushC k i q v)) stk
      (idx tm ly (.exec q v)) (update stk (sk tm ly k) (tu (N tm ly k) i ++ stk (sk tm ly k))) t := by
  have hiN : i ≤ Nm tm ly := by have := N_le_Nm tm ly k; omega
  have hU := reach_pushU (p := prog tm ly e₁) (j := sk tm ly k) (E := idx tm ly (.exec q v))
    (PU := fun i' => idx tm ly (.pushU k i' q v)) i
    (by rw [prog_idx tm ly e₁ (pushU_mem tm ly hq k (Nat.zero_le _) v)]; rfl)
    (fun i' hi' => by
      rw [prog_idx tm ly e₁ (pushU_mem tm ly hq k (by omega) v)]; rfl)
  have hC := prog_idx tm ly e₁ (pushC_mem tm ly hq k hiN v)
  by_cases ht : i + 1 < N tm ly k
  · have hC' : (prog tm ly e₁)[idx tm ly (.pushC k i q v)]? =
        some (.push (sk tm ly k) true (idx tm ly (.pushU k i q v))) := by
      rw [hC]; simp only [act, if_pos ht]
    have h1 := reach_push (O := ∅) (σ := stk) hC'
    refine ⟨1 + (i + 1), by omega, (h1.trans (hU i le_rfl _)).cast rfl ?_ rfl⟩
    simp [tu, ht]
  · have hC' : (prog tm ly e₁)[idx tm ly (.pushC k i q v)]? =
        some (nop (idx tm ly (.pushU k i q v))) := by
      rw [hC]; simp only [act, if_neg ht]
    have h1 := reach_nop (stk := stk) hC'
    refine ⟨1 + (i + 1), by omega, (h1.trans (hU i le_rfl _)).cast rfl ?_ rfl⟩
    simp [tu, ht]

theorem enc_cons (k : tm.K) (g : tm.Γ k) (s : List (tm.Γ k)) :
    enc tm ly k (g :: s) = tu (N tm ly k) (ix tm ly k g) ++ enc tm ly k s := rfl

theorem stkInA_update {S : ∀ k, List (tm.Γ k)} (hS : StkInA tm S) {k : tm.K}
    {s : List (tm.Γ k)} (hs : ∀ x ∈ s, x ∈ A tm k) : StkInA tm (update S k s) := by
  intro k' x hx
  by_cases hk : k' = k
  · subst hk; simp only [update_self] at hx; exact hs x hx
  · rw [update_of_ne hk] at hx; exact hS k' x hx

/-- Reading the top symbol `g` of stack `k` of `tm`. -/
theorem reach_top {k : tm.K} {z : ℕ} {R T : ℕ → ℕ}
    (hR : ∀ c, c + 1 < N tm ly k → (prog tm ly e₁)[R c]? = some
      (.pop (sk tm ly k) z (if c + 2 = N tm ly k then T (c + 1) else R (c + 1)) (T c)))
    {S : ∀ k, List (tm.Γ k)} {stk : ℕ → Str} (hS : StkInA tm S) (hE : Enc tm ly S stk)
    {g : tm.Γ k} {s : List (tm.Γ k)} (hSk : S k = g :: s) :
    ∃ t ≤ N tm ly k, Reach ∅ (prog tm ly e₁) (R 0) stk (T (ix tm ly k g))
      (update stk (sk tm ly k) (enc tm ly k s)) t := by
  have hg : g ∈ A tm k := hS k g (by simp [hSk])
  have hi := ix_lt tm ly hg
  have h2 := two_le_N tm ly k
  obtain ⟨t, ht, h⟩ := reach_read hR (ix tm ly k g) 0 (ix tm ly k g) (by omega) hi (by omega)
    stk (enc tm ly k s) (by rw [hE k, hSk, enc_cons, tu, List.append_assoc])
  exact ⟨t, by omega, h⟩

/-- The state representing a configuration of `tm`. -/
def rep (c : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) : Q tm := .exec (c.l.elim .halt tm.m) c.var

/-- Steps of our program per node of a statement. -/
noncomputable def B : ℕ := 2 * Nm tm ly + 4

theorem nop_of {s : Q tm} (hs : s ∈ states tm ly) {t : ℕ}
    (h : act tm ly e₁ s = nop t) : (prog tm ly e₁)[idx tm ly s]? = some (nop t) := by
  rw [prog_idx tm ly e₁ hs, h]

/-- **One statement.** Executing a statement `q` of `tm` (with `stepAux`) is simulated by at most
`sz q * B` steps of the compiled program. -/
theorem sim : ∀ (q : St tm) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) (stk : ℕ → Str),
    (∀ s ∈ pushSet q, s.2 ∈ A tm s.1) → (∀ r ∈ subs q, r ∈ SL tm) → StkInA tm S →
    Enc tm ly S stk →
    ∃ stk' t, Reach ∅ (prog tm ly e₁) (idx tm ly (.exec q v)) stk
      (idx tm ly (rep tm (stepAux q v S))) stk' t ∧ t ≤ sz q * B tm ly ∧
      Enc tm ly (stepAux q v S).stk stk'
  | .push k f q, v, S, stk, hP, hSub, hS, hE => by
    have hq : ∀ r ∈ subs q, r ∈ SL tm := fun r hr => hSub r (by simp [subs, hr])
    have hself : Stmt.push k f q ∈ SL tm := hSub _ (mem_subs_self _)
    have hqq : q ∈ SL tm := hq q (mem_subs_self q)
    have hg : f v ∈ A tm k := hP ⟨k, f v⟩ (Or.inl ⟨v, rfl⟩)
    have hi := ix_lt tm ly hg
    have hN := N_le_Nm tm ly k
    have h0 := reach_nop (stk := stk) (nop_of tm ly e₁ (exec_mem tm ly hself v) rfl)
    obtain ⟨t1, ht1, h1⟩ := reach_pushC tm ly e₁ hqq k hi v stk
    obtain ⟨stk', t2, h2, ht2, hE2⟩ := sim q v (update S k (f v :: S k))
      (update stk (sk tm ly k) (enc tm ly k (f v :: S k))) (fun s hs => hP s (Or.inr hs)) hq
      (stkInA_update tm hS (by
        intro x hx; simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hg
        · exact hS k x hx)) (hE.update tm ly k _)
    refine ⟨stk', 1 + t1 + t2, ?_, ?_, ?_⟩
    · simp only [stepAux]
      have e : update stk (sk tm ly k) (tu (N tm ly k) (ix tm ly k (f v)) ++ stk (sk tm ly k)) =
          update stk (sk tm ly k) (enc tm ly k (f v :: S k)) := by rw [hE k, enc_cons]
      rw [e] at h1
      exact (h0.trans h1).trans h2
    · simp only [sz, B] at ht2 ⊢; rw [Nat.add_mul]; nlinarith
    · simp only [stepAux]; exact hE2
  | .peek k f q, v, S, stk, hP, hSub, hS, hE => by
    have hq : ∀ r ∈ subs q, r ∈ SL tm := fun r hr => hSub r (by simp [subs, hr])
    have hself : Stmt.peek k f q ∈ SL tm := hSub _ (mem_subs_self _)
    have hqq : q ∈ SL tm := hq q (mem_subs_self q)
    have hN := N_le_Nm tm ly k
    have h2N := two_le_N tm ly k
    have h0 := reach_nop (stk := stk) (nop_of tm ly e₁ (exec_mem tm ly hself v) rfl)
    have hrd : ∀ c, c + 1 < N tm ly k → (prog tm ly e₁)[idx tm ly (.rd (.peek k f q) v c)]? =
        some (.pop (sk tm ly k) (idx tm ly (.exec q (f v none)))
          (if c + 2 = N tm ly k then idx tm ly (.pushC k (c + 1) q (f v (sy tm ly k (c + 1))))
            else idx tm ly (.rd (.peek k f q) v (c + 1)))
          (idx tm ly (.pushC k c q (f v (sy tm ly k c))))) := by
      intro c hc
      rw [prog_idx tm ly e₁ (rd_mem tm ly hself v (by omega))]; rfl
    rcases hSk : S k with _ | ⟨g, s⟩
    · -- empty stack
      have hnil : stk (sk tm ly k) = [] := by rw [hE k, hSk]; rfl
      have h1 := reach_pop_nil (O := ∅) (σ := stk) (hrd 0 (by omega)) hnil
      obtain ⟨stk', t2, h2, ht2, hE2⟩ := sim q (f v none) S stk hP hq hS hE
      refine ⟨stk', 1 + 1 + t2, ?_, ?_, ?_⟩
      · simp only [stepAux, hSk]; exact (h0.trans h1).trans h2
      · simp only [sz, B] at ht2 ⊢; rw [Nat.add_mul]; nlinarith
      · simp only [stepAux, hSk]; exact hE2
    · have hg : g ∈ A tm k := hS k g (by simp [hSk])
      have hi := ix_lt tm ly hg
      obtain ⟨t1, ht1, h1⟩ := reach_top tm ly e₁
        (R := fun c => idx tm ly (.rd (.peek k f q) v c))
        (T := fun i => idx tm ly (.pushC k i q (f v (sy tm ly k i)))) hrd hS hE hSk
      simp only [sy_ix tm ly hg] at h1
      obtain ⟨t3, ht3, h3⟩ := reach_pushC tm ly e₁ hqq k hi (f v (some g))
        (update stk (sk tm ly k) (enc tm ly k s))
      have e : update (update stk (sk tm ly k) (enc tm ly k s)) (sk tm ly k)
          (tu (N tm ly k) (ix tm ly k g) ++ update stk (sk tm ly k) (enc tm ly k s) (sk tm ly k)) =
          stk := by
        rw [update_idem, update_self, ← enc_cons, ← hSk, ← hE k, update_eq_self]
      rw [e] at h3
      obtain ⟨stk', t2, h2, ht2, hE2⟩ := sim q (f v (some g)) S stk hP hq hS hE
      refine ⟨stk', 1 + t1 + t3 + t2, ?_, ?_, ?_⟩
      · simp only [stepAux, hSk]; exact ((h0.trans h1).trans h3).trans h2
      · simp only [sz, B] at ht2 ⊢; rw [Nat.add_mul]; nlinarith
      · simp only [stepAux, hSk]; exact hE2
  | .pop k f q, v, S, stk, hP, hSub, hS, hE => by
    have hq : ∀ r ∈ subs q, r ∈ SL tm := fun r hr => hSub r (by simp [subs, hr])
    have hself : Stmt.pop k f q ∈ SL tm := hSub _ (mem_subs_self _)
    have hN := N_le_Nm tm ly k
    have h2N := two_le_N tm ly k
    have h0 := reach_nop (stk := stk) (nop_of tm ly e₁ (exec_mem tm ly hself v) rfl)
    have hrd : ∀ c, c + 1 < N tm ly k → (prog tm ly e₁)[idx tm ly (.rd (.pop k f q) v c)]? =
        some (.pop (sk tm ly k) (idx tm ly (.exec q (f v none)))
          (if c + 2 = N tm ly k then idx tm ly (.exec q (f v (sy tm ly k (c + 1))))
            else idx tm ly (.rd (.pop k f q) v (c + 1)))
          (idx tm ly (.exec q (f v (sy tm ly k c))))) := by
      intro c hc
      rw [prog_idx tm ly e₁ (rd_mem tm ly hself v (by omega))]; rfl
    rcases hSk : S k with _ | ⟨g, s⟩
    · have hnil : stk (sk tm ly k) = [] := by rw [hE k, hSk]; rfl
      have h1 := reach_pop_nil (O := ∅) (σ := stk) (hrd 0 (by omega)) hnil
      have hS' : update S k [] = S := by rw [← hSk, update_eq_self]
      obtain ⟨stk', t2, h2, ht2, hE2⟩ := sim q (f v none) S stk hP hq hS hE
      refine ⟨stk', 1 + 1 + t2, ?_, ?_, ?_⟩
      · simp only [stepAux, hSk]; simp only [List.head?_nil, List.tail_nil, hS']
        exact (h0.trans h1).trans h2
      · simp only [sz, B] at ht2 ⊢; rw [Nat.add_mul]; nlinarith
      · simp only [stepAux, hSk]; simp only [List.head?_nil, List.tail_nil, hS']; exact hE2
    · have hg : g ∈ A tm k := hS k g (by simp [hSk])
      obtain ⟨t1, ht1, h1⟩ := reach_top tm ly e₁
        (R := fun c => idx tm ly (.rd (.pop k f q) v c))
        (T := fun i => idx tm ly (.exec q (f v (sy tm ly k i)))) hrd hS hE hSk
      simp only [sy_ix tm ly hg] at h1
      obtain ⟨stk', t2, h2, ht2, hE2⟩ := sim q (f v (some g)) (update S k s)
        (update stk (sk tm ly k) (enc tm ly k s)) hP hq
        (stkInA_update tm hS (fun x hx => hS k x (by simp [hSk, hx]))) (hE.update tm ly k s)
      refine ⟨stk', 1 + t1 + t2, ?_, ?_, ?_⟩
      · simp only [stepAux, hSk]; exact (h0.trans h1).trans h2
      · simp only [sz, B] at ht2 ⊢; rw [Nat.add_mul]; nlinarith
      · simp only [stepAux, hSk]; exact hE2
  | .load a q, v, S, stk, hP, hSub, hS, hE => by
    have hq : ∀ r ∈ subs q, r ∈ SL tm := fun r hr => hSub r (by simp [subs, hr])
    have hself : Stmt.load a q ∈ SL tm := hSub _ (mem_subs_self _)
    have h0 := reach_nop (stk := stk) (nop_of tm ly e₁ (exec_mem tm ly hself v) rfl)
    obtain ⟨stk', t2, h2, ht2, hE2⟩ := sim q (a v) S stk hP hq hS hE
    refine ⟨stk', 1 + t2, ?_, ?_, ?_⟩
    · simp only [stepAux]; exact h0.trans h2
    · simp only [sz, B] at ht2 ⊢; rw [Nat.add_mul]; nlinarith
    · simp only [stepAux]; exact hE2
  | .branch f q₁ q₂, v, S, stk, hP, hSub, hS, hE => by
    have hself : Stmt.branch f q₁ q₂ ∈ SL tm := hSub _ (mem_subs_self _)
    have h0 := reach_nop (stk := stk) (nop_of tm ly e₁ (exec_mem tm ly hself v) rfl)
    cases hf : f v
    · have hq : ∀ r ∈ subs q₂, r ∈ SL tm := fun r hr => hSub r (by simp [subs, hr])
      obtain ⟨stk', t2, h2, ht2, hE2⟩ :=
        sim q₂ v S stk (fun s hs => hP s (Or.inr hs)) hq hS hE
      refine ⟨stk', 1 + t2, ?_, ?_, ?_⟩
      · simp only [stepAux, hf]; simp only [hf, cond_false] at h0; exact h0.trans h2
      · simp only [sz, B] at ht2 ⊢; rw [Nat.add_mul]
        have := le_max_right (sz q₁) (sz q₂); nlinarith
      · simp only [stepAux, hf]; exact hE2
    · have hq : ∀ r ∈ subs q₁, r ∈ SL tm := fun r hr => hSub r (by simp [subs, hr])
      obtain ⟨stk', t2, h2, ht2, hE2⟩ :=
        sim q₁ v S stk (fun s hs => hP s (Or.inl hs)) hq hS hE
      refine ⟨stk', 1 + t2, ?_, ?_, ?_⟩
      · simp only [stepAux, hf]; simp only [hf, cond_true] at h0; exact h0.trans h2
      · simp only [sz, B] at ht2 ⊢; rw [Nat.add_mul]
        have := le_max_left (sz q₁) (sz q₂); nlinarith
      · simp only [stepAux, hf]; exact hE2
  | .goto f, v, S, stk, _, hSub, _, hE => by
    have hself : Stmt.goto f ∈ SL tm := hSub _ (mem_subs_self _)
    have h0 := reach_nop (stk := stk) (nop_of tm ly e₁ (exec_mem tm ly hself v) rfl)
    exact ⟨stk, 1, h0, by simp [sz, B], hE⟩
  | .halt, v, S, stk, _, _, _, hE => ⟨stk, 0, Reach.refl, by simp, hE⟩

/-- Maximal size of the statements of `tm`. -/
noncomputable def Dm : ℕ := Finset.univ.sup fun l => sz (tm.m l)

theorem sz_le_Dm (l : tm.Λ) : sz (tm.m l) ≤ Dm tm :=
  Finset.le_sup (f := fun l => sz (tm.m l)) (Finset.mem_univ l)

/-- **One step of `tm`** (the total step `step'`) takes at most `Dm * B` steps. -/
theorem sim_step' (c : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) (stk : ℕ → Str) (hS : StkInA tm c.stk)
    (hE : Enc tm ly c.stk stk) :
    ∃ stk' t, Reach ∅ (prog tm ly e₁) (idx tm ly (rep tm c)) stk
      (idx tm ly (rep tm (step' tm c))) stk' t ∧ t ≤ Dm tm * B tm ly ∧
      Enc tm ly (step' tm c : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ).stk stk' := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none =>
    rw [Pnp.PPoly.step'_of_halted tm rfl]
    exact ⟨stk, 0, Reach.refl, Nat.zero_le _, hE⟩
  | some l =>
    rw [Pnp.PPoly.step'_eq_stepAux]
    obtain ⟨stk', t, h, ht, hE'⟩ := sim tm ly e₁ (tm.m l) v S stk
      (fun s hs => Or.inl (Set.mem_iUnion.2 ⟨l, hs⟩)) (subs_subset_SL tm l) hS hE
    exact ⟨stk', t, h, ht.trans (Nat.mul_le_mul_right _ (sz_le_Dm tm l)), hE'⟩

/-- **`n` steps of `tm`** take at most `n * (Dm * B)` steps. -/
theorem sim_iter (c₀ : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) (stk₀ : ℕ → Str)
    (hS : ∀ n, StkInA tm ((step' tm)^[n] c₀ : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ).stk)
    (hE : Enc tm ly c₀.stk stk₀) : ∀ n,
    ∃ stk' t, Reach ∅ (prog tm ly e₁) (idx tm ly (rep tm c₀)) stk₀
      (idx tm ly (rep tm ((step' tm)^[n] c₀))) stk' t ∧ t ≤ n * (Dm tm * B tm ly) ∧
      Enc tm ly ((step' tm)^[n] c₀ : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ).stk stk'
  | 0 => ⟨stk₀, 0, Reach.refl, by simp, hE⟩
  | n + 1 => by
    obtain ⟨stk₁, t₁, h₁, ht₁, hE₁⟩ := sim_iter c₀ stk₀ hS hE n
    obtain ⟨stk₂, t₂, h₂, ht₂, hE₂⟩ := sim_step' tm ly e₁ _ stk₁ (hS n) hE₁
    refine ⟨stk₂, t₁ + t₂, ?_, ?_, ?_⟩
    · rw [iterate_succ_apply']; exact h₁.trans h₂
    · rw [Nat.succ_mul]; omega
    · rw [iterate_succ_apply']; exact hE₂

/-- **A whole run.** If `tm` outputs `[g]` from input `l` within `T` steps, the compiled program
started (at address `0`) on an encoding of the initial stacks reaches the halting instruction
with answer `e₁ g` within `T * (Dm * B) + N + 1` steps. -/
theorem run_compiled {l : List (tm.Γ tm.k₀)} {g : tm.Γ tm.k₁} {T : ℕ}
    (ho : TM2OutputsInTime tm l (some [g]) T) (stk : ℕ → Str)
    (hE : Enc tm ly (initList tm l : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ).stk stk) :
    ∃ t σ', t ≤ T * (Dm tm * B tm ly) + 1 + N tm ly tm.k₁ ∧
      Reach ∅ (prog tm ly e₁) 0 stk (idx tm ly (.fin (e₁ g))) σ' t := by
  obtain ⟨hT, -⟩ := Pnp.PPoly.outputsInTime_step' tm ho
  have hS := Pnp.PPoly.iterate_step'_stkInA tm l
  obtain ⟨stk₁, t₁, h₁, ht₁, hE₁⟩ := sim_iter tm ly e₁ _ stk hS hE T
  rw [hT] at h₁ hE₁
  have hSf := hS T
  rw [hT] at hSf
  have hStop : (haltList tm [g] : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ).stk tm.k₁ = g :: [] := by
    simp [haltList]
  have hg : g ∈ A tm tm.k₁ := hSf tm.k₁ g (by rw [hStop]; simp)
  have hrep : rep tm (haltList tm [g]) = .exec .halt tm.initialState := rfl
  rw [hrep] at h₁
  have h₂ := reach_nop (stk := stk₁)
    (nop_of tm ly e₁ (exec_mem tm ly (halt_mem tm) tm.initialState) rfl)
  have hN := N_le_Nm tm ly tm.k₁
  obtain ⟨t₃, ht₃, h₃⟩ := reach_top tm ly e₁ (k := tm.k₁) (z := idx tm ly (.fin false))
    (R := fun c => idx tm ly (.out c)) (T := fun i => idx tm ly (.fin (ans tm ly e₁ i)))
    (fun c hc => by rw [prog_idx tm ly e₁ (out_mem tm ly (by omega))]; rfl) hSf hE₁ hStop
  have hans : ans tm ly e₁ (ix tm ly tm.k₁ g) = e₁ g := by
    simp only [ans, sy_ix tm ly hg]
  rw [hans] at h₃
  have h0 : idx tm ly (rep tm (initList tm l)) = 0 := idx_init tm ly
  rw [h0] at h₁
  exact ⟨t₁ + 1 + t₃, _, by omega, (h₁.trans h₂).trans h₃⟩

/-! ### The layout for the input alphabet `Bool` -/

section BoolLayout

variable (e₀ : tm.Γ tm.k₀ ≃ Bool)

/-- Input symbols `true, false` get the codes `[true]`, `[false]`; no stack offset. -/
def boolLayout : Layout tm := ⟨[e₀.symm true, e₀.symm false], 0⟩

theorem L_boolLayout : L tm (boolLayout tm e₀) tm.k₀ = [e₀.symm true, e₀.symm false] := by
  simp only [L, update_self, boolLayout]
  rw [List.filter_eq_nil_iff.2, List.append_nil]
  intro g _
  simp only [List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq, not_not]
  cases h : e₀ g
  · right; rw [← h, Equiv.symm_apply_apply]
  · left; rw [← h, Equiv.symm_apply_apply]

theorem N_k₀ : N tm (boolLayout tm e₀) tm.k₀ = 2 := by simp [N, L_boolLayout]

theorem code_k₀ (b : Bool) : code tm (boolLayout tm e₀) tm.k₀ (e₀.symm b) = [b] := by
  have hne : e₀.symm true ≠ e₀.symm false := by simp
  cases b
  · have : ix tm (boolLayout tm e₀) tm.k₀ (e₀.symm false) = 1 := by
      simp only [ix, L_boolLayout]
      rw [List.idxOf_cons_ne _ hne, List.idxOf_cons_eq _ rfl]
    simp [code, this, N_k₀, tu]
  · have : ix tm (boolLayout tm e₀) tm.k₀ (e₀.symm true) = 0 := by
      simp only [ix, L_boolLayout]
      exact List.idxOf_cons_eq _ rfl
    simp [code, this, N_k₀, tu]

theorem enc_k₀ (x : Str) : enc tm (boolLayout tm e₀) tm.k₀ (x.map e₀.symm) = x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simp only [enc, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [code_k₀, ih]; rfl

end BoolLayout

end Compile

end Pnp.Relativize.FromTM2
