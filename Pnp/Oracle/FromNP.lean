import Pnp.Oracle.FromTM2
import Pnp.Oracle.Shift

/-!
# Official `NP` ⊆ our `NP ∅`: building blocks

The verifier for an official `NP` language (checking relation decided by a Mathlib `FinTM2`
on `x # y`) works as follows on input `x` (stack `0`) and certificate `w` (stack `1`):

1. move `w` to stack `W` (reversing it) and `x` to stack `X` (reversing it), counting `|x|` on
   the counters of `Comb.pad`;
2. `Comb.pad k` writes a clock of `|x|^k` marks on stack `1`;
3. decode the certificate: a sequence of truncated unary codes of right-hand symbols of the
   pair alphabet, one clock mark per symbol (reject on any malformed code, wrong symbol or
   when the clock runs out); the codes are pushed on stack `Z`;
4. build the encoded input `x # y` of the official machine on stack `0`;
5. run the compiled official machine (`Pnp.Relativize.FromTM2`).

This file contains the generic loop lemmas.
-/

namespace Pnp.Relativize.FromNP

open Turing Function Pnp.Relativize.Comb Pnp.Relativize.FromTM2

/-! ### Truncated unary codes -/

theorem tu_ne_nil {n i : ℕ} (hi : i < n) (hn : 2 ≤ n) : tu n i ≠ [] := by
  unfold tu
  by_cases h : i + 1 < n
  · simp [h]
  · have : i ≠ 0 := by omega
    simp [h, this]

theorem tu_length_le {n i : ℕ} : (tu n i).length ≤ i + 1 := by
  unfold tu; split_ifs <;> simp

theorem tu_append_ne {n i i' : ℕ} {r r' : Str} (hlt : i < i') (hi' : i' < n) :
    tu n i ++ r ≠ tu n i' ++ r' := by
  obtain ⟨d, rfl⟩ : ∃ d, i' = i + d + 1 := ⟨i' - i - 1, by omega⟩
  have h1 : i + 1 < n := by omega
  simp only [tu, h1, if_true, List.replicate_add, List.append_assoc]
  simp only [List.replicate_succ', List.append_assoc]
  cases d <;> simp [List.replicate_succ]

/-- Truncated unary codes form a prefix code. -/
theorem tu_append_inj {n i i' : ℕ} {r r' : Str} (hi : i < n) (hi' : i' < n)
    (h : tu n i ++ r = tu n i' ++ r') : i = i' ∧ r = r' := by
  rcases lt_trichotomy i i' with hlt | rfl | hlt
  · exact absurd h (tu_append_ne hlt hi')
  · exact ⟨rfl, List.append_cancel_left h⟩
  · exact absurd h.symm (tu_append_ne hlt hi)

/-! ### Reading an arbitrary string as truncated unary codes -/

section Loops

variable {p : Prog}

/-- Reading from stack `j` with reading states `R c` (after `c` zeros): either a full code
`tu n i` is read (continuation `T i`), or the stack runs out after `c + d` zeros
(continuation `Z (c + d)`). -/
theorem reach_read_any {j n : ℕ} {R T Z : ℕ → ℕ}
    (hR : ∀ c, c + 1 < n →
      p[R c]? = some (.pop j (Z c) (if c + 2 = n then T (c + 1) else R (c + 1)) (T c))) :
    ∀ (s : Str) (c : ℕ) (σ : ℕ → Str), c + 1 < n → σ j = s →
      (∃ i rest t, c ≤ i ∧ i < n ∧ List.replicate c false ++ s = tu n i ++ rest ∧
        t ≤ n - c ∧ Reach ∅ p (R c) σ (T i) (update σ j rest) t) ∨
      (∃ d t, s = List.replicate d false ∧ c + d + 1 < n ∧ t ≤ n - c ∧
        Reach ∅ p (R c) σ (Z (c + d)) (update σ j []) t)
  | [], c, σ, hc, hs => by
    right
    have e : update σ j [] = σ := by rw [← hs, update_eq_self]
    exact ⟨0, 1, rfl, by omega, by omega, by
      rw [e]; simpa using reach_pop_nil (O := ∅) (hR c hc) hs⟩
  | true :: s, c, σ, hc, hs => by
    left
    refine ⟨c, s, 1, le_rfl, by omega, by simp [tu, hc], by omega, ?_⟩
    simpa using reach_pop_cons (O := ∅) (hR c hc) hs
  | false :: s, c, σ, hc, hs => by
    have h1 := reach_pop_cons (O := ∅) (σ := σ) (hR c hc) hs
    simp only [Bool.false_eq_true, if_false] at h1
    by_cases hc2 : c + 2 = n
    · rw [if_pos hc2] at h1
      left
      refine ⟨c + 1, s, 1, by omega, by omega, ?_, by omega, h1⟩
      have : ¬ c + 1 + 1 < n := by omega
      simp [tu, this, List.replicate_succ']
    · rw [if_neg hc2] at h1
      rcases reach_read_any hR s (c + 1) (update σ j s) (by omega) (update_self _ _ _) with
        ⟨i, rest, t, hci, hin, he, ht, h2⟩ | ⟨d, t, hd, hcd, ht, h2⟩
      · left
        refine ⟨i, rest, 1 + t, by omega, hin, ?_, by omega, (h1.trans h2).cast rfl (by simp) rfl⟩
        rw [← he]; simp [List.replicate_succ']
      · right
        refine ⟨d + 1, 1 + t, by simp [hd, List.replicate_succ], by omega, by omega, ?_⟩
        exact (h1.trans h2).cast (by congr 1; omega) (by simp) rfl

theorem tu_append_ne_replicate {n i d : ℕ} {r : Str} (hi : i < n) (hd : d + 1 < n) :
    tu n i ++ r ≠ List.replicate d false := by
  intro h
  by_cases h1 : i + 1 < n
  · have : true ∈ List.replicate d false := by rw [← h]; simp [tu, h1]
    simp at this
  · have hl := congrArg List.length h
    simp [tu, h1] at hl; omega

/-- Pushing the code `tu n i` on stack `j`. -/
theorem reach_pushCode {j n i E PC : ℕ} {PU : ℕ → ℕ}
    (hC : p[PC]? = some (if i + 1 < n then .push j true (PU i) else nop (PU i)))
    (h0 : p[PU 0]? = some (nop E))
    (hs : ∀ i', i' < i → p[PU (i' + 1)]? = some (.push j false (PU i'))) (σ : ℕ → Str) :
    Reach ∅ p PC σ E (update σ j (tu n i ++ σ j)) (i + 2) := by
  have hU := reach_pushU (p := p) (j := j) (E := E) (PU := PU) i h0 hs
  by_cases ht : i + 1 < n
  · rw [if_pos ht] at hC
    have h1 := reach_push (O := ∅) (σ := σ) hC
    refine (h1.trans (hU i le_rfl _)).cast rfl ?_ (by omega)
    simp [tu, ht]
  · rw [if_neg ht] at hC
    have h1 := reach_nop (stk := σ) hC
    refine (h1.trans (hU i le_rfl _)).cast rfl ?_ (by omega)
    simp [tu, ht]

end Loops

/-! ### Stage 1: move the certificate and the input, count the input -/

/-- Scratch stack for the (reversed) certificate. -/
def sW (k : ℕ) : ℕ := 2 * k + 2
/-- Scratch stack for the (reversed) input. -/
def sX (k : ℕ) : ℕ := 2 * k + 3
/-- Scratch stack for the decoded certificate codes. -/
def sZ (k : ℕ) : ℕ := 2 * k + 4

/-- Stage 1 (at address `0`, exit `7 + k`). -/
def pre1 (k : ℕ) : List Instr :=
  [.pop 1 3 1 2, .push (sW k) false 0, .push (sW k) true 0, .pop 0 (7 + k) 4 5,
    .push (sX k) false 6, .push (sX k) true 6] ++ pushes 6 (cs k) ++ [nop 3]

@[simp] theorem pre1_length (k : ℕ) : (pre1 k).length = 7 + k := by simp [pre1]; omega

section Stage1

variable {p : Prog} {k : ℕ}

theorem reach_mvW (h : CodeAt p 0 (pre1 k)) :
    ∀ (w : Str) (σ : ℕ → Str), σ 1 = w →
      Reach ∅ p 0 σ 3 (update (update σ 1 []) (sW k) (w.reverse ++ σ (sW k))) (2 * w.length + 1)
  | [], σ, hσ => by
    refine Reach.cast (reach_pop_nil h.head hσ) rfl ?_ (by simp)
    have e1 : update σ 1 [] = σ := by rw [← hσ, update_eq_self]
    rw [e1, List.reverse_nil, List.nil_append, update_eq_self]
  | b :: w, σ, hσ => by
    have hp := reach_pop_cons (O := ∅) h.head hσ
    have i1 : p[1]? = some (.push (sW k) false 0) := by
      simpa [pre1] using h 1 (by simp; omega)
    have i2 : p[2]? = some (.push (sW k) true 0) := by
      simpa [pre1] using h 2 (by simp; omega)
    have h12 : Reach ∅ p 0 σ 0 (update (update σ 1 w) (sW k) (b :: update σ 1 w (sW k))) 2 := by
      cases b
      · exact hp.trans (reach_push i1)
      · exact hp.trans (reach_push i2)
    have hW1 : sW k ≠ 1 := by unfold sW; omega
    have h3 := h12.trans (reach_mvW h w _ (by simp [update_of_ne hW1.symm]))
    refine h3.cast rfl ?_ (by simp; ring)
    funext j
    by_cases hj : j = sW k
    · subst hj; simp [update_of_ne hW1]
    · by_cases hj1 : j = 1
      · subst hj1; simp [update_of_ne hW1.symm]
      · simp [update_of_ne hj, update_of_ne hj1]

/-- The stacks after the input loop of stage 1. -/
def afterX (k : ℕ) (x : Str) (σ : ℕ → Str) : ℕ → Str := fun j =>
  if j = 0 then [] else if j = sX k then x.reverse ++ σ (sX k)
  else List.replicate (x.length * (cs k).count j) true ++ σ j

theorem count_sX (k : ℕ) : (cs k).count (sX k) = 0 :=
  count_cs_eq_zero (fun i => by unfold cnt sX; omega)

theorem reach_mvX (h : CodeAt p 0 (pre1 k)) :
    ∀ (x : Str) (σ : ℕ → Str), σ 0 = x →
      Reach ∅ p 3 σ (7 + k) (afterX k x σ) (x.length * (k + 3) + 1)
  | [], σ, hσ => by
    have i0 : p[3]? = some (.pop 0 (7 + k) 4 5) := by simpa [pre1] using h 3 (by simp; omega)
    refine Reach.cast (reach_pop_nil i0 hσ) rfl ?_ (by simp)
    funext j
    by_cases h0 : j = 0
    · subst h0; simp [afterX, hσ]
    · by_cases hX : j = sX k
      · subst hX; simp [afterX, h0]
      · simp [afterX, h0, hX]
  | b :: x, σ, hσ => by
    have i0 : p[3]? = some (.pop 0 (7 + k) 4 5) := by simpa [pre1] using h 3 (by simp; omega)
    have hp := reach_pop_cons (O := ∅) i0 hσ
    have i1 : p[4]? = some (.push (sX k) false 6) := by simpa [pre1] using h 4 (by simp; omega)
    have i2 : p[5]? = some (.push (sX k) true 6) := by simpa [pre1] using h 5 (by simp; omega)
    have h12 : Reach ∅ p 3 σ 6 (update (update σ 0 x) (sX k) (b :: update σ 0 x (sX k))) 2 := by
      cases b
      · exact hp.trans (reach_push i1)
      · exact hp.trans (reach_push i2)
    have hP : CodeAt p 6 (pushes 6 (cs k)) := by
      have := h.left.right
      simpa using this
    have iL : p[6 + k]? = some (nop 3) := by
      have := h (6 + k) (by simp)
      rw [Nat.zero_add] at this
      rw [this, pre1, List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.length_cons, pushes_length, cs_length,
        List.length_nil]
      rw [show 6 + k - (0 + 1 + 1 + 1 + 1 + 1 + 1 + k) = 0 by omega]; rfl
    have hX0 : sX k ≠ 0 := by unfold sX; omega
    have h3 := h12.trans ((reach_pushes _ _ _ hP).trans (reach_nop ((cs_length k).symm ▸ iL)))
    simp only [cs_length] at h3
    have h4 := h3.trans (reach_mvX h x _ (by
      simp [addTrues, update_of_ne hX0.symm]))
    refine Reach.cast h4 rfl ?_ (by simp; ring)
    funext j
    by_cases h0 : j = 0
    · subst h0; simp [afterX]
    · by_cases hX : j = sX k
      · subst hX; simp [afterX, addTrues, count_sX, update_of_ne hX0]
      · simp [afterX, h0, hX, addTrues]
        rw [Nat.succ_mul, List.replicate_add, List.append_assoc]

end Stage1

/-! ### Stages 3 and 4: decode the certificate, build the official input -/

/-- States of stages 3–4. -/
inductive Q2
  | /-- reading a certificate code, `c` zeros so far -/ rdW (c : ℕ)
  | /-- certificate symbol `i` read: consume a clock mark -/ ck (i : ℕ)
  | /-- push code `i` on `Z` -/ zc (i : ℕ)
  | /-- push `i` zeros on `Z` -/ zu (i : ℕ)
  | /-- reading a code from `Z` -/ rdZ (c : ℕ)
  | /-- push code `i` on stack `0`, then continue with `Z` (`bk`) or `X` -/ oc (i : ℕ) (bk : Bool)
  | /-- push `i` zeros on stack `0` -/ ou (i : ℕ) (bk : Bool)
  | /-- reading an input bit from `X` -/ rdX
  | /-- reject -/ rej
  | /-- exit (to the compiled official machine) -/ exit
  deriving DecidableEq

section Stage2

variable (tm : FinTM2) {Γ₁ : Type} (e₀ : tm.Γ tm.k₀ ≃ (Bool ⊕ Option Γ₁)) (k : ℕ)

attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin FinTM2.kFin FinTM2.kDecidableEq

open scoped Classical

/-- The layout of the compiled official machine: our stacks of its non-input stacks start
above all scratch stacks. -/
def lay : Layout tm := ⟨[], 2 * k + 5⟩

/-- Number of codes of the input stack. -/
noncomputable def n0 : ℕ := N tm (lay tm k) tm.k₀

/-- Index of a pair symbol. -/
noncomputable def cd (a : Bool ⊕ Option Γ₁) : ℕ := ix tm (lay tm k) tm.k₀ (e₀.symm a)

/-- Index `i` is the code of a certificate symbol. -/
def Good (i : ℕ) : Prop := ∃ γ, sy tm (lay tm k) tm.k₀ i = some (e₀.symm (.inr (some γ)))

/-- The states of stages 3–4. -/
noncomputable def S2 : List Q2 :=
  ((List.range (n0 tm k + 1)).flatMap fun c =>
    [.rdW c, .ck c, .zc c, .zu c, .rdZ c, .oc c false, .oc c true, .ou c false, .ou c true]) ++
    [.rdX, .rej]

/-- Address of a state. -/
noncomputable def i2 (s : Q2) : ℕ := (S2 tm k).idxOf s

/-- Instructions of stages 3–4. -/
noncomputable def act2 : Q2 → Instr
  | .rdW c => .pop (sW k) (if c = 0 then i2 tm k (.rdZ 0) else i2 tm k .rej)
      (if c + 2 = n0 tm k then i2 tm k (.ck (c + 1)) else i2 tm k (.rdW (c + 1)))
      (i2 tm k (.ck c))
  | .ck i => .pop 1 (i2 tm k .rej) (if Good tm e₀ k i then i2 tm k (.zc i) else i2 tm k .rej)
      (if Good tm e₀ k i then i2 tm k (.zc i) else i2 tm k .rej)
  | .zc i => if i + 1 < n0 tm k then .push (sZ k) true (i2 tm k (.zu i))
      else nop (i2 tm k (.zu i))
  | .zu 0 => nop (i2 tm k (.rdW 0))
  | .zu (i + 1) => .push (sZ k) false (i2 tm k (.zu i))
  | .rdZ c => .pop (sZ k)
      (if c = 0 then i2 tm k (.oc (cd tm e₀ k (.inr none)) false) else i2 tm k .rej)
      (if c + 2 = n0 tm k then i2 tm k (.oc (c + 1) true) else i2 tm k (.rdZ (c + 1)))
      (i2 tm k (.oc c true))
  | .oc i bk => if i + 1 < n0 tm k then .push 0 true (i2 tm k (.ou i bk))
      else nop (i2 tm k (.ou i bk))
  | .ou 0 bk => nop (if bk then i2 tm k (.rdZ 0) else i2 tm k .rdX)
  | .ou (i + 1) bk => .push 0 false (i2 tm k (.ou i bk))
  | .rdX => .pop (sX k) (i2 tm k .exit) (i2 tm k (.oc (cd tm e₀ k (.inl false)) false))
      (i2 tm k (.oc (cd tm e₀ k (.inl true)) false))
  | .rej => .halt false
  | .exit => .halt false

/-- The program of stages 3–4 (to be placed at an offset). -/
noncomputable def P2 : Prog := (S2 tm k).map (act2 tm e₀ k)

theorem mem_S2 {s : Q2} (h : ∃ c ≤ n0 tm k, s = .rdW c ∨ s = .ck c ∨ s = .zc c ∨ s = .zu c ∨
    s = .rdZ c ∨ s = .oc c false ∨ s = .oc c true ∨ s = .ou c false ∨ s = .ou c true) :
    s ∈ S2 tm k := by
  obtain ⟨c, hc, h⟩ := h
  simp only [S2, List.mem_append, List.mem_flatMap, List.mem_range]
  left; exact ⟨c, by omega, by rcases h with h | h | h | h | h | h | h | h | h <;> simp [h]⟩

theorem rdX_mem : Q2.rdX ∈ S2 tm k := by simp [S2]
theorem rej_mem : Q2.rej ∈ S2 tm k := by simp [S2]

theorem P2_idx {s : Q2} (hs : s ∈ S2 tm k) : (P2 tm e₀ k)[i2 tm k s]? = some (act2 tm e₀ k s) := by
  simp [P2, i2, List.getElem?_idxOf hs]

theorem i2_exit : i2 tm k .exit = (S2 tm k).length :=
  List.idxOf_eq_length (by simp [S2])

theorem two_le_n0 : 2 ≤ n0 tm k := two_le_N _ _ _

theorem cd_lt (a : Bool ⊕ Option Γ₁) : cd tm e₀ k a < n0 tm k :=
  ix_lt tm (lay tm k) (Or.inr rfl)

theorem L_lay_nodup : (L tm (lay tm k) tm.k₀).Nodup := by
  simp only [L, update_self, lay, List.nil_append]
  exact (Finset.nodup_toList _).filter _

theorem cd_of_sy {i : ℕ} {a : Bool ⊕ Option Γ₁}
    (h : sy tm (lay tm k) tm.k₀ i = some (e₀.symm a)) : cd tm e₀ k a = i := by
  unfold sy at h
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.1 h
  unfold cd ix
  rw [← he]
  exact (L_lay_nodup tm k).idxOf_getElem i hi

/-- The code of a certificate symbol. -/
noncomputable def cc (γ : Γ₁) : Str := tu (n0 tm k) (cd tm e₀ k (.inr (some γ)))

theorem honest_cons {s rest : Str} {i : ℕ} {ys : List Γ₁} (hs : s = ys.flatMap (cc tm e₀ k))
    (he : s = tu (n0 tm k) i ++ rest) (hi : i < n0 tm k) :
    ∃ γ ys', ys = γ :: ys' ∧ i = cd tm e₀ k (.inr (some γ)) ∧ rest = ys'.flatMap (cc tm e₀ k) := by
  cases ys with
  | nil =>
    simp only [List.flatMap_nil] at hs
    rw [hs] at he
    exact absurd he.symm (by simp [tu_ne_nil hi (two_le_n0 tm k)])
  | cons γ ys' =>
    rw [he, List.flatMap_cons, cc] at hs
    obtain ⟨h1, h2⟩ := tu_append_inj hi (cd_lt tm e₀ k _) hs
    exact ⟨γ, ys', rfl, h1, h2⟩

theorem good_cd (γ : Γ₁) : Good tm e₀ k (cd tm e₀ k (.inr (some γ))) :=
  ⟨γ, sy_ix tm (lay tm k) (Or.inr rfl)⟩

theorem cd_injective {a a' : Bool ⊕ Option Γ₁} (h : cd tm e₀ k a = cd tm e₀ k a') : a = a' := by
  have h1 := sy_ix tm (lay tm k) (g := e₀.symm a) (Or.inr rfl)
  have h2 := sy_ix tm (lay tm k) (g := e₀.symm a') (Or.inr rfl)
  unfold cd at h
  rw [h, h2] at h1
  exact e₀.symm.injective (Option.some.inj h1).symm

theorem flatMap_cc_injective : ∀ {ys ys' : List Γ₁},
    ys.flatMap (cc tm e₀ k) = ys'.flatMap (cc tm e₀ k) → ys = ys'
  | [], ys', h => by
    cases ys' with
    | nil => rfl
    | cons γ ys' =>
      simp only [List.flatMap_nil, List.flatMap_cons, cc] at h
      exact absurd h.symm (by simp [tu_ne_nil (cd_lt tm e₀ k _) (two_le_n0 tm k)])
  | γ :: ys, ys', h => by
    have he : ys'.flatMap (cc tm e₀ k) =
        tu (n0 tm k) (cd tm e₀ k (.inr (some γ))) ++ ys.flatMap (cc tm e₀ k) := by
      rw [← h, List.flatMap_cons, cc]
    obtain ⟨γ', ys'', rfl, hi, hr⟩ := honest_cons tm e₀ k rfl he (cd_lt tm e₀ k _)
    have := cd_injective tm e₀ k hi
    simp only [Sum.inr.injEq, Option.some.injEq] at this
    rw [this, flatMap_cc_injective hr]

theorem sW_ne_one : sW k ≠ 1 := by unfold sW; omega
theorem sZ_ne_one : sZ k ≠ 1 := by unfold sZ; omega
theorem sW_ne_sZ : sW k ≠ sZ k := by unfold sW sZ; omega

/-- **Stage 3.** Decoding an arbitrary certificate `s` with a clock of `m` marks either rejects,
or reads `s` as the codes of a certificate `ys` with `|ys| ≤ m`, pushing them on `Z`. -/
theorem decode : ∀ (s : Str) (m : ℕ) (σ : ℕ → Str), σ (sW k) = s → σ 1 = List.replicate m true →
    (∃ t σ', Reach ∅ (P2 tm e₀ k) (i2 tm k (.rdW 0)) σ (i2 tm k .rej) σ' t ∧
      ¬ ∃ ys : List Γ₁, ys.length ≤ m ∧ s = ys.flatMap (cc tm e₀ k)) ∨
    (∃ (ys : List Γ₁) (t : ℕ) (σ' : ℕ → Str), ys.length ≤ m ∧ s = ys.flatMap (cc tm e₀ k) ∧
      t ≤ ys.length * (2 * n0 tm k + 2) + n0 tm k ∧
      Reach ∅ (P2 tm e₀ k) (i2 tm k (.rdW 0)) σ (i2 tm k (.rdZ 0)) σ' t ∧
      σ' (sZ k) = ys.reverse.flatMap (cc tm e₀ k) ++ σ (sZ k) ∧
      ∀ j, j ≠ sW k → j ≠ sZ k → j ≠ 1 → σ' j = σ j)
  | s, m, σ, hs, hm => by
    have h2 := two_le_n0 tm k
    have hR : ∀ c, c + 1 < n0 tm k → (P2 tm e₀ k)[i2 tm k (.rdW c)]? = some (.pop (sW k)
        ((fun c => if c = 0 then i2 tm k (.rdZ 0) else i2 tm k .rej) c)
        (if c + 2 = n0 tm k then (fun i => i2 tm k (.ck i)) (c + 1)
          else (fun c => i2 tm k (.rdW c)) (c + 1)) ((fun i => i2 tm k (.ck i)) c)) := by
      intro c hc
      rw [P2_idx tm e₀ k (mem_S2 tm k (s := .rdW c) ⟨c, by omega, Or.inl rfl⟩)]; rfl
    rcases reach_read_any (n := n0 tm k) (j := sW k)
        (R := fun c => i2 tm k (.rdW c)) (T := fun i => i2 tm k (.ck i))
        (Z := fun c => if c = 0 then i2 tm k (.rdZ 0) else i2 tm k .rej) hR s 0 σ (by omega) hs with
      ⟨i, rest, t, -, hin, he, ht, h1⟩ | ⟨d, t, hd, hcd, ht, h1⟩
    · -- a full code `i` was read
      simp only [List.replicate_zero, List.nil_append] at he
      set σ1 := update σ (sW k) rest with hσ1
      have hm1 : σ1 1 = List.replicate m true := by
        rw [hσ1, update_of_ne (sW_ne_one k).symm, hm]
      have hck := P2_idx tm e₀ k (mem_S2 tm k (s := .ck i) ⟨i, by omega, Or.inr (Or.inl rfl)⟩)
      cases m with
      | zero =>
        left
        refine ⟨t + 1, σ1, h1.trans (reach_pop_nil (O := ∅) (σ := σ1) (hck.trans rfl) hm1), ?_⟩
        rintro ⟨ys, hyl, hys⟩
        obtain ⟨γ, ys', rfl, -, -⟩ := honest_cons tm e₀ k hys he hin
        simp at hyl
      | succ m =>
        have h2' := reach_pop_cons (O := ∅) (b := true) (s := List.replicate m true) (σ := σ1)
          (hck.trans rfl) (by rw [hm1, List.replicate_succ])
        simp only [if_true] at h2'
        by_cases hg : Good tm e₀ k i
        · rw [if_pos hg] at h2'
          obtain ⟨γ, hγ⟩ := hg
          have hci : cd tm e₀ k (.inr (some γ)) = i := cd_of_sy tm e₀ k hγ
          set σ2 := update σ1 1 (List.replicate m true) with hσ2
          have hpc := reach_pushCode (p := P2 tm e₀ k) (j := sZ k) (n := n0 tm k) (i := i)
            (E := i2 tm k (.rdW 0)) (PC := i2 tm k (.zc i)) (PU := fun i => i2 tm k (.zu i))
            (by rw [P2_idx tm e₀ k (mem_S2 tm k (s := .zc i) ⟨i, by omega, by simp⟩)]; rfl)
            (by rw [P2_idx tm e₀ k (mem_S2 tm k (s := .zu 0) ⟨0, by omega, by simp⟩)]; rfl)
            (fun i' hi' => by
              rw [P2_idx tm e₀ k (mem_S2 tm k (s := .zu (i' + 1)) ⟨i' + 1, by omega, by simp⟩)]; rfl)
            σ2
          set σ3 := update σ2 (sZ k) (tu (n0 tm k) i ++ σ2 (sZ k)) with hσ3
          have hlen : rest.length < s.length := by
            rw [he, List.length_append]
            have := List.length_pos_of_ne_nil (tu_ne_nil hin h2); omega
          have hW3 : σ3 (sW k) = rest := by
            rw [hσ3, update_of_ne (sW_ne_sZ k), hσ2, update_of_ne (sW_ne_one k), hσ1,
              update_self]
          have h13 : σ3 1 = List.replicate m true := by
            rw [hσ3, update_of_ne (sZ_ne_one k).symm, hσ2, update_self]
          have hall := (h1.trans h2').trans hpc
          rcases decode rest m σ3 hW3 h13 with ⟨t', σ', h4⟩ | ⟨ys, t', σ', hyl, hys, ht', h4, hZ, hfr⟩
          · left
            refine ⟨_, σ', hall.trans h4.1, ?_⟩
            rintro ⟨ys, hyl, hys⟩
            obtain ⟨γ', ys', rfl, hi', hr⟩ := honest_cons tm e₀ k hys he hin
            exact h4.2 ⟨ys', by simp at hyl; omega, hr⟩
          · right
            refine ⟨γ :: ys, t + 1 + (i + 2) + t', σ', by simp; omega, ?_, ?_, hall.trans h4, ?_, ?_⟩
            · rw [he, hys]; simp [cc, hci]
            · simp only [List.length_cons]
              simp only [Nat.sub_zero] at ht
              rw [Nat.add_mul]; omega
            · rw [hZ, hσ3, update_self, hσ2, update_of_ne (sZ_ne_one k), hσ1,
                update_of_ne (sW_ne_sZ k).symm]
              simp [cc, hci]
            · intro j h1j h2j h3j
              rw [hfr j h1j h2j h3j, hσ3, update_of_ne h2j, hσ2, update_of_ne h3j, hσ1,
                update_of_ne h1j]
        · rw [if_neg hg] at h2'
          left
          refine ⟨_, _, h1.trans h2', ?_⟩
          rintro ⟨ys, hyl, hys⟩
          obtain ⟨γ', ys', rfl, hi', hr⟩ := honest_cons tm e₀ k hys he hin
          exact hg (hi' ▸ good_cd tm e₀ k γ')
    · -- the certificate ran out: accept the boundary (`d = 0`) or reject
      cases d with
      | zero =>
        right
        refine ⟨[], t, update σ (sW k) [], by simp, by simpa using hd, by simp; omega, ?_,
          by simp [update_of_ne (sW_ne_sZ k).symm], fun j h1j _ _ => update_of_ne h1j _ _⟩
        simpa using h1
      | succ d =>
        left
        refine ⟨t, _, by simpa using h1, ?_⟩
        rintro ⟨ys, hyl, hys⟩
        cases ys with
        | nil => simp at hys; rw [hys] at hd; simp at hd
        | cons γ ys' =>
          rw [hd, List.flatMap_cons, cc] at hys
          exact tu_append_ne_replicate (cd_lt tm e₀ k _) (by omega) hys.symm
termination_by s => s.length

theorem sX_ne_zero : sX k ≠ 0 := by unfold sX; omega
theorem sZ_ne_zero : sZ k ≠ 0 := by unfold sZ; omega

/-- Pushing code `i` on stack `0` from state `oc i bk`. -/
theorem reach_oc {i : ℕ} (hi : i < n0 tm k) (bk : Bool) (σ : ℕ → Str) :
    Reach ∅ (P2 tm e₀ k) (i2 tm k (.oc i bk)) σ
      (if bk then i2 tm k (.rdZ 0) else i2 tm k .rdX) (update σ 0 (tu (n0 tm k) i ++ σ 0))
      (i + 2) := by
  refine reach_pushCode (p := P2 tm e₀ k) (j := 0) (n := n0 tm k) (i := i)
    (PU := fun i => i2 tm k (.ou i bk)) ?_ ?_ ?_ σ
  · rw [P2_idx tm e₀ k (mem_S2 tm k (s := .oc i bk) ⟨i, by omega, by cases bk <;> simp⟩)]; rfl
  · rw [P2_idx tm e₀ k (mem_S2 tm k (s := .ou 0 bk) ⟨0, by omega, by cases bk <;> simp⟩)]; rfl
  · intro i' hi'
    rw [P2_idx tm e₀ k (mem_S2 tm k (s := .ou (i' + 1) bk) ⟨i' + 1, by omega,
      by cases bk <;> simp⟩)]; rfl

/-- **Stage 4a.** Moving the codes on `Z` to stack `0` (reversing their order). -/
theorem transfer : ∀ (zs : List ℕ) (σ : ℕ → Str), (∀ i ∈ zs, i < n0 tm k) →
    σ (sZ k) = zs.flatMap (tu (n0 tm k)) →
    ∃ t σ', Reach ∅ (P2 tm e₀ k) (i2 tm k (.rdZ 0)) σ
      (i2 tm k (.oc (cd tm e₀ k (.inr none)) false)) σ' t ∧
      t ≤ zs.length * (2 * n0 tm k + 2) + n0 tm k ∧
      σ' 0 = zs.reverse.flatMap (tu (n0 tm k)) ++ σ 0 ∧ ∀ j, j ≠ 0 → j ≠ sZ k → σ' j = σ j
  | zs, σ, hzs, hσ => by
    have h2 := two_le_n0 tm k
    have hR : ∀ c, c + 1 < n0 tm k → (P2 tm e₀ k)[i2 tm k (.rdZ c)]? = some (.pop (sZ k)
        ((fun c => if c = 0 then i2 tm k (.oc (cd tm e₀ k (.inr none)) false)
          else i2 tm k .rej) c)
        (if c + 2 = n0 tm k then (fun i => i2 tm k (.oc i true)) (c + 1)
          else (fun c => i2 tm k (.rdZ c)) (c + 1)) ((fun i => i2 tm k (.oc i true)) c)) := by
      intro c hc
      rw [P2_idx tm e₀ k (mem_S2 tm k (s := .rdZ c) ⟨c, by omega, by simp⟩)]; rfl
    rcases reach_read_any (n := n0 tm k) (j := sZ k)
        (R := fun c => i2 tm k (.rdZ c)) (T := fun i => i2 tm k (.oc i true))
        (Z := fun c => if c = 0 then i2 tm k (.oc (cd tm e₀ k (.inr none)) false)
          else i2 tm k .rej) hR _ 0 σ (by omega) hσ with
      ⟨i, rest, t, -, hin, he, ht, h1⟩ | ⟨d, t, hd, hcd, ht, h1⟩
    · simp only [List.replicate_zero, List.nil_append] at he
      cases zs with
      | nil => simp at he; exact absurd he.1 (tu_ne_nil hin h2)
      | cons i₀ zs =>
        simp only [List.flatMap_cons] at he
        obtain ⟨rfl, rfl⟩ := tu_append_inj (hzs i₀ (by simp)) hin he
        have h2' := reach_oc tm e₀ k hin true (update σ (sZ k) (zs.flatMap (tu (n0 tm k))))
        simp only [if_true] at h2'
        obtain ⟨t', σ', h3, ht', h0, hfr⟩ := transfer zs
          (update (update σ (sZ k) (List.flatMap (tu (n0 tm k)) zs)) 0
            (tu (n0 tm k) i₀ ++ update σ (sZ k) (List.flatMap (tu (n0 tm k)) zs) 0))
          (fun i hi => hzs i (by simp [hi]))
          (by rw [update_of_ne (sZ_ne_zero k), update_self])
        refine ⟨t + (i₀ + 2) + t', σ', (h1.trans h2').trans h3, ?_, ?_, ?_⟩
        · simp only [Nat.sub_zero] at ht; simp only [List.length_cons]; rw [Nat.add_mul]; omega
        · rw [h0, update_self, update_of_ne (sZ_ne_zero k).symm]; simp
        · intro j h0j hZj
          rw [hfr j h0j hZj, update_of_ne h0j, update_of_ne hZj]
    · cases zs with
      | cons i₀ zs =>
        simp only [List.flatMap_cons] at hd
        exact absurd hd (tu_append_ne_replicate (hzs i₀ (by simp)) (by omega))
      | nil =>
        have hd0 : d = 0 := by simp at hd; cases d <;> simp_all
        subst hd0
        refine ⟨t, update σ (sZ k) [], by simpa using h1, by simp at ht ⊢; omega, ?_, ?_⟩
        · simp [update_of_ne (sZ_ne_zero k).symm]
        · intro j _ hZj; exact update_of_ne hZj _ _

/-- **Stage 4b.** Pushing the codes of the input bits (from `X`) on stack `0`. -/
theorem buildX : ∀ (xr : Str) (σ : ℕ → Str), σ (sX k) = xr →
    ∃ t σ', Reach ∅ (P2 tm e₀ k) (i2 tm k .rdX) σ (i2 tm k .exit) σ' t ∧
      t ≤ xr.length * (n0 tm k + 3) + 1 ∧
      σ' 0 = xr.reverse.flatMap (fun b => tu (n0 tm k) (cd tm e₀ k (.inl b))) ++ σ 0 ∧
      ∀ j, j ≠ 0 → j ≠ sX k → σ' j = σ j
  | [], σ, hσ => by
    have h1 := reach_pop_nil (O := ∅) (σ := σ)
      ((P2_idx tm e₀ k (rdX_mem tm k)).trans rfl) hσ
    exact ⟨1, σ, h1, by simp, by simp, fun _ _ _ => rfl⟩
  | b :: xr, σ, hσ => by
    have h1 := reach_pop_cons (O := ∅) (σ := σ)
      ((P2_idx tm e₀ k (rdX_mem tm k)).trans rfl) hσ
    have hb : (if b then i2 tm k (.oc (cd tm e₀ k (.inl true)) false)
        else i2 tm k (.oc (cd tm e₀ k (.inl false)) false)) =
        i2 tm k (.oc (cd tm e₀ k (.inl b)) false) := by cases b <;> rfl
    rw [hb] at h1
    have h2 := reach_oc tm e₀ k (cd_lt tm e₀ k (.inl b)) false (update σ (sX k) xr)
    simp only [Bool.false_eq_true, if_false] at h2
    obtain ⟨t', σ', h3, ht', h0, hfr⟩ := buildX xr
      (update (update σ (sX k) xr) 0
        (tu (n0 tm k) (cd tm e₀ k (.inl b)) ++ update σ (sX k) xr 0))
      (by rw [update_of_ne (sX_ne_zero k), update_self])
    have hc := cd_lt tm e₀ k (.inl b)
    refine ⟨1 + (cd tm e₀ k (.inl b) + 2) + t', σ', (h1.trans h2).trans h3, ?_, ?_, ?_⟩
    · simp only [List.length_cons]; rw [Nat.add_mul]; omega
    · rw [h0, update_self, update_of_ne (sX_ne_zero k).symm]; simp
    · intro j h0j hXj
      rw [hfr j h0j hXj, update_of_ne h0j, update_of_ne hXj]

end Stage2

end Pnp.Relativize.FromNP
