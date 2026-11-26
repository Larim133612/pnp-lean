import Pnp.Oracle.Machine

/-!
# Combinators for oracle stack machines

Small building blocks (straight-line pushes, a copy loop, nested counting loops) with
exact running times, used to build the deterministic machine of `Pnp.Oracle.BGSA`.
-/

namespace Pnp.Relativize

open Function

namespace Comb

/-- `p` goes from `(pc, σ)` to `(pc', σ')` in exactly `t` steps, without halting. -/
def Reach (O : Oracle) (p : Prog) (pc : ℕ) (σ : ℕ → Str) (pc' : ℕ) (σ' : ℕ → Str)
    (t : ℕ) : Prop :=
  runFor O p t (.run ⟨pc, σ⟩) = .run ⟨pc', σ'⟩

variable {O : Oracle} {p : Prog}

theorem Reach.refl {pc : ℕ} {σ : ℕ → Str} : Reach O p pc σ pc σ 0 := rfl

theorem Reach.trans {a b c t u : ℕ} {σ σ' σ'' : ℕ → Str} (h1 : Reach O p a σ b σ' t)
    (h2 : Reach O p b σ' c σ'' u) : Reach O p a σ c σ'' (t + u) := by
  unfold Reach at *; rw [runFor_add, h1, h2]

theorem Reach.cast {a b b' t t' : ℕ} {σ σ' σ'' : ℕ → Str} (h : Reach O p a σ b σ' t)
    (hb : b = b') (hσ : σ' = σ'') (ht : t = t') : Reach O p a σ b' σ'' t' := by
  subst hb hσ ht; exact h

theorem Reach.of_step {pc pc' : ℕ} {σ σ' : ℕ → Str}
    (h : step O p ⟨pc, σ⟩ = .run ⟨pc', σ'⟩) : Reach O p pc σ pc' σ' 1 := by
  unfold Reach; rw [runFor_succ_run, h]; rfl

theorem reach_push {pc k n : ℕ} {b : Bool} {σ : ℕ → Str}
    (h : p[pc]? = some (.push k b n)) : Reach O p pc σ n (update σ k (b :: σ k)) 1 :=
  Reach.of_step (by simp [step, h])

theorem reach_pop_cons {pc k z f t : ℕ} {b : Bool} {s : Str} {σ : ℕ → Str}
    (h : p[pc]? = some (.pop k z f t)) (hk : σ k = b :: s) :
    Reach O p pc σ (if b then t else f) (update σ k s) 1 :=
  Reach.of_step (by simp [step, h, hk])

theorem reach_pop_nil {pc k z f t : ℕ} {σ : ℕ → Str}
    (h : p[pc]? = some (.pop k z f t)) (hk : σ k = []) : Reach O p pc σ z σ 1 :=
  Reach.of_step (by simp [step, h, hk])

/-! ### Code placement -/

/-- The instructions `l` occur in `p` starting at address `b`. -/
def CodeAt (p : Prog) (b : ℕ) (l : List Instr) : Prop :=
  ∀ j, j < l.length → p[b + j]? = l[j]?

theorem codeAt_self (p : Prog) : CodeAt p 0 p := by
  intro j _; simp

theorem CodeAt.left {b : ℕ} {l₁ l₂ : List Instr} (h : CodeAt p b (l₁ ++ l₂)) :
    CodeAt p b l₁ := by
  intro j hj
  rw [h j (by simp; omega), List.getElem?_append_left hj]

theorem CodeAt.right {b : ℕ} {l₁ l₂ : List Instr} (h : CodeAt p b (l₁ ++ l₂)) :
    CodeAt p (b + l₁.length) l₂ := by
  intro j hj
  have := h (l₁.length + j) (by simp; omega)
  rw [← Nat.add_assoc] at this
  rw [this, List.getElem?_append_right (by omega)]
  simp

theorem CodeAt.head {b : ℕ} {i : Instr} {l : List Instr} (h : CodeAt p b (i :: l)) :
    p[b]? = some i := by
  simpa using h 0 (by simp)

theorem CodeAt.tail {b : ℕ} {i : Instr} {l : List Instr} (h : CodeAt p b (i :: l)) :
    CodeAt p (b + 1) l :=
  CodeAt.right (l₁ := [i]) h

theorem CodeAt.rebase {b b' : ℕ} {l : List Instr} (h : CodeAt p b l) (hb : b = b') :
    CodeAt p b' l := hb ▸ h

/-! ### Straight-line pushes of `true` -/

/-- Push `true` on stacks `ks` in order, starting at address `b`. -/
def pushes : ℕ → List ℕ → List Instr
  | _, [] => []
  | b, k :: ks => .push k true (b + 1) :: pushes (b + 1) ks

@[simp] theorem pushes_length : ∀ (b : ℕ) (ks : List ℕ), (pushes b ks).length = ks.length
  | _, [] => rfl
  | b, _ :: ks => by simp [pushes, pushes_length (b + 1) ks]

/-- The effect of `pushes`. -/
def addTrues (ks : List ℕ) (σ : ℕ → Str) : ℕ → Str :=
  fun j => List.replicate (ks.count j) true ++ σ j

theorem reach_pushes : ∀ (ks : List ℕ) (b : ℕ) (σ : ℕ → Str), CodeAt p b (pushes b ks) →
    Reach O p b σ (b + ks.length) (addTrues ks σ) ks.length
  | [], b, σ, _ => Reach.cast Reach.refl (by simp) (by funext j; simp [addTrues]) rfl
  | k :: ks, b, σ, h => by
    have h1 := reach_push (O := O) (σ := σ) h.head
    have h2 := reach_pushes ks (b + 1) (update σ k (true :: σ k)) h.tail
    refine Reach.cast (h1.trans h2) (by simp; omega) ?_ (by simp; omega)
    funext j
    by_cases hj : j = k
    · subst hj; simp [addTrues, List.replicate_succ']
    · simp [addTrues, hj, Ne.symm hj]

/-! ### Stack layout -/

/-- Counter stack number `j` of the nested loops. -/
def cnt (j : ℕ) : ℕ := 2 * j + 2

/-- Auxiliary stack number `j` of the nested loops. -/
def aux (j : ℕ) : ℕ := 2 * j + 3

/-- The counter stacks `cnt 0, …, cnt (d-1)`. -/
def cs (d : ℕ) : List ℕ := (List.range d).map cnt

@[simp] theorem cs_length (d : ℕ) : (cs d).length = d := by simp [cs]

theorem cnt_injective : Injective cnt := by
  intro a b h; unfold cnt at h; omega

theorem count_cnt_cs {d j : ℕ} (hj : j < d) : (cs d).count (cnt j) = 1 := by
  rw [cs, List.count_map_of_injective _ _ cnt_injective]
  exact List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 hj)

theorem count_cs_eq_zero {d j : ℕ} (hj : ∀ i, j ≠ cnt i) : (cs d).count j = 0 := by
  rw [List.count_eq_zero]
  simp only [cs, List.mem_map, not_exists, not_and]
  exact fun i _ h => hj i h.symm

@[simp] theorem count_cs_zero (d : ℕ) : (cs d).count 0 = 0 :=
  count_cs_eq_zero (fun i => by unfold cnt; omega)

@[simp] theorem count_cs_one (d : ℕ) : (cs d).count 1 = 0 :=
  count_cs_eq_zero (fun i => by unfold cnt; omega)

theorem count_aux_cs (d j : ℕ) : (cs d).count (aux j) = 0 :=
  count_cs_eq_zero (fun i => by unfold cnt aux; omega)

/-! ### Stage A: copy the input to stack 1, counting it on the counters -/

/-- The encoding of `x` written by stage A (read top first). -/
def enc (x : Str) : Str := x.reverse.flatMap fun b => [true, b]

/-- Pop `x` from stack 0; for each bit `b` push `b` then `true` on stack 1, and one
`true` on each counter stack. Must sit at address `0`; exits at `4 + d`. -/
def stageA (d : ℕ) : List Instr :=
  [.pop 0 (4 + d) 1 2, .push 1 false 3, .push 1 true 3] ++ pushes 3 (cs d) ++
    [.push 1 true 0]

@[simp] theorem stageA_length (d : ℕ) : (stageA d).length = 4 + d := by
  simp [stageA]; omega

/-- The stacks after stage A. -/
def afterA (d : ℕ) (x : Str) (σ : ℕ → Str) : ℕ → Str := fun j =>
  if j = 0 then [] else if j = 1 then enc x ++ σ 1
  else List.replicate (x.length * (cs d).count j) true ++ σ j

theorem reach_stageA {d : ℕ} (h : CodeAt p 0 (stageA d)) :
    ∀ (x : Str) (σ : ℕ → Str), σ 0 = x →
      Reach O p 0 σ (4 + d) (afterA d x σ) (x.length * (d + 3) + 1)
  | [], σ, hσ => by
    refine Reach.cast (reach_pop_nil (h.head) hσ) rfl ?_ (by simp)
    funext j
    by_cases h0 : j = 0
    · subst h0; simp [afterA, hσ]
    · by_cases h1 : j = 1
      · subst h1; simp [afterA, enc]
      · simp [afterA, h0, h1]
  | b :: x, σ, hσ => by
    have hp := reach_pop_cons (O := O) h.head hσ
    have i1 : p[1]? = some (.push 1 false 3) := by simpa [stageA] using h 1 (by simp; omega)
    have i2 : p[2]? = some (.push 1 true 3) := by simpa [stageA] using h 2 (by simp; omega)
    have h12 : Reach O p 0 σ 3 (update (update σ 0 x) 1 (b :: update σ 0 x 1)) 2 := by
      cases b
      · exact hp.trans (reach_push i1)
      · exact hp.trans (reach_push i2)
    have hP : CodeAt p 3 (pushes 3 (cs d)) := h.left.right.rebase (by simp)
    have iL : p[3 + d]? = some (.push 1 true 0) := (h.right.rebase (by simp; omega)).head
    have h3 := h12.trans ((reach_pushes _ _ _ hP).trans (reach_push ((cs_length d).symm ▸ iL)))
    simp only [cs_length] at h3
    have h4 := h3.trans (reach_stageA h x _ (by
      simp [addTrues]))
    refine Reach.cast h4 rfl ?_ (by simp; ring)
    funext j
    by_cases h0 : j = 0
    · subst h0; simp [afterA]
    · by_cases h1 : j = 1
      · subst h1
        simp [afterA, enc, addTrues]
      · simp [afterA, h0, h1, addTrues]
        rw [Nat.succ_mul, List.replicate_add, List.append_assoc]

/-! ### Restoring a counter -/

/-- Move all bits of the all-`true` stack `D` onto stack `C`, then jump to `E`. -/
theorem reach_restore {R E C D : ℕ} (hpop : p[R]? = some (.pop D E E (R + 1)))
    (hpush : p[R + 1]? = some (.push C true R)) (hCD : C ≠ D) :
    ∀ (r : ℕ) (σ : ℕ → Str), σ D = List.replicate r true →
      Reach O p R σ E (update (update σ D []) C (List.replicate r true ++ σ C)) (2 * r + 1)
  | 0, σ, hσ => by
    refine Reach.cast (reach_pop_nil hpop hσ) rfl ?_ rfl
    funext j
    by_cases hj : j = C
    · subst hj; simp
    · by_cases hj' : j = D
      · subst hj'; simpa [hj] using hσ
      · simp [hj, hj']
  | r + 1, σ, hσ => by
    have h1 := (reach_pop_cons (O := O) (b := true) (s := List.replicate r true) hpop
      (by rw [hσ, List.replicate_succ])).trans
      (reach_push (σ := update σ D (List.replicate r true)) hpush)
    have h2 := h1.trans (reach_restore hpop hpush hCD r _ (by simp [update_apply, hCD.symm]))
    refine Reach.cast h2 rfl ?_ (by ring)
    funext j
    by_cases hj : j = C
    · subst hj; simp [hCD, List.replicate_succ']
    · by_cases hj' : j = D
      · subst hj'; simp [update_apply, hCD.symm]
      · simp [update_apply, hj, hj']

/-! ### Nested counting loops -/

/-- `d` nested loops over the counters `cnt (d-1), …, cnt 0` (with auxiliary stacks
`aux j` used to restore them); the innermost body pushes `true` on stack 1. -/
def pad : ℕ → ℕ → List Instr
  | 0, b => [.push 1 true (b + 1)]
  | d + 1, b => .pop (cnt d) (b + 4 * d + 3) (b + 4 * d + 3) (b + 1) ::
      (pad d (b + 1) ++ [.push (aux d) true b, .pop (aux d) (b + 4 * d + 5) (b + 4 * d + 5)
        (b + 4 * d + 4), .push (cnt d) true (b + 4 * d + 3)])

@[simp] theorem pad_length : ∀ d b, (pad d b).length = 4 * d + 1
  | 0, _ => rfl
  | d + 1, b => by simp [pad, pad_length d (b + 1)]; ring

/-- Exact running time of `pad d` with counters of size `m`. -/
def Tpad (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => m * (Tpad m d + 2) + 1 + (2 * m + 1)

/-- The first `d` counters hold `m` bits `true` and their auxiliary stacks are empty. -/
def Full (d m : ℕ) (σ : ℕ → Str) : Prop :=
  ∀ j < d, σ (cnt j) = List.replicate m true ∧ σ (aux j) = []

/-- Loop state of `pad (d+1)`: `u` iterations to go, `r` done. -/
def loopSt (d m : ℕ) (σ : ℕ → Str) (u r : ℕ) : ℕ → Str := fun j =>
  if j = cnt d then List.replicate u true
  else if j = aux d then List.replicate r true
  else if j = 1 then List.replicate (r * m ^ d) true ++ σ 1
  else σ j

theorem cnt_ne_aux (i j : ℕ) : cnt i ≠ aux j := by unfold cnt aux; omega
theorem cnt_ne_one (i : ℕ) : cnt i ≠ 1 := by unfold cnt; omega
theorem aux_ne_one (i : ℕ) : aux i ≠ 1 := by unfold aux; omega
theorem aux_injective : Injective aux := by intro a b h; unfold aux at h; omega

theorem full_loopSt {d m : ℕ} {σ : ℕ → Str} (hf : Full d m σ) (u r : ℕ) :
    Full d m (loopSt d m σ u r) := by
  intro j hj
  have h1 : cnt j ≠ cnt d := fun h => by have := cnt_injective h; omega
  have h2 : aux j ≠ aux d := fun h => by have := aux_injective h; omega
  simp [loopSt, h1, h2, cnt_ne_aux, (cnt_ne_aux _ _).symm, cnt_ne_one, aux_ne_one, hf j hj]

theorem reach_pad_phase1 {d m b : ℕ} {σ : ℕ → Str} (hf : Full d m σ)
    (hpop : p[b]? = some (.pop (cnt d) (b + 4 * d + 3) (b + 4 * d + 3) (b + 1)))
    (hbody : ∀ τ, Full d m τ →
      Reach O p (b + 1) τ (b + 1 + (4 * d + 1)) (update τ 1 (List.replicate (m ^ d) true ++ τ 1))
        (Tpad m d))
    (hpush : p[b + 4 * d + 2]? = some (.push (aux d) true b)) :
    ∀ u r, Reach O p b (loopSt d m σ u r) (b + 4 * d + 3) (loopSt d m σ 0 (r + u))
      (u * (Tpad m d + 2) + 1)
  | 0, r => Reach.cast (reach_pop_nil hpop (by simp [loopSt])) rfl (by simp) (by simp)
  | u + 1, r => by
    have h1 := reach_pop_cons (O := O) (b := true) (s := List.replicate u true) hpop
      (σ := loopSt d m σ (u + 1) r) (by simp [loopSt, List.replicate_succ])
    have e1 : update (loopSt d m σ (u + 1) r) (cnt d) (List.replicate u true) =
        loopSt d m σ u r := by
      funext j; by_cases hj : j = cnt d
      · subst hj; simp [loopSt]
      · simp [loopSt, hj]
    rw [e1] at h1
    have h2 := (h1.trans (hbody _ (full_loopSt hf u r))).trans
      (reach_push (O := O) ((by omega : b + 4 * d + 2 = b + 1 + (4 * d + 1)) ▸ hpush))
    have e2 : update (update (loopSt d m σ u r) 1
        (List.replicate (m ^ d) true ++ loopSt d m σ u r 1)) (aux d)
        (true :: update (loopSt d m σ u r) 1
          (List.replicate (m ^ d) true ++ loopSt d m σ u r 1) (aux d)) =
        loopSt d m σ u (r + 1) := by
      funext j
      by_cases ha : j = aux d
      · subst ha; simp [loopSt, aux_ne_one, (cnt_ne_aux _ _).symm, List.replicate_succ]
      · by_cases h1 : j = 1
        · subst h1
          simp only [loopSt, update_apply, (cnt_ne_one _).symm, (aux_ne_one _).symm,
            if_true, if_false]
          rw [Nat.succ_mul, Nat.add_comm, List.replicate_add, List.append_assoc]
        · simp [loopSt, ha, h1]
    rw [e2] at h2
    exact Reach.cast (h2.trans (reach_pad_phase1 hf hpop hbody hpush u (r + 1))) rfl
      (by congr 1; omega) (by ring)

/-- `pad d` pushes `m ^ d` bits `true` on stack 1 and leaves all other stacks unchanged. -/
theorem reach_pad (m : ℕ) : ∀ (d b : ℕ) (σ : ℕ → Str), CodeAt p b (pad d b) → Full d m σ →
    Reach O p b σ (b + (4 * d + 1)) (update σ 1 (List.replicate (m ^ d) true ++ σ 1))
      (Tpad m d)
  | 0, b, σ, h, _ => Reach.cast (reach_push h.head) rfl (by simp) rfl
  | d + 1, b, σ, h, hf => by
    have hfd : Full d m σ := fun j hj => hf j (by omega)
    have hc := hf d (by omega)
    have ht := h.tail
    have hr := ht.right
    simp only [pad_length] at hr
    have i1 : p[b + 4 * d + 2]? = some (.push (aux d) true b) :=
      (hr.rebase (by omega)).head
    have i2 : p[b + 4 * d + 3]? = some (.pop (aux d) (b + 4 * d + 5) (b + 4 * d + 5)
        (b + 4 * d + 3 + 1)) :=
      (hr.tail.rebase (by omega)).head
    have i3 : p[b + 4 * d + 3 + 1]? = some (.push (cnt d) true (b + 4 * d + 3)) :=
      (hr.tail.tail.rebase (by omega)).head
    have e0 : σ = loopSt d m σ m 0 := by
      funext j
      by_cases hj : j = cnt d
      · subst hj; simp [loopSt, hc.1]
      · by_cases ha : j = aux d
        · subst ha; simp [loopSt, hc.2, (cnt_ne_aux _ _).symm]
        · by_cases h1 : j = 1
          · subst h1; simp [loopSt, (cnt_ne_one _).symm, (aux_ne_one _).symm]
          · simp [loopSt, hj, ha, h1]
    have h1 := reach_pad_phase1 (O := O) hfd h.head
      (fun τ hτ => reach_pad m d (b + 1) τ ht.left hτ) i1 m 0
    rw [← e0, Nat.zero_add] at h1
    have h2 := h1.trans (reach_restore i2 i3 (cnt_ne_aux d d) m _ (by simp [loopSt,
      (cnt_ne_aux _ _).symm]))
    refine Reach.cast h2 (by omega) ?_ (by simp [Tpad])
    funext j
    by_cases hj : j = cnt d
    · subst hj; simp [loopSt, hc.1, cnt_ne_one]
    · by_cases ha : j = aux d
      · subst ha; simp [loopSt, hc.2, aux_ne_one, (cnt_ne_aux _ _).symm]
      · by_cases h1 : j = 1
        · subst h1
          simp [loopSt, (cnt_ne_one _).symm, (aux_ne_one _).symm, pow_succ, Nat.mul_comm]
        · simp [loopSt, hj, ha, h1]

/-! ### The query machine -/

/-- Query on stack `k`, then halt with the answer. -/
theorem runFor_query_halt {a k : ℕ} {σ : ℕ → Str}
    (hq : p[a]? = some (.query k (a + 1) (a + 2))) (ht : p[a + 1]? = some (.halt true))
    (hf : p[a + 2]? = some (.halt false)) :
    ∃ b, runFor O p 2 (.run ⟨a, σ⟩) = .done b ∧ (b = true ↔ σ k ∈ O) := by
  rw [runFor_succ_run]
  by_cases hm : σ k ∈ O
  · exact ⟨true, by simp [step, hq, hm, runFor_succ_run, ht], by simp [hm]⟩
  · exact ⟨false, by simp [step, hq, hm, runFor_succ_run, hf], by simp [hm]⟩

end Comb

open Comb

/-- The padded code of `(i, x)`: `1^i 0 1^T 0 enc(x)`. -/
def code (i : ℕ) (x : Str) (T : ℕ) : Str :=
  List.replicate i true ++ false :: (List.replicate T true ++ false :: enc x)

/-- A machine that writes `code i x ((|x|+2)^d)` on stack 1 and queries it. -/
def queryProg (i d : ℕ) : Prog :=
  stageA d ++ (.push 1 false (5 + d) :: (pushes (5 + d) (cs d) ++
    (pushes (5 + 2 * d) (cs d) ++ (pad d (5 + 3 * d) ++ (.push 1 false (7 + 7 * d) ::
    (pushes (7 + 7 * d) (List.replicate i 1) ++
      [.query 1 (8 + 7 * d + i) (9 + 7 * d + i), .halt true, .halt false]))))))

/-- Exact running time of `queryProg i d` on inputs of length `n`. -/
def queryTime (i d n : ℕ) : ℕ :=
  n * (d + 3) + 1 + 1 + d + d + Tpad (n + 2) d + 1 + i + 2

theorem queryProg_run (O : Oracle) (i d : ℕ) (x : Str) :
    ∃ b, runFor O (queryProg i d) (queryTime i d x.length) (.run (init [x])) = .done b ∧
      (b = true ↔ code i x ((x.length + 2) ^ d) ∈ O) := by
  set p := queryProg i d with hp
  have h := codeAt_self p
  have hA : CodeAt p 0 (stageA d) := h.left
  have h1 := h.right.rebase (by simp : 0 + (stageA d).length = 4 + d)
  have h2 := h1.tail.rebase (by omega : 4 + d + 1 = 5 + d)
  have h3 := h2.right.rebase (by simp; omega : 5 + d + (pushes (5 + d) (cs d)).length = 5 + 2 * d)
  have h4 := h3.right.rebase
    (by simp; omega : 5 + 2 * d + (pushes (5 + 2 * d) (cs d)).length = 5 + 3 * d)
  have h5 := h4.right.rebase (by simp; omega : 5 + 3 * d + (pad d (5 + 3 * d)).length = 6 + 7 * d)
  have h6 := h5.tail.rebase (by omega : 6 + 7 * d + 1 = 7 + 7 * d)
  have h7 := h6.right.rebase
    (by simp : 7 + 7 * d + (pushes (7 + 7 * d) (List.replicate i 1)).length = 7 + 7 * d + i)
  let σ0 : ℕ → Str := fun k => [x].getD k []
  have hσ0 : ∀ k, k ≠ 0 → σ0 k = [] := by
    intro k hk; obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk; simp [σ0]
  have rA := reach_stageA (O := O) hA x σ0 rfl
  set σA := afterA d x σ0
  have rB := reach_push (O := O) (σ := σA) h1.head
  set σB := update σA 1 (false :: σA 1)
  have rC := reach_pushes (O := O) (cs d) (5 + d) σB h2.left
  set σC := addTrues (cs d) σB
  have rD := reach_pushes (O := O) (cs d) (5 + 2 * d) σC h3.left
  set σD := addTrues (cs d) σC
  have hfull : Full d (x.length + 2) σD := by
    intro j hj
    have hj0 : cnt j ≠ 0 := by unfold cnt; omega
    have ha0 : aux j ≠ 0 := by unfold aux; omega
    simp [σD, σC, σB, σA, addTrues, afterA, count_cnt_cs hj, count_aux_cs, cnt_ne_one,
      aux_ne_one, hj0, ha0, hσ0]
    rfl
  have rE := reach_pad (O := O) (x.length + 2) d (5 + 3 * d) σD h4.left hfull
  set σE := update σD 1 (List.replicate ((x.length + 2) ^ d) true ++ σD 1)
  have rF := reach_push (O := O) (σ := σE) h5.head
  set σF := update σE 1 (false :: σE 1)
  have rG := reach_pushes (O := O) (List.replicate i 1) (7 + 7 * d) σF h6.left
  set σG := addTrues (List.replicate i 1) σF
  have hG : σG 1 = code i x ((x.length + 2) ^ d) := by
    simp [σG, σF, σE, σD, σC, σB, σA, addTrues, afterA, code, hσ0]
  have rC' := rC.cast (by simp; omega : 5 + d + (cs d).length = 5 + 2 * d) rfl
    (by simp : (cs d).length = d)
  have rD' := rD.cast (by simp; omega : 5 + 2 * d + (cs d).length = 5 + 3 * d) rfl
    (by simp : (cs d).length = d)
  have rE' := rE.cast (by omega : 5 + 3 * d + (4 * d + 1) = 6 + 7 * d) rfl rfl
  have rG' := rG.cast (by simp : 7 + 7 * d + (List.replicate i 1).length = 7 + 7 * d + i) rfl
    (by simp : (List.replicate i 1).length = i)
  have rAll := rA.trans (rB.trans (rC'.trans (rD'.trans (rE'.trans (rF.trans rG')))))
  have iq : p[7 + 7 * d + i]? = some (.query 1 (7 + 7 * d + i + 1) (7 + 7 * d + i + 2)) := by
    rw [h7.head]; congr 2 <;> omega
  have it : p[7 + 7 * d + i + 1]? = some (.halt true) := h7.tail.head
  have iF : p[7 + 7 * d + i + 2]? = some (.halt false) := h7.tail.tail.head
  obtain ⟨b, hb, hiff⟩ := runFor_query_halt (O := O) (σ := σG) iq it iF
  refine ⟨b, ?_, hG ▸ hiff⟩
  have e : queryTime i d x.length = (x.length * (d + 3) + 1 + (1 + (d + (d +
      (Tpad (x.length + 2) d + (1 + i)))))) + 2 := by unfold queryTime; ring
  rw [e, runFor_add]
  unfold Reach at rAll
  rw [show init [x] = ⟨0, σ0⟩ from rfl, rAll]
  exact hb

theorem Tpad_le {m : ℕ} (hm : 2 ≤ m) : ∀ d, Comb.Tpad m d ≤ m ^ (3 * d + 1)
  | 0 => by simp [Comb.Tpad]; omega
  | d + 1 => by
    have ih := Tpad_le hm d
    have hX : m ≤ m ^ (3 * d + 1) := by
      calc m = m ^ 1 := (pow_one m).symm
        _ ≤ m ^ (3 * d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have e : m ^ (3 * (d + 1) + 1) = m * m * (m * m ^ (3 * d + 1)) := by ring
    rw [e]
    simp only [Comb.Tpad]
    set X := m ^ (3 * d + 1)
    have h4 : 4 ≤ m * m := by nlinarith
    have a1 : 4 * (m * X) ≤ m * m * (m * X) := Nat.mul_le_mul_right _ h4
    have a2 : m * Comb.Tpad m d ≤ m * X := Nat.mul_le_mul_left _ ih
    have a3 : m * m ≤ m * X := Nat.mul_le_mul_left _ hX
    nlinarith

theorem queryTime_le (i d n : ℕ) : queryTime i d n ≤ (n + 2) ^ (3 * d + i + 11) := by
  set m := n + 2
  have hm : 2 ≤ m := by omega
  have hT := Tpad_le hm d
  have hpos : 0 < m := by omega
  have h1 : m ^ (3 * d + 1) ≤ m ^ (3 * d + i + 10) := Nat.pow_le_pow_right hpos (by omega)
  have h2 : 3 * d + i + 9 ≤ m ^ (3 * d + i + 9) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hm _)
  have h3 : m ^ (3 * d + i + 10) = m * m ^ (3 * d + i + 9) := by ring
  have h4 : m ^ (3 * d + i + 11) = m * m ^ (3 * d + i + 10) := by ring
  have h5 : n * (d + 3) + 2 * d + i + 6 ≤ m * (3 * d + i + 9) := by
    have : n * (d + 3) ≤ m * (d + 3) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have h6 : m * (3 * d + i + 9) ≤ m * m ^ (3 * d + i + 9) := Nat.mul_le_mul_left _ h2
  unfold queryTime
  rw [h4]
  nlinarith

end Pnp.Relativize
