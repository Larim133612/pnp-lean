import Pnp.Oracle.Struct

/-!
# More utility commands for the structured language

Generic commands with exact (or upper-bound) semantics, on top of `Pnp/Oracle/Struct.lean`:

* `ExecLe` rules for pops, loops (`ExecLe.loop_iter`), and casts;
* `marks a d t`: push `|σ a|` marks (`true`) onto `d` (unary length);
* `mul a b c ta tm`: push `|σ a| · |σ b|` marks onto `c` (unary multiplication);
* `eqLen a b r`: compare the lengths of two stacks, emptying both (halt `r` if they differ);
* `gtCmd yes no`: halt `true` if `|σ yes| > |σ no|`, otherwise empty both stacks;
* `drainR o N`: empty the stacks `o, …, o + N - 1`;
* `callDrain`: call a program at offset `o` and clean up all its stacks afterwards;
* `segCmd src dst`: parse one segment of a bit-pair code (`[false, b]` = data bit `b`,
  `[true, _]` = separator).
-/

namespace Pnp.Relativize.Struct

open Function

/-! ### `ExecLe` rules -/

theorem ExecLe.of_eq {c : Cmd} {σ : ℕ → Str} {r r' : Res} {t T : ℕ} (h : Exec c σ r t)
    (hr : r = r') (ht : t ≤ T) : ExecLe c σ r' T := ⟨t, ht, hr ▸ h⟩

theorem ExecLe.cast {c : Cmd} {σ : ℕ → Str} {r r' : Res} {T T' : ℕ} (h : ExecLe c σ r T)
    (hr : r = r') (ht : T ≤ T') : ExecLe c σ r' T' := by
  obtain ⟨t, h1, h2⟩ := h; exact ⟨t, h1.trans ht, hr ▸ h2⟩

theorem ExecLe.pop_nil {k : ℕ} {cn cf ct : Cmd} {σ : ℕ → Str} {r : Res} {T : ℕ} (hk : σ k = [])
    (h : ExecLe cn σ r T) : ExecLe (.pop k cn cf ct) σ r (T + 1) := by
  obtain ⟨t, h1, h2⟩ := h; exact ⟨t + 1, by omega, .pop_nil hk h2⟩

theorem ExecLe.pop_cons {k : ℕ} {cn cf ct : Cmd} {σ : ℕ → Str} {b : Bool} {s : Str} {r : Res}
    {T : ℕ} (hk : σ k = b :: s) (h : ExecLe (if b then ct else cf) (update σ k s) r T) :
    ExecLe (.pop k cn cf ct) σ r (T + 1) := by
  obtain ⟨t, h1, h2⟩ := h; exact ⟨t + 1, by omega, .pop_cons hk h2⟩

/-- Pop with identical branches for both bits. -/
theorem ExecLe.pop_same {k : ℕ} {cn c : Cmd} {σ : ℕ → Str} {b : Bool} {s : Str} {r : Res}
    {T : ℕ} (hk : σ k = b :: s) (h : ExecLe c (update σ k s) r T) :
    ExecLe (.pop k cn c c) σ r (T + 1) :=
  ExecLe.pop_cons hk (by rw [ite_self]; exact h)

theorem ExecLe.loop_brk {c : Cmd} {σ σ' : ℕ → Str} {T : ℕ} (h : ExecLe c σ (.brk σ') T) :
    ExecLe (.loop c) σ (.norm σ') T := by
  obtain ⟨t, h1, h2⟩ := h; exact ⟨t, h1, .loop_brk h2⟩

theorem ExecLe.loop_halt {c : Cmd} {σ : ℕ → Str} {b : Bool} {T : ℕ}
    (h : ExecLe c σ (.halt b) T) : ExecLe (.loop c) σ (.halt b) T := by
  obtain ⟨t, h1, h2⟩ := h; exact ⟨t, h1, .loop_halt h2⟩

theorem ExecLe.loop_norm {c : Cmd} {σ σ' : ℕ → Str} {r : Res} {T₁ T₂ : ℕ}
    (h1 : ExecLe c σ (.norm σ') T₁) (h2 : ExecLe (.loop c) σ' r T₂) :
    ExecLe (.loop c) σ r (T₁ + T₂) := by
  obtain ⟨t₁, a1, e1⟩ := h1; obtain ⟨t₂, a2, e2⟩ := h2
  exact ⟨t₁ + t₂, by omega, .loop_norm e1 e2⟩

/-- Iterating a loop body `n` times (each within `T`), then running the loop from the last
state. -/
theorem ExecLe.loop_iter {c : Cmd} {r : Res} {T T' : ℕ} :
    ∀ (n : ℕ) (f : ℕ → ℕ → Str), (∀ i < n, ExecLe c (f i) (.norm (f (i + 1))) T) →
      ExecLe (.loop c) (f n) r T' → ExecLe (.loop c) (f 0) r (n * T + T')
  | 0, f, _, h => h.cast rfl (by simp)
  | n + 1, f, hs, h => by
    have ih := ExecLe.loop_iter n (fun i => f (i + 1)) (fun i hi => hs (i + 1) (by omega)) h
    exact (ExecLe.loop_norm (hs 0 (by omega)) ih).cast rfl (by rw [Nat.succ_mul]; omega)

theorem ExecLe.push (k : ℕ) (b : Bool) (σ : ℕ → Str) :
    ExecLe (.push k b) σ (.norm (update σ k (b :: σ k))) 1 := ExecLe.of (.push k b σ)

theorem ExecLe.skip (σ : ℕ → Str) : ExecLe .skip σ (.norm σ) 1 := ExecLe.of (.skip σ)

theorem ExecLe.halt (b : Bool) (σ : ℕ → Str) : ExecLe (.halt b) σ (.halt b) 1 :=
  ExecLe.of (.halt b σ)

theorem ExecLe.brk (σ : ℕ → Str) : ExecLe .brk σ (.brk σ) 1 := ExecLe.of (.brk σ)

/-! ### Unary lengths -/

/-- Loop part of `marks`. -/
def marksLoop (a d t : ℕ) : Cmd :=
  .loop (.pop a .brk (.seq (.push t false) (.push d true)) (.seq (.push t true) (.push d true)))

/-- Push `|σ a|` marks onto `d`, using the empty temporary stack `t` (`a` is restored). -/
def marks (a d t : ℕ) : Cmd := .seq (marksLoop a d t) (move t a)

theorem exec_marksLoop {a d t : ℕ} (had : a ≠ d) (hat : a ≠ t) (hdt : d ≠ t) :
    ∀ (l : Str) (σ : ℕ → Str), σ a = l →
    Exec (marksLoop a d t) σ
      (.norm (update (update (update σ a []) t (l.reverse ++ σ t))
        d (List.replicate l.length true ++ σ d))) (3 * l.length + 2)
  | [], σ, hk => (Exec.loop_brk (Exec.pop_nil hk (Exec.brk σ))).cast
      (by
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [List.replicate_succ']) rfl
  | x :: l, σ, hk => by
    have h1 : Exec (.pop a .brk (.seq (.push t false) (.push d true))
        (.seq (.push t true) (.push d true))) σ
        (.norm (update (update (update σ a l) t (x :: σ t)) d (true :: σ d))) 3 := by
      have ea : update σ a l t = σ t := update_of_ne (Ne.symm hat) _ _
      have eb : update (update σ a l) t (x :: σ t) d = σ d := by
        rw [update_of_ne hdt, update_of_ne (Ne.symm had)]
      refine Exec.pop_cons hk ?_
      cases x
      · exact (Exec.seq_norm (Exec.push t false _) (Exec.push d true _)).cast
          (by rw [ea, eb]) rfl
      · exact (Exec.seq_norm (Exec.push t true _) (Exec.push d true _)).cast
          (by rw [ea, eb]) rfl
    have h2 := exec_marksLoop had hat hdt l
      (update (update (update σ a l) t (x :: σ t)) d (true :: σ d))
      (by rw [update_of_ne had, update_of_ne hat, update_self])
    refine (Exec.loop_norm h1 h2).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [List.replicate_succ']

theorem exec_marks {a d t : ℕ} (had : a ≠ d) (hat : a ≠ t) (hdt : d ≠ t) (σ : ℕ → Str)
    (ht : σ t = []) :
    Exec (marks a d t) σ (.norm (update σ d (List.replicate (σ a).length true ++ σ d)))
      (5 * (σ a).length + 4) := by
  have h1 := exec_marksLoop had hat hdt (σ a) σ rfl
  set σ1 := update (update (update σ a []) t ((σ a).reverse ++ σ t)) d
    (List.replicate (σ a).length true ++ σ d) with hσ1
  have e1 : σ1 t = (σ a).reverse := by simp [σ1, ht, Ne.symm hdt]
  have h2 := exec_move (Ne.symm hat) _ σ1 e1
  refine (Exec.seq_norm h1 h2).cast ?_ (by simp; omega)
  congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [List.replicate_succ']

/-! ### Unary multiplication -/

/-- Loop body of `mul`. -/
def mulBody (b c ta tm : ℕ) : Cmd := .seq (.push ta true) (copyVia b c tm)

/-- Loop part of `mul`. -/
def mulLoop (a b c ta tm : ℕ) : Cmd := .loop (.pop a .brk (mulBody b c ta tm) (mulBody b c ta tm))

/-- Push `|σ a| · |σ b|` marks onto `c`, if `a` and `b` hold marks (`a` is restored). -/
def mul (a b c ta tm : ℕ) : Cmd := .seq (mulLoop a b c ta tm) (move ta a)

section Mul

variable {a b c ta tm : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hata : a ≠ ta) (hatm : a ≠ tm)
  (hbc : b ≠ c) (hbta : b ≠ ta) (hbtm : b ≠ tm) (hcta : c ≠ ta) (hctm : c ≠ tm) (htatm : ta ≠ tm)

include hab hac hata hatm hbc hbta hbtm hcta hctm htatm in
theorem exec_mulLoop (y : ℕ) : ∀ (m : ℕ) (σ : ℕ → Str), σ a = List.replicate m true →
    σ b = List.replicate y true → σ tm = [] →
    Exec (mulLoop a b c ta tm) σ
      (.norm (update (update (update σ a []) ta (List.replicate m true ++ σ ta))
        c (List.replicate (m * y) true ++ σ c))) (m * (5 * y + 6) + 2)
  | 0, σ, hk, _, _ => (Exec.loop_brk (Exec.pop_nil hk (Exec.brk σ))).cast
      (by
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [List.replicate_succ']) (by simp)
  | m + 1, σ, hk, hb, htm => by
    set σ1 := update (update (update σ a (List.replicate m true)) ta (true :: σ ta)) c
      (List.replicate y true ++ σ c) with hσ1
    have h1 : Exec (.pop a .brk (mulBody b c ta tm) (mulBody b c ta tm)) σ (.norm σ1)
        (5 * y + 6) := by
      have hk' : σ a = true :: List.replicate m true := by rw [hk, List.replicate_succ]
      refine (Exec.pop_cons hk' ?_).cast rfl (show 5 * y + 5 + 1 = _ by omega)
      rw [ite_self]
      set σ0 := update (update σ a (List.replicate m true)) ta (true :: σ ta)
      have e0 : update σ a (List.replicate m true) ta = σ ta := update_of_ne (Ne.symm hata) _ _
      have hcv := exec_copyVia hbc hbtm hctm (update (update σ a (List.replicate m true)) ta
        (true :: σ ta)) (by rw [update_of_ne (Ne.symm htatm), update_of_ne (Ne.symm hatm), htm])
      refine (Exec.seq_norm ((Exec.push ta true _).cast (by rw [e0]) rfl) hcv).cast ?_
        (by rw [update_of_ne hbta, update_of_ne (Ne.symm hab), hb]; simp; omega)
      rw [update_of_ne hbta, update_of_ne (Ne.symm hab), hb,
        update_of_ne hcta, update_of_ne (Ne.symm hac)]
    have h2 := exec_mulLoop y m σ1 (by simp [σ1, hac, hata]) (by simp [σ1, hbc, hbta, Ne.symm hab, hb])
      (by simp [σ1, hctm.symm, htatm.symm, hatm.symm, htm])
    refine (Exec.loop_norm h1 h2).cast ?_ (by ring)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> (simp_all [List.replicate_succ', Nat.succ_mul]; try rw [List.replicate_add, List.append_assoc])

include hab hac hata hatm hbc hbta hbtm hcta hctm htatm in
theorem exec_mul (x y : ℕ) (σ : ℕ → Str) (ha : σ a = List.replicate x true)
    (hb : σ b = List.replicate y true) (hta : σ ta = []) (htm : σ tm = []) :
    Exec (mul a b c ta tm) σ (.norm (update σ c (List.replicate (x * y) true ++ σ c)))
      (x * (5 * y + 8) + 4) := by
  have h1 := exec_mulLoop hab hac hata hatm hbc hbta hbtm hcta hctm htatm y x σ ha hb htm
  set σ1 := update (update (update σ a []) ta (List.replicate x true ++ σ ta)) c
    (List.replicate (x * y) true ++ σ c) with hσ1
  have e1 : σ1 ta = List.replicate x true := by simp [σ1, hta, Ne.symm hcta]
  have h2 := exec_move (Ne.symm hata) _ σ1 e1
  refine (Exec.seq_norm h1 h2).cast ?_ (by simp; ring)
  congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all

end Mul

/-! ### Comparing lengths -/

/-- Second pop of `eqLen` after a successful first pop. -/
def eqLenE (b : ℕ) (r : Bool) : Cmd := .pop b (.halt r) .skip .skip

/-- Compare `|σ a|` and `|σ b|`, popping both in lockstep; halt `r` if they differ. -/
def eqLen (a b : ℕ) (r : Bool) : Cmd :=
  .loop (.pop a (.pop b .brk (.halt r) (.halt r)) (eqLenE b r) (eqLenE b r))

theorem exec_eqLen {a b : ℕ} (hab : a ≠ b) (r : Bool) : ∀ (l1 l2 : Str) (σ : ℕ → Str),
    σ a = l1 → σ b = l2 →
    (l1.length = l2.length →
      Exec (eqLen a b r) σ (.norm (update (update σ a []) b [])) (3 * l1.length + 3)) ∧
    (l1.length ≠ l2.length → ExecLe (eqLen a b r) σ (.halt r) (3 * l1.length + 3))
  | [], [], σ, h1, h2 => ⟨fun _ => (Exec.loop_brk (Exec.pop_nil h1 (Exec.pop_nil h2
      (Exec.brk σ)))).cast (by
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all) rfl,
      fun h => absurd rfl h⟩
  | [], x :: s, σ, h1, h2 => ⟨fun h => by simp at h, fun _ =>
      (ExecLe.loop_halt (ExecLe.pop_nil h1 (ExecLe.pop_same h2 (ExecLe.halt r _)))).cast rfl
        (by simp)⟩
  | x :: s, [], σ, h1, h2 => ⟨fun h => by simp at h, fun _ =>
      (ExecLe.loop_halt (ExecLe.pop_same h1 (ExecLe.pop_nil
        (by rw [update_of_ne (Ne.symm hab), h2]) (ExecLe.halt r _)))).cast rfl (by simp)⟩
  | x :: s, y :: s2, σ, h1, h2 => by
    have hb1 : update σ a s b = y :: s2 := by rw [update_of_ne (Ne.symm hab), h2]
    have hbody : Exec (.pop a (.pop b .brk (.halt r) (.halt r)) (eqLenE b r) (eqLenE b r)) σ
        (.norm (update (update σ a s) b s2)) 3 :=
      Exec.pop_cons h1 (by
        rw [ite_self]; exact Exec.pop_cons hb1 (by rw [ite_self]; exact Exec.skip _))
    have ih := exec_eqLen hab r s s2 (update (update σ a s) b s2)
      (by rw [update_of_ne hab, update_self]) (by rw [update_self])
    refine ⟨fun h => ?_, fun h => ?_⟩
    · refine (Exec.loop_norm hbody (ih.1 (by simpa using h))).cast ?_ (by simp; omega)
      congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all
    · obtain ⟨t, ht, he⟩ := ih.2 (by simpa using h)
      exact ⟨3 + t, by simp; omega, Exec.loop_norm hbody he⟩

/-- Second pop of `gtLoop` after a successful first pop. -/
def gtE (yes : ℕ) : Cmd := .pop yes .brk .skip .skip

/-- Pop `no` and `yes` in lockstep; halt `true` iff `yes` is strictly longer. -/
def gtLoop (yes no : ℕ) : Cmd :=
  .loop (.pop no (.pop yes .brk (.halt true) (.halt true)) (gtE yes) (gtE yes))

/-- Halt `true` if `|σ yes| > |σ no|`; otherwise empty both stacks. -/
def gtCmd (yes no : ℕ) : Cmd := .seq (gtLoop yes no) (.seq (drain yes) (drain no))

theorem exec_gtLoop {yes no : ℕ} (hyn : yes ≠ no) : ∀ (l2 l1 : Str) (σ : ℕ → Str),
    σ yes = l1 → σ no = l2 →
    (l2.length < l1.length → ExecLe (gtLoop yes no) σ (.halt true) (3 * l2.length + 3)) ∧
    (¬ l2.length < l1.length → ∃ s1 s2 : Str, s1.length ≤ l1.length ∧ s2.length ≤ l2.length ∧
      ExecLe (gtLoop yes no) σ (.norm (update (update σ yes s1) no s2)) (3 * l2.length + 3))
  | [], [], σ, h1, h2 => ⟨fun h => by simp at h, fun _ => ⟨[], [], by simp, by simp,
      (ExecLe.loop_brk (ExecLe.pop_nil h2 (ExecLe.pop_nil h1 (ExecLe.brk σ)))).cast
        (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all) (by simp)⟩⟩
  | [], x :: s, σ, h1, h2 => ⟨fun _ =>
      (ExecLe.loop_halt (ExecLe.pop_nil h2 (ExecLe.pop_same h1 (ExecLe.halt true _)))).cast rfl
        (by simp), fun h => by simp at h⟩
  | x :: s, [], σ, h1, h2 => ⟨fun h => by simp at h, fun _ => ⟨[], s, by simp, by simp,
      (ExecLe.loop_brk (ExecLe.pop_same h2 (ExecLe.pop_nil
        (by rw [update_of_ne hyn, h1]) (ExecLe.brk _)))).cast
        (by
          congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all) (by simp)⟩⟩
  | x :: s, y :: s1, σ, h1, h2 => by
    have hb1 : update σ no s yes = y :: s1 := by rw [update_of_ne hyn, h1]
    have hbody : ExecLe (.pop no (.pop yes .brk (.halt true) (.halt true)) (gtE yes) (gtE yes)) σ
        (.norm (update (update σ no s) yes s1)) 3 :=
      ExecLe.pop_same h2 (ExecLe.pop_same hb1 (ExecLe.skip _))
    have ih := exec_gtLoop hyn s s1 (update (update σ no s) yes s1)
      (by rw [update_self]) (by rw [update_of_ne (Ne.symm hyn), update_self])
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact (ExecLe.loop_norm hbody (ih.1 (by simpa using h))).cast rfl (by simp; omega)
    · obtain ⟨t1, t2, ht1, ht2, he⟩ := ih.2 (by simpa using h)
      refine ⟨t1, t2, by simp; omega, by simp; omega,
        (ExecLe.loop_norm hbody he).cast ?_ (by simp; omega)⟩
      congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all

theorem exec_gtCmd {yes no : ℕ} (hyn : yes ≠ no) (σ : ℕ → Str) :
    ((σ no).length < (σ yes).length →
      ExecLe (gtCmd yes no) σ (.halt true) (3 * (σ no).length + 3)) ∧
    (¬ (σ no).length < (σ yes).length →
      ExecLe (gtCmd yes no) σ (.norm (update (update σ yes []) no []))
        (5 * (σ no).length + 2 * (σ yes).length + 7)) := by
  have h := exec_gtLoop hyn (σ no) (σ yes) σ rfl rfl
  refine ⟨fun hl => ExecLe.seq_halt (h.1 hl), fun hl => ?_⟩
  obtain ⟨s1, s2, h1, h2, he⟩ := h.2 hl
  have d1 := exec_drain yes s1 (update (update σ yes s1) no s2)
    (by rw [update_of_ne hyn, update_self])
  have d2 := exec_drain no s2 (update (update (update σ yes s1) no s2) yes [])
    (by rw [update_of_ne (Ne.symm hyn), update_self])
  refine (ExecLe.seq_norm he (ExecLe.seq_norm (ExecLe.of d1) (ExecLe.of d2))).cast ?_
    (by omega)
  congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all

/-! ### Draining a range of stacks -/

/-- Empty the stacks `o, …, o + N - 1`. -/
def drainR (o : ℕ) : ℕ → Cmd
  | 0 => .skip
  | N + 1 => .seq (drainR o N) (drain (o + N))

theorem exec_drainR (o : ℕ) : ∀ (N : ℕ) (σ : ℕ → Str),
    Exec (drainR o N) σ (.norm (fun j => if o ≤ j ∧ j < o + N then [] else σ j))
      (∑ j ∈ Finset.range N, (2 * (σ (o + j)).length + 2) + 1)
  | 0, σ => (Exec.skip σ).cast (by congr 1; funext j; simp) (by simp)
  | N + 1, σ => by
    have h1 := exec_drainR o N σ
    have h2 := exec_drain (o + N) _ (fun j => if o ≤ j ∧ j < o + N then [] else σ j) rfl
    refine (Exec.seq_norm h1 h2).cast ?_ ?_
    · congr 1; funext j; simp only [update_apply]
      by_cases hj : j = o + N
      · simp [hj]
      · rw [if_neg hj]; congr 1; apply propext; omega
    · rw [Finset.sum_range_succ]; simp; omega

/-! ### Calls with clean-up -/

theorem sum_view_two (σ : ℕ → Str) (o M : ℕ) (hσ : ∀ j, o + 2 ≤ j → σ j = []) :
    ∑ j ∈ Finset.range (M + 2), (σ (o + j)).length = (σ o).length + (σ (o + 1)).length := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have : ∑ j ∈ Finset.range M, (σ (o + (j + 1 + 1))).length = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hσ _ (by omega)]; rfl
  rw [this]; simp; omega

theorem lift_lt (σ : ℕ → Str) (o : ℕ) (τ : ℕ → Str) {j : ℕ} (hj : j < o) :
    lift σ o τ j = σ j := by unfold lift; rw [if_pos hj]

/-- Call `q` at offset `o` (stacks `≥ o + 2` empty), push a mark on `yes`/`no` by its answer,
and empty the stacks `o, …, o + nW q + 1` afterwards. -/
def callDrain (q : Prog) (o yes no : ℕ) : Cmd :=
  .seq (.call q o (.push no true) (.push yes true)) (drainR o (Official.nW q + 2))

theorem exec_callDrain {q : Prog} {o yes no : ℕ} {σ : ℕ → Str} {T : ℕ} {b : Bool}
    (hy : yes < o) (hn : no < o) (hσ : ∀ j, o + 2 ≤ j → σ j = [])
    (h : runFor ∅ q T (.run ⟨0, view σ o⟩) = .done b) :
    ExecLe (callDrain q o yes no) σ
      (.norm (fun j => if j < o then update σ (if b then yes else no)
        (true :: σ (if b then yes else no)) j else []))
      (3 * T + 2 * ((σ o).length + (σ (o + 1)).length) + 2 * (Official.nW q + 2) + 3) := by
  obtain ⟨t, τ, ht, h1, h2, hc⟩ := Exec.call_of_runFor (cf := .push no true)
    (ct := .push yes true) h
  set k := if b then yes else no with hk
  have hko : k < o := by rw [hk]; split <;> assumption
  have hpush : Exec (if b then Cmd.push yes true else Cmd.push no true) (lift σ o τ)
      (.norm (update (lift σ o τ) k (true :: σ k))) 1 := by
    rw [← lift_lt σ o τ hko, hk]; cases b <;> exact Exec.push _ _ _
  have hcall := hc hpush
  set N := Official.nW q + 2
  have hd := exec_drainR o N (update (lift σ o τ) k (true :: σ k))
  refine (ExecLe.of (Exec.seq_norm hcall hd)).cast ?_ ?_
  · congr 1; funext j
    by_cases hj : j < o
    · rw [if_neg (by omega), if_pos hj, update_apply, update_apply, lift_lt σ o τ hj]
    · rw [if_neg hj]
      by_cases hj2 : j < o + N
      · rw [if_pos ⟨by omega, hj2⟩]
      · rw [if_neg (by omega), update_of_ne (by omega)]
        unfold lift; rw [if_neg hj, h1 _ (by omega), hσ _ (by omega)]
  · have e1 : ∀ j, update (lift σ o τ) k (true :: σ k) (o + j) = τ j := by
      intro j; rw [update_of_ne (by omega)]; unfold lift; rw [if_neg (by omega)]; congr 1; omega
    simp only [e1]
    have hs := h2 N
    rw [sum_view_two σ o _ hσ] at hs
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega

/-! ### Parsing bit-pair codes -/

/-- One segment of a bit-pair code: `[false, b]` is the data bit `b`, `[true, _]` ends the
segment; returns the data bits and the rest. -/
def seg : Str → Str × Str
  | false :: b :: r => (b :: (seg r).1, (seg r).2)
  | true :: _ :: r => ([], r)
  | _ => ([], [])

/-- Doubling code: each bit `b` becomes `[false, b]`. -/
def dbl (s : Str) : Str := s.flatMap fun b => [false, b]

@[simp] theorem dbl_nil : dbl [] = [] := rfl
@[simp] theorem dbl_cons (b : Bool) (s : Str) : dbl (b :: s) = false :: b :: dbl s := rfl

theorem seg_dbl_sep (w r : Str) : seg (dbl w ++ true :: true :: r) = (w, r) := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [dbl_cons, List.cons_append, seg, ih]

theorem seg_dbl (y : Str) : seg (dbl y) = (y, []) := by
  induction y with
  | nil => rfl
  | cons b y ih => simp only [dbl_cons, seg, ih]

theorem seg_length : ∀ z : Str, (seg z).1.length + (seg z).2.length ≤ z.length
  | [] => by simp [seg]
  | [b] => by cases b <;> simp [seg]
  | false :: b :: r => by have := seg_length r; simp [seg]; omega
  | true :: _ :: r => by simp [seg]; omega

/-- Loop parsing one segment from `src`, pushing the data bits onto `dst`. -/
def segCmd (src dst : ℕ) : Cmd :=
  .loop (.pop src .brk (.pop src .brk (.push dst false) (.push dst true)) (.pop src .brk .brk .brk))

theorem exec_seg {src dst : ℕ} (hsd : src ≠ dst) : ∀ (z : Str) (σ : ℕ → Str), σ src = z →
    ExecLe (segCmd src dst) σ
      (.norm (update (update σ src (seg z).2) dst ((seg z).1.reverse ++ σ dst)))
      (2 * z.length + 3)
  | [], σ, h => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk σ))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [seg]) (by simp)
  | [false], σ, h => (ExecLe.loop_brk (ExecLe.pop_cons h (ExecLe.pop_nil (by simp)
      (ExecLe.brk _)))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [seg]) (by simp)
  | [true], σ, h => (ExecLe.loop_brk (ExecLe.pop_cons h (ExecLe.pop_nil (by simp)
      (ExecLe.brk _)))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [seg]) (by simp)
  | true :: x :: r, σ, h => (ExecLe.loop_brk (ExecLe.pop_cons h (ExecLe.pop_same (b := x) (s := r)
      (by simp) (ExecLe.brk _)))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [seg]) (by simp)
  | false :: b :: r, σ, h => by
    have hbody : ExecLe (.pop src .brk (.pop src .brk (.push dst false) (.push dst true))
        (.pop src .brk .brk .brk)) σ (.norm (update (update σ src r) dst (b :: σ dst))) 3 := by
      refine ExecLe.pop_cons h ?_
      simp only [Bool.false_eq_true, if_false]
      refine ExecLe.pop_cons (s := r) (b := b) (by simp) ?_
      cases b
      · exact (ExecLe.push dst false _).cast (by rw [update_idem, update_of_ne (Ne.symm hsd)]) le_rfl
      · exact (ExecLe.push dst true _).cast (by rw [update_idem, update_of_ne (Ne.symm hsd)]) le_rfl
    have ih := exec_seg hsd r (update (update σ src r) dst (b :: σ dst))
      (by rw [update_of_ne hsd, update_self])
    refine (ExecLe.loop_norm hbody ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [seg]

end Pnp.Relativize.Struct
