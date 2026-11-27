import Pnp.KarpLipton.EvalCmd

/-!
# Table look-up and parsing loops for the Karp–Lipton program (M32e, part 1)

The program deciding the inner predicate of the official `Σ₂ᴾ` form must halt within polynomial
time on **every** bit string, but the official decider of `L''` (from
`Pnp.Relativize.OfficialCode.decide_of_inPolynomialTime`) is only known to halt on valid codes.
So the program never copies input bits into a call of that decider: every input symbol is read by
a **fixed-width table look-up** whose actions push fixed (valid) codes.

* `fi r l`: position of the first `true` among the first `r` bits of `l` (missing bits read
  `false`).
* `tabK src a b S T d i r`: pop `r` bits of `src`; at the first `true` (position `j`) push
  `S (i + j)` on `a` and `T (i + j)` on `b`, otherwise push `S d`, `T d` (`exec_tabK`).
* `slLoop`: repeat “pop a tag bit; if `false`, a table look-up and a mark” until a `true` tag or
  the end of the stack (`exec_slLoop`, semantics `sl`).
* `selLoop`: skip `m` segments of a bit-pair code (`exec_selLoop`, semantics `segIt`).
-/

namespace Pnp.Relativize.Struct

open Function

/-! ## First `true` among the first `r` bits -/

/-- Position of the first `true` among the first `r` bits (missing bits read `false`). -/
def fi : ℕ → Str → Option ℕ
  | 0, _ => none
  | r + 1, l => if l.getD 0 false then some 0 else (fi r (l.drop 1)).map (· + 1)

@[simp] theorem fi_nil : ∀ r, fi r [] = none
  | 0 => rfl
  | r + 1 => by simp [fi, fi_nil r]

theorem fi_false (r : ℕ) (l : Str) : fi (r + 1) (false :: l) = (fi r l).map (· + 1) := by
  simp [fi]

theorem fi_true (r : ℕ) (l : Str) : fi (r + 1) (true :: l) = some 0 := by
  simp [fi]

theorem fi_lt : ∀ (r : ℕ) (l : Str) (j : ℕ), fi r l = some j → j < r
  | 0, _, j, h => by simp [fi] at h
  | r + 1, l, j, h => by
    unfold fi at h
    split_ifs at h with h1
    · cases h; omega
    · cases e : fi r (l.drop 1) with
      | none => rw [e] at h; simp at h
      | some j' => rw [e] at h; simp at h; have := fi_lt r _ j' e; omega

/-- The first `true` of a one-hot block. -/
theorem fi_block (i k : ℕ) (rest : Str) (hi : i < k) :
    fi k (List.replicate i false ++ true :: List.replicate (k - 1 - i) false ++ rest) = some i := by
  induction i generalizing k with
  | zero =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [fi]
  | succ i ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have := ih k (by omega)
    rw [List.replicate_succ, List.cons_append, List.cons_append, fi_false]
    rw [show k + 1 - 1 - (i + 1) = k - 1 - i by omega]
    rw [List.append_assoc] at this ⊢
    rw [this]; rfl

/-! ## Table look-up -/

section Tab

variable (src a b : ℕ) (S T : ℕ → Str) (d : ℕ)

/-- Push `S j` on `a` and `T j` on `b`. -/
def push2 (j : ℕ) : Cmd := .seq (pushList a (S j)) (pushList b (T j))

/-- Fixed-width table look-up (see the module doc). -/
def tabK : ℕ → ℕ → Cmd
  | _, 0 => push2 a b S T d
  | i, r + 1 => .pop src (push2 a b S T d) (tabK (i + 1) r) (.seq (dropN src r) (push2 a b S T i))

end Tab

/-- The state after the pushes of `push2`. -/
def st2 (a b : ℕ) (s t : Str) (σ : ℕ → Str) : ℕ → Str :=
  update (update σ a (s ++ σ a)) b (t ++ σ b)

theorem exec_push2 (a b : ℕ) (S T : ℕ → Str) (j : ℕ) (σ : ℕ → Str) (hab : a ≠ b) :
    ExecLe (push2 a b S T j) σ (.norm (st2 a b (S j) (T j) σ)) ((S j).length + (T j).length + 2) := by
  have h1 := exec_pushList a (S j) σ
  have h2 := exec_pushList b (T j) (update σ a (S j ++ σ a))
  refine (ExecLe.of (Exec.seq_norm h1 h2)).cast ?_ (by omega)
  rw [update_of_ne (Ne.symm hab)]; rfl

theorem exec_tabK {src a b : ℕ} (S T : ℕ → Str) (d B : ℕ) (hsa : src ≠ a) (hsb : src ≠ b)
    (hab : a ≠ b) (hB : ∀ j, (S j).length + (T j).length ≤ B) :
    ∀ (r i : ℕ) (σ : ℕ → Str),
      ExecLe (tabK src a b S T d i r) σ
        (.norm (st2 a b (S ((fi r (σ src)).elim d (i + ·))) (T ((fi r (σ src)).elim d (i + ·)))
          (update σ src ((σ src).drop r)))) (2 * r + B + 3)
  | 0, i, σ => by
    refine (exec_push2 a b S T d σ hab).cast ?_ (by have := hB d; omega)
    simp [fi]
  | r + 1, i, σ => by
    cases hs : σ src with
    | nil =>
      refine (ExecLe.pop_nil hs (exec_push2 a b S T d σ hab)).cast ?_ (by have := hB d; omega)
      simp only [fi_nil, Option.elim_none, List.drop_nil]
      rw [← hs, update_eq_self]
    | cons x l =>
      cases x
      · have ih := exec_tabK S T d B hsa hsb hab hB r (i + 1) (update σ src l)
        refine (ExecLe.pop_cons hs ih).cast ?_ (by omega)
        simp only [update_self, update_idem, fi_false, List.drop_succ_cons]
        congr 3 <;> cases fi r l <;> simp [Nat.add_assoc, Nat.add_comm 1]
      · have h1 := exec_dropN src r (update σ src l)
        have h2 := exec_push2 a b S T i (update (update σ src l) src
          ((update σ src l src).drop r)) hab
        refine (ExecLe.pop_cons hs (h1.seq_norm h2)).cast ?_ (by have := hB i; omega)
        simp [fi_true]

/-! ## Parsing loops -/

/-- Semantics of the parsing loop: the table indices read and the rest of the stack. -/
def sl (r d : ℕ) : Str → List ℕ × Str
  | [] => ([], [])
  | true :: l => ([], l)
  | false :: l => ((fi r l).getD d :: (sl r d (l.drop r)).1, (sl r d (l.drop r)).2)
termination_by l => l.length
decreasing_by all_goals (simp only [List.length_drop, List.length_cons]; omega)

theorem sl_nil (r d : ℕ) : sl r d [] = ([], []) := by unfold sl; rfl
theorem sl_true (r d : ℕ) (l : Str) : sl r d (true :: l) = ([], l) := by
  unfold sl; rfl
theorem sl_false (r d : ℕ) (l : Str) :
    sl r d (false :: l) = ((fi r l).getD d :: (sl r d (l.drop r)).1, (sl r d (l.drop r)).2) :=
  by conv_lhs => unfold sl

theorem sl_length : ∀ (r d : ℕ) (l : Str), (sl r d l).1.length + (sl r d l).2.length ≤ l.length
  | _, _, [] => by simp [sl_nil]
  | _, _, true :: l => by simp [sl_true]
  | r, d, false :: l => by
    have := sl_length r d (l.drop r)
    rw [sl_false]; simp only [List.length_cons, List.length_drop] at this ⊢; omega
termination_by _ _ l => l.length
decreasing_by all_goals (simp only [List.length_drop, List.length_cons]; omega)

section Loop

variable (src a b c : ℕ) (S T : ℕ → Str) (r d : ℕ)

/-- The parsing loop: tag `false` ↦ table look-up and a mark on `c`; tag `true` or end ↦ stop. -/
def slLoop : Cmd :=
  .loop (.pop src .brk (.seq (tabK src a b S T d 0 r) (.push c true)) .brk)

end Loop

theorem exec_slLoop {src a b c : ℕ} (S T : ℕ → Str) (r d B : ℕ) (hsa : src ≠ a) (hsb : src ≠ b)
    (hsc : src ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hB : ∀ j, (S j).length + (T j).length ≤ B) :
    ∀ (n : ℕ) (σ : ℕ → Str), (σ src).length ≤ n →
      ExecLe (slLoop src a b c S T r d) σ
        (.norm (update (update (update (update σ src (sl r d (σ src)).2)
          a ((sl r d (σ src)).1.reverse.flatMap S ++ σ a))
          b ((sl r d (σ src)).1.reverse.flatMap T ++ σ b))
          c (List.replicate (sl r d (σ src)).1.length true ++ σ c)))
        ((σ src).length * (2 * r + B + 6) + 2)
  | n, σ, hn => by
    cases hs : σ src with
    | nil =>
      refine (ExecLe.loop_brk (ExecLe.pop_nil hs (ExecLe.brk σ))).cast ?_ (by simp)
      congr 1; funext j; simp only [update_apply, sl_nil]; split_ifs <;> simp_all
    | cons x l =>
      cases x
      · rw [hs] at hn
        obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
        have ht := exec_tabK S T d B hsa hsb hab hB r 0 (update σ src l)
        simp only [update_self] at ht
        set j := (fi r l).elim d (0 + ·) with hj
        have hj' : j = (fi r l).getD d := by rcases h : fi r l with _ | j0 <;> simp [hj, h]
        set σ1 := st2 a b (S j) (T j) (update (update σ src l) src (l.drop r)) with hσ1
        have hp := ExecLe.push c true σ1
        have hbody := ExecLe.pop_cons (cn := .brk) (ct := .brk) hs (ht.seq_norm hp)
        have hσ1s : σ1 src = l.drop r := by simp [σ1, st2, hsa, hsb]
        have ih := exec_slLoop S T r d B hsa hsb hsc hab hac hbc hB n
          (update σ1 c (true :: σ1 c)) (by
            rw [update_of_ne hsc, hσ1s, List.length_drop]; simp at hn; omega)
        rw [update_of_ne hsc, hσ1s] at ih
        refine (ExecLe.loop_norm hbody ih).cast ?_ ?_
        · congr 1; funext k
          simp only [σ1, st2, update_apply, sl_false, ← hj']
          split_ifs <;> simp_all [List.replicate_succ']
        · simp only [List.length_cons, List.length_drop]
          have : (l.length - r) * (2 * r + B + 6) ≤ l.length * (2 * r + B + 6) :=
            Nat.mul_le_mul_right _ (by omega)
          nlinarith
      · refine (ExecLe.loop_brk (ExecLe.pop_cons hs (ExecLe.brk _))).cast ?_ (by simp)
        congr 1; funext j; simp only [update_apply, sl_true]; split_ifs <;> simp_all

/-! ## Skipping segments -/

/-- The rest after skipping `m` segments. -/
def segIt (W : Str) : ℕ → Str
  | 0 => W
  | m + 1 => (seg (segIt W m)).2

/-- The skipped data bits (reversed, latest on top). -/
def segJ (W : Str) : ℕ → Str
  | 0 => []
  | m + 1 => (seg (segIt W m)).1.reverse ++ segJ W m

theorem segIt_length (W : Str) : ∀ m, (segIt W m).length + (segJ W m).length ≤ W.length
  | 0 => by simp [segIt, segJ]
  | m + 1 => by
    have := segIt_length W m
    have := seg_length (segIt W m)
    simp only [segIt, segJ, List.length_append, List.length_reverse]; omega

/-- Skip as many segments of `ws` as there are marks on `cnt`, into `jk`. -/
def selLoop (cnt ws jk : ℕ) : Cmd := .loop (.pop cnt .brk (segCmd ws jk) (segCmd ws jk))

theorem exec_selLoop {cnt ws jk : ℕ} (hcw : cnt ≠ ws) (hcj : cnt ≠ jk) (hwj : ws ≠ jk)
    (W : Str) : ∀ (m i : ℕ) (σ : ℕ → Str), σ cnt = List.replicate m true →
      σ ws = segIt W i → σ jk = segJ W i →
      ExecLe (selLoop cnt ws jk) σ
        (.norm (update (update (update σ cnt []) ws (segIt W (i + m))) jk (segJ W (i + m))))
        (m * (2 * W.length + 4) + 2)
  | 0, i, σ, hc, hw, hj => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil hc (ExecLe.brk σ))).cast ?_ (by simp)
    congr 1; funext k; simp only [update_apply]; split_ifs <;> simp_all
  | m + 1, i, σ, hc, hw, hj => by
    rw [List.replicate_succ] at hc
    have hs := exec_seg hwj (σ ws) (update σ cnt (List.replicate m true))
      (by rw [update_of_ne (Ne.symm hcw)])
    have hb := ExecLe.pop_same (cn := .brk) hc hs
    set σ1 := update (update (update σ cnt (List.replicate m true)) ws (seg (σ ws)).2) jk
      ((seg (σ ws)).1.reverse ++ update σ cnt (List.replicate m true) jk) with hσ1
    have ih := exec_selLoop hcw hcj hwj W m (i + 1) σ1 (by simp [σ1, hcw, hcj])
      (by simp [σ1, hwj, hw, segIt]) (by simp [σ1, hw, segJ, update_of_ne (Ne.symm hcj), hj])
    refine (ExecLe.loop_norm hb ih).cast ?_ ?_
    · congr 1; funext k; simp only [σ1, update_apply]
      rw [show i + 1 + m = i + (m + 1) by omega]
      split_ifs <;> simp_all
    · have := segIt_length W i
      rw [hw]; nlinarith

end Pnp.Relativize.Struct
