import Pnp.Oracle.Machine

/-!
# Truncating certificates

A run of `t` steps pops at most `t` bits from the certificate stack, so it cannot tell a
certificate `w` apart from its prefix `w.take t` (for the empty oracle, whose answers do not
depend on the query string).

* `runFor_take`: if `p` halts with answer `b` on `(x, w)` within `t` steps, it halts with the
  same answer on `(x, w.take t)`.
-/

namespace Pnp.Relativize

/-- `c'` is `c` with the certificate stack `1` cut off below the next `m` cells that can be
reached by popping. -/
def TruncRel (m : ℕ) (c c' : Cfg) : Prop :=
  c'.pc = c.pc ∧ (∀ j, j ≠ 1 → c'.stk j = c.stk j) ∧
    ∃ u r : Str, c.stk 1 = u ++ r ∧ c'.stk 1 = u ++ r.take m

theorem TruncRel.mono {m m' : ℕ} {c c' : Cfg} (h : TruncRel m' c c') (hm : m ≤ m') :
    TruncRel m c c' := by
  obtain ⟨hpc, hj, u, r, h1, h2⟩ := h
  refine ⟨hpc, hj, u ++ r.take (m' - m), r.drop (m' - m), ?_, ?_⟩
  · rw [h1, List.append_assoc, List.take_append_drop]
  · rw [h2, List.append_assoc, ← List.take_add]
    congr 2; omega

theorem TruncRel.update {m : ℕ} {c c' : Cfg} (h : TruncRel m c c') {k : ℕ} (hk : k ≠ 1)
    (s : Str) (pc : ℕ) :
    TruncRel m ⟨pc, Function.update c.stk k s⟩ ⟨pc, Function.update c'.stk k s⟩ := by
  obtain ⟨_, hj, u, r, h1, h2⟩ := h
  refine ⟨rfl, fun j hj1 => ?_, u, r, ?_, ?_⟩
  · by_cases hjk : j = k
    · subst hjk; simp
    · simp [Function.update_of_ne hjk, hj j hj1]
  · simp [Function.update_of_ne (Ne.symm hk), h1]
  · simp [Function.update_of_ne (Ne.symm hk), h2]

theorem truncRel_step {p : Prog} {m : ℕ} {c c' : Cfg} (h : TruncRel (m + 1) c c') :
    (∀ b, step ∅ p c = .done b → step ∅ p c' = .done b) ∧
      (∀ d, step ∅ p c = .run d → ∃ d', step ∅ p c' = .run d' ∧ TruncRel m d d') := by
  have hrel := h
  obtain ⟨hpc, hj, u, r, h1, h2⟩ := h
  unfold step
  rw [hpc]
  rcases hp : p[c.pc]? with _ | ins
  · exact ⟨fun b h => h, fun d h => by simp at h⟩
  cases ins with
  | halt b => exact ⟨fun b' h => h, fun d h => by simp at h⟩
  | query k y n =>
    refine ⟨fun b h => by simp at h, fun d h => ?_⟩
    simp only [Set.mem_empty_iff_false, if_false, State.run.injEq] at h ⊢
    subst h
    exact ⟨_, rfl, (show TruncRel (m + 1) ⟨n, c.stk⟩ ⟨n, c'.stk⟩ from
      ⟨rfl, hj, u, r, h1, h2⟩).mono (by omega)⟩
  | push k b n =>
    refine ⟨fun b h => by simp at h, fun d h => ?_⟩
    simp only [State.run.injEq] at h ⊢
    subst h
    refine ⟨_, rfl, ?_⟩
    by_cases hk : k = 1
    · subst hk
      refine TruncRel.mono ⟨rfl, fun j hj1 => ?_, b :: u, r, ?_, ?_⟩ (by omega : m ≤ m + 1)
      · simp [Function.update_of_ne hj1, hj j hj1]
      · simp [h1]
      · simp [h2]
    · rw [hj k hk]
      exact (TruncRel.update hrel hk _ n).mono (by omega)
  | pop k z f t =>
    refine ⟨fun b h => ?_, fun d h => ?_⟩
    · rcases hck : c.stk k with _ | ⟨a, s⟩ <;> simp [hck] at h
    by_cases hk : k = 1
    · subst hk
      rcases u with _ | ⟨a, u⟩
      · rcases r with _ | ⟨a, r⟩
        · simp only [List.nil_append, List.take_nil] at h1 h2
          simp only [h1, h2, State.run.injEq] at h ⊢
          subst h
          exact ⟨_, rfl, rfl, hj, [], [], by simp [h1], by simp [h2]⟩
        · simp only [List.nil_append, List.take_succ_cons] at h1 h2
          simp only [h1, h2, State.run.injEq] at h ⊢
          subst h
          refine ⟨_, rfl, rfl, fun j hj1 => ?_, [], r, by simp, by simp⟩
          simp [Function.update_of_ne hj1, hj j hj1]
      · simp only [List.cons_append] at h1 h2
        simp only [h1, h2, State.run.injEq] at h ⊢
        subst h
        refine ⟨_, rfl, TruncRel.mono ⟨rfl, fun j hj1 => ?_, u, r, by simp, by simp⟩
          (by omega : m ≤ m + 1)⟩
        simp [Function.update_of_ne hj1, hj j hj1]
    · simp only [hj k hk]
      rcases hck : c.stk k with _ | ⟨a, s⟩
      · simp only [hck, State.run.injEq] at h ⊢
        subst h
        exact ⟨_, rfl, (show TruncRel (m + 1) ⟨z, c.stk⟩ ⟨z, c'.stk⟩ from
          ⟨rfl, hj, u, r, h1, h2⟩).mono (by omega)⟩
      · simp only [hck, State.run.injEq] at h ⊢
        subst h
        exact ⟨_, rfl, (TruncRel.update hrel hk s _).mono (by omega)⟩

theorem runFor_truncRel {p : Prog} {b : Bool} :
    ∀ (t m : ℕ) (c c' : Cfg), t ≤ m → TruncRel m c c' →
      runFor ∅ p t (.run c) = .done b → runFor ∅ p t (.run c') = .done b
  | 0, _, _, _, _, _, h => by simp at h
  | t + 1, m, c, c', ht, hr, h => by
    have hr' := hr.mono ht
    rw [runFor_succ_run] at h ⊢
    rcases hs : step ∅ p c with d | b'
    · rw [hs] at h
      obtain ⟨d', hd', hrel⟩ := (truncRel_step hr').2 d hs
      rw [hd']
      exact runFor_truncRel t t d d' le_rfl hrel h
    · rw [hs, runFor_done] at h
      rw [(truncRel_step hr').1 b' hs, h, runFor_done]

/-- A run of `t` steps only sees the first `t` bits of the certificate. -/
theorem runFor_take {p : Prog} {t : ℕ} {x w : Str} {b : Bool}
    (h : runFor ∅ p t (.run (init [x, w])) = .done b) :
    runFor ∅ p t (.run (init [x, w.take t])) = .done b := by
  refine runFor_truncRel t t (init [x, w]) (init [x, w.take t]) le_rfl ⟨rfl, fun j hj => ?_, [], w, by simp [init], by
    simp [init]⟩ h
  rcases j with _ | _ | j
  · rfl
  · exact absurd rfl hj
  · simp [init]

end Pnp.Relativize
