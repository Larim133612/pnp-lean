import Pnp.Oracle.Combinators

/-!
# Baker–Gill–Solovay, first half: an oracle `A` with `NP^A ⊆ P^A`

Fix a surjection `e : ℕ → Prog × ℕ` enumerating all verifiers. The oracle `A` is defined
by well-founded recursion on string length: a string `q` lies in `A` iff
`q = code i x T` and verifier `e i` accepts `x` with some short certificate, querying
`A` only on strings shorter than `q`. With padding `T = (|x|+2)^(k+1)` every query of
the verifier is shorter than `q`, so the restriction is harmless (query locality); hence
`x ∈ L ↔ code i x T ∈ A`, which the deterministic machine `queryProg` decides by
writing the code and asking one query.
-/

namespace Pnp.Relativize

open Function Comb

/-! ### The code -/

theorem replicate_false_inj : ∀ {a a' : ℕ} {s s' : Str},
    List.replicate a true ++ false :: s = List.replicate a' true ++ false :: s' →
      a = a' ∧ s = s'
  | 0, 0, _, _, h => by simpa using h
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | a + 1, a' + 1, s, s', h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    have := replicate_false_inj h
    exact ⟨by omega, this.2⟩

theorem flatMap_pair_inj : ∀ {x y : Str},
    (x.flatMap fun b => [true, b]) = (y.flatMap fun b => [true, b]) → x = y
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: x, b :: y, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
      true_and] at h
    rw [h.1, flatMap_pair_inj h.2]

theorem enc_injective : Injective enc := fun _ _ h =>
  List.reverse_injective (flatMap_pair_inj h)

theorem code_inj {i i' T T' : ℕ} {x x' : Str} (h : code i x T = code i' x' T') :
    i = i' ∧ x = x' := by
  obtain ⟨h1, h2⟩ := replicate_false_inj h
  obtain ⟨_, h4⟩ := replicate_false_inj h2
  exact ⟨h1, enc_injective h4⟩

theorem length_flatMap_pair : ∀ x : Str, (x.flatMap fun b => [true, b]).length = 2 * x.length
  | [] => rfl
  | _ :: x => by simp [length_flatMap_pair x]; ring

theorem code_length (i : ℕ) (x : Str) (T : ℕ) :
    (code i x T).length = i + T + 2 * x.length + 2 := by
  simp [code, enc]; ring

/-! ### Query locality -/

theorem step_len {O : Oracle} {p : Prog} {c c' : Cfg} {L : ℕ} (h : step O p c = .run c')
    (hc : ∀ j, (c.stk j).length ≤ L) : ∀ j, (c'.stk j).length ≤ L + 1 := by
  intro j
  unfold step at h
  split at h
  · cases h
  · cases h
  · cases h
    simp only [update_apply]
    split_ifs with hj
    · subst hj; simpa using hc _
    · exact (hc j).trans (Nat.le_succ L)
  · rename_i k z f t _
    split at h
    · cases h; exact (hc j).trans (Nat.le_succ L)
    · rename_i b s hs
      cases h
      simp only [update_apply]
      split_ifs with hj
      · subst hj; have := hc j; rw [hs] at this; simp at this; omega
      · exact (hc j).trans (Nat.le_succ L)
  · cases h; exact (hc j).trans (Nat.le_succ L)

theorem step_congr_short {O₁ O₂ : Oracle} {p : Prog} {c : Cfg} {N : ℕ}
    (hc : ∀ j, (c.stk j).length < N) (hO : ∀ s : Str, s.length < N → (s ∈ O₁ ↔ s ∈ O₂)) :
    step O₁ p c = step O₂ p c := by
  unfold step
  split
  · rfl
  · rfl
  · rfl
  · rfl
  · rename_i k y n _
    by_cases h1 : c.stk k ∈ O₁
    · have h2 := (hO _ (hc k)).1 h1; simp [h1, h2]
    · have h2 : c.stk k ∉ O₂ := fun h => h1 ((hO _ (hc k)).2 h); simp [h1, h2]

/-- A run of `t` steps from stacks of length `≤ L` only depends on the oracle on strings
of length `< N` whenever `L + t ≤ N`. -/
theorem runFor_congr_short {O₁ O₂ : Oracle} {p : Prog} {N : ℕ}
    (hO : ∀ s : Str, s.length < N → (s ∈ O₁ ↔ s ∈ O₂)) :
    ∀ (t : ℕ) (c : Cfg) (L : ℕ), (∀ j, (c.stk j).length ≤ L) → L + t ≤ N →
      runFor O₁ p t (.run c) = runFor O₂ p t (.run c)
  | 0, _, _, _, _ => rfl
  | t + 1, c, L, hc, hLt => by
    rw [runFor_succ_run, runFor_succ_run,
      step_congr_short (fun j => lt_of_le_of_lt (hc j) (by omega)) hO]
    cases hs : step O₂ p c with
    | done b => simp
    | run c' =>
      exact runFor_congr_short hO t c' (L + 1) (step_len hs hc) (by omega)

theorem init_two_length (x w : Str) (j : ℕ) :
    ((init [x, w]).stk j).length ≤ x.length + w.length := by
  rcases j with _ | _ | j <;> simp [init]

/-! ### The oracle -/

section Oracle

variable (e : ℕ → Prog × ℕ)

/-- `q` is a code `code i x T` and verifier `e i` accepts `x` with oracle `O`. -/
def Cond (q : Str) (O : Oracle) : Prop :=
  ∃ i x T, q = code i x T ∧ ∃ w : Str, w.length ≤ tb (e i).2 x.length ∧
    runFor O (e i).1 (tb (e i).2 x.length) (.run (init [x, w])) = .done true

/-- Membership in the oracle, by well-founded recursion on length. -/
noncomputable def memA : Str → Prop :=
  (measure List.length).wf.fix fun q rec => Cond e q {s | ∃ h : s.length < q.length, rec s h}

/-- The oracle `A` (depending on the enumeration `e`). -/
def oracleA : Oracle := {q | memA e q}

theorem memA_iff (q : Str) :
    memA e q ↔ Cond e q {s | s.length < q.length ∧ memA e s} := by
  unfold memA
  rw [WellFounded.fix_eq]
  simp only [exists_prop]

theorem mem_oracleA_code (i : ℕ) (x : Str) (T : ℕ)
    (hT : x.length + 2 * tb (e i).2 x.length ≤ (code i x T).length) :
    code i x T ∈ oracleA e ↔ ∃ w : Str, w.length ≤ tb (e i).2 x.length ∧
      runFor (oracleA e) (e i).1 (tb (e i).2 x.length) (.run (init [x, w])) = .done true := by
  have hO : ∀ s : Str, s.length < (code i x T).length →
      (s ∈ {s : Str | s.length < (code i x T).length ∧ memA e s} ↔ s ∈ oracleA e) :=
    fun s hs => by simp [oracleA, hs]
  have hrun : ∀ w : Str, w.length ≤ tb (e i).2 x.length →
      runFor {s : Str | s.length < (code i x T).length ∧ memA e s} (e i).1
        (tb (e i).2 x.length) (.run (init [x, w])) =
      runFor (oracleA e) (e i).1 (tb (e i).2 x.length) (.run (init [x, w])) :=
    fun w hw => runFor_congr_short hO _ _ (x.length + w.length) (init_two_length x w) (by omega)
  change memA e _ ↔ _
  rw [memA_iff]
  constructor
  · rintro ⟨i', x', T', hq, w, hw, hr⟩
    obtain ⟨rfl, rfl⟩ := code_inj hq
    exact ⟨w, hw, (hrun w hw) ▸ hr⟩
  · rintro ⟨w, hw, hr⟩
    exact ⟨i, x, T, rfl, w, hw, (hrun w hw).symm ▸ hr⟩

theorem NP_subset_P_oracleA (he : Surjective e) : NP (oracleA e) ⊆ P (oracleA e) := by
  rintro L ⟨p, k, hv⟩
  obtain ⟨i, hi⟩ := he (p, k)
  refine ⟨queryProg i (k + 1), 3 * (k + 1) + i + 11, fun x => ?_⟩
  obtain ⟨b, hb, hiff⟩ := queryProg_run (oracleA e) i (k + 1) x
  refine ⟨b, runFor_mono hb (queryTime_le _ _ _), ?_⟩
  have hT : x.length + 2 * tb (e i).2 x.length ≤
      (code i x ((x.length + 2) ^ (k + 1))).length := by
    rw [code_length, hi, tb, pow_succ]
    dsimp only
    have : 2 * (x.length + 2) ^ k ≤ (x.length + 2) ^ k * (x.length + 2) := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  rw [hiff, mem_oracleA_code e i x _ hT, hv x, hi]

end Oracle

/-- **Baker–Gill–Solovay** (first half): there is an oracle `A` with `NP^A ⊆ P^A`. -/
theorem exists_oracle_NP_subset_P : ∃ A : Oracle, NP A ⊆ P A := by
  obtain ⟨e, he⟩ := exists_surjective_nat (Prog × ℕ)
  exact ⟨oracleA e, NP_subset_P_oracleA e he⟩

end Pnp.Relativize
