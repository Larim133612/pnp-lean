import Pnp.Oracle.Locality
import Pnp.Oracle.PSubsetNP

/-!
# Baker–Gill–Solovay: an oracle `B` with `P B ≠ NP B`

`LB B` (strings whose length is that of some string in `B`) is in `NP B` via an explicit
verifier.  A diagonalization over all `(p, k)` builds `B` stage by stage so that machine
`p` with time bound `tb k` errs on `0^n` for a suitable length `n`; locality
(`Pnp.Oracle.Locality`) transfers the stage's run to the final oracle.
-/

namespace Pnp.Relativize

/-- The test language: strings whose length is the length of some oracle string. -/
def LB (B : Oracle) : Set Str := {x | ∃ w ∈ B, w.length = x.length}

namespace BGS

/-! ## `LB B ∈ NP B` -/

/-- Verifier: query the certificate (stack 1); then pop stacks 0 and 1 in lockstep. -/
def verifier : Prog :=
  [ .query 1 1 5,      -- 0: certificate in oracle?
    .pop 0 3 2 2,      -- 1: pop input; empty → 3
    .pop 1 5 1 1,      -- 2: pop certificate; empty → reject
    .pop 1 4 5 5,      -- 3: certificate must be empty too
    .halt true,        -- 4
    .halt false ]      -- 5

theorem v0 : verifier[0]? = some (.query 1 1 5) := rfl
theorem v1 : verifier[1]? = some (.pop 0 3 2 2) := rfl
theorem v2 : verifier[2]? = some (.pop 1 5 1 1) := rfl
theorem v3 : verifier[3]? = some (.pop 1 4 5 5) := rfl
theorem v4 : verifier[4]? = some (.halt true) := rfl
theorem v5 : verifier[5]? = some (.halt false) := rfl

theorem halt4 (B : Oracle) (t : ℕ) (c : Cfg) (h : c.pc = 4) :
    runFor B verifier (t + 1) (.run c) = .done true := by
  rw [runFor_succ_run]; simp [step, h, v4]

theorem halt5 (B : Oracle) (t : ℕ) (c : Cfg) (h : c.pc = 5) :
    runFor B verifier (t + 1) (.run c) = .done false := by
  rw [runFor_succ_run]; simp [step, h, v5]

theorem loop (B : Oracle) (a : Str) : ∀ (b : Str) (stk : ℕ → Str) (t : ℕ),
    stk 0 = a → stk 1 = b → 2 * a.length + 3 ≤ t →
    runFor B verifier t (.run ⟨1, stk⟩) = .done (decide (a.length = b.length)) := by
  induction a with
  | nil =>
    intro b stk t h0 h1 ht
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show 2 * ([] : Str).length + 3 + t = t + 1 + 1 + 1 by simp; omega]
    rw [runFor_succ_run]
    simp only [step, v1, h0]
    rw [runFor_succ_run]
    cases b with
    | nil => simp only [step, v3, h1]; rw [halt4 _ _ _ rfl]; simp
    | cons y b => simp only [step, v3, h1, ite_self]; rw [halt5 _ _ _ rfl]; simp
  | cons x a ih =>
    intro b stk t h0 h1 ht
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show 2 * (x :: a).length + 3 + t = (2 * a.length + 3 + t) + 1 + 1 by simp; omega]
    rw [runFor_succ_run]
    simp only [step, v1, h0, ite_self]
    rw [runFor_succ_run]
    have h1' : Function.update stk 0 a 1 = b := by
      rw [Function.update_of_ne (by omega), h1]
    cases b with
    | nil =>
      simp only [step, v2, h1']
      rw [show 2 * a.length + 3 + t = (2 * a.length + 2 + t) + 1 by omega, halt5 _ _ _ rfl]
      simp
    | cons y b =>
      simp only [step, v2, h1', ite_self]
      rw [ih b _ _ (by simp) (by simp) (by omega)]
      simp

theorem verifier_run_mem (B : Oracle) (x w : Str) (hw : w ∈ B) :
    runFor B verifier (tb 2 x.length) (.run (init [x, w])) =
      .done (decide (x.length = w.length)) := by
  have ht : 2 * x.length + 3 + 1 ≤ tb 2 x.length := by unfold tb; nlinarith
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le ht
  rw [hu, show 2 * x.length + 3 + 1 + u = (2 * x.length + 3 + u) + 1 by omega,
    runFor_succ_run]
  have hw' : (init [x, w]).stk 1 ∈ B := hw
  simp only [step, init, v0] at hw' ⊢
  rw [if_pos hw']
  exact loop B x w _ _ rfl rfl (by omega)

theorem verifier_run_not_mem (B : Oracle) (x w : Str) (hw : w ∉ B) :
    runFor B verifier (tb 2 x.length) (.run (init [x, w])) = .done false := by
  have ht : 2 ≤ tb 2 x.length := by
    unfold tb; nlinarith [Nat.zero_le x.length]
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le ht
  rw [hu, show 2 + u = (u + 1) + 1 by omega, runFor_succ_run]
  have hw' : (init [x, w]).stk 1 ∉ B := hw
  simp only [step, init, v0] at hw' ⊢
  rw [if_neg hw']
  exact halt5 _ _ _ rfl

theorem verifier_accepts (B : Oracle) (x w : Str) :
    runFor B verifier (tb 2 x.length) (.run (init [x, w])) = .done true ↔
      w ∈ B ∧ x.length = w.length := by
  by_cases hw : w ∈ B
  · rw [verifier_run_mem B x w hw]; simp [hw]
  · rw [verifier_run_not_mem B x w hw]; simp [hw]

end BGS

open BGS in
theorem LB_mem_NP (B : Oracle) : LB B ∈ NP B := by
  refine ⟨verifier, 2, fun x => ?_⟩
  simp only [verifier_accepts]
  constructor
  · rintro ⟨w, hw, hl⟩
    refine ⟨w, ?_, hw, hl.symm⟩
    rw [hl]; unfold tb; nlinarith
  · rintro ⟨w, -, hw, hl⟩
    exact ⟨w, hw, hl.symm⟩

namespace BGS

/-! ## Diagonalization: `LB B ∉ P B` for some `B` -/

theorem sq_le_two_pow (m : ℕ) (hm : 4 ≤ m) : m ^ 2 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ 2]
    nlinarith

/-- Arbitrarily large lengths `n` with `(n+2)^k < 2^n`. -/
theorem exists_len (N k : ℕ) : ∃ n, N ≤ n ∧ tb k n < 2 ^ n := by
  have hm := sq_le_two_pow (N + k + 4) (by omega)
  set m := N + k + 4 with hmdef
  have h2 : m * k + 2 < 2 ^ m := by nlinarith
  refine ⟨2 ^ m - 2, ?_, ?_⟩
  · have hmm : m + 2 ≤ 2 ^ m := by nlinarith
    omega
  · unfold tb
    rw [show 2 ^ m - 2 + 2 = 2 ^ m by omega, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- Fewer than `2^n` strings miss some string of length `n`. -/
theorem exists_fresh (Q : List Str) (n : ℕ) (h : Q.length < 2 ^ n) :
    ∃ y : Str, y.length = n ∧ y ∉ Q := by
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ.image (fun f : Fin n → Bool => List.ofFn f)) ⊆ Q.toFinset := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨f, -, rfl⟩ := hy
    exact List.mem_toFinset.2 (hc _ (List.length_ofFn))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h1
  have := List.toFinset_card_le Q
  omega

/-- A fixed enumeration of all machines with time exponents. -/
noncomputable def enum : ℕ → Prog × ℕ := Classical.choose (exists_surjective_nat (Prog × ℕ))

theorem enum_surjective : Function.Surjective enum :=
  Classical.choose_spec (exists_surjective_nat (Prog × ℕ))

/-- A stage of the construction: the oracle built so far and a length bound. -/
structure Stage where
  orc : Oracle
  bound : ℕ

/-- The input length used at a stage, for machine `pk`. -/
noncomputable def len (s : Stage) (pk : Prog × ℕ) : ℕ := Classical.choose (exists_len s.bound pk.2)

theorem bound_le_len (s : Stage) (pk : Prog × ℕ) : s.bound ≤ len s pk :=
  (Classical.choose_spec (exists_len s.bound pk.2)).1

theorem tb_len_lt (s : Stage) (pk : Prog × ℕ) : tb pk.2 (len s pk) < 2 ^ len s pk :=
  (Classical.choose_spec (exists_len s.bound pk.2)).2

/-- The diagonal input. -/
noncomputable def inp (s : Stage) (pk : Prog × ℕ) : Str := List.replicate (len s pk) false

/-- The (initial) state the stage's machine is started in. -/
noncomputable def start (s : Stage) (pk : Prog × ℕ) : State := .run (init [inp s pk])

/-- The queries of the stage's machine on the diagonal input, with the current oracle. -/
noncomputable def qs (s : Stage) (pk : Prog × ℕ) : List Str :=
  queries s.orc pk.1 (tb pk.2 (len s pk)) (start s pk)

/-- The result of the stage's machine on the diagonal input, with the current oracle. -/
noncomputable def res (s : Stage) (pk : Prog × ℕ) : State :=
  runFor s.orc pk.1 (tb pk.2 (len s pk)) (start s pk)

theorem exists_fresh_stage (s : Stage) (pk : Prog × ℕ) :
    ∃ y : Str, y.length = len s pk ∧ y ∉ qs s pk :=
  exists_fresh _ _ (lt_of_le_of_lt (queries_length_le _ _ _ _) (tb_len_lt s pk))

/-- An unqueried string of the stage's length. -/
noncomputable def fresh (s : Stage) (pk : Prog × ℕ) : Str :=
  Classical.choose (exists_fresh_stage s pk)

open Classical in
/-- The strings added at this stage: nothing if the machine accepts, else a fresh one. -/
noncomputable def add (s : Stage) (pk : Prog × ℕ) : Set Str :=
  if res s pk = .done true then ∅ else {fresh s pk}

/-- The next stage. -/
noncomputable def Stage.next (s : Stage) (pk : Prog × ℕ) : Stage :=
  ⟨s.orc ∪ add s pk, len s pk + 1 + ((qs s pk).map List.length).sum⟩

/-- The stages of the construction. -/
noncomputable def stage : ℕ → Stage
  | 0 => ⟨∅, 0⟩
  | i + 1 => (stage i).next (enum i)

/-- Abbreviations for stage `i`. -/
noncomputable def A (i : ℕ) : Set Str := add (stage i) (enum i)
noncomputable def n (i : ℕ) : ℕ := len (stage i) (enum i)

/-- The final oracle. -/
def oracle : Oracle := {y | ∃ i, y ∈ A i}

theorem mem_A {i : ℕ} {y : Str} (h : y ∈ A i) :
    y = fresh (stage i) (enum i) ∧ res (stage i) (enum i) ≠ .done true := by
  unfold A add at h
  split_ifs at h with hr
  · exact h.elim
  · exact ⟨h, hr⟩

theorem length_of_mem_A {i : ℕ} {y : Str} (h : y ∈ A i) : y.length = n i := by
  rw [(mem_A h).1]
  exact (Classical.choose_spec (exists_fresh_stage _ _)).1

theorem not_mem_qs_of_mem_A {i : ℕ} {y : Str} (h : y ∈ A i) : y ∉ qs (stage i) (enum i) := by
  rw [(mem_A h).1]
  exact (Classical.choose_spec (exists_fresh_stage _ _)).2

theorem stage_orc (i : ℕ) : (stage i).orc = {y | ∃ j < i, y ∈ A j} := by
  induction i with
  | zero => ext y; simp [stage]
  | succ i ih =>
    ext y
    change y ∈ (stage i).orc ∪ A i ↔ _
    rw [Set.mem_union, ih]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro (⟨j, hj, hy⟩ | hy)
      · exact ⟨j, by omega, hy⟩
      · exact ⟨i, by omega, hy⟩
    · rintro ⟨j, hj, hy⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact Or.inl ⟨j, hj, hy⟩
      · exact Or.inr hy

theorem bound_succ (i : ℕ) :
    (stage (i + 1)).bound = n i + 1 + ((qs (stage i) (enum i)).map List.length).sum := rfl

theorem bound_le_n (i : ℕ) : (stage i).bound ≤ n i := bound_le_len _ _

theorem bound_mono {i j : ℕ} (h : i ≤ j) : (stage i).bound ≤ (stage j).bound := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    have := bound_le_n j
    rw [bound_succ]
    omega

theorem n_lt_bound_succ (i : ℕ) : n i < (stage (i + 1)).bound := by
  rw [bound_succ]; omega

theorem qs_length_lt (i : ℕ) {q : Str} (hq : q ∈ qs (stage i) (enum i)) :
    q.length < (stage (i + 1)).bound := by
  rw [bound_succ]
  have : q.length ≤ ((qs (stage i) (enum i)).map List.length).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hq)
  omega

theorem n_strictMono : StrictMono n := by
  intro i j hij
  have h1 := n_lt_bound_succ i
  have h2 := bound_mono (show i + 1 ≤ j by omega)
  have h3 := bound_le_n j
  omega

/-- The final oracle agrees with stage `i`'s oracle on every query of stage `i`. -/
theorem agree (i : ℕ) (q : Str) (hq : q ∈ qs (stage i) (enum i)) :
    q ∈ (stage i).orc ↔ q ∈ oracle := by
  rw [stage_orc]
  constructor
  · rintro ⟨j, -, hj⟩; exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_, hj⟩
    rcases lt_trichotomy j i with h | rfl | h
    · exact h
    · exact absurd hq (not_mem_qs_of_mem_A hj)
    · exfalso
      have h1 := length_of_mem_A hj
      have h2 := qs_length_lt i hq
      have h3 := bound_mono (show i + 1 ≤ j by omega)
      have h4 := bound_le_n j
      omega

theorem run_oracle (i : ℕ) :
    runFor oracle (enum i).1 (tb (enum i).2 (n i)) (start (stage i) (enum i)) =
      res (stage i) (enum i) :=
  (runFor_eq_of_agree _ _ _ (agree i)).symm

theorem mem_LB_iff (i : ℕ) : inp (stage i) (enum i) ∈ LB oracle ↔ ∃ y, y ∈ A i := by
  simp only [LB, inp, List.length_replicate, Set.mem_setOf_eq, oracle]
  constructor
  · rintro ⟨w, ⟨j, hj⟩, hl⟩
    have : j = i := n_strictMono.injective ((length_of_mem_A hj).symm.trans hl)
    subst this
    exact ⟨w, hj⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, ⟨i, hy⟩, length_of_mem_A hy⟩

theorem LB_oracle_not_mem_P : LB oracle ∉ P oracle := by
  rintro ⟨p, k, hp⟩
  obtain ⟨i, hi⟩ := enum_surjective (p, k)
  obtain ⟨b, hrun, hb⟩ := hp (inp (stage i) (enum i))
  have hlen : (inp (stage i) (enum i)).length = n i := List.length_replicate
  rw [hlen, show p = (enum i).1 by rw [hi], show k = (enum i).2 by rw [hi]] at hrun
  have hres : res (stage i) (enum i) = .done b := by rw [← run_oracle]; exact hrun
  rw [mem_LB_iff] at hb
  by_cases hacc : res (stage i) (enum i) = .done true
  · have hA : A i = ∅ := by unfold A add; rw [if_pos hacc]
    have hbt : b = true := State.done.inj (hres.symm.trans hacc)
    obtain ⟨y, hy⟩ := hb.1 hbt
    rw [hA] at hy
    exact hy
  · have hy : fresh (stage i) (enum i) ∈ A i := by
      unfold A add; rw [if_neg hacc]; rfl
    exact hacc (hres.trans (by rw [hb.2 ⟨_, hy⟩]))

end BGS

theorem LB_not_mem_P : ∃ B : Oracle, LB B ∉ P B := ⟨BGS.oracle, BGS.LB_oracle_not_mem_P⟩

/-- **Baker–Gill–Solovay** (one half): some oracle separates `P` from `NP`. -/
theorem exists_oracle_P_ne_NP : ∃ B : Oracle, P B ≠ NP B := by
  obtain ⟨B, hB⟩ := LB_not_mem_P
  exact ⟨B, fun h => hB (h ▸ LB_mem_NP B)⟩

/-- Strict version: `P B ⊊ NP B`. -/
theorem exists_oracle_P_ssubset_NP : ∃ B : Oracle, P B ⊂ NP B := by
  obtain ⟨B, hB⟩ := LB_not_mem_P
  exact ⟨B, (P_subset_NP B).ssubset_of_not_subset fun h => hB (h (LB_mem_NP B))⟩

end Pnp.Relativize
