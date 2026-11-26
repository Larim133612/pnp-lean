import Pnp.NaturalProofs.Barrier
import Pnp.Circuits.Multi

/-!
# Pseudorandom generators give pseudorandom functions: the GGM construction (M14)

Goldreich–Goldwasser–Micali (1986). From a length-doubling generator
`s ↦ G₀(s) G₁(s)` (`{0,1}^m → {0,1}^{2m}`), the GGM function with key `k` is
`x ↦ first bit of G_{x_{n-1}}(⋯ G_{x_1}(G_{x_0}(k)))`: walk down a binary tree of depth `n`
whose root carries the key and whose nodes carry seeds.

Main results:

* `hybrid`, `hybrid_exists`: the hybrid argument for `|ι|` independent samples — replacing
  every `G(sᵢ)` by a uniform sample changes any acceptance probability by at most `|ι|` times
  the advantage at one coordinate (the other coordinates fixed).
* `ggm_reduction` (one input length, explicit parameters): a truth-table test `T` with `cT` gates
  that distinguishes GGM functions from random functions with advantage `α` yields a
  distinguisher for the generator with `2ⁿ(n·sG + 1) + cT` gates and advantage `≥ α / 2ⁿ`
  (`sG` = circuit size of `G₀`, `G₁`). Proof: hybrids `H₀, …, Hₙ` (uniform seeds at depth `i`),
  and the hybrid lemma inside each step `Hᵢ → Hᵢ₊₁` (`2^i` nodes).
* `hasCircuit_ggm`: every GGM function has a circuit with `(n+m) + n(n+m)(3 sG + 3) + 1` gates.
* `PRG.ggmFamily_inPPoly`, `PRG.ggmFamily_secure`: if the generator is in P/poly and secure
  along seed lengths `μ(n)` (`PRG.SecureAlong`, an explicit hypothesis), the GGM family is a
  pseudorandom function family in P/poly that is secure in the Razborov–Rudich sense
  (`PRFamily.Secure` of `Pnp.NaturalProofs.Barrier`).
* `no_natural_property_of_secure_prg`: hence such a generator rules out natural proofs against
  P/poly.
* `ggmFamily_id_inPPoly`: sanity check that the hypothesis `PRFamily.InPPoly` of the barrier is
  satisfiable.

What remains a hypothesis: the existence of a generator with `PRG.SecureAlong` (believed, e.g.
from strong one-way functions via Håstad–Impagliazzo–Levin–Luby; not formalized).
-/

namespace Pnp.NaturalProofs

open Pnp.Circuits Classical

noncomputable section

/-! ## Uniform probability: basic rules -/

theorem prob_eq_sum {α : Type} [Fintype α] (P : α → Prop) :
    prob P = (∑ a, if P a then (1 : ℝ) else 0) / Fintype.card α := by
  rw [prob, Finset.sum_boole]

/-- Uniform probability is invariant under bijections. -/
theorem prob_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop) :
    prob (fun a => P (e a)) = prob P := by
  rw [prob_eq_sum, prob_eq_sum, Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e (fun b => if P b then (1 : ℝ) else 0)

/-- On a product, the probability is the average of the probabilities of the sections. -/
theorem prob_prod {α β : Type} [Fintype α] [Fintype β] (Q : α × β → Prop) :
    prob Q = (∑ a, prob (fun b => Q (a, b))) / Fintype.card α := by
  rw [prob_eq_sum, Fintype.sum_prod_type, Fintype.card_prod]
  simp only [prob_eq_sum]
  rw [← Finset.sum_div, Nat.cast_mul, div_div, mul_comm (Fintype.card β : ℝ)]

/-- An event depending only on the first coordinate. -/
theorem prob_fst {α β : Type} [Fintype α] [Fintype β] [Nonempty β] (P : α → Prop) :
    prob (fun p : α × β => P p.1) = prob P := by
  rw [prob_prod]
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have : ∀ a : α, prob (fun _ : β => P a) = if P a then 1 else 0 := by
    intro a
    rw [prob_eq_sum]
    split_ifs <;> simp [hβ.ne']
  simp only [this, prob_eq_sum]

/-- An event depending only on the second coordinate. -/
theorem prob_snd {α β : Type} [Fintype α] [Fintype β] [Nonempty α] (P : β → Prop) :
    prob (fun p : α × β => P p.2) = prob P := by
  rw [← prob_fst (β := α) P]
  exact prob_equiv (Equiv.prodComm α β) (fun p : β × α => P p.1)

/-- `|avg f − avg g| ≤ ε` when `|f a − g a| ≤ ε` for all `a`. -/
theorem abs_avg_sub_le {α : Type} [Fintype α] [Nonempty α] (f g : α → ℝ) {ε : ℝ}
    (h : ∀ a, |f a - g a| ≤ ε) :
    |(∑ a, f a) / Fintype.card α - (∑ a, g a) / Fintype.card α| ≤ ε := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα, div_le_iff₀ hα]
  calc |∑ a, (f a - g a)| ≤ ∑ a, |f a - g a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : α, ε := Finset.sum_le_sum fun a _ => h a
    _ = ε * Fintype.card α := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]; rfl

/-! ## The hybrid argument for independent copies -/

section Hybrid

variable {ι A B : Type} [DecidableEq ι]

/-- Hybrid `S`: coordinates in `S` are uniform in `B`, the others are `G` of a uniform seed. -/
def mix (G : A → B) (S : Finset ι) (ω : (ι → A) × (ι → B)) : ι → B :=
  fun k => if k ∈ S then ω.2 k else G (ω.1 k)

/-- The advantage of the test `D` at coordinate `j`, the other coordinates fixed to `c`. -/
def coordAdv [Fintype A] [Fintype B] (G : A → B) (D : (ι → B) → Bool) (c : ι → B) (j : ι) : ℝ :=
  |prob (fun y : B => D (Function.update c j y) = true) -
    prob (fun s : A => D (Function.update c j (G s)) = true)|

theorem mix_insert_update (G : A → B) {S : Finset ι} {j : ι} (a : ι → A) (b : ι → B) (y : B) :
    mix G (insert j S) (a, Function.update b j y) = Function.update (mix G S (a, b)) j y := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [mix]
  · simp [mix, hk]

theorem mix_update_seed (G : A → B) {S : Finset ι} {j : ι} (hj : j ∉ S) (a : ι → A)
    (b : ι → B) (s : A) :
    mix G S (Function.update a j s, b) = Function.update (mix G S (a, b)) j (G s) := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [mix, hj]
  · simp [mix, hk]

theorem hybrid_step [Fintype ι] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (G : A → B) (D : (ι → B) → Bool) {ε : ℝ}
    (hε : ∀ c j, coordAdv G D c j ≤ ε) {S : Finset ι} {j : ι} (hj : j ∉ S) :
    |prob (fun ω => D (mix G (insert j S) ω) = true) - prob (fun ω => D (mix G S ω) = true)|
      ≤ ε := by
  -- resample the `B`-coordinate `j`
  let σ : ((ι → A) × (ι → B)) × B → ((ι → A) × (ι → B)) × B :=
    fun q => ((q.1.1, Function.update q.1.2 j q.2), q.1.2 j)
  have hσ : Function.Involutive σ := by
    rintro ⟨⟨a, b⟩, y⟩
    simp only [σ, Function.update_self, Function.update_idem, Function.update_eq_self]
  -- resample the `A`-coordinate `j`
  let τ : ((ι → A) × (ι → B)) × A → ((ι → A) × (ι → B)) × A :=
    fun q => ((Function.update q.1.1 j q.2, q.1.2), q.1.1 j)
  have hτ : Function.Involutive τ := by
    rintro ⟨⟨a, b⟩, s⟩
    simp only [τ, Function.update_self, Function.update_idem, Function.update_eq_self]
  have h1 : prob (fun ω => D (mix G (insert j S) ω) = true) =
      prob (fun q : ((ι → A) × (ι → B)) × B =>
        D (Function.update (mix G S q.1) j q.2) = true) := by
    have e1 := (prob_fst (β := B) (fun ω => D (mix G (insert j S) ω) = true)).symm
    have e2 := (prob_equiv (hσ.toPerm σ)
      (fun q : ((ι → A) × (ι → B)) × B => D (mix G (insert j S) q.1) = true)).symm
    refine e1.trans (e2.trans (congrArg prob (funext fun q => ?_)))
    obtain ⟨⟨a, b⟩, y⟩ := q
    show (D (mix G (insert j S) (a, Function.update b j y)) = true) = _
    rw [mix_insert_update]
  have h2 : prob (fun ω => D (mix G S ω) = true) =
      prob (fun q : ((ι → A) × (ι → B)) × A =>
        D (Function.update (mix G S q.1) j (G q.2)) = true) := by
    have e1 := (prob_fst (β := A) (fun ω => D (mix G S ω) = true)).symm
    have e2 := (prob_equiv (hτ.toPerm τ)
      (fun q : ((ι → A) × (ι → B)) × A => D (mix G S q.1) = true)).symm
    refine e1.trans (e2.trans (congrArg prob (funext fun q => ?_)))
    obtain ⟨⟨a, b⟩, s⟩ := q
    show (D (mix G S (Function.update a j s, b)) = true) = _
    rw [mix_update_seed G hj]
  rw [h1, h2, prob_prod (fun q : ((ι → A) × (ι → B)) × B =>
      D (Function.update (mix G S q.1) j q.2) = true),
    prob_prod (fun q : ((ι → A) × (ι → B)) × A =>
      D (Function.update (mix G S q.1) j (G q.2)) = true)]
  exact abs_avg_sub_le
    (fun ω => prob (fun y : B => D (Function.update (mix G S ω) j y) = true))
    (fun ω => prob (fun s : A => D (Function.update (mix G S ω) j (G s)) = true))
    (fun ω => hε (mix G S ω) j)

/-- **Hybrid lemma.** Replacing `|ι|` independent pseudorandom samples `G(sᵢ)` by uniform
samples changes the acceptance probability of `D` by at most `|ι| · ε`, where `ε` bounds the
advantage at a single coordinate with the others fixed. -/
theorem hybrid [Fintype ι] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (G : A → B) (D : (ι → B) → Bool) {ε : ℝ} (hε : ∀ c j, coordAdv G D c j ≤ ε) :
    |prob (fun b : ι → B => D b = true) - prob (fun a : ι → A => D (G ∘ a) = true)|
      ≤ Fintype.card ι * ε := by
  have key : ∀ S : Finset ι, |prob (fun ω => D (mix G S ω) = true) -
      prob (fun ω => D (mix G ∅ ω) = true)| ≤ S.card * ε := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp only [sub_self, abs_zero, Finset.card_empty, Nat.cast_zero, zero_mul, le_refl]
    | insert j S hj ih =>
      rw [Finset.card_insert_of_notMem hj, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      calc _ ≤ |prob (fun ω => D (mix G (insert j S) ω) = true) -
              prob (fun ω => D (mix G S ω) = true)| +
            |prob (fun ω => D (mix G S ω) = true) - prob (fun ω => D (mix G ∅ ω) = true)| :=
            abs_sub_le _ _ _
        _ ≤ ε + S.card * ε := add_le_add (hybrid_step G D hε hj) ih
        _ = _ := add_comm _ _
  have hu : prob (fun ω => D (mix G Finset.univ ω) = true) =
      prob (fun b : ι → B => D b = true) := by
    rw [← prob_snd (α := ι → A) (fun b : ι → B => D b = true)]
    exact congrArg prob (funext fun ω => by
      show (D (mix G Finset.univ ω) = true) = (D ω.2 = true)
      congr 2; funext k; simp [mix])
  have he : prob (fun ω => D (mix G ∅ ω) = true) =
      prob (fun a : ι → A => D (G ∘ a) = true) := by
    rw [← prob_fst (β := ι → B) (fun a : ι → A => D (G ∘ a) = true)]
    exact congrArg prob (funext fun ω => by
      show (D (mix G ∅ ω) = true) = (D (G ∘ ω.1) = true)
      congr 2)
  have := key Finset.univ
  rwa [hu, he, Finset.card_univ] at this

/-- Hybrid lemma, with the worst coordinate made explicit. -/
theorem hybrid_exists [Nonempty ι] [Fintype ι] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] (G : A → B) (D : (ι → B) → Bool) :
    ∃ c j, |prob (fun b : ι → B => D b = true) - prob (fun a : ι → A => D (G ∘ a) = true)|
      ≤ Fintype.card ι * coordAdv G D c j := by
  obtain ⟨⟨c, j⟩, h⟩ := Finite.exists_max (fun p : (ι → B) × ι => coordAdv G D p.1 p.2)
  exact ⟨c, j, hybrid G D fun c' j' => h (c', j')⟩

end Hybrid

/-! ## Length-doubling generators and the GGM tree -/

/-- Seeds of length `m`. -/
abbrev Seed (m : ℕ) := Fin m → Bool

/-- The left (`b = false`) or right (`b = true`) half of a length-doubling generator. -/
def sel {m : ℕ} (G₀ G₁ : Seed m → Seed m) (b : Bool) : Seed m → Seed m :=
  if b then G₁ else G₀

/-- The generator `s ↦ G₀(s) G₁(s)`, of output length `2m`. -/
def pair {m : ℕ} (G₀ G₁ : Seed m → Seed m) (s : Seed m) : Fin (m + m) → Bool :=
  Fin.append (G₀ s) (G₁ s)

/-- The left or right half of a string of length `2m`. -/
def half {m : ℕ} (b : Bool) (y : Fin (m + m) → Bool) : Seed m :=
  fun k => y (if b then Fin.natAdd m k else Fin.castAdd m k)

theorem half_pair {m : ℕ} (G₀ G₁ : Seed m → Seed m) (b : Bool) (s : Seed m) :
    half b (pair G₀ G₁ s) = sel G₀ G₁ b s := by
  cases b <;> funext k <;>
    simp only [half, pair, sel, Fin.append_left, Fin.append_right, Bool.false_eq_true, ↓reduceIte]

theorem half_append {m : ℕ} (b : Bool) (u v : Seed m) :
    half b (Fin.append u v) = if b then v else u := by
  cases b <;> funext k <;>
    simp only [half, Fin.append_left, Fin.append_right, Bool.false_eq_true, ↓reduceIte]

/-- Distinguishing advantage of `D` against the generator `pair G₀ G₁`:
`|Pr_y[D(y) = 1] − Pr_s[D(G₀(s) G₁(s)) = 1]|`. -/
def prgAdv {m : ℕ} (G₀ G₁ : Seed m → Seed m) (D : (Fin (m + m) → Bool) → Bool) : ℝ :=
  |prob (fun y : Fin (m + m) → Bool => D y = true) -
    prob (fun s : Seed m => D (pair G₀ G₁ s) = true)|

/-- Bit `a` of `x` (`false` out of range). -/
def xb {n : ℕ} (x : Fin n → Bool) (a : ℕ) : Bool :=
  if h : a < n then x ⟨a, h⟩ else false

/-- The first `i` bits of `x`. -/
def pre {n : ℕ} (i : ℕ) (x : Fin n → Bool) : Fin i → Bool := fun k => xb x k

/-- Walk `d` levels down the GGM tree from a node at depth `a`, following the bits
`x_a, …, x_{a+d-1}`. -/
def walk {m n : ℕ} (G₀ G₁ : Seed m → Seed m) (x : Fin n → Bool) : ℕ → ℕ → Seed m → Seed m
  | _, 0, s => s
  | a, d + 1, s => walk G₀ G₁ x (a + 1) d (sel G₀ G₁ (xb x a) s)

theorem walk_zero {m n : ℕ} (G₀ G₁ : Seed m → Seed m) (x : Fin n → Bool) (a : ℕ) (s : Seed m) :
    walk G₀ G₁ x a 0 s = s := rfl

theorem walk_succ {m n : ℕ} (G₀ G₁ : Seed m → Seed m) (x : Fin n → Bool) (a d : ℕ)
    (s : Seed m) : walk G₀ G₁ x a (d + 1) s = walk G₀ G₁ x (a + 1) d (sel G₀ G₁ (xb x a) s) :=
  rfl

/-- The output bit of a leaf: the first bit of its seed. -/
def bit0 {m : ℕ} (s : Seed m) : Bool := if h : 0 < m then s ⟨0, h⟩ else false

/-- **The GGM function** with key `k`: `x ↦ first bit of G_{x_{n-1}}(⋯ G_{x_0}(k))`. -/
def ggm {m : ℕ} (G₀ G₁ : Seed m → Seed m) (n : ℕ) (k : Seed m) : BoolFun n :=
  fun x => bit0 (walk G₀ G₁ x 0 n k)

/-! ## Hybrids -/

/-- Hybrid `i`: the `2^i` nodes at depth `i` carry independent uniform seeds, and the leaves
are computed from them by the GGM tree. -/
def hyb {m n : ℕ} (G₀ G₁ : Seed m → Seed m) (T : (Fin (2 ^ n) → Bool) → Bool) (i : ℕ) : ℝ :=
  prob (fun u : (Fin i → Bool) → Seed m =>
    T (truthTable (fun x => bit0 (walk G₀ G₁ x i (n - i) (u (pre i x))))) = true)

theorem hyb_zero {m n : ℕ} (G₀ G₁ : Seed m → Seed m) (T : (Fin (2 ^ n) → Bool) → Bool) :
    hyb G₀ G₁ T 0 = prob (fun k : Seed m => T (truthTable (ggm G₀ G₁ n k)) = true) := by
  rw [hyb, ← prob_equiv (Equiv.funUnique (Fin 0 → Bool) (Seed m)).symm]
  rfl

/-- Taking the first bit of independent uniform seeds gives a uniform function. -/
theorem prob_bit0 {X : Type} [Fintype X] [DecidableEq X] {m : ℕ} (hm : 0 < m)
    (P : (X → Bool) → Prop) :
    prob (fun u : X → Seed m => P (fun x => bit0 (u x))) = prob P := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  let e : (X → Seed (m + 1)) ≃ (X → Bool) × (X → Seed m) :=
    { toFun := fun u => (fun x => u x 0, fun x => Fin.tail (u x))
      invFun := fun p x => Fin.cons (p.1 x) (p.2 x)
      left_inv := fun u => by funext x; simp
      right_inv := fun p => by ext x <;> simp }
  rw [← prob_fst (β := X → Seed m) P, ← prob_equiv e]
  rfl

theorem hyb_self {m n : ℕ} (hm : 0 < m) (G₀ G₁ : Seed m → Seed m)
    (T : (Fin (2 ^ n) → Bool) → Bool) :
    hyb G₀ G₁ T n = prob (fun f : BoolFun n => T (truthTable f) = true) := by
  have hpre : ∀ x : Fin n → Bool, pre n x = x := fun x => by
    funext k; simp [pre, xb, k.2]
  rw [hyb, ← prob_bit0 hm (fun f : BoolFun n => T (truthTable f) = true)]
  refine congrArg prob (funext fun u => ?_)
  simp only [Nat.sub_self, walk_zero, hpre]

/-- Splitting the depth-`(i+1)` seeds into pairs indexed by their depth-`i` parents. -/
def splitEquiv (m i : ℕ) :
    ((Fin i → Bool) → (Fin (m + m) → Bool)) ≃ ((Fin (i + 1) → Bool) → Seed m) where
  toFun b z := half (z (Fin.last i)) (b (Fin.init z))
  invFun v z := Fin.append (v (Fin.snoc z false)) (v (Fin.snoc z true))
  left_inv b := by
    funext z
    have h0 : (Fin.snoc z false : Fin (i + 1) → Bool) (Fin.last i) = false := Fin.snoc_last _ _
    have h1 : (Fin.snoc z true : Fin (i + 1) → Bool) (Fin.last i) = true := Fin.snoc_last _ _
    have i0 : Fin.init (Fin.snoc z false : Fin (i + 1) → Bool) = z := Fin.init_snoc _ _
    have i1 : Fin.init (Fin.snoc z true : Fin (i + 1) → Bool) = z := Fin.init_snoc _ _
    show Fin.append (half ((Fin.snoc z false : Fin (i + 1) → Bool) (Fin.last i))
        (b (Fin.init (Fin.snoc z false : Fin (i + 1) → Bool))))
      (half ((Fin.snoc z true : Fin (i + 1) → Bool) (Fin.last i))
        (b (Fin.init (Fin.snoc z true : Fin (i + 1) → Bool)))) = b z
    rw [h0, h1, i0, i1]
    exact Fin.append_castAdd_natAdd
  right_inv v := by
    funext z
    show half (z (Fin.last i)) (Fin.append (v (Fin.snoc (Fin.init z) false))
      (v (Fin.snoc (Fin.init z) true))) = v z
    rw [half_append]
    cases h : z (Fin.last i) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [← h, Fin.snoc_init_self]

/-- The test `D` used at level `i`: it reads the `2^i` pairs at depth `i + 1`. -/
def levelTest {m n : ℕ} (G₀ G₁ : Seed m → Seed m) (T : (Fin (2 ^ n) → Bool) → Bool) (i : ℕ)
    (w : (Fin i → Bool) → (Fin (m + m) → Bool)) : Bool :=
  T (truthTable (fun x =>
    bit0 (walk G₀ G₁ x (i + 1) (n - (i + 1)) (half (xb x i) (w (pre i x))))))

theorem hyb_eq_levelTest_pair {m n : ℕ} (G₀ G₁ : Seed m → Seed m)
    (T : (Fin (2 ^ n) → Bool) → Bool) {i : ℕ} (hi : i < n) :
    hyb G₀ G₁ T i = prob (fun a : (Fin i → Bool) → Seed m =>
      levelTest G₀ G₁ T i (pair G₀ G₁ ∘ a) = true) := by
  rw [hyb]
  refine congrArg prob (funext fun u => ?_)
  have h : n - i = n - (i + 1) + 1 := by omega
  simp only [levelTest, Function.comp, half_pair, h, walk_succ]

theorem hyb_succ_eq_levelTest {m n : ℕ} (G₀ G₁ : Seed m → Seed m)
    (T : (Fin (2 ^ n) → Bool) → Bool) (i : ℕ) :
    hyb G₀ G₁ T (i + 1) = prob (fun b : (Fin i → Bool) → (Fin (m + m) → Bool) =>
      levelTest G₀ G₁ T i b = true) := by
  rw [hyb, ← prob_equiv (splitEquiv m i)]
  rfl

/-! ## Circuit size of the reduction -/

theorem hasMCircuit_walk {m n sG : ℕ} {G₀ G₁ : Seed m → Seed m}
    (hG : ∀ b, HasMCircuitOfSize (sel G₀ G₁ b) sG) (x : Fin n → Bool) :
    ∀ d a, HasMCircuitOfSize (walk G₀ G₁ x a d) (d * sG)
  | 0, a => by
    rw [Nat.zero_mul]
    exact hasMCircuitOfSize_id m
  | d + 1, a => by
    have := (hG (xb x a)).comp (hasMCircuit_walk hG x d (a + 1))
    rw [show (d + 1) * sG = sG + d * sG by ring]
    convert this using 1
    funext s; rfl

/-- One leaf bit, as a function of the pair `y` at its depth-`(i+1)` ancestor. -/
theorem hasCircuit_leaf {m n sG : ℕ} (hm : 0 < m) {G₀ G₁ : Seed m → Seed m}
    (hG : ∀ b, HasMCircuitOfSize (sel G₀ G₁ b) sG) (x : Fin n → Bool) (a d : ℕ) (b : Bool) :
    HasCircuitOfSize (fun y : Fin (m + m) → Bool => bit0 (walk G₀ G₁ x a d (half b y)))
      (d * sG) := by
  have h := ((hasMCircuitOfSize_rewire (n := m + m) (m := m)
    (fun k => if b then Fin.natAdd m k else Fin.castAdd m k)).comp
    (hasMCircuit_walk hG x d a)).output ⟨0, hm⟩
  rw [Nat.zero_add] at h
  convert h using 2 with y
  simp only [bit0, dif_pos hm, Function.comp]
  rfl

/-- The distinguisher `y ↦ levelTest (update c j y)` has small circuits. -/
theorem hasCircuit_levelTest_update {m n sG cT : ℕ} (hm : 0 < m) {G₀ G₁ : Seed m → Seed m}
    (hG : ∀ b, HasMCircuitOfSize (sel G₀ G₁ b) sG) {T : (Fin (2 ^ n) → Bool) → Bool}
    (hT : HasCircuitOfSize T cT) (i : ℕ) (c : (Fin i → Bool) → (Fin (m + m) → Bool))
    (j : Fin i → Bool) :
    HasCircuitOfSize (fun y => levelTest G₀ G₁ T i (Function.update c j y))
      (2 ^ n * (n * sG + 1) + cT) := by
  let L : (Fin (m + m) → Bool) → (Fin (2 ^ n) → Bool) := fun y k =>
    bit0 (walk G₀ G₁ ((inputEquiv n).symm k) (i + 1) (n - (i + 1))
      (half (xb ((inputEquiv n).symm k) i)
        (Function.update c j y (pre i ((inputEquiv n).symm k)))))
  have hL : HasMCircuitOfSize L (2 ^ n * (n * sG + 1)) := by
    refine hasMCircuitOfSize_of_forall L fun k => ?_
    set x := (inputEquiv n).symm k
    by_cases hx : pre i x = j
    · have h := hasCircuit_leaf hm hG x (i + 1) (n - (i + 1)) (xb x i)
      have hle : (n - (i + 1)) * sG ≤ n * sG + 1 :=
        (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans (Nat.le_succ _)
      convert h.mono hle using 2 with y
      show bit0 (walk G₀ G₁ x _ _ (half _ (Function.update c j y (pre i x)))) = _
      rw [hx, Function.update_self]
    · have h := hasCircuitOfSize_const (n := m + m) (by omega)
        (bit0 (walk G₀ G₁ x (i + 1) (n - (i + 1)) (half (xb x i) (c (pre i x)))))
      convert h.mono (by omega : 1 ≤ n * sG + 1) using 2 with y
      show bit0 (walk G₀ G₁ x _ _ (half _ (Function.update c j y (pre i x)))) = _
      rw [Function.update_of_ne hx]
  have := hL.comp_single hT
  convert this using 1
  funext y; rfl

theorem sum_two_pow_le (n : ℕ) : ∑ i ∈ Finset.range n, (2 : ℝ) ^ i ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; linarith

/-! ## The GGM reduction, one input length -/

/-- **GGM reduction (concrete).** If `G₀, G₁` have circuits of size `sG` and the truth-table
test `T` (size `cT`) distinguishes the GGM functions from random functions, then some circuit
of size `2ⁿ(n·sG + 1) + cT` distinguishes `G₀(s) G₁(s)` from a uniform string with at least a
`2⁻ⁿ` fraction of that advantage. -/
theorem ggm_reduction {m n sG cT : ℕ} (hm : 0 < m) (hn : 0 < n) {G₀ G₁ : Seed m → Seed m}
    (hG : ∀ b, HasMCircuitOfSize (sel G₀ G₁ b) sG) {T : (Fin (2 ^ n) → Bool) → Bool}
    (hT : HasCircuitOfSize T cT) :
    ∃ D : (Fin (m + m) → Bool) → Bool, HasCircuitOfSize D (2 ^ n * (n * sG + 1) + cT) ∧
      advantage T (ggm G₀ G₁ n) ≤ 2 ^ n * prgAdv G₀ G₁ D := by
  have step : ∀ i, i < n → ∃ D : (Fin (m + m) → Bool) → Bool,
      HasCircuitOfSize D (2 ^ n * (n * sG + 1) + cT) ∧
        |hyb G₀ G₁ T (i + 1) - hyb G₀ G₁ T i| ≤ 2 ^ i * prgAdv G₀ G₁ D := by
    intro i hi
    obtain ⟨c, j, h⟩ := hybrid_exists (pair G₀ G₁) (levelTest G₀ G₁ T i)
    refine ⟨fun y => levelTest G₀ G₁ T i (Function.update c j y),
      hasCircuit_levelTest_update hm hG hT i c j, ?_⟩
    rw [hyb_succ_eq_levelTest, hyb_eq_levelTest_pair G₀ G₁ T hi]
    have hcard : (Fintype.card (Fin i → Bool) : ℝ) = 2 ^ i := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; rfl
    rw [hcard] at h
    exact h
  choose! D hDc hDadv using step
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (Finset.range n)
    (fun i => prgAdv G₀ G₁ (D i)) ⟨0, Finset.mem_range.2 hn⟩
  have hi₀' : i₀ < n := Finset.mem_range.1 hi₀
  refine ⟨D i₀, hDc i₀ hi₀', ?_⟩
  have hadv : advantage T (ggm G₀ G₁ n) = |hyb G₀ G₁ T n - hyb G₀ G₁ T 0| := by
    rw [advantage, hyb_zero, hyb_self hm]
  have h0 : 0 ≤ prgAdv G₀ G₁ (D i₀) := abs_nonneg _
  rw [hadv, ← Finset.sum_range_sub (fun i => hyb G₀ G₁ T i)]
  calc _ ≤ ∑ i ∈ Finset.range n, |hyb G₀ G₁ T (i + 1) - hyb G₀ G₁ T i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, 2 ^ i * prgAdv G₀ G₁ (D i₀) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        exact (hDadv i hi').trans
          (mul_le_mul_of_nonneg_left (hmax i hi) (by positivity))
    _ = (∑ i ∈ Finset.range n, (2 : ℝ) ^ i) * prgAdv G₀ G₁ (D i₀) := by
        rw [Finset.sum_mul]
    _ ≤ 2 ^ n * prgAdv G₀ G₁ (D i₀) := mul_le_mul_of_nonneg_right (sum_two_pow_le n) h0

/-! ## GGM functions have small circuits -/

theorem walk_succ' {m n : ℕ} (G₀ G₁ : Seed m → Seed m) (x : Fin n → Bool) :
    ∀ d a s, walk G₀ G₁ x a (d + 1) s = sel G₀ G₁ (xb x (a + d)) (walk G₀ G₁ x a d s)
  | 0, a, s => rfl
  | d + 1, a, s => by
    rw [walk_succ, walk_succ' G₀ G₁ x d (a + 1), walk_succ G₀ G₁ x a d]
    congr 2; omega

/-- One step of the GGM evaluation on the state `(x, s)`: `s ↦ G_{x_t}(s)`. -/
def evalStep {m n : ℕ} (G₀ G₁ : Seed m → Seed m) (t : ℕ) (z : Fin (n + m) → Bool) :
    Fin (n + m) → Bool :=
  Fin.append (fun k => z (Fin.castAdd m k))
    (sel G₀ G₁ (xb (fun k => z (Fin.castAdd m k)) t) (fun k => z (Fin.natAdd n k)))

/-- The first `d` steps. -/
def evalSteps {m n : ℕ} (G₀ G₁ : Seed m → Seed m) : ℕ → (Fin (n + m) → Bool) → Fin (n + m) → Bool
  | 0 => id
  | d + 1 => evalStep G₀ G₁ d ∘ evalSteps G₀ G₁ d

theorem evalSteps_append {m n : ℕ} (G₀ G₁ : Seed m → Seed m) (x : Fin n → Bool) (k : Seed m) :
    ∀ d, evalSteps G₀ G₁ d (Fin.append x k) = Fin.append x (walk G₀ G₁ x 0 d k)
  | 0 => rfl
  | d + 1 => by
    rw [evalSteps, Function.comp_apply, evalSteps_append G₀ G₁ x k d, walk_succ', Nat.zero_add]
    simp only [evalStep, Fin.append_left, Fin.append_right]

theorem hasCircuit_evalStep_bit {m n sG : ℕ} {G₀ G₁ : Seed m → Seed m}
    (hG : ∀ b, HasMCircuitOfSize (sel G₀ G₁ b) sG) {t : ℕ} (ht : t < n) (j : Fin (n + m)) :
    HasCircuitOfSize (fun z => evalStep G₀ G₁ t z j) (3 * sG + 3) := by
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · have := hasCircuitOfSize_var (Fin.castAdd m k)
    convert this.mono (Nat.zero_le _) using 2 with z
    simp [evalStep]
  · have hsel : ∀ b, HasCircuitOfSize (fun z : Fin (n + m) → Bool =>
        sel G₀ G₁ b (fun k => z (Fin.natAdd n k)) k) sG := fun b => by
      have := ((hasMCircuitOfSize_rewire (n := n + m) (fun k : Fin m => Fin.natAdd n k)).comp
        (hG b)).output k
      rw [Nat.zero_add] at this
      exact this
    let tr : (Fin (n + m) → Bool) → Fin 3 → Bool := fun z =>
      ![z (Fin.castAdd m ⟨t, ht⟩), sel G₀ G₁ true (fun k => z (Fin.natAdd n k)) k,
        sel G₀ G₁ false (fun k => z (Fin.natAdd n k)) k]
    have htr : HasMCircuitOfSize tr (3 * sG) := by
      refine hasMCircuitOfSize_of_forall tr fun i => ?_
      fin_cases i
      · exact (hasCircuitOfSize_var _).mono (Nat.zero_le _)
      · exact hsel true
      · exact hsel false
    have := htr.comp_single hasCircuitOfSize_mux
    convert this using 2 with z
    simp only [evalStep, Fin.append_right, Function.comp, tr, xb, dif_pos ht]
    cases z (Fin.castAdd m ⟨t, ht⟩) <;> rfl

theorem hasMCircuit_evalSteps {m n sG : ℕ} {G₀ G₁ : Seed m → Seed m}
    (hG : ∀ b, HasMCircuitOfSize (sel G₀ G₁ b) sG) :
    ∀ d, d ≤ n → HasMCircuitOfSize (evalSteps G₀ G₁ (n := n) d) (d * ((n + m) * (3 * sG + 3)))
  | 0, _ => by rw [Nat.zero_mul]; exact hasMCircuitOfSize_id _
  | d + 1, hd => by
    have h1 := hasMCircuit_evalSteps (n := n) hG d (by omega)
    have h2 := hasMCircuitOfSize_of_forall (evalStep G₀ G₁ (n := n) d)
      (hasCircuit_evalStep_bit hG (by omega : d < n))
    rw [Nat.succ_mul]
    exact h1.comp h2

/-- The GGM function with any fixed key has a circuit with
`(n + m) + n (n + m)(3 sG + 3) + 1` gates. -/
theorem hasCircuit_ggm {m n sG : ℕ} (hn : 0 < n) {G₀ G₁ : Seed m → Seed m}
    (hG : ∀ b, HasMCircuitOfSize (sel G₀ G₁ b) sG) (k : Seed m) :
    HasCircuitOfSize (ggm G₀ G₁ n k) ((n + m) + n * ((n + m) * (3 * sG + 3)) + 1) := by
  by_cases hm : 0 < m
  · have hinit : HasMCircuitOfSize (fun x : Fin n → Bool => (Fin.append x k : Fin (n + m) → Bool))
        ((n + m) * 1) := by
      refine hasMCircuitOfSize_of_forall _ fun j => ?_
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have := hasCircuitOfSize_var i
        convert this.mono (Nat.zero_le 1) using 2 with x
        simp
      · have := hasCircuitOfSize_const hn (k i)
        convert this using 2 with x
        simp
    have h := (hinit.comp (hasMCircuit_evalSteps hG n le_rfl)).output (Fin.natAdd n ⟨0, hm⟩)
    have hle : (n + m) * 1 + n * ((n + m) * (3 * sG + 3)) ≤
        (n + m) + n * ((n + m) * (3 * sG + 3)) + 1 := by rw [Nat.mul_one]; omega
    convert h.mono hle using 2 with x
    simp only [Function.comp, evalSteps_append, Fin.append_right, ggm, bit0, dif_pos hm]
  · have := hasCircuitOfSize_const hn false
    convert this.mono (Nat.le_add_left 1 _) using 2 with x
    simp [ggm, bit0, hm]

/-! ## Asymptotic version: secure PRGs give secure PRFs -/

theorem polynomial_eval_mono (P : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : P.eval a ≤ P.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- A family of length-doubling generators: for every seed length `ℓ`, the two halves
`G₀ ℓ, G₁ ℓ : {0,1}^ℓ → {0,1}^ℓ` of `s ↦ G₀(s) G₁(s) ∈ {0,1}^{2ℓ}`. -/
structure PRG where
  G₀ : ∀ ℓ, Seed ℓ → Seed ℓ
  G₁ : ∀ ℓ, Seed ℓ → Seed ℓ

/-- Both halves have (multi-output) circuits of size polynomial in the seed length. -/
def PRG.InPPoly (G : PRG) : Prop :=
  ∃ p : Polynomial ℕ, ∀ ℓ b, HasMCircuitOfSize (sel (G.G₀ ℓ) (G.G₁ ℓ) b) (p.eval ℓ)

/-- **Security along the seed lengths `μ(n)`** (an explicit hypothesis): for all polynomials
`q`, `r` and all large `n`, every distinguisher with `q(2ⁿ)` gates tells `G(s)`, `s` a uniform
seed of length `μ(n)`, from a uniform string of length `2μ(n)` only with advantage
`< 1 / r(2ⁿ)`.

This is the strong ("exponential") security needed by Razborov–Rudich: measured in the seed
length `ℓ = μ(n)`, distinguishers may have size `2^{O(n)}`. For `μ(n) = n^c` it is the usual
sub-exponential hardness `2^{ℓ^{1/c}}`. -/
def PRG.SecureAlong (G : PRG) (μ : Polynomial ℕ) : Prop :=
  ∀ q r : Polynomial ℕ, ∃ N, ∀ n ≥ N, ∀ D : (Fin (μ.eval n + μ.eval n) → Bool) → Bool,
    HasCircuitOfSize D (q.eval (2 ^ n)) →
      prgAdv (G.G₀ (μ.eval n)) (G.G₁ (μ.eval n)) D * r.eval (2 ^ n) < 1

/-- **The GGM pseudorandom function family** with keys of length `μ(n)`. -/
def PRG.ggmFamily (G : PRG) (μ : Polynomial ℕ) : PRFamily where
  Key n := Seed (μ.eval n)
  F n k := ggm (G.G₀ (μ.eval n)) (G.G₁ (μ.eval n)) n k

theorem PRG.ggmFamily_inPPoly (G : PRG) (μ : Polynomial ℕ) (hG : G.InPPoly) :
    (G.ggmFamily μ).InPPoly := by
  obtain ⟨p, hp⟩ := hG
  open Polynomial in
  refine ⟨(X + μ) + X * ((X + μ) * (3 * p.comp μ + 3)) + 1, fun n hn k => ?_⟩
  have := hasCircuit_ggm hn (hp (μ.eval n)) k
  convert this using 1
  · rfl
  · simp [Polynomial.eval_comp]

/-- **GGM: secure PRGs give secure PRFs.** If the generator is in P/poly and secure along the
(positive) seed lengths `μ(n)`, the GGM family is a secure pseudorandom function family. -/
theorem PRG.ggmFamily_secure (G : PRG) (μ : Polynomial ℕ) (hμ : ∀ n, 0 < μ.eval n)
    (hG : G.InPPoly) (hS : G.SecureAlong μ) : (G.ggmFamily μ).Secure := by
  obtain ⟨p, hp⟩ := hG
  intro q r
  open Polynomial in
  obtain ⟨N, hN⟩ := hS (X * (X * p.comp μ + 1) + q) (X * r)
  refine ⟨N + 1, fun n hn T hT => ?_⟩
  obtain ⟨D, hD, hadv⟩ := ggm_reduction (hμ n) (by omega) (hp (μ.eval n)) hT
  have hsize : 2 ^ n * (n * p.eval (μ.eval n) + 1) + q.eval (2 ^ n) ≤
      (Polynomial.X * (Polynomial.X * p.comp μ + 1) + q).eval (2 ^ n) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_comp]
    have h1 : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
    have h2 : p.eval (μ.eval n) ≤ p.eval (μ.eval (2 ^ n)) :=
      polynomial_eval_mono p (polynomial_eval_mono μ h1)
    have := Nat.mul_le_mul h1 h2
    have := Nat.mul_le_mul_left (2 ^ n) (Nat.add_le_add_right this 1)
    omega
  have hlt := hN n (by omega) D (hD.mono hsize)
  have hr : (((Polynomial.X * r).eval (2 ^ n) : ℕ) : ℝ) = 2 ^ n * r.eval (2 ^ n) := by
    simp
  rw [hr] at hlt
  have hr0 : (0 : ℝ) ≤ r.eval (2 ^ n) := Nat.cast_nonneg _
  calc advantage T ((G.ggmFamily μ).F n) * r.eval (2 ^ n)
      ≤ 2 ^ n * prgAdv (G.G₀ (μ.eval n)) (G.G₁ (μ.eval n)) D * r.eval (2 ^ n) :=
        mul_le_mul_of_nonneg_right hadv hr0
    _ = prgAdv (G.G₀ (μ.eval n)) (G.G₁ (μ.eval n)) D * (2 ^ n * r.eval (2 ^ n)) := by ring
    _ < 1 := hlt

/-- **Natural proofs barrier from pseudorandom generators.** If a length-doubling generator in
P/poly is secure along seed lengths `μ(n) > 0`, then no property of Boolean functions is
constructive, large and useful against P/poly. -/
theorem no_natural_property_of_secure_prg (G : PRG) (μ : Polynomial ℕ) (hμ : ∀ n, 0 < μ.eval n)
    (hG : G.InPPoly) (hS : G.SecureAlong μ) (Γ : ∀ n, Set (BoolFun n)) :
    ¬ NaturalAgainstPPoly Γ :=
  no_natural_property_of_secure_prf (G.ggmFamily μ) (G.ggmFamily_inPPoly μ hG)
    (G.ggmFamily_secure μ hμ hG hS) Γ

/-! ## Sanity check -/

/-- The identity "generator" (insecure) is in P/poly. -/
theorem PRG.id_inPPoly : (PRG.mk (fun _ => id) (fun _ => id)).InPPoly :=
  ⟨0, fun ℓ b => by
    cases b <;> exact (hasMCircuitOfSize_id ℓ).mono (Nat.zero_le _)⟩

/-- The hypothesis `PRFamily.InPPoly` of the natural-proofs barrier is satisfiable. -/
theorem ggmFamily_id_inPPoly :
    ((PRG.mk (fun _ => id) (fun _ => id)).ggmFamily (Polynomial.X + 1)).InPPoly :=
  PRG.ggmFamily_inPPoly _ _ PRG.id_inPPoly

end

end Pnp.NaturalProofs
