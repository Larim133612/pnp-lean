import Pnp.Circuits.GateElim

/-!
# Schnorr's bound for the class `Q²,³` (M12a)

Generalization of `th2_lower_bound` (M7): every function in (a restriction-closed
version of) Schnorr's class `Q²,³` needs at least `2 n - 3` gates in the full binary basis
`B₂`.

A *restriction* is a pair `(Z, c)`: the variables of `Z` are fixed, variable `z ∈ Z` to the
constant `c z`; the subcube is `RDom Z c`. A family `R` of "good" restrictions is a
`Q23` family for `f` when for every good restriction with `m = n - |Z|` free variables:

* (`dep`, `m ≥ 2`) `f` depends on every free variable on the subcube;
* (`three`, `m ≥ 3`) for any two distinct free variables `x_i, x_j`, the four ways of
  fixing `(x_i, x_j)` give at least three pairwise distinct subfunctions (`ThreeSub`);
* (`fix`, `m ≥ 3`) every free variable can be fixed to *some* constant so that the
  restriction stays good.

Taking `R` = all restrictions gives Schnorr's class `Q²,³ₙ`; allowing only constants
`false` recovers threshold-2.

* `q23_lower_bound`: `Q23 f R` and `R ∅ c₀` ⇒ every circuit for `f` has `≥ 2 n - 3` gates.
* Symmetric functions: `sym_dep`, `sym_three` reduce the hypotheses to arithmetic.
* Instances: `mod3_lower_bound` (`[#ones ≡ t mod 3]`, any `t < 3`) and
  `th2_lower_bound'` (Schnorr's threshold-2 bound re-derived from the general theorem).

Note: PARITY is *not* in `Q²,³` (fixing `(x_i, x_j)` to `00` and `11` gives the same
subfunction), and indeed it has circuits of size `n - 1`.
-/

namespace Pnp.Circuits

namespace GateElim

open GC

variable {n : ℕ}

/-- The subcube of a restriction: variables in `Z` are fixed to the values of `c`. -/
def RDom (Z : Finset (Fin n)) (c : Fin n → Bool) : Set (Fin n → Bool) :=
  {x | ∀ z ∈ Z, x z = c z}

/-- `x` and `y` agree outside the variables `i, j`. -/
def AgreeOff (i j : Fin n) (x y : Fin n → Bool) : Prop := ∀ l, l ≠ i → l ≠ j → x l = y l

/-- On `D`, the subfunctions of `f` obtained by fixing `(x_i, x_j)` to `α` and to `β`
differ. -/
def SubDiff (f : (Fin n → Bool) → Bool) (D : Set (Fin n → Bool)) (i j : Fin n)
    (α β : Bool × Bool) : Prop :=
  ∃ x ∈ D, ∃ y ∈ D, AgreeOff i j x y ∧ (x i, x j) = α ∧ (y i, y j) = β ∧ f x ≠ f y

/-- Fixing `(x_i, x_j)` gives at least three pairwise distinct subfunctions of `f` on `D`. -/
def ThreeSub (f : (Fin n → Bool) → Bool) (D : Set (Fin n → Bool)) (i j : Fin n) : Prop :=
  ∃ α β γ : Bool × Bool, SubDiff f D i j α β ∧ SubDiff f D i j β γ ∧ SubDiff f D i j α γ

/-- On `D`, `f` depends on the variable `p`. -/
def DependsOn (f : (Fin n → Bool) → Bool) (D : Set (Fin n → Bool)) (p : Fin n) : Prop :=
  ∃ x ∈ D, ∃ y ∈ D, (∀ l, l ≠ p → x l = y l) ∧ f x ≠ f y

/-- A family `R` of good restrictions witnessing that `f` is in (a restriction-closed
version of) Schnorr's class `Q²,³`. -/
structure Q23 (f : (Fin n → Bool) → Bool) (R : Finset (Fin n) → (Fin n → Bool) → Prop) :
    Prop where
  dep : ∀ Z c, R Z c → 2 ≤ n - Z.card → ∀ p, p ∉ Z → DependsOn f (RDom Z c) p
  three : ∀ Z c, R Z c → 3 ≤ n - Z.card → ∀ i j, i ∉ Z → j ∉ Z → i ≠ j →
    ThreeSub f (RDom Z c) i j
  fix : ∀ Z c, R Z c → 3 ≤ n - Z.card → ∀ v, v ∉ Z →
    ∃ b, R (insert v Z) (Function.update c v b)

/-- If `f` depends on two free variables, it is not computed by a circuit whose output wire
is an input. -/
theorem no_lit' (C : GC n) (f : (Fin n → Bool) → Bool) (D : Set (Fin n → Bool))
    (hC : ∀ x ∈ D, C.eval x = f x) (ho : C.out < n) (p q : Fin n) (hpq : p ≠ q)
    (hp : DependsOn f D p) (hq : DependsOn f D q) : False := by
  have hev : ∀ x, C.eval x = C.outf (x ⟨C.out, ho⟩) := fun x => by
    unfold GC.eval; rw [C.val_input x ho]
  have key : ∀ r : Fin n, DependsOn f D r → r = ⟨C.out, ho⟩ := by
    rintro r ⟨x, hx, y, hy, hxy, hne⟩
    by_contra h
    apply hne
    rw [← hC x hx, ← hC y hy, hev, hev, hxy _ (Ne.symm h)]
  exact hpq ((key p hp).trans (key q hq).symm)

/-- The fan-out argument: if the first gate reads two variables `i ≠ j` that no other gate
reads, `f` has at most two subfunctions with respect to `(x_i, x_j)`. -/
theorem three_sub' (C : GC n) (f : (Fin n → Bool) → Bool) (D : Set (Fin n → Bool))
    (hC : ∀ x ∈ D, C.eval x = f x) (hs : 0 < C.s) (i j : Fin n)
    (hi : C.a 0 = i.val) (hj : C.b 0 = j.val) (_hij : i ≠ j) (hout : n ≤ C.out)
    (hrest : ∀ k, 1 ≤ k → k < C.s →
      C.a k ≠ i.val ∧ C.a k ≠ j.val ∧ C.b k ≠ i.val ∧ C.b k ≠ j.val)
    (h3 : ThreeSub f D i j) : False := by
  have hval0 : ∀ x, C.val x n = C.op 0 (x i) (x j) := by
    intro x
    have := C.val_gate x hs
    rw [Nat.add_zero] at this
    rw [this, hi, hj, C.val_input x i.2, C.val_input x j.2]
  have indep : ∀ x y : Fin n → Bool, AgreeOff i j x y → C.val x n = C.val y n →
      ∀ w, w < n + C.s → w ≠ i.val → w ≠ j.val → C.val x w = C.val y w := by
    intro x y hxy h0 w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hwi hwj
      by_cases hwn : w < n
      · rw [C.val_input x hwn, C.val_input y hwn]
        exact hxy _ (fun h => hwi (congrArg Fin.val h)) (fun h => hwj (congrArg Fin.val h))
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simpa using h0
        · have hks : k < C.s := by omega
          obtain ⟨h1, h2, h3, h4⟩ := hrest k hk hks
          have ha := C.ha k hks
          have hb := C.hb k hks
          rw [C.val_gate x hks, C.val_gate y hks, ih _ (by omega) (by omega) h1 h2,
            ih _ (by omega) (by omega) h3 h4]
  have hsd : ∀ α β : Bool × Bool, SubDiff f D i j α β →
      C.op 0 α.1 α.2 ≠ C.op 0 β.1 β.2 := by
    rintro α β ⟨x, hx, y, hy, hxy, rfl, rfl, hne⟩ hop
    apply hne
    rw [← hC x hx, ← hC y hy]
    unfold GC.eval
    have := i.2; have := j.2
    rw [indep x y hxy (by rw [hval0, hval0]; exact hop) C.out C.hout (by omega) (by omega)]
  obtain ⟨α, β, γ, h1, h2, h3⟩ := h3
  have e1 := hsd α β h1
  have e2 := hsd β γ h2
  have e3 := hsd α γ h3
  revert e1 e2 e3
  cases C.op 0 α.1 α.2 <;> cases C.op 0 β.1 β.2 <;> cases C.op 0 γ.1 γ.2 <;> simp

/-- **Schnorr's bound for `Q23` families, on a subcube.** If `C` computes `f` on the
subcube of a good restriction with `m = n - |Z| ≥ 2` free variables, then `C` has at
least `2 m - 3` gates. -/
theorem q23_lower_bound_gc (f : (Fin n → Bool) → Bool)
    (R : Finset (Fin n) → (Fin n → Bool) → Prop) (hf : Q23 f R) :
    ∀ (s : ℕ) (C : GC n) (Z : Finset (Fin n)) (c : Fin n → Bool), C.s = s → R Z c →
      2 ≤ n - Z.card → (∀ x ∈ RDom Z c, C.eval x = f x) → 2 * (n - Z.card) ≤ C.s + 3 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C Z c hs hR hm hC
    by_cases hel : ∃ k < C.s, C.Removable (RDom Z c) k
    · obtain ⟨k, hk, he⟩ := hel
      obtain ⟨C', hs', hC'⟩ := C.exists_elim (RDom Z c) hk he
      have := ih (C.s - 1) (by omega) C' Z c hs' hR hm
        (fun x hx => (hC' x hx).trans (hC x hx))
      omega
    push Not at hel
    obtain ⟨p, hp, q, hq, hpq⟩ : ∃ p ∈ Finset.univ \ Z, ∃ q ∈ Finset.univ \ Z, p ≠ q := by
      apply Finset.one_lt_card.mp
      rw [card_free]; omega
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hp hq
    have hlit : ¬ C.out < n := fun ho =>
      no_lit' C f _ hC ho p q hpq (hf.dep Z c hR hm p hp) (hf.dep Z c hR hm q hq)
    have hs0 : 0 < C.s := by
      by_contra h0
      exact hlit (by have := C.hout; omega)
    by_cases hm2 : n - Z.card = 2
    · omega
    have hm3 : 3 ≤ n - Z.card := by omega
    have ha0 : C.a 0 < n := by simpa using C.ha 0 hs0
    have hb0 : C.b 0 < n := by simpa using C.hb 0 hs0
    have hab : C.a 0 ≠ C.b 0 := fun h => hel 0 hs0 (C.removable_of_eq _ hs0 h)
    let i : Fin n := ⟨C.a 0, ha0⟩
    let j : Fin n := ⟨C.b 0, hb0⟩
    have hiZ : i ∉ Z := fun hz => hel 0 hs0 (C.removable_of_a _ hs0 (c i)
      (fun x hx => by rw [C.val_input x ha0]; exact hx i hz))
    have hjZ : j ∉ Z := fun hz => hel 0 hs0 (C.removable_of_b _ hs0 (c j)
      (fun x hx => by rw [C.val_input x hb0]; exact hx j hz))
    have hij : i ≠ j := fun h => hab (congrArg Fin.val h)
    have hout : n ≤ C.out := by omega
    obtain ⟨k, hk1, hks, hread⟩ : ∃ k, 1 ≤ k ∧ k < C.s ∧
        (C.a k = C.a 0 ∨ C.a k = C.b 0 ∨ C.b k = C.a 0 ∨ C.b k = C.b 0) := by
      by_contra hne
      push Not at hne
      exact three_sub' C f _ hC hs0 i j rfl rfl hij hout (fun k hk1 hks => hne k hk1 hks)
        (hf.three Z c hR hm3 i j hiZ hjZ hij)
    obtain ⟨v, hvZ, hv0, hvk⟩ : ∃ v : Fin n, v ∉ Z ∧ (C.a 0 = v.val ∨ C.b 0 = v.val) ∧
        (C.a k = v.val ∨ C.b k = v.val) := by
      rcases hread with h | h | h | h
      · exact ⟨i, hiZ, Or.inl rfl, Or.inl h⟩
      · exact ⟨j, hjZ, Or.inr rfl, Or.inl h⟩
      · exact ⟨i, hiZ, Or.inl rfl, Or.inr h⟩
      · exact ⟨j, hjZ, Or.inr rfl, Or.inr h⟩
    obtain ⟨b, hRb⟩ := hf.fix Z c hR hm3 v hvZ
    set Z' := insert v Z with hZ'
    set c' := Function.update c v b with hc'
    have hcard : Z'.card = Z.card + 1 := Finset.card_insert_of_notMem hvZ
    have hsub : ∀ x ∈ RDom Z' c', x ∈ RDom Z c := fun x hx z hz => by
      have hzv : z ≠ v := fun h => hvZ (h ▸ hz)
      rw [hx z (Finset.mem_insert_of_mem hz), hc', Function.update_of_ne hzv]
    have hdead : ∀ x ∈ RDom Z' c', x v = b := fun x hx => by
      rw [hx v (Finset.mem_insert_self _ _), hc', Function.update_self]
    have hremk : C.Removable (RDom Z' c') k := by
      rcases hvk with h | h
      · exact C.removable_of_a _ hks b (fun x hx => by
          rw [h, C.val_input x v.2]; exact hdead x hx)
      · exact C.removable_of_b _ hks b (fun x hx => by
          rw [h, C.val_input x v.2]; exact hdead x hx)
    obtain ⟨w, hw, u, hu⟩ := hremk
    set C1 := C.elim k w u hks hw with hC1
    have hC1s : C1.s = C.s - 1 := rfl
    have hC1eval : ∀ x ∈ RDom Z' c', C1.eval x = f x := fun x hx =>
      (C.elim_eval k w u hks hw x (hu x hx)).trans (hC x (hsub x hx))
    have hC1s0 : 0 < C1.s := by omega
    have hC1a : C1.a 0 = C.a 0 := by
      show (if 0 < k then C.a 0 else _) = C.a 0; rw [if_pos (show 0 < k by omega)]
    have hC1b : C1.b 0 = C.b 0 := by
      show (if 0 < k then C.b 0 else _) = C.b 0; rw [if_pos (show 0 < k by omega)]
    have hrem0 : C1.Removable (RDom Z' c') 0 := by
      rcases hv0 with h | h
      · exact C1.removable_of_a _ hC1s0 b (fun x hx => by
          rw [hC1a, h, C1.val_input x v.2]; exact hdead x hx)
      · exact C1.removable_of_b _ hC1s0 b (fun x hx => by
          rw [hC1b, h, C1.val_input x v.2]; exact hdead x hx)
    obtain ⟨C2, hC2s, hC2⟩ := C1.exists_elim (RDom Z' c') hC1s0 hrem0
    have := ih (C.s - 2) (by omega) C2 Z' c' (by omega) hRb (by omega)
      (fun x hx => (hC2 x hx).trans (hC1eval x hx))
    omega

end GateElim

open GateElim in
/-- **Schnorr (1974), class `Q²,³`.** If `R` is a `Q23` family for `f` containing some
restriction with no fixed variables, every `B₂` circuit computing `f` on `n ≥ 2`
variables has at least `2 n - 3` gates. -/
theorem q23_lower_bound {n s : ℕ} (hn : 2 ≤ n) (f : (Fin n → Bool) → Bool)
    (R : Finset (Fin n) → (Fin n → Bool) → Prop) (hf : Q23 f R) (c₀ : Fin n → Bool)
    (hR : R ∅ c₀) (C : Circuit n s) (hC : C.eval = f) : 2 * n - 3 ≤ s := by
  have := q23_lower_bound_gc f R hf s (GC.ofCircuit C) ∅ c₀ rfl hR (by simpa using hn)
    (fun x _ => by rw [GC.ofCircuit_eval, hC])
  simp only [Finset.card_empty, Nat.sub_zero] at this
  exact Nat.sub_le_of_le_add (by simpa [GC.ofCircuit] using this)

/-! ## Symmetric functions -/

namespace GateElim

variable {n : ℕ}

/-- Number of `true` inputs. -/
def ones (x : Fin n → Bool) : ℕ := (Finset.univ.filter fun l => x l = true).card

/-- The point of the subcube `RDom Z c` whose free variables are `true` exactly on `S`. -/
def pt (Z : Finset (Fin n)) (c : Fin n → Bool) (S : Finset (Fin n)) : Fin n → Bool :=
  fun l => if l ∈ Z then c l else decide (l ∈ S)

/-- Number of fixed variables fixed to `true`. -/
def ones₀ (Z : Finset (Fin n)) (c : Fin n → Bool) : ℕ := (Z.filter fun l => c l = true).card

theorem pt_mem (Z : Finset (Fin n)) (c : Fin n → Bool) (S : Finset (Fin n)) :
    pt Z c S ∈ RDom Z c := fun z hz => by simp [pt, hz]

theorem ones_pt (Z : Finset (Fin n)) (c : Fin n → Bool) (S : Finset (Fin n))
    (hS : Disjoint S Z) : ones (pt Z c S) = ones₀ Z c + S.card := by
  unfold ones ones₀
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left
    (Finset.filter_subset _ _) hS.symm)]
  congr 1
  ext l
  by_cases hl : l ∈ Z
  · have : l ∉ S := fun h => Finset.disjoint_left.mp hS h hl
    simp [pt, hl, this]
  · simp [pt, hl]

theorem pt_of_notMem {Z : Finset (Fin n)} (c : Fin n → Bool) (S : Finset (Fin n)) {l : Fin n}
    (hl : l ∉ Z) : pt Z c S l = decide (l ∈ S) := by simp [pt, hl]

/-- Dependence for a symmetric function `f = g ∘ ones`. -/
theorem sym_dep (g : ℕ → Bool) (f : (Fin n → Bool) → Bool) (hf : ∀ x, f x = g (ones x))
    (Z : Finset (Fin n)) (c : Fin n → Bool) (p : Fin n) (hp : p ∉ Z) (k : ℕ)
    (hk : k + 1 ≤ n - Z.card) (hg : g (ones₀ Z c + k) ≠ g (ones₀ Z c + k + 1)) :
    DependsOn f (RDom Z c) p := by
  have hF : k ≤ ((Finset.univ \ Z).erase p).card := by
    rw [Finset.card_erase_of_mem (by simpa using hp), card_free]; omega
  obtain ⟨S, hS, hSk⟩ := Finset.exists_subset_card_eq hF
  have hpS : p ∉ S := fun h => by simpa using hS h
  have hSZ : Disjoint S Z := Finset.disjoint_left.mpr fun l hl hlZ => by
    simpa [hlZ] using hS hl
  have hSZ' : Disjoint (insert p S) Z := Finset.disjoint_insert_left.mpr ⟨hp, hSZ⟩
  refine ⟨pt Z c S, pt_mem _ _ _, pt Z c (insert p S), pt_mem _ _ _, fun l hl => ?_, ?_⟩
  · by_cases hlZ : l ∈ Z
    · simp [pt, hlZ]
    · simp [pt, hlZ, hl]
  · rw [hf, hf, ones_pt _ _ _ hSZ, ones_pt _ _ _ hSZ', Finset.card_insert_of_notMem hpS, hSk]
    simpa [Nat.add_assoc] using hg

/-- Distinct subfunctions for a symmetric function: fixing `(x_i, x_j)` to the values coded
by `A, B ⊆ {i, j}` gives different subfunctions if `g` separates the corresponding counts
for some number `r ≤ m - 2` of further ones. -/
theorem sym_subDiff (g : ℕ → Bool) (f : (Fin n → Bool) → Bool) (hf : ∀ x, f x = g (ones x))
    (Z : Finset (Fin n)) (c : Fin n → Bool) (i j : Fin n) (hi : i ∉ Z) (hj : j ∉ Z) (hij : i ≠ j)
    (A B : Finset (Fin n)) (hA : A ⊆ {i, j}) (hB : B ⊆ {i, j}) (r : ℕ)
    (hr : r + 2 ≤ n - Z.card) (hg : g (ones₀ Z c + A.card + r) ≠ g (ones₀ Z c + B.card + r)) :
    SubDiff f (RDom Z c) i j (decide (i ∈ A), decide (j ∈ A)) (decide (i ∈ B), decide (j ∈ B)) := by
  have hF : r ≤ ((Finset.univ \ Z) \ {i, j}).card := by
    rw [Finset.card_sdiff_of_subset (by
      intro l hl; simp at hl; rcases hl with rfl | rfl <;> simpa), card_free,
      Finset.card_pair hij]; omega
  obtain ⟨S, hS, hSk⟩ := Finset.exists_subset_card_eq hF
  have hiS : i ∉ S := fun h => by simpa using hS h
  have hjS : j ∉ S := fun h => by simpa using hS h
  have hSZ : Disjoint S Z := Finset.disjoint_left.mpr fun l hl hlZ => by
    simpa [hlZ] using hS hl
  have hdisj : ∀ T ⊆ ({i, j} : Finset (Fin n)),
      Disjoint (T ∪ S) Z ∧ (T ∪ S).card = T.card + r := by
    intro T hT
    have hTZ : Disjoint T Z := Finset.disjoint_left.mpr fun l hl hlZ => by
      have := hT hl; simp at this; rcases this with rfl | rfl
      · exact hi hlZ
      · exact hj hlZ
    refine ⟨Finset.disjoint_union_left.mpr ⟨hTZ, hSZ⟩, ?_⟩
    rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun l hl hlS => by
      have := hT hl; simp at this; rcases this with rfl | rfl
      · exact hiS hlS
      · exact hjS hlS), hSk]
  obtain ⟨hAZ, hAc⟩ := hdisj A hA
  obtain ⟨hBZ, hBc⟩ := hdisj B hB
  refine ⟨pt Z c (A ∪ S), pt_mem _ _ _, pt Z c (B ∪ S), pt_mem _ _ _, ?_, ?_, ?_, ?_⟩
  · intro l hli hlj
    by_cases hlZ : l ∈ Z
    · simp [pt, hlZ]
    · have h1 : l ∉ A := fun h => by have := hA h; simp at this; tauto
      have h2 : l ∉ B := fun h => by have := hB h; simp at this; tauto
      simp [pt, hlZ, h1, h2]
  · simp [pt, hi, hj, hiS, hjS]
  · simp [pt, hi, hj, hiS, hjS]
  · rw [hf, hf, ones_pt _ _ _ hAZ, ones_pt _ _ _ hBZ, hAc, hBc, ← Nat.add_assoc,
      ← Nat.add_assoc]
    exact hg

/-- Three distinct subfunctions for a symmetric function `f = g ∘ ones`: fixing
`(x_i, x_j)` to `00`, `10`, `11` adds `0, 1, 2` ones; it suffices that `g` separates each
pair of these shifts for some `r ≤ m - 2` further ones. -/
theorem sym_three (g : ℕ → Bool) (f : (Fin n → Bool) → Bool) (hf : ∀ x, f x = g (ones x))
    (Z : Finset (Fin n)) (c : Fin n → Bool) (i j : Fin n) (hi : i ∉ Z) (hj : j ∉ Z)
    (hij : i ≠ j)
    (h01 : ∃ r, r + 2 ≤ n - Z.card ∧ g (ones₀ Z c + r) ≠ g (ones₀ Z c + 1 + r))
    (h12 : ∃ r, r + 2 ≤ n - Z.card ∧ g (ones₀ Z c + 1 + r) ≠ g (ones₀ Z c + 2 + r))
    (h02 : ∃ r, r + 2 ≤ n - Z.card ∧ g (ones₀ Z c + r) ≠ g (ones₀ Z c + 2 + r)) :
    ThreeSub f (RDom Z c) i j := by
  have s0 : (∅ : Finset (Fin n)) ⊆ {i, j} := Finset.empty_subset _
  have s1 : ({i} : Finset (Fin n)) ⊆ {i, j} := by simp
  have s2 : ({i, j} : Finset (Fin n)) ⊆ {i, j} := Finset.Subset.refl _
  have c1 : ({i} : Finset (Fin n)).card = 1 := Finset.card_singleton _
  have c2 : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
  obtain ⟨r1, hr1, g1⟩ := h01
  obtain ⟨r2, hr2, g2⟩ := h12
  obtain ⟨r3, hr3, g3⟩ := h02
  have d1 := sym_subDiff g f hf Z c i j hi hj hij ∅ {i} s0 s1 r1 hr1 (by
    rw [Finset.card_empty, c1, Nat.add_zero]; exact g1)
  have d2 := sym_subDiff g f hf Z c i j hi hj hij {i} {i, j} s1 s2 r2 hr2 (by
    rw [c1, c2]; exact g2)
  have d3 := sym_subDiff g f hf Z c i j hi hj hij ∅ {i, j} s0 s2 r3 hr3 (by
    rw [Finset.card_empty, c2, Nat.add_zero]; exact g3)
  exact ⟨_, _, _, d1, d2, d3⟩

/-! ## Instances -/

/-- `MOD₃` with residue `t`: the number of ones is `≡ t (mod 3)`. -/
def mod3 (t : ℕ) (x : Fin n → Bool) : Bool := decide (ones x % 3 = t)

theorem mod3_sep (t : ℕ) (ht : t < 3) (a k l : ℕ) (hkl : k < l) (hl : l ≤ 2) :
    ∃ r, r ≤ 1 ∧ decide ((a + k + r) % 3 = t) ≠ decide ((a + l + r) % 3 = t) := by
  by_cases h : (a + k) % 3 = t
  · exact ⟨0, by omega, by simp only [Nat.add_zero, h, decide_true]; simp; omega⟩
  · by_cases h' : (a + l) % 3 = t
    · exact ⟨0, by omega, by simp only [Nat.add_zero, h, h', decide_true, decide_false]; simp⟩
    · refine ⟨1, le_rfl, ?_⟩
      have : (a + k + 1) % 3 = t ∨ (a + l + 1) % 3 = t := by omega
      have hne : ¬ ((a + k + 1) % 3 = t ∧ (a + l + 1) % 3 = t) := by omega
      rcases this with h1 | h1
      · have : ¬ (a + l + 1) % 3 = t := fun h2 => hne ⟨h1, h2⟩
        simp [h1, this]
      · have : ¬ (a + k + 1) % 3 = t := fun h2 => hne ⟨h2, h1⟩
        simp [h1, this]

/-- `MOD₃` (any residue) is in Schnorr's class `Q²,³` (all restrictions are good). -/
theorem q23_mod3 (t : ℕ) (ht : t < 3) : Q23 (mod3 (n := n) t) (fun _ _ => True) where
  dep Z c _ hm p hp := by
    obtain ⟨r, hr, hg⟩ := mod3_sep t ht (ones₀ Z c) 0 1 (by omega) (by omega)
    exact sym_dep (fun k => decide (k % 3 = t)) _ (fun _ => rfl) Z c p hp r (by omega)
      (by simpa [Nat.add_assoc, Nat.add_comm 1 r] using hg)
  three Z c _ hm i j hi hj hij := by
    refine sym_three (fun k => decide (k % 3 = t)) _ (fun _ => rfl) Z c i j hi hj hij ?_ ?_ ?_
    · obtain ⟨r, hr, hg⟩ := mod3_sep t ht (ones₀ Z c) 0 1 (by omega) (by omega)
      exact ⟨r, by omega, by simpa using hg⟩
    · obtain ⟨r, hr, hg⟩ := mod3_sep t ht (ones₀ Z c) 1 2 (by omega) (by omega)
      exact ⟨r, by omega, hg⟩
    · obtain ⟨r, hr, hg⟩ := mod3_sep t ht (ones₀ Z c) 0 2 (by omega) (by omega)
      exact ⟨r, by omega, by simpa using hg⟩
  fix _ _ _ _ _ _ := ⟨false, trivial⟩

theorem th2_eq_ones (x : Fin n → Bool) : th2 x = decide (2 ≤ ones x) := rfl

/-- Good restrictions for threshold-2: fixed variables are `false`. -/
def FalseFixed (Z : Finset (Fin n)) (c : Fin n → Bool) : Prop := ∀ z ∈ Z, c z = false

theorem ones₀_of_falseFixed {Z : Finset (Fin n)} {c : Fin n → Bool} (h : FalseFixed Z c) :
    ones₀ Z c = 0 := by
  unfold ones₀
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro z hz; simp [h z hz]

/-- Threshold-2 is a `Q23` family member when only constants `false` are allowed. -/
theorem q23_th2 : Q23 (th2 (n := n)) FalseFixed where
  dep Z c hR hm p hp :=
    sym_dep (fun k => decide (2 ≤ k)) _ th2_eq_ones Z c p hp 1 (by omega)
      (by rw [ones₀_of_falseFixed hR]; decide)
  three Z c hR hm i j hi hj hij := by
    refine sym_three (fun k => decide (2 ≤ k)) _ th2_eq_ones Z c i j hi hj hij ?_ ?_ ?_ <;>
      rw [ones₀_of_falseFixed hR]
    · exact ⟨1, by omega, by decide⟩
    · exact ⟨0, by omega, by decide⟩
    · exact ⟨0, by omega, by decide⟩
  fix Z c hR _ v _ := ⟨false, fun z hz => by
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simp
    · by_cases hzv : z = v
      · subst hzv; simp
      · rw [Function.update_of_ne hzv]; exact hR z hz⟩

end GateElim

open GateElim in
/-- **`MOD₃` needs `2 n - 3` gates.** Every `B₂` circuit deciding whether the number of
ones is `≡ t (mod 3)` (any `t < 3`) on `n ≥ 2` variables has at least `2 n - 3` gates. -/
theorem mod3_lower_bound {n s : ℕ} (hn : 2 ≤ n) (t : ℕ) (ht : t < 3) (C : Circuit n s)
    (hC : C.eval = mod3 t) : 2 * n - 3 ≤ s :=
  q23_lower_bound hn _ _ (q23_mod3 t ht) (fun _ => false) trivial C hC

open GateElim in
/-- Schnorr's threshold-2 bound, re-derived from the general `Q²,³` theorem. -/
theorem th2_lower_bound' {n s : ℕ} (hn : 2 ≤ n) (C : Circuit n s) (hC : C.eval = th2) :
    2 * n - 3 ≤ s :=
  q23_lower_bound hn _ _ q23_th2 (fun _ => false) (fun _ h => by simp at h) C hC

end Pnp.Circuits
