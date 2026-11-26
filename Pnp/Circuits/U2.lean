import Pnp.Circuits.Schnorr

/-!
# PARITY needs `3 (n - 1)` gates over the basis `U₂` (M13)

`U₂` is the full binary basis `B₂` without the two XOR-type operations `⊕` and `≡`.
Every `U₂` operation that depends on both of its arguments is of "AND type"
`(p ^ a ∧ q ^ b) ^ c`: each argument has a value that makes the gate constant.

* `parity_u2_lower_bound` (Schnorr 1974; see also Red'kin 1973): every `U₂` circuit
  computing PARITY on `n ≥ 1` variables has at least `3 (n - 1)` gates.
* `parity_u2_hasCircuitOfSize`: the bound is tight (chain of `n - 1` XORs, each built from
  three `U₂` gates `(p ∧ ¬q) ∨ (¬p ∧ q)`).

## Proof (gate elimination)

Work in the generalized circuits `GC n` of `GateElim` on a subcube `RDom Z c` with
`m = n - |Z|` free variables, keeping the invariant that all operations are in `U₂`
(`NoXor`; preserved by `GC.elim`, since absorbing unary functions into an operation never
creates XOR). After removing gates that are unary on the subcube and gates whose value is
never used, let `G` be gate `0`, reading free variables `x_i ≠ x_j`, with AND-type operation:
`G` is constant when `x_i = α`, and also when `x_j = β`.

* `x_i` is read by another gate `H` (otherwise fix `x_j = β`: the circuit no longer depends
  on `x_i`, but PARITY does); likewise for `x_j`.
* `G` is not the output and is read by some gate `K`.
* Fixing `x_i = α` makes `G`, `H` and `K` have a constant input, so three gates disappear,
  unless every such `H` equals every such `K`, i.e. the only other reader of `x_i` is the
  only reader of `G`. If this happens for both `x_i` and `x_j`, that one gate `K` reads
  the three different wires `x_i`, `x_j`, `G`: impossible with fan-in 2.

So fixing one variable removes three gates, and induction gives `3 (m - 1)`.
-/

namespace Pnp.Circuits

namespace GateElim

open GC

/-! ## The basis `U₂` -/

/-- `op` is `⊕` or `≡`. -/
def IsXorType (op : Bool → Bool → Bool) : Prop :=
  (∀ p q, op p q = xor p q) ∨ (∀ p q, op p q = !(xor p q))

instance (op : Bool → Bool → Bool) : Decidable (IsXorType op) := by
  unfold IsXorType; infer_instance

/-- The basis `U₂ = B₂ \ {⊕, ≡}`. -/
def InU2 (op : Bool → Bool → Bool) : Prop := ¬ IsXorType op

instance (op : Bool → Bool → Bool) : Decidable (InU2 op) := by
  unfold InU2; infer_instance

/-- Composing a `U₂` operation with unary functions on its inputs stays in `U₂`. -/
theorem inU2_comp : ∀ (op : Bool → Bool → Bool), InU2 op → ∀ (u v : Bool → Bool),
    InU2 (fun p q => op (u p) (v q)) := by decide

/-- A `U₂` operation depending on both arguments has a value of the first argument making
it constant. -/
theorem u2_left : ∀ (op : Bool → Bool → Bool), InU2 op →
    (¬ ∃ u : Bool → Bool, ∀ p q, op p q = u p) → (¬ ∃ u : Bool → Bool, ∀ p q, op p q = u q) →
    ∃ a, op a true = op a false := by decide

/-- A `U₂` operation depending on both arguments has a value of the second argument making
it constant. -/
theorem u2_right : ∀ (op : Bool → Bool → Bool), InU2 op →
    (¬ ∃ u : Bool → Bool, ∀ p q, op p q = u p) → (¬ ∃ u : Bool → Bool, ∀ p q, op p q = u q) →
    ∃ b, op true b = op false b := by decide

variable {n : ℕ}

/-- All operations of a generalized circuit are in `U₂`. -/
def NoXor (C : GC n) : Prop := ∀ i < C.s, InU2 (C.op i)

theorem elim_noXor (C : GC n) (k w : ℕ) (u : Bool → Bool) (hk : k < C.s) (hw : w < n + k)
    (hN : NoXor C) : NoXor (C.elim k w u hk hw) := by
  intro i hi
  have hi' : i < C.s - 1 := hi
  show InU2 (if i < k then C.op i else _)
  split_ifs with h
  · exact hN i (by omega)
  · exact inU2_comp _ (hN (i + 1) (by omega)) _ _

/-! ## More on `GC.elim` -/

theorem elim_op_lt (C : GC n) (k w : ℕ) (u : Bool → Bool) (hk : k < C.s) (hw : w < n + k)
    {i : ℕ} (hi : i < k) : (C.elim k w u hk hw).op i = C.op i := by
  show (if i < k then _ else _) = _; rw [if_pos hi]

theorem elim_a_lt (C : GC n) (k w : ℕ) (u : Bool → Bool) (hk : k < C.s) (hw : w < n + k)
    {i : ℕ} (hi : i < k) : (C.elim k w u hk hw).a i = C.a i := by
  show (if i < k then _ else _) = _; rw [if_pos hi]

theorem elim_b_lt (C : GC n) (k w : ℕ) (u : Bool → Bool) (hk : k < C.s) (hw : w < n + k)
    {i : ℕ} (hi : i < k) : (C.elim k w u hk hw).b i = C.b i := by
  show (if i < k then _ else _) = _; rw [if_pos hi]

/-- Wires below the deleted gate keep their values. -/
theorem elim_val_lt (C : GC n) (k w : ℕ) (u : Bool → Bool) (hk : k < C.s) (hw : w < n + k)
    (x : Fin n → Bool) : ∀ j, j < n + k → (C.elim k w u hk hw).val x j = C.val x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjn : j < n
    · rw [GC.val_input _ x hjn, GC.val_input _ x hjn]
    · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
      have hik : i < k := by omega
      have hi' : i < (C.elim k w u hk hw).s := by show i < C.s - 1; omega
      have ha := C.ha i (by omega)
      have hb := C.hb i (by omega)
      rw [GC.val_gate _ x hi', GC.val_gate _ x (by omega : i < C.s), elim_op_lt _ _ _ _ _ _ hik,
        elim_a_lt _ _ _ _ _ _ hik, elim_b_lt _ _ _ _ _ _ hik, ih _ (by omega) (by omega),
        ih _ (by omega) (by omega)]

/-- The wire of gate `k` is used: read by a gate, or the output. -/
def Used (C : GC n) (k : ℕ) : Prop :=
  (∃ i < C.s, C.a i = n + k ∨ C.b i = n + k) ∨ C.out = n + k

/-- An unused gate can be deleted. -/
theorem elim_eval_dead (C : GC n) (k w : ℕ) (u : Bool → Bool) (hk : k < C.s) (hw : w < n + k)
    (hd : ¬ Used C k) (x : Fin n → Bool) : (C.elim k w u hk hw).eval x = C.eval x := by
  simp only [Used, not_or, not_exists, not_and] at hd
  obtain ⟨hd1, hd2⟩ := hd
  let emb : ℕ → ℕ := fun j => if j < n + k then j else j + 1
  have key : ∀ j, j ≠ n + k → tr n k u j (C.val x (emb (ren n k w j))) = C.val x j := by
    intro j hjk
    simp only [emb, ren, tr]
    by_cases h1 : j < n + k
    · simp [h1, hjk]
    · rw [if_neg h1, if_neg hjk, if_neg hjk, if_neg (by omega)]
      simp only [id]
      congr 1; omega
  have hval : ∀ j < n + (C.s - 1), C.val x (emb j) = (C.elim k w u hk hw).val x j := by
    refine wv_mkGates_unique x (fun j => C.val x (emb j)) (fun j hj => ?_) (fun i hi => ?_)
    · simp only [emb, if_pos (show j < n + k by omega)]
      exact C.val_input x hj
    · by_cases hik : i < k
      · simp only [GC.elim, emb, if_pos hik, if_pos (show n + i < n + k by omega)]
        have := C.ha i (by omega)
        have := C.hb i (by omega)
        rw [if_pos (show C.a i < n + k by omega), if_pos (show C.b i < n + k by omega)]
        exact C.val_gate x (by omega)
      · simp only [GC.elim, if_neg hik]
        have h1 := hd1 (i + 1) (by omega)
        rw [key _ h1.1, key _ h1.2]
        simp only [emb, if_neg (show ¬ n + i < n + k by omega)]
        rw [show n + i + 1 = n + (i + 1) by omega]
        exact C.val_gate x (i := i + 1) (by omega)
  unfold GC.eval
  have hout := (C.elim k w u hk hw).hout
  rw [← hval _ hout]
  exact congrArg C.outf (key C.out hd2)

/-- Gate `g` has an input that is constant on `D`. -/
def ConstIn (C : GC n) (D : Set (Fin n → Bool)) (g : ℕ) : Prop :=
  g < C.s ∧ ((∃ c, ∀ x ∈ D, C.val x (C.a g) = c) ∨ (∃ c, ∀ x ∈ D, C.val x (C.b g) = c))

theorem ConstIn.removable {C : GC n} {D : Set (Fin n → Bool)} {g : ℕ} (h : ConstIn C D g) :
    C.Removable D g := by
  obtain ⟨hg, ⟨c, hc⟩ | ⟨c, hc⟩⟩ := h
  · exact C.removable_of_a D hg c hc
  · exact C.removable_of_b D hg c hc

theorem ConstIn.elim {C : GC n} {D : Set (Fin n → Bool)} {g : ℕ} (h : ConstIn C D g)
    (k w : ℕ) (u : Bool → Bool) (hk : k < C.s) (hw : w < n + k) (hgk : g < k) :
    ConstIn (C.elim k w u hk hw) D g := by
  obtain ⟨hg, hc⟩ := h
  refine ⟨show g < C.s - 1 by omega, ?_⟩
  rw [elim_a_lt _ _ _ _ _ _ hgk, elim_b_lt _ _ _ _ _ _ hgk]
  have ha := C.ha g hg
  have hb := C.hb g hg
  rcases hc with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Or.inl ⟨c, fun x hx => by rw [elim_val_lt C k w u hk hw x _ (by omega)]; exact hc x hx⟩
  · exact Or.inr ⟨c, fun x hx => by rw [elim_val_lt C k w u hk hw x _ (by omega)]; exact hc x hx⟩

/-- Deleting a gate with a constant input; lower gates with constant inputs stay so. -/
theorem elim_constIn (C : GC n) (D : Set (Fin n → Bool)) {k : ℕ} (hN : NoXor C)
    (hk : ConstIn C D k) :
    ∃ C' : GC n, C'.s = C.s - 1 ∧ NoXor C' ∧ (∀ x ∈ D, C'.eval x = C.eval x) ∧
      ∀ g < k, ConstIn C D g → ConstIn C' D g := by
  obtain ⟨w, hw, u, hu⟩ := hk.removable
  exact ⟨C.elim k w u hk.1 hw, rfl, elim_noXor _ _ _ _ _ _ hN,
    fun x hx => C.elim_eval k w u hk.1 hw x (hu x hx),
    fun g hg h => h.elim k w u hk.1 hw hg⟩

/-- Deleting three gates with constant inputs. -/
theorem elim_three (C : GC n) (D : Set (Fin n → Bool)) (hN : NoXor C) {g₀ g₁ g₂ : ℕ}
    (h01 : g₀ < g₁) (h12 : g₁ < g₂) (h0 : ConstIn C D g₀) (h1 : ConstIn C D g₁)
    (h2 : ConstIn C D g₂) :
    ∃ C' : GC n, C'.s = C.s - 3 ∧ NoXor C' ∧ ∀ x ∈ D, C'.eval x = C.eval x := by
  obtain ⟨C1, hs1, hN1, he1, hk1⟩ := elim_constIn C D hN h2
  have h1' := hk1 g₁ h12 h1
  have h0' := hk1 g₀ (by omega) h0
  obtain ⟨C2, hs2, hN2, he2, hk2⟩ := elim_constIn C1 D hN1 h1'
  have h0'' := hk2 g₀ h01 h0'
  obtain ⟨C3, hs3, hN3, he3, -⟩ := elim_constIn C2 D hN2 h0''
  exact ⟨C3, by omega, hN3, fun x hx => (he3 x hx).trans ((he2 x hx).trans (he1 x hx))⟩

/-! ## PARITY -/

/-- PARITY: an odd number of inputs is `true`. -/
def parityB (x : Fin n → Bool) : Bool := decide (ones x % 2 = 1)

theorem ones_eq_add (x : Fin n → Bool) (p : Fin n) :
    ones x = (if x p = true then 1 else 0) +
      ∑ l ∈ Finset.univ.erase p, if x l = true then 1 else 0 := by
  unfold ones
  rw [Finset.card_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]

/-- Flipping one input flips PARITY. -/
theorem parityB_flip (x : Fin n → Bool) (p : Fin n) :
    parityB (Function.update x p (!x p)) = !parityB x := by
  have h1 := ones_eq_add x p
  have h2 := ones_eq_add (Function.update x p (!x p)) p
  have hsum : (∑ l ∈ Finset.univ.erase p,
      if Function.update x p (!x p) l = true then 1 else 0) =
      ∑ l ∈ Finset.univ.erase p, if x l = true then 1 else 0 := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [hsum, Function.update_self] at h2
  unfold parityB
  generalize ones (Function.update x p (!x p)) = A at h2 ⊢
  generalize ones x = B at h1 ⊢
  generalize (∑ l ∈ Finset.univ.erase p, if x l = true then 1 else 0) = R at h1 h2
  generalize x p = b at h1 h2
  cases b <;> simp at h1 h2 <;>
    (rcases Nat.mod_two_eq_zero_or_one A with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one B with h' | h' <;> simp [h, h'] <;> omega)

theorem update_mem_rdom {Z : Finset (Fin n)} {c x : Fin n → Bool} (hx : x ∈ RDom Z c)
    {p : Fin n} (hp : p ∉ Z) (b : Bool) : Function.update x p b ∈ RDom Z c := fun z hz => by
  rw [Function.update_of_ne (by rintro rfl; exact hp hz)]; exact hx z hz

theorem parity_dep {Z : Finset (Fin n)} (c : Fin n → Bool) {p : Fin n} (hp : p ∉ Z) :
    DependsOn parityB (RDom Z c) p := by
  refine ⟨pt Z c ∅, pt_mem Z c ∅, _, update_mem_rdom (pt_mem Z c ∅) hp (!(pt Z c ∅ p)),
    fun l hl => (Function.update_of_ne hl _ _).symm, ?_⟩
  rw [parityB_flip]
  cases parityB (pt Z c ∅) <;> simp

/-- If no gate other than gate `0` reads input `e`, then two inputs differing only at `e`
and giving gate `0` the same value give every wire other than `e` the same value. -/
theorem indep1 (C : GC n) (e : Fin n)
    (hrest : ∀ k, 1 ≤ k → k < C.s → C.a k ≠ e.val ∧ C.b k ≠ e.val)
    (x y : Fin n → Bool) (hxy : ∀ l, l ≠ e → x l = y l) (h0 : C.val x n = C.val y n) :
    ∀ w, w < n + C.s → w ≠ e.val → C.val x w = C.val y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hwe
    by_cases hwn : w < n
    · rw [C.val_input x hwn, C.val_input y hwn]
      exact hxy _ (fun h => hwe (congrArg Fin.val h))
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using h0
      · have hks : k < C.s := by omega
        obtain ⟨h1, h2⟩ := hrest k hk hks
        have ha := C.ha k hks
        have hb := C.hb k hks
        rw [C.val_gate x hks, C.val_gate y hks, ih _ (by omega) (by omega) h1,
          ih _ (by omega) (by omega) h2]

theorem constIn_of_reads (C : GC n) (D : Set (Fin n → Bool)) {g w : ℕ} (hg : g < C.s)
    (hr : C.a g = w ∨ C.b g = w) (c : Bool) (hc : ∀ x ∈ D, C.val x w = c) :
    ConstIn C D g := by
  rcases hr with h | h
  · exact ⟨hg, Or.inl ⟨c, fun x hx => h ▸ hc x hx⟩⟩
  · exact ⟨hg, Or.inr ⟨c, fun x hx => h ▸ hc x hx⟩⟩

/-- **The `3 (m - 1)` bound for generalized `U₂` circuits on a subcube.** -/
theorem parity_u2_gc :
    ∀ (s : ℕ) (C : GC n) (Z : Finset (Fin n)) (c : Fin n → Bool), C.s = s → NoXor C →
      1 ≤ n - Z.card → (∀ x ∈ RDom Z c, C.eval x = parityB x) →
      3 * (n - Z.card) ≤ C.s + 3 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C Z c hs hN hm hC
    have hn : 0 < n := by omega
    -- 1. gates that are unary functions of an earlier wire
    by_cases hel : ∃ k < C.s, C.Removable (RDom Z c) k
    · obtain ⟨k, hk, w, hw, u, hu⟩ := hel
      have := ih (C.s - 1) (by omega) (C.elim k w u hk hw) Z c rfl
        (elim_noXor _ _ _ _ _ _ hN) hm
        (fun x hx => (C.elim_eval k w u hk hw x (hu x hx)).trans (hC x hx))
      have h' : (C.elim k w u hk hw).s = C.s - 1 := rfl
      omega
    push Not at hel
    -- 2. unused gates
    by_cases hdead : ∃ k < C.s, ¬ Used C k
    · obtain ⟨k, hk, hd⟩ := hdead
      have := ih (C.s - 1) (by omega) (C.elim k 0 id hk (by omega)) Z c rfl
        (elim_noXor _ _ _ _ _ _ hN) hm
        (fun x hx => (elim_eval_dead C k 0 id hk (by omega) hd x).trans (hC x hx))
      have h' : (C.elim k 0 id hk (by omega)).s = C.s - 1 := rfl
      omega
    push Not at hdead
    by_cases hm1 : n - Z.card = 1
    · omega
    have hm2 : 2 ≤ n - Z.card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ : ∃ p ∈ Finset.univ \ Z, ∃ q ∈ Finset.univ \ Z, p ≠ q := by
      apply Finset.one_lt_card.mp
      rw [card_free]; omega
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hp hq
    have hlit : ¬ C.out < n := fun ho =>
      no_lit' C parityB _ hC ho p q hpq (parity_dep c hp) (parity_dep c hq)
    have hs0 : 0 < C.s := by
      by_contra h0
      exact hlit (by have := C.hout; omega)
    have ha0 : C.a 0 < n := by simpa using C.ha 0 hs0
    have hb0 : C.b 0 < n := by simpa using C.hb 0 hs0
    have hab : C.a 0 ≠ C.b 0 := fun h => hel 0 hs0 (C.removable_of_eq _ hs0 h)
    set i : Fin n := ⟨C.a 0, ha0⟩ with hi_def
    set j : Fin n := ⟨C.b 0, hb0⟩ with hj_def
    have hiZ : i ∉ Z := fun hz => hel 0 hs0 (C.removable_of_a _ hs0 (c i)
      (fun x hx => by rw [C.val_input x ha0]; exact hx i hz))
    have hjZ : j ∉ Z := fun hz => hel 0 hs0 (C.removable_of_b _ hs0 (c j)
      (fun x hx => by rw [C.val_input x hb0]; exact hx j hz))
    have hij : i ≠ j := fun h => hab (congrArg Fin.val h)
    have hijv : i.val ≠ j.val := hab
    have hval0 : ∀ x, C.val x n = C.op 0 (x i) (x j) := by
      intro x
      have := C.val_gate x hs0
      rw [Nat.add_zero] at this
      rw [this, C.val_input x ha0, C.val_input x hb0]
    -- the operation of gate 0 is of AND type
    have hnd1 : ¬ ∃ u : Bool → Bool, ∀ p q, C.op 0 p q = u p := by
      rintro ⟨u, hu⟩
      exact hel 0 hs0 ⟨C.a 0, C.ha 0 hs0, u, fun x _ => by rw [C.val_gate x hs0, hu]⟩
    have hnd2 : ¬ ∃ u : Bool → Bool, ∀ p q, C.op 0 p q = u q := by
      rintro ⟨u, hu⟩
      exact hel 0 hs0 ⟨C.b 0, C.hb 0 hs0, u, fun x _ => by rw [C.val_gate x hs0, hu]⟩
    obtain ⟨α, hα⟩ := u2_left (C.op 0) (hN 0 hs0) hnd1 hnd2
    obtain ⟨β, hβ⟩ := u2_right (C.op 0) (hN 0 hs0) hnd1 hnd2
    have hα' : ∀ q, C.op 0 α q = C.op 0 α true := by intro q; cases q <;> simp [hα]
    have hβ' : ∀ p, C.op 0 p β = C.op 0 true β := by intro p; cases p <;> simp [hβ]
    -- a base point of the subcube
    set x₀ : Fin n → Bool := pt Z c ∅ with hx₀
    have hx₀m : x₀ ∈ RDom Z c := pt_mem Z c ∅
    -- Fact A: both inputs of gate 0 have another reader
    have factA : ∀ (e f : Fin n) (γ : Bool), e ∉ Z → f ∉ Z → e ≠ f →
        (∀ x, x f = γ → C.val x n = C.val (Function.update x e (!x e)) n) →
        ∃ h, 1 ≤ h ∧ h < C.s ∧ (C.a h = e.val ∨ C.b h = e.val) := by
      intro e f γ heZ hfZ hef hconst
      by_contra hne
      push Not at hne
      set x := Function.update x₀ f γ with hx
      have hxm : x ∈ RDom Z c := update_mem_rdom hx₀m hfZ γ
      set y := Function.update x e (!x e) with hy
      have hym : y ∈ RDom Z c := update_mem_rdom hxm heZ _
      have hxf : x f = γ := by rw [hx, Function.update_self]
      have hw := indep1 C e (fun k hk1 hks => hne k hk1 hks) x y
        (fun l hl => (Function.update_of_ne hl _ _).symm) (hconst x hxf)
        C.out C.hout (by have := e.2; omega)
      have hpe := parityB_flip x e
      have := hC x hxm
      have := hC y hym
      unfold GC.eval at *
      rw [hw] at *
      cases hpx : parityB x <;> simp_all
    have hAi : ∃ h, 1 ≤ h ∧ h < C.s ∧ (C.a h = i.val ∨ C.b h = i.val) :=
      factA i j β hiZ hjZ hij (fun x hxf => by
        rw [hval0, hval0, Function.update_of_ne (Ne.symm hij), hxf, hβ' (x i),
          hβ' (Function.update x i (!x i) i)])
    have hAj : ∃ h, 1 ≤ h ∧ h < C.s ∧ (C.a h = j.val ∨ C.b h = j.val) :=
      factA j i α hjZ hiZ (Ne.symm hij) (fun x hxf => by
        rw [hval0, hval0, Function.update_of_ne hij, hxf, hα' (x j),
          hα' (Function.update x j (!x j) j)])
    -- Fact B: gate 0 is not the output, hence read by some gate
    have hout0 : C.out ≠ n := by
      intro ho
      set x := Function.update x₀ i α with hx
      have hxm : x ∈ RDom Z c := update_mem_rdom hx₀m hiZ α
      set y := Function.update x j (!x j) with hy
      have hym : y ∈ RDom Z c := update_mem_rdom hxm hjZ _
      have hyi : y i = α := by
        rw [hy, Function.update_of_ne hij, hx, Function.update_self]
      have hxi : x i = α := by rw [hx, Function.update_self]
      have hev : C.eval x = C.eval y := by
        unfold GC.eval; rw [ho, hval0, hval0, hxi, hyi, hα', hα' (y j)]
      have hpe := parityB_flip x j
      rw [hC x hxm, hC y hym] at hev
      rw [← hev] at hpe
      cases hpx : parityB x <;> simp_all
    obtain ⟨K, hKs, hK⟩ : ∃ K < C.s, C.a K = n ∨ C.b K = n := by
      rcases hdead 0 hs0 with ⟨K, hKs, hK⟩ | ho
      · exact ⟨K, hKs, by simpa using hK⟩
      · exact absurd (by simpa using ho) hout0
    have hK1 : 1 ≤ K := by
      by_contra h0
      have : K = 0 := by omega
      subst this
      omega
    -- Fixing one variable removes three gates.
    have finish : ∀ (v : Fin n) (b : Bool) (H K' : ℕ), v ∉ Z → 1 ≤ H → 1 ≤ K' → H ≠ K' →
        ConstIn C (RDom (insert v Z) (Function.update c v b)) 0 →
        ConstIn C (RDom (insert v Z) (Function.update c v b)) H →
        ConstIn C (RDom (insert v Z) (Function.update c v b)) K' →
        3 * (n - Z.card) ≤ C.s + 3 := by
      intro v b H K' hvZ hH1 hK1' hHK h0 hH hK
      have hsub : ∀ x ∈ RDom (insert v Z) (Function.update c v b), x ∈ RDom Z c :=
        fun x hx z hz => by
          have hzv : z ≠ v := fun h => hvZ (h ▸ hz)
          rw [hx z (Finset.mem_insert_of_mem hz), Function.update_of_ne hzv]
      have hcard : (insert v Z).card = Z.card + 1 := Finset.card_insert_of_notMem hvZ
      have hHs := hH.1
      have hKs := hK.1
      obtain ⟨C', hs', hN', he'⟩ : ∃ C' : GC n, C'.s = C.s - 3 ∧ NoXor C' ∧
          ∀ x ∈ RDom (insert v Z) (Function.update c v b), C'.eval x = C.eval x := by
        rcases lt_or_gt_of_ne hHK with hlt | hlt
        · exact elim_three C _ hN (by omega) hlt h0 hH hK
        · exact elim_three C _ hN (by omega) hlt h0 hK hH
      have := ih (C.s - 3) (by omega) C' (insert v Z) (Function.update c v b) hs' hN'
        (by omega) (fun x hx => (he' x hx).trans (hC x (hsub x hx)))
      omega
    have hfix : ∀ (v : Fin n) (b : Bool) (x : Fin n → Bool),
        x ∈ RDom (insert v Z) (Function.update c v b) → x v = b := fun v b x hx => by
      rw [hx v (Finset.mem_insert_self _ _), Function.update_self]
    by_cases hI : ∃ H, 1 ≤ H ∧ H < C.s ∧ (C.a H = i.val ∨ C.b H = i.val) ∧
        ∃ K' < C.s, (C.a K' = n ∨ C.b K' = n) ∧ H ≠ K'
    · obtain ⟨H, hH1, hHs, hHr, K', hK's, hK'r, hHK⟩ := hI
      have hK'1 : 1 ≤ K' := by
        by_contra h0
        have : K' = 0 := by omega
        subst this
        omega
      exact finish i α H K' hiZ hH1 hK'1 hHK
        (constIn_of_reads C _ hs0 (Or.inl rfl) α (fun x hx => by
          rw [C.val_input x ha0]; exact hfix i α x hx))
        (constIn_of_reads C _ hHs hHr α (fun x hx => by
          rw [C.val_input x i.2]; exact hfix i α x hx))
        (constIn_of_reads C _ hK's hK'r (C.op 0 α true) (fun x hx => by
          rw [hval0, hfix i α x hx, hα']))
    by_cases hJ : ∃ H, 1 ≤ H ∧ H < C.s ∧ (C.a H = j.val ∨ C.b H = j.val) ∧
        ∃ K' < C.s, (C.a K' = n ∨ C.b K' = n) ∧ H ≠ K'
    · obtain ⟨H, hH1, hHs, hHr, K', hK's, hK'r, hHK⟩ := hJ
      have hK'1 : 1 ≤ K' := by
        by_contra h0
        have : K' = 0 := by omega
        subst this
        omega
      exact finish j β H K' hjZ hH1 hK'1 hHK
        (constIn_of_reads C _ hs0 (Or.inr rfl) β (fun x hx => by
          rw [C.val_input x hb0]; exact hfix j β x hx))
        (constIn_of_reads C _ hHs hHr β (fun x hx => by
          rw [C.val_input x j.2]; exact hfix j β x hx))
        (constIn_of_reads C _ hK's hK'r (C.op 0 true β) (fun x hx => by
          rw [hval0, hfix j β x hx, hβ']))
    -- Both fail: the unique reader `K` of gate 0 reads `x_i`, `x_j` and gate 0.
    exfalso
    obtain ⟨H, hH1, hHs, hHr⟩ := hAi
    obtain ⟨H', hH'1, hH's, hH'r⟩ := hAj
    have e1 : H = K := by
      by_contra hne; exact hI ⟨H, hH1, hHs, hHr, K, hKs, hK, hne⟩
    have e2 : H' = K := by
      by_contra hne; exact hJ ⟨H', hH'1, hH's, hH'r, K, hKs, hK, hne⟩
    subst e1 e2
    have := i.2
    have := j.2
    rcases hHr with h1 | h1 <;> rcases hH'r with h2 | h2 <;> rcases hK with h3 | h3 <;> omega

end GateElim

open GateElim in
/-- **Schnorr (1974): PARITY over `U₂`.** Every circuit over the basis `U₂` (all binary
operations except `⊕` and `≡`) computing PARITY on `n ≥ 1` variables has at least
`3 (n - 1)` gates. -/
theorem parity_u2_lower_bound {n s : ℕ} (hn : 1 ≤ n) (C : Circuit n s)
    (hU : ∀ i, InU2 (C.1 i).1) (hC : C.eval = parityB) : 3 * (n - 1) ≤ s := by
  have hN : NoXor (GC.ofCircuit C) := by
    intro i hi
    show InU2 (opOf C.1 i)
    simp only [opOf, dif_pos (show i < s from hi)]
    exact hU _
  have := parity_u2_gc s (GC.ofCircuit C) ∅ (fun _ => false) rfl hN (by simpa using hn)
    (fun x _ => by rw [GC.ofCircuit_eval, hC])
  simp only [Finset.card_empty, Nat.sub_zero] at this
  have h' : (GC.ofCircuit C).s = s := rfl
  omega

/-! ## Non-vacuity: a `U₂` circuit with `3 (n - 1)` gates -/

namespace ParityCircuit

open Th2Circuit GateElim

variable {n : ℕ}

/-- Parity of the first `t + 1` inputs. -/
def P (x : Fin n → Bool) (t : ℕ) : Bool := decide (cnt x (t + 1) % 2 = 1)

theorem P_succ (x : Fin n → Bool) (t : ℕ) : P x (t + 1) = xor (P x t) (xk x (t + 1)) := by
  unfold P; rw [cnt_succ x (t + 1)]
  rcases Nat.mod_two_eq_zero_or_one (cnt x (t + 1)) with h | h <;>
    cases xk x (t + 1) <;> simp [h, Nat.add_mod]

/-- Intended value of gate `3 t + r`: `P t ∧ ¬x_{t+1}`, `¬P t ∧ x_{t+1}`, `P (t+1)`. -/
def gsem (x : Fin n → Bool) (i : ℕ) : Bool :=
  if i % 3 = 0 then (P x (i / 3) && !xk x (i / 3 + 1))
  else if i % 3 = 1 then (!P x (i / 3) && xk x (i / 3 + 1)) else P x (i / 3 + 1)

def wsem (x : Fin n → Bool) (j : ℕ) : Bool := if j < n then xk x j else gsem x (j - n)

/-- The wire carrying `P t`. -/
def pw (n t : ℕ) : ℕ := if t = 0 then 0 else n + 3 * t - 1

def op (i : ℕ) : Bool → Bool → Bool :=
  if i % 3 = 0 then (fun p q => p && !q) else if i % 3 = 1 then (fun p q => !p && q)
  else (· || ·)

def ia (n i : ℕ) : ℕ := if i % 3 = 2 then n + 3 * (i / 3) else pw n (i / 3)

def ib (n i : ℕ) : ℕ := if i % 3 = 2 then n + 3 * (i / 3) + 1 else i / 3 + 1

theorem op_u2 (i : ℕ) : InU2 (op i) := by
  unfold op; split_ifs <;> decide

theorem wsem_input (x : Fin n → Bool) {k : ℕ} (hk : k < n) : wsem x k = xk x k := by
  simp [wsem, hk]

theorem wsem_gate (x : Fin n → Bool) (i : ℕ) : wsem x (n + i) = gsem x i := by
  simp [wsem]

theorem wsem_pw (x : Fin n → Bool) (hn : 0 < n) (t : ℕ) : wsem x (pw n t) = P x t := by
  rcases t with _ | t
  · simp only [pw, if_true]
    rw [wsem_input x hn]
    simp only [P, cnt, zero_add, Finset.sum_range_one]
    cases xk x 0 <;> simp
  · simp only [pw, if_neg (Nat.succ_ne_zero t)]
    rw [show n + 3 * (t + 1) - 1 = n + (3 * t + 2) by omega, wsem_gate]
    unfold gsem
    rw [if_neg (by omega), if_neg (by omega), show (3 * t + 2) / 3 = t by omega]

theorem gate_eq (x : Fin n → Bool) (hn : 0 < n) {i : ℕ} (hi : i < 3 * (n - 1)) :
    wsem x (n + i) = op i (wsem x (ia n i)) (wsem x (ib n i)) := by
  obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 3 ∧ i = 3 * t + r :=
    ⟨i / 3, i % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  have ht : t + 1 < n := by omega
  have e1 : (3 * t + r) / 3 = t := by omega
  have e2 : (3 * t + r) % 3 = r := by omega
  rw [wsem_gate]
  unfold gsem op ia ib
  rw [e1, e2]
  interval_cases r
  · simp only [if_true, if_neg (show (0 : ℕ) ≠ 2 by norm_num), wsem_pw x hn,
      wsem_input x ht]
  · simp only [if_neg (show (1 : ℕ) ≠ 0 by norm_num), if_true,
      if_neg (show (1 : ℕ) ≠ 2 by norm_num), wsem_pw x hn, wsem_input x ht]
  · simp only [if_neg (show (2 : ℕ) ≠ 0 by norm_num), if_neg (show (2 : ℕ) ≠ 1 by norm_num),
      if_true]
    rw [wsem_gate, Nat.add_assoc, wsem_gate]
    unfold gsem
    rw [if_pos (by omega), if_neg (by omega), if_pos (by omega),
      show 3 * t / 3 = t by omega, show (3 * t + 1) / 3 = t by omega, P_succ]
    cases P x t <;> cases xk x (t + 1) <;> rfl

theorem P_eq_parity (x : Fin n → Bool) (hn : 0 < n) : P x (n - 1) = parityB x := by
  have hc : ones x = cnt x n := by
    unfold ones
    rw [Finset.card_filter, cnt,
      ← Fin.sum_univ_eq_sum_range (fun i => if xk x i then 1 else 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [xk, i.2]
  unfold P parityB
  rw [Nat.sub_add_cancel hn, hc]

theorem ha (n : ℕ) : ∀ i < 3 * (n - 1), ia n i < n + i := by
  intro i hi; unfold ia pw; split_ifs <;> omega

theorem hb (n : ℕ) : ∀ i < 3 * (n - 1), ib n i < n + i := by
  intro i hi; unfold ib; split_ifs <;> omega

/-- The circuit: a chain of `n - 1` XORs, each made of three `U₂` gates. -/
def gates (n : ℕ) : Gates n (3 * (n - 1)) := mkGates n (3 * (n - 1)) op (ia n) (ib n) (ha n) (hb n)

end ParityCircuit

open GateElim ParityCircuit in
/-- **Tightness.** PARITY on `n ≥ 1` variables has a `U₂` circuit with `3 (n - 1)` gates. -/
theorem parity_u2_hasCircuit {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : Circuit n (3 * (n - 1)), (∀ i, InU2 (C.1 i).1) ∧ C.eval = parityB := by
  have hout : pw n (n - 1) < n + 3 * (n - 1) := by unfold pw; split_ifs <;> omega
  refine ⟨(ParityCircuit.gates n, ⟨pw n (n - 1), hout⟩), fun i => op_u2 i.val, ?_⟩
  funext x
  have := wv_mkGates_unique (s := 3 * (n - 1)) x (op := op) (a := ia n) (b := ib n)
    (ha := ParityCircuit.ha n) (hb := ParityCircuit.hb n) (wsem x)
    (fun j hj => by rw [wsem_input x hj]; simp [Th2Circuit.xk, hj])
    (fun i hi => gate_eq x (by omega) hi) (pw n (n - 1)) hout
  simp only [Circuit.eval, wires_eq_wv]
  rw [← P_eq_parity x (by omega), ← wsem_pw x (by omega)]
  exact this.symm

open GateElim in
/-- **The `U₂`-complexity of PARITY is exactly `3 (n - 1)`.** -/
theorem parity_u2_complexity {n : ℕ} (hn : 1 ≤ n) :
    (∃ C : Circuit n (3 * (n - 1)), (∀ i, InU2 (C.1 i).1) ∧ C.eval = parityB) ∧
    ∀ (s : ℕ) (C : Circuit n s), (∀ i, InU2 (C.1 i).1) → C.eval = parityB → 3 * (n - 1) ≤ s :=
  ⟨parity_u2_hasCircuit hn, fun _ C hU hC => parity_u2_lower_bound hn C hU hC⟩

end Pnp.Circuits
