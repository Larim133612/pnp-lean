import Pnp.Circuits.Multi

/-!
# Gate elimination (M7)

Explicit linear lower bounds for general (`B₂`, fan-in 2) circuits.

* **Warm-up** (`le_size_of_depends`): a function that depends essentially on all `n`
  variables needs at least `n - 1` gates. The proof is a support-counting argument: the
  output of a circuit with `t` gates is determined by at most `t + 1` input variables
  (`support_bound`).
* **Schnorr (1974)** (`th2_lower_bound`): the threshold-2 function
  `th2 x = decide (2 ≤ #{i | x i})` needs at least `2 n - 3` gates for `n ≥ 2`.

The gate elimination argument is carried out in an auxiliary model `GC n` of generalized
circuits: `ℕ`-indexed straight-line programs whose output is an arbitrary unary function
`outf` of one wire. Restrictions are not implemented by deleting inputs; instead, a set `Z`
of *dead* variables is fixed to `false` and everything is evaluated on the subcube
`Dom Z`. The only syntactic operation is `GC.elim`, which deletes a gate that, on the
current subcube, is a unary function of an earlier wire, rewiring its readers (the unary
function is absorbed into the operations of the readers, and into `outf`).

* **Non-vacuity** (`th2_hasCircuitOfSize`): `th2` has a circuit with `3 n + 2` gates.
-/

namespace Pnp.Circuits

/-! ## Warm-up: `n - 1` for functions depending on all variables -/

/-- The wires in a set `W` of wires below `n + t` are determined by at most `t + |W|`
input variables. -/
theorem support_bound {n s : ℕ} (g : Gates n s) :
    ∀ t ≤ s, ∀ W : Finset ℕ, (∀ w ∈ W, w < n + t) →
      ∃ T : Finset (Fin n), T.card ≤ t + W.card ∧
        ∀ x y : Fin n → Bool, (∀ l ∈ T, x l = y l) → ∀ w ∈ W, wv x s g w = wv y s g w := by
  intro t
  induction t with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun l : Fin n => l.val ∈ W), ?_, ?_⟩
    · have := Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun l : Fin n => l.val ∈ W))
        (t := W) (fun l => l.val) (by intro l hl; simpa using hl)
        (by intro a _ b _ h; exact Fin.ext h)
      omega
    · intro x y hxy w hw
      have hwn : w < n := by simpa using hW w hw
      rw [wv_input x s g hwn, wv_input y s g hwn]
      exact hxy _ (by simpa using hw)
  | succ t ih =>
    intro hts W hW
    by_cases hmem : n + t ∈ W
    · have ht : t < s := by omega
      set W' : Finset ℕ := insert (inA g t) (insert (inB g t) (W.erase (n + t))) with hW'
      have hW'lt : ∀ w ∈ W', w < n + t := by
        intro w hw
        simp only [hW', Finset.mem_insert, Finset.mem_erase] at hw
        rcases hw with rfl | rfl | ⟨hne, hw⟩
        · exact inA_lt g ht
        · exact inB_lt g ht
        · have := hW w hw; omega
      obtain ⟨T, hT, hTW⟩ := ih (by omega) W' hW'lt
      have hcard : W'.card ≤ W.card + 1 := by
        have h1 : W'.card ≤ (insert (inB g t) (W.erase (n + t))).card + 1 :=
          Finset.card_insert_le _ _
        have h2 := Finset.card_insert_le (inB g t) (W.erase (n + t))
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.mpr ⟨_, hmem⟩
        omega
      refine ⟨T, by omega, fun x y hxy w hw => ?_⟩
      by_cases hwt : w = n + t
      · rw [hwt, wv_gate' x g ht, wv_gate' y g ht, hTW x y hxy (inA g t) (by simp [hW']),
          hTW x y hxy (inB g t) (by simp [hW'])]
      · exact hTW x y hxy w (by simp [hW', hwt, hw])
    · obtain ⟨T, hT, hTW⟩ := ih (by omega) W (fun w hw => by
        have := hW w hw
        have : w ≠ n + t := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hTW⟩

/-- **Warm-up lower bound.** If `f` depends essentially on each of its `n` variables, every
circuit computing `f` has at least `n - 1` gates. -/
theorem le_size_of_depends {n s : ℕ} (f : (Fin n → Bool) → Bool)
    (hf : ∀ i, ∃ x, f x ≠ f (Function.update x i (!x i))) (C : Circuit n s)
    (hC : C.eval = f) : n - 1 ≤ s := by
  obtain ⟨T, hT, hTW⟩ := support_bound C.1 s le_rfl {C.2.val} (by simp [C.2.2])
  have huniv : (Finset.univ : Finset (Fin n)) ⊆ T := by
    intro i _
    by_contra hi
    obtain ⟨x, hx⟩ := hf i
    apply hx
    rw [← hC]
    simp only [Circuit.eval, wires_eq_wv]
    refine hTW _ _ (fun l hl => ?_) _ (Finset.mem_singleton_self _)
    have : l ≠ i := fun h => hi (h ▸ hl)
    rw [Function.update_of_ne this]
  have := Finset.card_le_card huniv
  rw [Finset.card_univ, Fintype.card_fin] at this
  simp at hT
  omega

/-! ## Generalized circuits -/

namespace GateElim

/-- A generalized circuit on `n` inputs: `s` gates in `ℕ`-indexed form, and an output given
by an arbitrary unary function `outf` of the wire `out`. -/
structure GC (n : ℕ) where
  s : ℕ
  op : ℕ → Bool → Bool → Bool
  a : ℕ → ℕ
  b : ℕ → ℕ
  ha : ∀ i < s, a i < n + i
  hb : ∀ i < s, b i < n + i
  out : ℕ
  hout : out < n + s
  outf : Bool → Bool

namespace GC

variable {n : ℕ}

/-- The underlying gate list. -/
def gates (C : GC n) : Gates n C.s := mkGates n C.s C.op C.a C.b C.ha C.hb

/-- Wire values. -/
def val (C : GC n) (x : Fin n → Bool) (j : ℕ) : Bool := wv x C.s C.gates j

/-- The computed function. -/
def eval (C : GC n) (x : Fin n → Bool) : Bool := C.outf (C.val x C.out)

theorem val_input (C : GC n) (x : Fin n → Bool) {j : ℕ} (hj : j < n) :
    C.val x j = x ⟨j, hj⟩ := wv_input x _ _ hj

theorem val_gate (C : GC n) (x : Fin n → Bool) {i : ℕ} (hi : i < C.s) :
    C.val x (n + i) = C.op i (C.val x (C.a i)) (C.val x (C.b i)) :=
  wv_gate x C.s C.gates ⟨i, hi⟩

/-- Renaming of old wires after deleting gate `k` (replaced by wire `w`). -/
def ren (n k w j : ℕ) : ℕ := if j < n + k then j else if j = n + k then w else j - 1

/-- The unary function to apply to a renamed wire (`u` on the deleted gate, else `id`). -/
def tr (n k : ℕ) (u : Bool → Bool) (j : ℕ) : Bool → Bool := if j = n + k then u else id

/-- Delete gate `k`, assumed to compute `u` of the earlier wire `w`. -/
def elim (C : GC n) (k w : ℕ) (u : Bool → Bool) (hk : k < C.s) (hw : w < n + k) : GC n where
  s := C.s - 1
  op i := if i < k then C.op i else
    fun p q => C.op (i + 1) (tr n k u (C.a (i + 1)) p) (tr n k u (C.b (i + 1)) q)
  a i := if i < k then C.a i else ren n k w (C.a (i + 1))
  b i := if i < k then C.b i else ren n k w (C.b (i + 1))
  ha i hi := by
    split_ifs with h
    · exact C.ha i (by omega)
    · have := C.ha (i + 1) (by omega); unfold ren; split_ifs <;> omega
  hb i hi := by
    split_ifs with h
    · exact C.hb i (by omega)
    · have := C.hb (i + 1) (by omega); unfold ren; split_ifs <;> omega
  out := ren n k w C.out
  hout := by have := C.hout; unfold ren; split_ifs <;> omega
  outf := C.outf ∘ tr n k u C.out

theorem elim_eval (C : GC n) (k w : ℕ) (u : Bool → Bool) (hk : k < C.s) (hw : w < n + k)
    (x : Fin n → Bool) (h : C.val x (n + k) = u (C.val x w)) :
    (C.elim k w u hk hw).eval x = C.eval x := by
  let emb : ℕ → ℕ := fun j => if j < n + k then j else j + 1
  have key : ∀ j, tr n k u j (C.val x (emb (ren n k w j))) = C.val x j := by
    intro j
    simp only [emb, ren, tr]
    by_cases h1 : j < n + k
    · simp [h1, show j ≠ n + k by omega]
    · by_cases h2 : j = n + k
      · simp [h2, hw, h]
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg (by omega)]
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
        rw [key, key]
        simp only [emb, if_neg (show ¬ n + i < n + k by omega)]
        rw [show n + i + 1 = n + (i + 1) by omega]
        exact C.val_gate x (i := i + 1) (by omega)
  unfold GC.eval
  have hout := (C.elim k w u hk hw).hout
  rw [← hval _ hout]
  exact congrArg C.outf (key C.out)

/-- Gate `k` is, on the set of inputs `D`, a unary function of an earlier wire. -/
def Removable (C : GC n) (D : Set (Fin n → Bool)) (k : ℕ) : Prop :=
  ∃ w < n + k, ∃ u : Bool → Bool, ∀ x ∈ D, C.val x (n + k) = u (C.val x w)

theorem exists_elim (C : GC n) (D : Set (Fin n → Bool)) {k : ℕ} (hk : k < C.s)
    (he : C.Removable D k) :
    ∃ C' : GC n, C'.s = C.s - 1 ∧ ∀ x ∈ D, C'.eval x = C.eval x := by
  obtain ⟨w, hw, u, hu⟩ := he
  exact ⟨C.elim k w u hk hw, rfl, fun x hx => C.elim_eval k w u hk hw x (hu x hx)⟩

theorem removable_of_a (C : GC n) (D : Set (Fin n → Bool)) {k : ℕ} (hk : k < C.s) (c : Bool)
    (h : ∀ x ∈ D, C.val x (C.a k) = c) : C.Removable D k :=
  ⟨C.b k, C.hb k hk, C.op k c, fun x hx => by rw [C.val_gate x hk, h x hx]⟩

theorem removable_of_b (C : GC n) (D : Set (Fin n → Bool)) {k : ℕ} (hk : k < C.s) (c : Bool)
    (h : ∀ x ∈ D, C.val x (C.b k) = c) : C.Removable D k :=
  ⟨C.a k, C.ha k hk, fun p => C.op k p c, fun x hx => by rw [C.val_gate x hk, h x hx]⟩

theorem removable_of_eq (C : GC n) (D : Set (Fin n → Bool)) {k : ℕ} (hk : k < C.s)
    (h : C.a k = C.b k) : C.Removable D k :=
  ⟨C.a k, C.ha k hk, fun p => C.op k p p, fun x _ => by rw [C.val_gate x hk, h]⟩

/-- The generalized circuit of a circuit. -/
def ofCircuit {s : ℕ} (C : Circuit n s) : GC n where
  s := s
  op := opOf C.1
  a := inA C.1
  b := inB C.1
  ha _ hi := inA_lt C.1 hi
  hb _ hi := inB_lt C.1 hi
  out := C.2.val
  hout := C.2.2
  outf := id

theorem ofCircuit_eval {s : ℕ} (C : Circuit n s) : (ofCircuit C).eval = C.eval := by
  funext x
  have := wv_mkGates_unique (s := s) x (op := opOf C.1) (a := inA C.1) (b := inB C.1)
    (ha := fun _ hi => inA_lt C.1 hi) (hb := fun _ hi => inB_lt C.1 hi) (wv x s C.1)
    (fun j hj => wv_input x s C.1 hj) (fun i hi => wv_gate' x C.1 hi) C.2.val C.2.2
  simp only [GC.eval, Circuit.eval, wires_eq_wv]
  exact this.symm

end GC

/-! ## The threshold-2 function -/

end GateElim

/-- The threshold-2 function: at least two inputs are `true`. -/
def th2 {n : ℕ} (x : Fin n → Bool) : Bool :=
  decide (2 ≤ (Finset.univ.filter fun i => x i = true).card)

namespace GateElim

open GC

variable {n : ℕ}

/-- The subcube on which the variables of `Z` are fixed to `false`. -/
def Dom (Z : Finset (Fin n)) : Set (Fin n → Bool) := {x | ∀ z ∈ Z, x z = false}

/-- The indicator vector of a set of variables. -/
def ind (S : Finset (Fin n)) : Fin n → Bool := fun l => decide (l ∈ S)

theorem th2_ind (S : Finset (Fin n)) : th2 (ind S) = decide (2 ≤ S.card) := by
  unfold th2 ind
  congr 3
  ext l; simp

theorem ind_mem_dom {S Z : Finset (Fin n)} (h : ∀ l ∈ S, l ∉ Z) : ind S ∈ Dom Z := by
  show ∀ z ∈ Z, _
  intro z hz
  simp only [ind, decide_eq_false_iff_not]
  exact fun hzS => h z hzS hz

theorem card_free (Z : Finset (Fin n)) : (Finset.univ \ Z).card = n - Z.card := by
  rw [Finset.card_univ_sdiff, Fintype.card_fin]

/-- With at least two free variables, `th2` is not a unary function of one input. -/
theorem no_lit (C : GC n) (Z : Finset (Fin n)) (hm : 2 ≤ n - Z.card)
    (hC : ∀ x ∈ Dom Z, C.eval x = th2 x) (ho : C.out < n) : False := by
  obtain ⟨p, hp, q, hq, hpq⟩ : ∃ p ∈ Finset.univ \ Z, ∃ q ∈ Finset.univ \ Z, p ≠ q := by
    apply Finset.one_lt_card.mp
    rw [card_free]; omega
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hp hq
  have hev : ∀ x, C.eval x = C.outf (x ⟨C.out, ho⟩) := fun x => by
    unfold GC.eval; rw [C.val_input x ho]
  have h1 := hC (ind ∅) (ind_mem_dom (by simp))
  have h2 := hC (ind {p, q}) (ind_mem_dom (by simp [hp, hq]))
  rw [hev, th2_ind] at h1 h2
  simp only [ind, Finset.notMem_empty, decide_false, Finset.card_empty] at h1
  rw [Finset.card_pair hpq] at h2
  have hoS : (⟨C.out, ho⟩ : Fin n) ∈ ({p, q} : Finset (Fin n)) := by
    by_contra hno
    simp only [ind, hno, decide_false] at h2
    simp [h1] at h2
  have hoZ : (⟨C.out, ho⟩ : Fin n) ∉ Z := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hoS
    rcases hoS with h | h <;> rw [h] <;> assumption
  have h3 := hC (ind {⟨C.out, ho⟩}) (ind_mem_dom (by simpa using hoZ))
  rw [hev, th2_ind, Finset.card_singleton] at h3
  simp only [ind, hoS, decide_true] at h2
  simp [ind] at h3
  simp [h3] at h2

/-- The fan-out argument: if the first gate reads two free variables `i ≠ j` and no other
gate (and not the output) reads them, `th2` (with at least three free variables) cannot
be computed, since it has three distinct subfunctions for `(x_i, x_j) = 00, 01, 11`. -/
theorem three_sub (C : GC n) (Z : Finset (Fin n)) (hm : 3 ≤ n - Z.card)
    (hC : ∀ x ∈ Dom Z, C.eval x = th2 x) (hs : 0 < C.s) (i j : Fin n)
    (hi : C.a 0 = i.val) (hj : C.b 0 = j.val) (hij : i ≠ j) (hiZ : i ∉ Z) (hjZ : j ∉ Z)
    (hout : n ≤ C.out)
    (hrest : ∀ k, 1 ≤ k → k < C.s →
      C.a k ≠ i.val ∧ C.a k ≠ j.val ∧ C.b k ≠ i.val ∧ C.b k ≠ j.val) :
    False := by
  have hi2 := i.2
  have hj2 := j.2
  have hval0 : ∀ x, C.val x n = C.op 0 (x i) (x j) := by
    intro x
    have := C.val_gate x hs
    rw [Nat.add_zero] at this
    rw [this, hi, hj, C.val_input x i.2, C.val_input x j.2]
  have indep : ∀ x y : Fin n → Bool, (∀ l : Fin n, l ≠ i → l ≠ j → x l = y l) →
      C.val x n = C.val y n →
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
  have heval : ∀ x y : Fin n → Bool, (∀ l : Fin n, l ≠ i → l ≠ j → x l = y l) →
      C.op 0 (x i) (x j) = C.op 0 (y i) (y j) → C.eval x = C.eval y := by
    intro x y hxy hop
    unfold GC.eval
    rw [indep x y hxy (by rw [hval0, hval0, hop]) C.out C.hout (by omega) (by omega)]
  obtain ⟨r, hrZ, hri, hrj⟩ : ∃ r : Fin n, r ∉ Z ∧ r ≠ i ∧ r ≠ j := by
    by_contra hcon
    push Not at hcon
    have hsub : Finset.univ \ Z ⊆ {i, j} := by
      intro r hr
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hr
      by_cases h : r = i
      · simp [h]
      · simp [hcon r hr h]
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_le_two (a := i) (b := j)
    rw [card_free] at h1
    omega
  have key : C.op 0 false false = C.op 0 false true ∨ C.op 0 false true = C.op 0 true true ∨
      C.op 0 false false = C.op 0 true true := by
    cases C.op 0 false false <;> cases C.op 0 false true <;> cases C.op 0 true true <;> simp
  rcases key with h | h | h
  · have e := heval (ind {r}) (ind {j, r}) (by intro l hli hlj; simp [ind, hlj])
      (by simpa [ind, hij, hij.symm, hri, hri.symm, hrj, hrj.symm] using h)
    rw [hC _ (ind_mem_dom (by simpa using hrZ)), hC _ (ind_mem_dom (by simp [hjZ, hrZ])),
      th2_ind, th2_ind, Finset.card_singleton, Finset.card_pair hrj.symm] at e
    simp at e
  · have e := heval (ind {j}) (ind {i, j}) (by intro l hli hlj; simp [ind, hli, hlj])
      (by simpa [ind, hij, hij.symm] using h)
    rw [hC _ (ind_mem_dom (by simpa using hjZ)), hC _ (ind_mem_dom (by simp [hiZ, hjZ])),
      th2_ind, th2_ind, Finset.card_singleton, Finset.card_pair hij] at e
    simp at e
  · have e := heval (ind ∅) (ind {i, j}) (by intro l hli hlj; simp [ind, hli, hlj])
      (by simpa [ind, hij, hij.symm] using h)
    rw [hC _ (ind_mem_dom (by simp)), hC _ (ind_mem_dom (by simp [hiZ, hjZ])),
      th2_ind, th2_ind, Finset.card_empty, Finset.card_pair hij] at e
    simp at e

/-- **Schnorr's bound for generalized circuits on a subcube.** If `C` computes `th2` on the
subcube where the variables of `Z` are `false`, and `m = n - |Z| ≥ 2` variables are free,
then `C` has at least `2 m - 3` gates. -/
theorem th2_lower_bound_gc : ∀ (s : ℕ) (C : GC n) (Z : Finset (Fin n)), C.s = s →
    2 ≤ n - Z.card → (∀ x ∈ Dom Z, C.eval x = th2 x) → 2 * (n - Z.card) ≤ C.s + 3 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C Z hs hm hC
    by_cases hel : ∃ k < C.s, C.Removable (Dom Z) k
    · obtain ⟨k, hk, he⟩ := hel
      obtain ⟨C', hs', hC'⟩ := C.exists_elim (Dom Z) hk he
      have := ih (C.s - 1) (by omega) C' Z hs' hm (fun x hx => (hC' x hx).trans (hC x hx))
      omega
    push Not at hel
    have hs0 : 0 < C.s := by
      by_contra h0
      exact no_lit C Z hm hC (by have := C.hout; omega)
    by_cases hm2 : n - Z.card = 2
    · omega
    have hm3 : 3 ≤ n - Z.card := by omega
    have ha0 : C.a 0 < n := by simpa using C.ha 0 hs0
    have hb0 : C.b 0 < n := by simpa using C.hb 0 hs0
    have hab : C.a 0 ≠ C.b 0 := fun h => hel 0 hs0 (C.removable_of_eq _ hs0 h)
    let i : Fin n := ⟨C.a 0, ha0⟩
    let j : Fin n := ⟨C.b 0, hb0⟩
    have hiZ : i ∉ Z := fun hz => hel 0 hs0 (C.removable_of_a _ hs0 false
      (fun x hx => by rw [C.val_input x ha0]; exact hx i hz))
    have hjZ : j ∉ Z := fun hz => hel 0 hs0 (C.removable_of_b _ hs0 false
      (fun x hx => by rw [C.val_input x hb0]; exact hx j hz))
    have hout : n ≤ C.out := by
      by_contra h
      exact no_lit C Z hm hC (by omega)
    obtain ⟨k, hk1, hks, hread⟩ : ∃ k, 1 ≤ k ∧ k < C.s ∧
        (C.a k = C.a 0 ∨ C.a k = C.b 0 ∨ C.b k = C.a 0 ∨ C.b k = C.b 0) := by
      by_contra hne
      push Not at hne
      exact three_sub C Z hm3 hC hs0 i j rfl rfl (fun h => hab (congrArg Fin.val h)) hiZ hjZ
        hout (fun k hk1 hks => hne k hk1 hks)
    obtain ⟨v, hvZ, hv0, hvk⟩ : ∃ v : Fin n, v ∉ Z ∧ (C.a 0 = v.val ∨ C.b 0 = v.val) ∧
        (C.a k = v.val ∨ C.b k = v.val) := by
      rcases hread with h | h | h | h
      · exact ⟨i, hiZ, Or.inl rfl, Or.inl h⟩
      · exact ⟨j, hjZ, Or.inr rfl, Or.inl h⟩
      · exact ⟨i, hiZ, Or.inl rfl, Or.inr h⟩
      · exact ⟨j, hjZ, Or.inr rfl, Or.inr h⟩
    set Z' := insert v Z with hZ'
    have hcard : Z'.card = Z.card + 1 := Finset.card_insert_of_notMem hvZ
    have hsub : ∀ x ∈ Dom Z', x ∈ Dom Z := fun x hx z hz => hx z (Finset.mem_insert_of_mem hz)
    have hdead : ∀ x ∈ Dom Z', C.val x v.val = false := fun x hx => by
      rw [C.val_input x v.2]; exact hx v (Finset.mem_insert_self _ _)
    have hremk : C.Removable (Dom Z') k := by
      rcases hvk with h | h
      · exact C.removable_of_a _ hks false (fun x hx => by rw [h]; exact hdead x hx)
      · exact C.removable_of_b _ hks false (fun x hx => by rw [h]; exact hdead x hx)
    obtain ⟨w, hw, u, hu⟩ := hremk
    set C1 := C.elim k w u hks hw with hC1
    have hC1s : C1.s = C.s - 1 := rfl
    have hC1eval : ∀ x ∈ Dom Z', C1.eval x = th2 x := fun x hx =>
      (C.elim_eval k w u hks hw x (hu x hx)).trans (hC x (hsub x hx))
    have hC1s0 : 0 < C1.s := by omega
    have hC1a : C1.a 0 = C.a 0 := by
      show (if 0 < k then C.a 0 else _) = C.a 0; rw [if_pos (show 0 < k by omega)]
    have hC1b : C1.b 0 = C.b 0 := by
      show (if 0 < k then C.b 0 else _) = C.b 0; rw [if_pos (show 0 < k by omega)]
    have hdead1 : ∀ x ∈ Dom Z', C1.val x v.val = false := fun x hx => by
      rw [C1.val_input x v.2]; exact hx v (Finset.mem_insert_self _ _)
    have hrem0 : C1.Removable (Dom Z') 0 := by
      rcases hv0 with h | h
      · exact C1.removable_of_a _ hC1s0 false (fun x hx => by rw [hC1a, h]; exact hdead1 x hx)
      · exact C1.removable_of_b _ hC1s0 false (fun x hx => by rw [hC1b, h]; exact hdead1 x hx)
    obtain ⟨C2, hC2s, hC2⟩ := C1.exists_elim (Dom Z') hC1s0 hrem0
    have := ih (C.s - 2) (by omega) C2 Z' (by omega) (by omega)
      (fun x hx => (hC2 x hx).trans (hC1eval x hx))
    omega

end GateElim

open GateElim in
/-- **Schnorr (1974).** Every circuit (fan-in 2, full binary basis `B₂`) computing the
threshold-2 function on `n ≥ 2` variables has at least `2 n - 3` gates. -/
theorem th2_lower_bound {n s : ℕ} (hn : 2 ≤ n) (C : Circuit n s) (hC : C.eval = th2) :
    2 * n - 3 ≤ s := by
  have := th2_lower_bound_gc s (GC.ofCircuit C) ∅ rfl (by simpa using hn)
    (fun x _ => by rw [GC.ofCircuit_eval, hC])
  simp only [Finset.card_empty, Nat.sub_zero] at this
  exact Nat.sub_le_of_le_add (by simpa [GC.ofCircuit] using this)

/-- `HasCircuitOfSize` form of Schnorr's bound. -/
theorem not_hasCircuitOfSize_th2 {n s : ℕ} (hn : 2 ≤ n) (hs : s + 3 < 2 * n) :
    ¬ HasCircuitOfSize (th2 (n := n)) s := by
  rintro ⟨t, ht, C, hC⟩
  have := th2_lower_bound hn C hC
  omega

/-! ## Non-vacuity: a linear-size circuit for `th2` -/

namespace Th2Circuit

variable {n : ℕ}

/-- Input `k` (junk `false` beyond `n`). -/
def xk (x : Fin n → Bool) (k : ℕ) : Bool := if h : k < n then x ⟨k, h⟩ else false

/-- Number of `true` inputs among the first `k`. -/
def cnt (x : Fin n → Bool) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, if xk x i then 1 else 0

/-- Threshold 2 / OR of the first `k` inputs. -/
def T (x : Fin n → Bool) (k : ℕ) : Bool := decide (2 ≤ cnt x k)
def O (x : Fin n → Bool) (k : ℕ) : Bool := decide (1 ≤ cnt x k)

/-- Intended value of gate `i`: gates `0, 1` are the constants `T 0`, `O 0`; for step `k`,
gates `3k+2, 3k+3, 3k+4` compute `O k ∧ x_k`, `T (k+1) = T k ∨ (O k ∧ x_k)` and
`O (k+1) = O k ∨ x_k`. -/
def gsem (x : Fin n → Bool) (i : ℕ) : Bool :=
  if i < 2 then false else
    if (i - 2) % 3 = 0 then (O x ((i - 2) / 3) && xk x ((i - 2) / 3))
    else if (i - 2) % 3 = 1 then T x ((i - 2) / 3 + 1) else O x ((i - 2) / 3 + 1)

def wsem (x : Fin n → Bool) (j : ℕ) : Bool := if j < n then xk x j else gsem x (j - n)

def op (i : ℕ) : Bool → Bool → Bool :=
  if i < 2 then fun _ _ => false else if (i - 2) % 3 = 0 then (· && ·) else (· || ·)

def ia (n i : ℕ) : ℕ :=
  if i < 2 then 0 else if (i - 2) % 3 = 1 then n + 3 * ((i - 2) / 3) else n + 3 * ((i - 2) / 3) + 1

def ib (n i : ℕ) : ℕ :=
  if i < 2 then 0 else if (i - 2) % 3 = 1 then n + 3 * ((i - 2) / 3) + 2 else (i - 2) / 3

theorem cnt_succ (x : Fin n → Bool) (k : ℕ) :
    cnt x (k + 1) = cnt x k + if xk x k then 1 else 0 := Finset.sum_range_succ _ _

theorem T_succ (x : Fin n → Bool) (k : ℕ) : T x (k + 1) = (T x k || (O x k && xk x k)) := by
  unfold T O; rw [cnt_succ]
  cases xk x k <;> simp; omega

theorem O_succ (x : Fin n → Bool) (k : ℕ) : O x (k + 1) = (O x k || xk x k) := by
  unfold O; rw [cnt_succ]
  cases xk x k <;> simp

theorem wsem_gate (x : Fin n → Bool) (i : ℕ) : wsem x (n + i) = gsem x i := by
  simp [wsem]

theorem wsem_T (x : Fin n → Bool) (k : ℕ) : wsem x (n + 3 * k) = T x k := by
  rw [wsem_gate]
  rcases k with _ | k
  · simp [gsem, T, cnt]
  · unfold gsem
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show (3 * (k + 1) - 2) / 3 = k by omega]

theorem wsem_O (x : Fin n → Bool) (k : ℕ) : wsem x (n + 3 * k + 1) = O x k := by
  rw [Nat.add_assoc, wsem_gate]
  rcases k with _ | k
  · simp [gsem, O, cnt]
  · unfold gsem
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show (3 * (k + 1) + 1 - 2) / 3 = k by omega]

theorem wsem_G (x : Fin n → Bool) (k : ℕ) : wsem x (n + 3 * k + 2) = (O x k && xk x k) := by
  rw [Nat.add_assoc, wsem_gate]
  unfold gsem
  rw [if_neg (by omega), if_pos (by omega), show (3 * k + 2 - 2) / 3 = k by omega]

theorem wsem_input (x : Fin n → Bool) {k : ℕ} (hk : k < n) : wsem x k = xk x k := by
  simp [wsem, hk]

theorem gate_eq (x : Fin n → Bool) {i : ℕ} (hi : i < 3 * n + 2) :
    wsem x (n + i) = op i (wsem x (ia n i)) (wsem x (ib n i)) := by
  rw [wsem_gate]
  by_cases h2 : i < 2
  · simp [gsem, op, h2]
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 3 ∧ i = 3 * k + 2 + r :=
    ⟨(i - 2) / 3, (i - 2) % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  have hk : k < n := by omega
  have e1 : (3 * k + 2 + r - 2) / 3 = k := by omega
  have e2 : (3 * k + 2 + r - 2) % 3 = r := by omega
  unfold gsem op ia ib
  rw [if_neg h2, if_neg h2, if_neg h2, if_neg h2, e1, e2]
  interval_cases r
  · simp only [if_true, if_neg (show (0 : ℕ) ≠ 1 by norm_num), wsem_O, wsem_input x hk]
  · simp only [if_neg (show (1 : ℕ) ≠ 0 by norm_num), if_true, wsem_T, wsem_G, T_succ]
  · simp only [if_neg (show (2 : ℕ) ≠ 0 by norm_num), if_neg (show (2 : ℕ) ≠ 1 by norm_num),
      wsem_O, wsem_input x hk, O_succ]

theorem T_eq_th2 (x : Fin n → Bool) : T x n = th2 x := by
  unfold T th2
  congr 2
  rw [Finset.card_filter, cnt, ← Fin.sum_univ_eq_sum_range (fun i => if xk x i then 1 else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [xk, i.2]

/-- The circuit: `3 n + 2` gates. -/
def gates (n : ℕ) (hn : 1 ≤ n) : Gates n (3 * n + 2) :=
  mkGates n (3 * n + 2) op (ia n) (ib n)
    (fun i hi => by unfold ia; split_ifs <;> omega)
    (fun i hi => by unfold ib; split_ifs <;> omega)

end Th2Circuit

open Th2Circuit in
/-- **Non-vacuity.** `th2` on `n ≥ 1` variables has a circuit with `3 n + 2` gates. -/
theorem th2_hasCircuitOfSize {n : ℕ} (hn : 1 ≤ n) : HasCircuitOfSize (th2 (n := n)) (3 * n + 2) := by
  refine ⟨3 * n + 2, le_rfl, (Th2Circuit.gates n hn, ⟨n + 3 * n, by omega⟩), ?_⟩
  funext x
  have := wv_mkGates_unique (s := 3 * n + 2) x (op := op) (a := ia n) (b := ib n)
    (ha := fun i hi => by unfold ia; split_ifs <;> omega)
    (hb := fun i hi => by unfold ib; split_ifs <;> omega) (wsem x)
    (fun j hj => by rw [wsem_input x hj]; simp [xk, hj])
    (fun i hi => gate_eq x hi) (n + 3 * n) (by omega)
  simp only [Circuit.eval, wires_eq_wv]
  rw [← T_eq_th2, ← wsem_T]
  exact this.symm

end Pnp.Circuits
