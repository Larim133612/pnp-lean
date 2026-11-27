import Pnp.PPoly.Simulate

/-!
# Column-major local encoding of `FinTM2` configurations (M33)

For the uniform Cook–Levin tableau we encode a configuration of a Mathlib `FinTM2` with stacks
into a *slice* of bits (with `B` real columns, the slice has length `L1 + (B + 2 Dp)·w`):

* `c0` control bits (one-hot label and one-hot state, `encCtrl`);
* `Dp` *copy columns* holding the top `Dp` cells (`tcopy`);
* `B + 2 Dp` columns of width `w`; the real cell `j` (of all stacks at once) is column `Dp + j`,
  the others are padding (all `false`).

A column holds, for every stack `k`, the one-hot code of the cell content (an `Option` of the
finite reachable alphabet `A tm k`, see `Pnp/PPoly/TM2Local.lean`).

The new control bits depend only on the control bits and the copy columns (`gC`); the new bits
of real cell `j` depend only on those and on the *window* of columns `j, …, j + 2 Dp` (`gX`).
`gC_slice` and `gX_slice` state that these local functions compute the total step `step'` on the
slice encoding of a configuration.  Here `Dp = D tm + 1` where `D tm` bounds the number of stack
operations of one step.
-/

namespace Pnp.CookLevin.Tab

open Turing Turing.TM2 Function Pnp.PPoly

variable (tm : FinTM2)

attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin FinTM2.kFin

open Classical

/-- Column bit indices: a stack and a (coded) cell content. -/
abbrev CI : Type := Σ k : tm.K, Option (A tm k)

/-- Control bit indices. -/
abbrev CtI : Type := Option tm.Λ ⊕ tm.σ

/-- Column width. -/
noncomputable def w : ℕ := Fintype.card (CI tm)

/-- Number of control bits. -/
noncomputable def c0 : ℕ := Fintype.card (CtI tm)

/-- Enumeration of the column bits. -/
noncomputable def eC : CI tm ≃ Fin (w tm) := Fintype.equivFin _

/-- Enumeration of the control bits. -/
noncomputable def eT : CtI tm ≃ Fin (c0 tm) := Fintype.equivFin _

/-- Number of copy / padding columns. -/
def Dp : ℕ := D tm + 1

/-- Start of the columns in a slice. -/
noncomputable def L1 : ℕ := c0 tm + Dp tm * w tm

/-! ### Columns -/

/-- Bits of a column holding the cells `cell`. -/
noncomputable def encCol (cell : ∀ k, Option (tm.Γ k)) (i : ℕ) : Bool :=
  if h : i < w tm then
    decide (code tm (cell ((eC tm).symm ⟨i, h⟩).1) = ((eC tm).symm ⟨i, h⟩).2)
  else false

/-- Decoded cells of a column. -/
noncomputable def decCol (f : ℕ → Bool) (k : tm.K) : Option (tm.Γ k) :=
  (decOH (fun o => f (eC tm ⟨k, o⟩)) none).map Subtype.val

/-- Cells whose contents are reachable symbols. -/
def CellsA (cell : ∀ k, Option (tm.Γ k)) : Prop := ∀ k x, cell k = some x → x ∈ A tm k

theorem encCol_eC (cell : ∀ k, Option (tm.Γ k)) (k : tm.K) (o : Option (A tm k)) :
    encCol tm cell (eC tm ⟨k, o⟩) = decide (code tm (cell k) = o) := by
  unfold encCol
  rw [dif_pos (eC tm ⟨k, o⟩).isLt]
  simp only [Fin.eta]
  rw [Equiv.symm_apply_apply]

theorem decCol_encCol {cell : ∀ k, Option (tm.Γ k)} (h : CellsA tm cell) :
    decCol tm (encCol tm cell) = cell := by
  funext k
  unfold decCol
  rw [decOH_spec _ (b₀ := code tm (cell k)) fun o => by rw [encCol_eC]; simp [eq_comm]]
  exact map_code tm fun x hx => h k x hx

theorem decCol_zero (k : tm.K) : decCol tm (fun _ => false) k = none := by
  unfold decCol decOH
  simp

theorem decCol_congr {f g : ℕ → Bool} (h : ∀ i < w tm, f i = g i) : decCol tm f = decCol tm g := by
  funext k
  unfold decCol
  congr 2
  funext o
  exact h _ (eC tm ⟨k, o⟩).isLt

/-- The column is all `false` (padding). -/
noncomputable def padB (f : ℕ → Bool) : Bool := (List.range (w tm)).all fun i => !f i

theorem padB_iff (f : ℕ → Bool) : padB tm f = true ↔ ∀ i < w tm, f i = false := by
  simp [padB]

theorem padB_zero : padB tm (fun _ => false) = true := by simp [padB]

theorem padB_encCol (cell : ∀ k, Option (tm.Γ k)) : padB tm (encCol tm cell) = false := by
  rcases h : padB tm (encCol tm cell) with _ | _
  · rfl
  · rw [padB_iff] at h
    have := h _ (eC tm ⟨tm.k₀, code tm (cell tm.k₀)⟩).isLt
    rw [encCol_eC] at this
    simp at this

/-! ### Control bits -/

/-- Control bits of a label and a state. -/
noncomputable def encCtrl (l : Option tm.Λ) (v : tm.σ) (i : ℕ) : Bool :=
  if h : i < c0 tm then
    match (eT tm).symm ⟨i, h⟩ with
    | .inl o => decide (l = o)
    | .inr s => decide (v = s)
  else false

theorem encCtrl_eT (l : Option tm.Λ) (v : tm.σ) (e : CtI tm) :
    encCtrl tm l v (eT tm e) = match e with
      | .inl o => decide (l = o)
      | .inr s => decide (v = s) := by
  unfold encCtrl
  rw [dif_pos (eT tm e).isLt]
  simp

/-- Decoded label. -/
noncomputable def decLab (f : ℕ → Bool) : Option tm.Λ := decOH (fun o => f (eT tm (.inl o))) none

/-- Decoded state. -/
noncomputable def decSt (f : ℕ → Bool) : tm.σ := decOH (fun s => f (eT tm (.inr s))) tm.initialState

theorem decLab_encCtrl (l : Option tm.Λ) (v : tm.σ) : decLab tm (encCtrl tm l v) = l :=
  decOH_spec _ fun o => by rw [encCtrl_eT]; simp [eq_comm]

theorem decSt_encCtrl (l : Option tm.Λ) (v : tm.σ) : decSt tm (encCtrl tm l v) = v :=
  decOH_spec _ fun s => by rw [encCtrl_eT]; simp [eq_comm]

theorem decLab_congr {f g : ℕ → Bool} (h : ∀ i < c0 tm, f i = g i) : decLab tm f = decLab tm g := by
  unfold decLab; congr 1; funext o; exact h _ (eT tm _).isLt

theorem decSt_congr {f g : ℕ → Bool} (h : ∀ i < c0 tm, f i = g i) : decSt tm f = decSt tm g := by
  unfold decSt; congr 1; funext o; exact h _ (eT tm _).isLt

/-! ### Slices -/

/-- Cells of column `q` of the slice of `c` (`B` real columns). -/
def cellsAt (c : tm.Cfg) (q : ℕ) (k : tm.K) : Option (tm.Γ k) :=
  ((c : Cfg tm.Γ tm.Λ tm.σ).stk k)[q]?

/-- Bits of column `q` of a slice (left padding: all `false`; right of the stack contents the
cells are `none`). -/
noncomputable def colOf (c : tm.Cfg) (q : ℕ) : ℕ → Bool :=
  if Dp tm ≤ q then encCol tm (cellsAt tm c (q - Dp tm)) else fun _ => false

/-- **The slice of a configuration.** -/
noncomputable def sliceOf (c : tm.Cfg) (i : ℕ) : Bool :=
  if i < c0 tm then encCtrl tm (c : Cfg tm.Γ tm.Λ tm.σ).l (c : Cfg tm.Γ tm.Λ tm.σ).var i
  else if i < L1 tm then colOf tm c (Dp tm + (i - c0 tm) / w tm) ((i - c0 tm) % w tm)
  else colOf tm c ((i - L1 tm) / w tm) ((i - L1 tm) % w tm)

/-- A configuration whose stacks only contain reachable symbols. -/
abbrev Valid (c : tm.Cfg) : Prop := StkInA tm (c : Cfg tm.Γ tm.Λ tm.σ).stk

theorem cellsA (c : tm.Cfg) (hc : StkInA tm (c : Cfg tm.Γ tm.Λ tm.σ).stk) (q : ℕ) :
    CellsA tm (cellsAt tm c q) := fun k x hx =>
  hc k x (List.mem_of_getElem? hx)

theorem w_pos : 0 < w tm := Fintype.card_pos_iff.2 ⟨⟨tm.k₀, none⟩⟩

/-- Decoding column `q ≥ Dp` of a valid slice gives the cells `q - Dp`. -/
theorem decCol_colOf {c : tm.Cfg} (hc : Valid tm c) {q : ℕ} (hq : Dp tm ≤ q) :
    decCol tm (colOf tm c q) = cellsAt tm c (q - Dp tm) := by
  unfold colOf
  rw [if_pos hq]
  exact decCol_encCol tm (cellsA tm c hc _)

theorem padB_colOf {c : tm.Cfg} (q : ℕ) :
    padB tm (colOf tm c q) = !(decide (Dp tm ≤ q)) := by
  unfold colOf
  split_ifs with h
  · rw [padB_encCol]; simp [h]
  · rw [padB_zero]; simp [h]

theorem sliceOf_ctrl (c : tm.Cfg) {i : ℕ} (hi : i < c0 tm) :
    sliceOf tm c i = encCtrl tm (c : Cfg tm.Γ tm.Λ tm.σ).l (c : Cfg tm.Γ tm.Λ tm.σ).var i := by
  unfold sliceOf; rw [if_pos hi]

theorem sliceOf_copy (c : tm.Cfg) {q b : ℕ} (hq : q < Dp tm) (hb : b < w tm) :
    sliceOf tm c (c0 tm + q * w tm + b) = colOf tm c (Dp tm + q) b := by
  unfold sliceOf
  have h1 : (q * w tm + b) / w tm = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (w_pos tm), Nat.div_eq_of_lt hb, zero_add]
  have h2 : (q * w tm + b) % w tm = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have h3 : q * w tm + b < Dp tm * w tm := by
    have := Nat.mul_le_mul_right (w tm) (Nat.succ_le_of_lt hq)
    rw [Nat.succ_mul] at this; omega
  rw [if_neg (by omega), if_pos (by unfold L1; omega),
    show c0 tm + q * w tm + b - c0 tm = q * w tm + b by omega, h1, h2]

theorem sliceOf_col (c : tm.Cfg) (q : ℕ) {b : ℕ} (hb : b < w tm) :
    sliceOf tm c (L1 tm + q * w tm + b) = colOf tm c q b := by
  unfold sliceOf
  have h1 : (q * w tm + b) / w tm = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (w_pos tm), Nat.div_eq_of_lt hb, zero_add]
  have h2 : (q * w tm + b) % w tm = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have hL : c0 tm ≤ L1 tm := by unfold L1; omega
  rw [if_neg (by omega), if_neg (by omega),
    show L1 tm + q * w tm + b - L1 tm = q * w tm + b by omega, h1, h2]

/-! ### Local functions -/

/-- Bit access to a list. -/
abbrev gb (α : List Bool) (i : ℕ) : Bool := α.getD i false

/-- The tops (first `Dp` cells) of every stack, decoded from the copy columns. -/
noncomputable def topsOf (α₁ : List Bool) (k : tm.K) : List (tm.Γ k) :=
  prefixList (fun q => decCol tm (fun b => gb α₁ (c0 tm + q * w tm + b)) k) (Dp tm)

/-- Column `i` of a window. -/
noncomputable abbrev wcol (α₂ : List Bool) (i : ℕ) : ℕ → Bool := fun b => gb α₂ (i * w tm + b)

/-- Number of leading padding columns of a window. -/
noncomputable def lpad (α₂ : List Bool) : ℕ :=
  ((List.range (2 * Dp tm + 1)).takeWhile fun i => padB tm (wcol tm α₂ i)).length

/-- **New control bit** `e`, from the control bits and the copy columns. -/
noncomputable def gC (e : CtI tm) (α₁ : List Bool) : Bool :=
  match decLab tm (gb α₁) with
  | none => gb α₁ (eT tm e)
  | some l₀ =>
    let r := nf (tm.m l₀) (decSt tm (gb α₁)) (topsOf tm α₁)
    match e with
    | .inl o => decide (r.l = o)
    | .inr s => decide (r.var = s)

/-- The new content of the window center for stack `k`, when the label is `some l₀`. -/
noncomputable def newCell (l₀ : tm.Λ) (α₁ α₂ : List Bool) (k : tm.K) : Option (tm.Γ k) :=
  let r := nf (tm.m l₀) (decSt tm (gb α₁)) (topsOf tm α₁)
  if 0 < lpad tm α₂ ∧ Dp tm - lpad tm α₂ < (r.W k).length then (r.W k)[Dp tm - lpad tm α₂]?
  else decCol tm (wcol tm α₂ (Dp tm - (r.W k).length + r.P k)) k

/-- **New bit** `(k, o)` of the window center. -/
noncomputable def gX (k : tm.K) (o : Option (A tm k)) (α₁ α₂ : List Bool) : Bool :=
  match decLab tm (gb α₁) with
  | none => gb α₂ (Dp tm * w tm + eC tm ⟨k, o⟩)
  | some l₀ => decide (code tm (newCell tm l₀ α₁ α₂ k) = o)

/-! ### Correctness of the local functions -/

/-- The control-and-copy block of a slice. -/
noncomputable def blk₁ (c : tm.Cfg) : List Bool :=
  (List.range (L1 tm)).map (sliceOf tm c)

/-- The window of real column `j` of a slice. -/
noncomputable def win (c : tm.Cfg) (j : ℕ) : List Bool :=
  (List.range ((2 * Dp tm + 1) * w tm)).map fun i => sliceOf tm c (L1 tm + j * w tm + i)

theorem gb_blk₁ (c : tm.Cfg) {i : ℕ} (hi : i < L1 tm) :
    gb (blk₁ tm c) i = sliceOf tm c i := by
  simp [blk₁, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

theorem gb_blk₁_ctrl (c : tm.Cfg) :
    ∀ i < c0 tm, gb (blk₁ tm c) i =
      encCtrl tm (c : Cfg tm.Γ tm.Λ tm.σ).l (c : Cfg tm.Γ tm.Λ tm.σ).var i := fun i hi => by
  rw [gb_blk₁ tm c (by unfold L1; omega), sliceOf_ctrl tm c hi]

theorem decLab_blk₁ (c : tm.Cfg) :
    decLab tm (gb (blk₁ tm c)) = (c : Cfg tm.Γ tm.Λ tm.σ).l := by
  rw [decLab_congr tm (gb_blk₁_ctrl tm c), decLab_encCtrl]

theorem decSt_blk₁ (c : tm.Cfg) :
    decSt tm (gb (blk₁ tm c)) = (c : Cfg tm.Γ tm.Λ tm.σ).var := by
  rw [decSt_congr tm (gb_blk₁_ctrl tm c), decSt_encCtrl]

theorem topsOf_blk₁ {c : tm.Cfg} (hc : Valid tm c) (k : tm.K) :
    topsOf tm (blk₁ tm c) k = ((c : Cfg tm.Γ tm.Λ tm.σ).stk k).take (Dp tm) := by
  unfold topsOf
  rw [← prefixList_getElem?]
  refine prefixList_congr _ fun q hq => ?_
  have : decCol tm (fun b => gb (blk₁ tm c) (c0 tm + q * w tm + b)) =
      decCol tm (colOf tm c (Dp tm + q)) := by
    refine decCol_congr tm fun b hb => ?_
    have h3 : c0 tm + q * w tm + b < L1 tm := by
      have := Nat.mul_le_mul_right (w tm) (Nat.succ_le_of_lt hq)
      rw [Nat.succ_mul] at this; unfold L1; omega
    rw [gb_blk₁ tm c h3, sliceOf_copy tm c hq hb]
  rw [this, decCol_colOf tm hc (by omega)]
  simp [cellsAt]

theorem gb_win (c : tm.Cfg) (j : ℕ) {i b : ℕ} (hi : i ≤ 2 * Dp tm) (hb : b < w tm) :
    wcol tm (win tm c j) i b = colOf tm c (j + i) b := by
  have hlt : i * w tm + b < (2 * Dp tm + 1) * w tm := by
    have := Nat.mul_le_mul_right (w tm) (show i + 1 ≤ 2 * Dp tm + 1 by omega)
    rw [Nat.add_mul, one_mul] at this; omega
  simp only [wcol, win, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
    Option.map_some, Option.getD_some]
  rw [show L1 tm + j * w tm + (i * w tm + b) = L1 tm + (j + i) * w tm + b by ring,
    sliceOf_col tm c _ hb]

theorem takeWhile_range_length (p : ℕ → Bool) {m n : ℕ} (hm : m ≤ n)
    (h1 : ∀ i < m, p i = true) (h2 : m < n → p m = false) :
    ((List.range n).takeWhile p).length = m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [List.range_add, List.takeWhile_append_of_pos (fun a ha => h1 a (List.mem_range.1 ha))]
  cases d with
  | zero => simp
  | succ d =>
    rw [List.range_succ_eq_map, List.map_cons, List.takeWhile_cons_of_neg (by simpa using h2 (by omega))]
    simp

theorem padB_win (c : tm.Cfg) (j : ℕ) {i : ℕ} (hi : i ≤ 2 * Dp tm) :
    padB tm (wcol tm (win tm c j) i) = padB tm (colOf tm c (j + i)) := by
  rw [Bool.eq_iff_iff, padB_iff, padB_iff]
  exact forall₂_congr fun b hb => by rw [gb_win tm c j hi hb]

theorem lpad_win (c : tm.Cfg) (j : ℕ) :
    lpad tm (win tm c j) = Dp tm - j := by
  unfold lpad
  refine takeWhile_range_length _ (by omega) (fun i hi => ?_) (fun hlt => ?_)
  · rw [padB_win tm c j (by omega), padB_colOf]; simp; omega
  · rw [padB_win tm c j (by omega), padB_colOf]; simp; omega

theorem depth_lt_Dp (l : tm.Λ) : depth (tm.m l) < Dp tm := by
  have := depth_le_D tm l; unfold Dp; omega

theorem topsOf_blk₁' {c : tm.Cfg} (hc : Valid tm c) :
    topsOf tm (blk₁ tm c) = fun k => ((c : Cfg tm.Γ tm.Λ tm.σ).stk k).take (Dp tm) :=
  funext (topsOf_blk₁ tm hc)

/-- **The local control function is correct.** -/
theorem gC_slice {c : tm.Cfg} (hc : Valid tm c) (e : CtI tm) :
    gC tm e (blk₁ tm c) = sliceOf tm (step' tm c) (eT tm e) := by
  have he : (eT tm e : ℕ) < c0 tm := (eT tm e).isLt
  unfold gC
  rw [decLab_blk₁]
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none =>
    rw [step'_of_halted tm (c := ⟨none, v, S⟩) rfl]
    exact gb_blk₁ tm _ (by unfold L1; omega)
  | some l₀ =>
    simp only
    rw [decSt_blk₁, topsOf_blk₁' tm hc, sliceOf_ctrl tm _ he, step'_eq_stepAux,
      stepAux_eq_nf (depth_lt_Dp tm l₀).le, encCtrl_eT]
    rfl

/-- **The local cell function is correct.** -/
theorem gX_slice {c : tm.Cfg} (hc : Valid tm c) (j : ℕ) (k : tm.K)
    (o : Option (A tm k)) :
    gX tm k o (blk₁ tm c) (win tm c j) =
      sliceOf tm (step' tm c) (L1 tm + (Dp tm + j) * w tm + eC tm ⟨k, o⟩) := by
  have hb : (eC tm ⟨k, o⟩ : ℕ) < w tm := (eC tm ⟨k, o⟩).isLt
  rw [sliceOf_col tm _ _ hb]
  have hcol : ∀ c' : tm.Cfg, colOf tm c' (Dp tm + j) (eC tm ⟨k, o⟩) =
      decide (code tm (cellsAt tm c' j k) = o) := by
    intro c'
    unfold colOf
    rw [if_pos (by omega), Nat.add_sub_cancel_left, encCol_eC]
  rw [hcol]
  unfold gX
  rw [decLab_blk₁]
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none =>
    rw [step'_of_halted tm (c := ⟨none, v, S⟩) rfl]
    simp only
    have := gb_win tm ⟨none, v, S⟩ j (i := Dp tm) (by omega) hb
    simp only [wcol] at this
    rw [this, show j + Dp tm = Dp tm + j by omega, hcol]
  | some l₀ =>
    simp only
    congr 2
    unfold newCell
    rw [decSt_blk₁, topsOf_blk₁' tm hc, lpad_win tm _ j]
    simp only
    rw [cellsAt, step'_eq_stepAux, stk_getElem?_stepAux (depth_lt_Dp tm l₀).le]
    set r := nf (tm.m l₀) v (fun k => (S k).take (Dp tm)) with hr
    have hW : (r.W k).length < Dp tm :=
      lt_of_le_of_lt (nf_W_length _ _ _ k) (depth_lt_Dp tm l₀)
    have hP : r.P k < Dp tm := lt_of_le_of_lt (nf_P_le _ _ _ k) (depth_lt_Dp tm l₀)
    by_cases hjW : j < (r.W k).length
    · rw [if_pos ⟨by omega, by omega⟩, if_pos hjW, show Dp tm - (Dp tm - j) = j by omega]
    · rw [if_neg (by omega), if_neg hjW]
      have e1 : decCol tm (wcol tm (win tm ⟨some l₀, v, S⟩ j) (Dp tm - (r.W k).length + r.P k)) =
          decCol tm (colOf tm ⟨some l₀, v, S⟩ (j + (Dp tm - (r.W k).length + r.P k))) :=
        decCol_congr tm fun b hb' => gb_win tm _ j (by omega) hb'
      rw [e1, decCol_colOf tm hc (by omega), cellsAt]
      congr 2
      omega

end Pnp.CookLevin.Tab
