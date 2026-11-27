import Pnp.PPoly.TM2Local
import Pnp.PPoly.Encode

/-!
# Simulating a `FinTM2` run by a circuit

Configurations whose stacks have length `≤ B` are encoded one-hot into the bits `Bits tm B`
(`enc`). The bit-level step `stepBits` is a local map (every output bit depends on the bits
indexed by the fixed finite type `DepG tm`, `stepBits_congr`) and simulates the total step
`step'` on encodings of valid configurations (`stepBits_enc`).
-/

namespace Pnp.PPoly

open Turing Turing.TM2 Function Pnp.Circuits

section Sim

variable (tm : FinTM2)

attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin FinTM2.kFin

/-- Bit positions of the encoding of a configuration with stacks of length `≤ B`. -/
abbrev Bits (B : ℕ) : Type := Option tm.Λ ⊕ tm.σ ⊕ (Σ k : tm.K, Fin B × Option (A tm k))

open Classical in
/-- Code a cell content into the reachable alphabet (`none` if absent or unreachable). -/
noncomputable def code {k : tm.K} (o : Option (tm.Γ k)) : Option (A tm k) :=
  o.bind fun x => if h : x ∈ A tm k then some ⟨x, h⟩ else none

theorem map_code {k : tm.K} {o : Option (tm.Γ k)} (h : ∀ x ∈ o, x ∈ A tm k) :
    (code tm o).map Subtype.val = o := by
  cases o with
  | none => rfl
  | some x => simp [code, dif_pos (h x rfl)]

open Classical in
/-- Encoding from a label, a state and cell contents. -/
noncomputable def encC {B : ℕ} (l : Option tm.Λ) (v : tm.σ)
    (cell : ∀ k, ℕ → Option (tm.Γ k)) : Bits tm B → Bool
  | .inl o => decide (l = o)
  | .inr (.inl s) => decide (v = s)
  | .inr (.inr ⟨k, i, o⟩) => decide (code tm (cell k i.val) = o)

/-- One-hot encoding of a configuration. -/
noncomputable def enc (B : ℕ) (c : Cfg tm.Γ tm.Λ tm.σ) : Bits tm B → Bool :=
  encC tm c.l c.var fun k i => (c.stk k)[i]?

/-- Decoded label. -/
noncomputable def decL {B : ℕ} (x : Bits tm B → Bool) : Option tm.Λ :=
  decOH (fun o => x (.inl o)) none

/-- Decoded state. -/
noncomputable def decV {B : ℕ} (x : Bits tm B → Bool) : tm.σ :=
  decOH (fun s => x (.inr (.inl s))) tm.initialState

/-- The bit `(k, j, o)` (junk if `j ≥ B`). -/
def cellBit {B : ℕ} (k : tm.K) (j : ℕ) (o : Option (A tm k)) : Bits tm B :=
  if h : j < B then .inr (.inr ⟨k, ⟨j, h⟩, o⟩) else .inl none

/-- Decoded cell `j` of stack `k` (`none` beyond `B`). -/
noncomputable def decCell {B : ℕ} (x : Bits tm B → Bool) (k : tm.K) (j : ℕ) :
    Option (tm.Γ k) :=
  if h : j < B then (decOH (fun o => x (.inr (.inr ⟨k, ⟨j, h⟩, o⟩))) none).map Subtype.val
  else none

theorem decL_enc {B : ℕ} (c : Cfg tm.Γ tm.Λ tm.σ) : decL tm (enc tm B c) = c.l :=
  decOH_spec _ fun o => by simp [enc, encC, eq_comm]

theorem decV_enc {B : ℕ} (c : Cfg tm.Γ tm.Λ tm.σ) : decV tm (enc tm B c) = c.var :=
  decOH_spec _ fun o => by simp [enc, encC, eq_comm]

theorem decCell_enc {B : ℕ} (c : Cfg tm.Γ tm.Λ tm.σ) (k : tm.K)
    (hA : ∀ x ∈ c.stk k, x ∈ A tm k) (hlen : (c.stk k).length ≤ B) (j : ℕ) :
    decCell tm (enc tm B c) k j = (c.stk k)[j]? := by
  unfold decCell
  split_ifs with h
  · rw [decOH_spec _ (b₀ := code tm ((c.stk k)[j]?)) fun o => by simp [enc, encC, eq_comm]]
    exact map_code tm fun x hx => hA x (List.mem_of_getElem? hx)
  · rw [List.getElem?_eq_none (by omega)]

theorem decCell_congr {B : ℕ} {x y : Bits tm B → Bool} {k : tm.K} {j : ℕ}
    (h : ∀ o, x (cellBit tm k j o) = y (cellBit tm k j o)) :
    decCell tm x k j = decCell tm y k j := by
  unfold decCell
  split_ifs with hj
  · congr 2
    funext o
    simpa [cellBit, hj] using h o
  · rfl

/-! ### Reading a stack prefix from cells -/

/-- The list `[f 0, f 1, …]` up to the first `none`, of length `≤ N`. -/
def prefixList {β : Type*} (f : ℕ → Option β) : ℕ → List β
  | 0 => []
  | N + 1 =>
    match f 0 with
    | none => []
    | some a => a :: prefixList (fun i => f (i + 1)) N

theorem prefixList_getElem? {β : Type*} (N : ℕ) : ∀ l : List β,
    prefixList (fun i => l[i]?) N = l.take N := by
  induction N with
  | zero => intro l; rfl
  | succ N ih =>
    intro l
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [prefixList, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take_succ_cons]
      rw [ih l]

theorem prefixList_congr {β : Type*} (N : ℕ) : ∀ {f g : ℕ → Option β},
    (∀ i < N, f i = g i) → prefixList f N = prefixList g N := by
  induction N with
  | zero => intro f g _; rfl
  | succ N ih =>
    intro f g h
    simp only [prefixList]
    rw [h 0 (by omega)]
    cases g 0 with
    | none => rfl
    | some a => rw [ih fun i hi => h (i + 1) (by omega)]

/-! ### The bit-level step -/

/-- New cell contents from normal-form data and old cells. -/
def newCells (r : NF tm.Γ tm.Λ tm.σ) (cells : ∀ k, ℕ → Option (tm.Γ k)) :
    ∀ k, ℕ → Option (tm.Γ k) :=
  fun k i => if i < (r.W k).length then (r.W k)[i]? else cells k (i - (r.W k).length + r.P k)

/-- The step on bits, from decoded data. -/
noncomputable def Gfun {B : ℕ} (lo : Option tm.Λ) (v : tm.σ) (S' : ∀ k, List (tm.Γ k))
    (cells : ∀ k, ℕ → Option (tm.Γ k)) (x : Bits tm B → Bool) : Bits tm B → Bool :=
  match lo with
  | none => x
  | some l₀ =>
    let r := nf (tm.m l₀) v S'
    encC tm r.l r.var (newCells tm r cells)

/-- **The bit-level step.** -/
noncomputable def stepBits {B : ℕ} (x : Bits tm B → Bool) : Bits tm B → Bool :=
  Gfun tm (decL tm x) (decV tm x) (fun k => prefixList (decCell tm x k) (D tm)) (decCell tm x) x

theorem stepBits_enc {B : ℕ} (c : Cfg tm.Γ tm.Λ tm.σ) (hA : StkInA tm c.stk)
    (hlen : ∀ k, (c.stk k).length ≤ B) :
    stepBits tm (enc tm B c) = enc tm B (step' tm c) := by
  have hcell : decCell tm (enc tm B c) = fun k j => (c.stk k)[j]? :=
    funext fun k => funext fun j => decCell_enc tm c k (hA k) (hlen k) j
  have hpre : (fun k => prefixList (decCell tm (enc tm B c) k) (D tm)) =
      fun k => (c.stk k).take (D tm) := by
    rw [hcell]; funext k; exact prefixList_getElem? _ _
  unfold stepBits
  rw [decL_enc, decV_enc, hpre, hcell]
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => exact (congrArg (enc tm B) (step'_of_halted tm (c := ⟨none, v, S⟩) rfl)).symm
  | some l₀ =>
    simp only [Gfun]
    rw [step'_eq_stepAux]
    have h1 := stepAux_eq_nf (depth_le_D tm l₀) v S
    unfold enc
    congr 1
    · rw [h1]; rfl
    · rw [h1]; rfl
    · funext k i
      exact (stk_getElem?_stepAux (depth_le_D tm l₀) v S k i).symm

/-- The dependence index type of `stepBits`: label and state bits, the top `D` cells of every
stack, a window of `2D+1` cells of every stack, and the bit itself. -/
abbrev DepG : Type :=
  Option tm.Λ ⊕ tm.σ ⊕ (Σ k : tm.K, Fin (D tm) × Option (A tm k)) ⊕
    (Σ k : tm.K, Fin (2 * D tm + 1) × Option (A tm k)) ⊕ Unit

/-- Cell index of a bit (`0` for label and state bits). -/
def cellIdx {B : ℕ} : Bits tm B → ℕ
  | .inr (.inr ⟨_, i, _⟩) => i.val
  | _ => 0

/-- The bits on which output bit `b` of `stepBits` depends. -/
def depG {B : ℕ} (b : Bits tm B) : DepG tm → Bits tm B
  | .inl o => .inl o
  | .inr (.inl s) => .inr (.inl s)
  | .inr (.inr (.inl ⟨k, j, o⟩)) => cellBit tm k j.val o
  | .inr (.inr (.inr (.inl ⟨k, t, o⟩))) => cellBit tm k (cellIdx tm b + t.val - D tm) o
  | .inr (.inr (.inr (.inr _))) => b

theorem stepBits_congr {B : ℕ} (b : Bits tm B) (x y : Bits tm B → Bool)
    (h : ∀ d, x (depG tm b d) = y (depG tm b d)) : stepBits tm x b = stepBits tm y b := by
  have hL : decL tm x = decL tm y := by
    unfold decL; congr 1; funext o; exact h (.inl o)
  have hV : decV tm x = decV tm y := by
    unfold decV; congr 1; funext s; exact h (.inr (.inl s))
  have hC : ∀ k, ∀ j < D tm, decCell tm x k j = decCell tm y k j := fun k j hj =>
    decCell_congr tm fun o => h (.inr (.inr (.inl ⟨k, ⟨j, hj⟩, o⟩)))
  have hW : ∀ k j, j ≤ cellIdx tm b + D tm → cellIdx tm b ≤ j + D tm →
      decCell tm x k j = decCell tm y k j := by
    intro k j h1 h2
    refine decCell_congr tm fun o => ?_
    have := h (.inr (.inr (.inr (.inl ⟨k, ⟨j + D tm - cellIdx tm b, by omega⟩, o⟩))))
    simpa [depG, show cellIdx tm b + (j + D tm - cellIdx tm b) - D tm = j by omega] using this
  have hS : (fun k => prefixList (decCell tm x k) (D tm)) =
      (fun k => prefixList (decCell tm y k) (D tm)) :=
    funext fun k => prefixList_congr _ (hC k)
  unfold stepBits
  rw [hL, hV, hS]
  cases hl : decL tm y with
  | none => exact h (.inr (.inr (.inr (.inr ()))))
  | some l₀ =>
    simp only [Gfun]
    rcases b with o | s | ⟨k, i, o⟩
    · rfl
    · rfl
    · simp only [encC]
      congr 3
      unfold newCells
      split_ifs with hi
      · rfl
      · have hw := nf_W_length (tm.m l₀) (decV tm y)
          (fun k => prefixList (decCell tm y k) (D tm)) k
        have hp := nf_P_le (tm.m l₀) (decV tm y)
          (fun k => prefixList (decCell tm y k) (D tm)) k
        have hd := depth_le_D tm l₀
        apply hW <;> simp only [cellIdx] <;> omega

theorem iterate_stepBits {B : ℕ} (s : List (tm.Γ tm.k₀)) (T : ℕ)
    (hlen : ∀ t < T, ∀ k,
      (((step' tm)^[t] (initList tm s) : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤ B) :
    ∀ t ≤ T, (stepBits tm (B := B))^[t] (enc tm B (initList tm s)) =
      enc tm B ((step' tm)^[t] (initList tm s)) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [iterate_succ_apply', ih (by omega), iterate_succ_apply',
      stepBits_enc tm _ (iterate_step'_stkInA tm s t) (hlen t (by omega))]


theorem haltList_stk (s : List (tm.Γ tm.k₁)) (k : tm.K) :
    ((haltList tm s : Cfg tm.Γ tm.Λ tm.σ).stk k) =
      if h : k = tm.k₁ then h ▸ s else [] := by
  simp only [haltList]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem initList_getElem?_congr {s s' : List (tm.Γ tm.k₀)} {i : ℕ} (h : s[i]? = s'[i]?)
    (k : tm.K) :
    ((initList tm s : Cfg tm.Γ tm.Λ tm.σ).stk k)[i]? =
      ((initList tm s' : Cfg tm.Γ tm.Λ tm.σ).stk k)[i]? := by
  rw [initList_stk, initList_stk]
  split_ifs with hk
  · subst hk; exact h
  · rfl

theorem card_bits (B : ℕ) :
    Fintype.card (Bits tm B) = (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) +
      B * ∑ k, Fintype.card (Option (A tm k)) := by
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sigma, Finset.mul_sum]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-! ### Input map, Fin-indexed step and output -/

variable {α : Type} [Fintype α] [Nonempty α] (eIn : tm.Γ tm.k₀ ≃ α)

/-- The input map on bits: decode the one-hot string and encode the initial configuration. -/
noncomputable def encIn (n B : ℕ) (x : Fin (n * Fintype.card α) → Bool) : Bits tm B → Bool :=
  enc tm B (initList tm ((decWord n x).map eIn.symm))

/-- Row of the input read for cell index `i`. -/
def rowOf (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := if h : i < n then ⟨i, h⟩ else ⟨0, hn⟩

theorem encIn_congr {n B : ℕ} (hn : 0 < n) (b : Bits tm B) (x y : Fin (n * Fintype.card α) → Bool)
    (h : ∀ a : α, x (finProdFinEquiv (rowOf n hn (cellIdx tm b), Fintype.equivFin α a)) =
      y (finProdFinEquiv (rowOf n hn (cellIdx tm b), Fintype.equivFin α a))) :
    encIn tm eIn n B x b = encIn tm eIn n B y b := by
  rcases b with o | s | ⟨k, i, o⟩
  · rfl
  · rfl
  · have hw : ((decWord n x).map eIn.symm)[i.val]? = ((decWord n y).map eIn.symm)[i.val]? := by
      rw [List.getElem?_map, List.getElem?_map]
      congr 1
      refine decWord_getElem?_congr _ fun hi a => ?_
      have := h a
      simpa [cellIdx, rowOf, hi] using this
    have e := initList_getElem?_congr tm hw k
    simp only [encIn, enc, encC]
    exact decide_eq_decide.2 (by rw [e])

/-- Input map, `Fin`-indexed. -/
noncomputable def inF (n B : ℕ) (x : Fin (n * Fintype.card α) → Bool) :
    Fin (Fintype.card (Bits tm B)) → Bool :=
  encIn tm eIn n B x ∘ (Fintype.equivFin (Bits tm B)).symm

/-- Step map, `Fin`-indexed. -/
noncomputable def stF (B : ℕ) (y : Fin (Fintype.card (Bits tm B)) → Bool) :
    Fin (Fintype.card (Bits tm B)) → Bool :=
  stepBits tm (y ∘ Fintype.equivFin (Bits tm B)) ∘ (Fintype.equivFin (Bits tm B)).symm

open Classical in
/-- Output map, `Fin`-indexed: is cell `0` of the output stack equal to `y₁`? -/
noncomputable def outF (B : ℕ) (y₁ : tm.Γ tm.k₁) (y : Fin (Fintype.card (Bits tm B)) → Bool) :
    Bool :=
  decide (decCell tm (y ∘ Fintype.equivFin (Bits tm B)) tm.k₁ 0 = some y₁)

theorem stF_iterate (B : ℕ) (z : Bits tm B → Bool) (t : ℕ) :
    (stF tm B)^[t] (z ∘ (Fintype.equivFin (Bits tm B)).symm) =
      ((stepBits tm)^[t] z) ∘ (Fintype.equivFin (Bits tm B)).symm := by
  induction t generalizing z with
  | zero => rfl
  | succ t ih =>
    rw [iterate_succ_apply, iterate_succ_apply, ← ih]
    congr 1
    unfold stF
    congr 2
    funext b
    simp

open Classical in
theorem outF_comp (B : ℕ) (y₁ : tm.Γ tm.k₁) (z : Bits tm B → Bool) :
    outF tm B y₁ (z ∘ (Fintype.equivFin (Bits tm B)).symm) =
      decide (decCell tm z tm.k₁ 0 = some y₁) := by
  unfold outF
  congr 3
  funext b
  simp

theorem hasMCircuitOfSize_inF {n : ℕ} (hn : 0 < n) (B : ℕ) :
    HasMCircuitOfSize (inF tm eIn n B)
      (Fintype.card (Bits tm B) * juntaSize (Fintype.card α)) :=
  hasMCircuitOfSize_dep (Nat.mul_pos hn Fintype.card_pos) _
    (fun j a => finProdFinEquiv
      (rowOf n hn (cellIdx tm ((Fintype.equivFin (Bits tm B)).symm j)), Fintype.equivFin α a))
    fun _ x y h => encIn_congr tm eIn hn _ x y h

theorem hasMCircuitOfSize_stF (B : ℕ) :
    HasMCircuitOfSize (stF tm B)
      (Fintype.card (Bits tm B) * juntaSize (Fintype.card (DepG tm))) :=
  hasMCircuitOfSize_dep (Fintype.card_pos_iff.2 ⟨.inl none⟩) _
    (fun j d => Fintype.equivFin (Bits tm B) (depG tm ((Fintype.equivFin (Bits tm B)).symm j) d))
    fun _ x y h => stepBits_congr tm _ _ _ fun d => by simpa using h d

theorem hasCircuitOfSize_outF (B : ℕ) (y₁ : tm.Γ tm.k₁) :
    HasCircuitOfSize (outF tm B y₁) (juntaSize (Fintype.card (Option (A tm tm.k₁)))) :=
  hasCircuitOfSize_dep (Fintype.card_pos_iff.2 ⟨.inl none⟩) _
    (fun o => Fintype.equivFin (Bits tm B) (cellBit tm tm.k₁ 0 o))
    fun x y h => by
      unfold outF
      rw [decCell_congr tm (x := x ∘ _) (y := y ∘ _) fun o => by simpa using h o]

end Sim

/-- **Circuit simulation of a polynomial-time `FinTM2` on a set `S` of inputs.** If `tm` maps
every string `w ∈ S` (input alphabet `α`, via `eIn`) to the one-symbol output `[out w]` within
`time.eval |w|` steps, then the predicate `out w = y₁` has polynomial-size circuits that are
correct on the one-hot encodings of the strings in `S`. -/
theorem simulateOn {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (tm : FinTM2)
    (eIn : tm.Γ tm.k₀ ≃ α) (time : Polynomial ℕ) (out : List α → tm.Γ tm.k₁) (y₁ : tm.Γ tm.k₁)
    (S : List α → Prop)
    (hrun : ∀ w : List α, S w →
      TM2OutputsInTime tm (w.map eIn.symm) (some [out w]) (time.eval w.length)) :
    ∃ p : Polynomial ℕ, ∀ n, 0 < n → ∃ f : (Fin (n * Fintype.card α) → Bool) → Bool,
      HasCircuitOfSize f (p.eval n) ∧
        ∀ w : List α, S w → w.length = n → (f (oneHot n w) = true ↔ out w = y₁) := by
  letI := tm.ΛFin; letI := tm.σFin; letI := tm.kFin
  let c₀ := Fintype.card (Option tm.Λ) + Fintype.card tm.σ
  let c₁ := ∑ k, Fintype.card (Option (A tm k))
  let J₀ := juntaSize (Fintype.card α)
  let J := juntaSize (Fintype.card (DepG tm))
  let J₁ := juntaSize (Fintype.card (Option (A tm tm.k₁)))
  let Mp : Polynomial ℕ :=
    Polynomial.C c₀ + (Polynomial.X + time * Polynomial.C (D tm) + 1) * Polynomial.C c₁
  refine ⟨Mp * Polynomial.C J₀ + time * (Mp * Polynomial.C J) + Polynomial.C J₁, fun n hn => ?_⟩
  let T := time.eval n
  let B := n + T * D tm + 1
  have hM : Fintype.card (Bits tm B) = c₀ + B * c₁ := card_bits tm B
  refine ⟨outF tm B y₁ ∘ ((stF tm B)^[T] ∘ inF tm eIn n B), ?_, ?_⟩
  · have := ((hasMCircuitOfSize_inF tm eIn hn B).comp
      ((hasMCircuitOfSize_stF tm B).iterate T)).comp_single (hasCircuitOfSize_outF tm B y₁)
    refine this.mono (le_of_eq ?_)
    rw [hM]
    simp only [Mp, B, T, J₀, J, J₁, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
  · intro w hS hw
    obtain ⟨hfin, hlen⟩ := outputsInTime_step' tm (hrun w hS)
    simp only [List.length_map, hw] at hlen
    rw [hw] at hfin
    have hlen' : ∀ t < T, ∀ k, (((step' tm)^[t] (initList tm (w.map eIn.symm)) :
        Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤ B := fun t ht k => by
      have := hlen t ht.le k; simp only [B, T]; omega
    have hit := iterate_stepBits tm (B := B) (w.map eIn.symm) T hlen' T le_rfl
    rw [hfin] at hit
    have hA := iterate_step'_stkInA tm (w.map eIn.symm) T
    rw [hfin] at hA
    have hstk : ((haltList tm [out w] : Cfg tm.Γ tm.Λ tm.σ).stk tm.k₁) = [out w] := by
      rw [haltList_stk, dif_pos rfl]
    have hcell := decCell_enc tm (B := B) (haltList tm [out w]) tm.k₁ (hA tm.k₁)
      (by rw [hstk]; simp [B]) 0
    rw [hstk] at hcell
    have hin : inF tm eIn n B (oneHot n w) =
        enc tm B (initList tm (w.map eIn.symm)) ∘ (Fintype.equivFin (Bits tm B)).symm := by
      unfold inF encIn
      rw [decWord_oneHot w hw]
    simp only [Function.comp_apply]
    rw [hin, stF_iterate, hit, outF_comp, hcell]
    simp

/-- **Circuit simulation of a polynomial-time `FinTM2`** (all inputs). -/
theorem simulate {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (tm : FinTM2)
    (eIn : tm.Γ tm.k₀ ≃ α) (time : Polynomial ℕ) (out : List α → tm.Γ tm.k₁) (y₁ : tm.Γ tm.k₁)
    (hrun : ∀ w : List α,
      TM2OutputsInTime tm (w.map eIn.symm) (some [out w]) (time.eval w.length)) :
    ∃ p : Polynomial ℕ, ∀ n, 0 < n → ∃ f : (Fin (n * Fintype.card α) → Bool) → Bool,
      HasCircuitOfSize f (p.eval n) ∧
        ∀ w : List α, w.length = n → (f (oneHot n w) = true ↔ out w = y₁) := by
  obtain ⟨p, hp⟩ := simulateOn tm eIn time out y₁ (fun _ => True) fun w _ => hrun w
  exact ⟨p, fun n hn => (hp n hn).imp fun f hf => ⟨hf.1, fun w hw => hf.2 w trivial hw⟩⟩

end Pnp.PPoly
