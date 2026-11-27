import Pnp.KarpLipton.DProg
import Pnp.KarpLipton.DenseWitness
import Pnp.KarpLipton.Equiv
import Pnp.Oracle.OfficialCode
import Pnp.Derandomization.LautemannList
import Pnp.TM2.Homomorphism

/-!
# The official Karp–Lipton collapse `Π₂ᴾ ⊆ Σ₂ᴾ` under `NP ⊆ P/poly` (M32e, part 3)

`pi2_subset_sigma2`: if every official `NP` language has polynomial-size circuits
(`Pnp.KarpLipton.NPSubsetPPoly`), then every language of the official second level `Π₂ᴾ`
(`Millennium.polynomial_hierarchy_pi_level 2`, strings over a finite nonempty alphabet) is in
the official `Σ₂ᴾ` (`Millennium.polynomial_hierarchy_sigma_level 2`).

The `Σ₂` witness is the list of dense circuit codes `G₀, …, G_{p(n)}` of `dense_search` (one per
length of the universally quantified string `b`), written as a bit-pair code.  The inner
predicate is decided by the program of `Pnp.KarpLipton.DP` instantiated here: its tables push the
truncated-unary codes of the official decider of `L''` (`decide_of_inPolynomialTime`) and the
one-hot blocks of `oneHot (w#b)`.

This is a conditional collapse of the polynomial hierarchy; it does not prove or refute
`P ≠ NP`.
-/

namespace Pnp.KarpLipton.Collapse

open Pnp.Relativize Pnp.Relativize.Struct Pnp.KarpLipton.DP Pnp.PPoly Pnp.CookLevin Classical

noncomputable section

/-! ## List lemmas -/

/-- The one-hot block of width `r` with its `true` at position `i`. -/
def oneB (r i : ℕ) : Str := List.replicate i false ++ true :: List.replicate (r - 1 - i) false

theorem length_oneB {r i : ℕ} (h : i < r) : (oneB r i).length = r := by
  simp [oneB]; omega

theorem sl_blocks (r d : ℕ) (rest : Str) : ∀ l : List ℕ, (∀ i ∈ l, i < r) →
    sl r d ((l.flatMap fun i => false :: oneB r i) ++ rest) = (l ++ (sl r d rest).1, (sl r d rest).2)
  | [], _ => by simp
  | i :: l, h => by
    have hi := h i (by simp)
    have ih := sl_blocks r d rest l (fun j hj => h j (by simp [hj]))
    simp only [List.flatMap_cons, List.cons_append, List.append_assoc]
    rw [sl_false]
    have e1 : fi r (oneB r i ++ ((l.flatMap fun i => false :: oneB r i) ++ rest)) = some i := by
      unfold oneB
      exact fi_block i r _ hi
    have e2 : (oneB r i ++ ((l.flatMap fun i => false :: oneB r i) ++ rest)).drop r =
        (l.flatMap fun i => false :: oneB r i) ++ rest := List.drop_left' (length_oneB hi)
    rw [e1, e2, ih]; simp

theorem rev_flatMap_rev (F : ℕ → Str) : ∀ l : List ℕ,
    (l.reverse.flatMap fun j => (F j).reverse).reverse = l.flatMap F
  | [] => by simp
  | j :: l => by
    have ih := rev_flatMap_rev F l
    simp only [List.reverse_cons, List.flatMap_append, List.reverse_append, ih, List.flatMap_cons]
    simp

/-- Push nothing for an invalid index. -/
def oF {δ : Type} (o : ℕ → Option δ) (G : δ → Str) (j : ℕ) : Str :=
  match o j with
  | some a => G a
  | none => []

theorem flatMap_oF {δ : Type} (o : ℕ → Option δ) (G : δ → Str) :
    ∀ l : List ℕ, l.flatMap (oF o G) = (l.filterMap o).flatMap G
  | [] => rfl
  | j :: l => by
    have ih := flatMap_oF o G l
    cases h : o j <;> simp [oF, h, ih]

/-- The symbol with index `j`, if any. -/
def sym (δ : Type) [Fintype δ] (j : ℕ) : Option δ :=
  if h : j < Fintype.card δ then some ((Fintype.equivFin δ).symm ⟨j, h⟩) else none

theorem sym_e {δ : Type} [Fintype δ] (a : δ) : sym δ (Fintype.equivFin δ a) = some a := by
  simp [sym]

theorem filterMap_sym {δ : Type} [Fintype δ] (w : List δ) :
    (w.map fun a => ((Fintype.equivFin δ a : Fin _) : ℕ)).filterMap (sym δ) = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [sym_e, ih]

theorem length_filterMap_le {δ : Type} (o : ℕ → Option δ) (l : List ℕ) :
    (l.filterMap o).length ≤ l.length := List.length_filterMap_le _ _

/-- The one-hot block of a symbol. -/
def blkV {δ : Type} [Fintype δ] [DecidableEq δ] (h : δ) : Str :=
  List.ofFn fun i : Fin (Fintype.card δ) => decide (h = (Fintype.equivFin δ).symm i)

theorem length_blkV {δ : Type} [Fintype δ] [DecidableEq δ] (h : δ) :
    (blkV h).length = Fintype.card δ := by simp [blkV]

theorem ofFn_oneHot {δ : Type} [Fintype δ] [DecidableEq δ] (y : List δ) :
    List.ofFn (oneHot y.length y) = y.flatMap blkV := by
  rw [List.ofFn_mul]
  have e : y.flatMap blkV = (List.ofFn fun i : Fin y.length => blkV y[i]).flatten := by
    rw [List.flatMap_def]
    congr 1
    exact (List.ofFn_getElem_eq_map y blkV).symm
  rw [e]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  refine List.ofFn_inj.2 (funext fun j => ?_)
  have hij : (⟨i * Fintype.card δ + j, by
      calc ↑i * Fintype.card δ + ↑j < (↑i + 1) * Fintype.card δ := by nlinarith [j.isLt]
        _ ≤ _ := Nat.mul_le_mul_right _ i.isLt⟩ : Fin (y.length * Fintype.card δ)) =
      finProdFinEquiv (i, j) := by
    ext; rw [finProdFinEquiv_val]
  rw [hij]
  simp [oneHot, Equiv.symm_apply_apply, List.getElem?_eq_getElem i.isLt]

/-! ## Decoding -/

theorem fi_eq_firstIdx : ∀ (r : ℕ) (l : Str),
    fi r l = firstIdx ((List.range r).map fun j => l.getD j false)
  | 0, l => rfl
  | r + 1, l => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have ih := fi_eq_firstIdx r (l.drop 1)
    have e : ((fun j => (l.drop 1).getD j false) : ℕ → Bool) = (fun j => l.getD j false) ∘ Nat.succ := by
      funext j; simp [getD_drop_one]
    rw [e] at ih
    unfold fi
    cases h : l.getD 0 false
    · simp only [Bool.false_eq_true, if_false, List.map_cons, h, ih]
      rfl
    · simp only [if_true, List.map_cons, h]
      rfl

theorem filterMap_eq_map' {δ ε : Type} (f : δ → Option ε) (g : δ → ε) (hfg : ∀ x, f x = some (g x)) :
    ∀ l : List δ, l.filterMap f = l.map g
  | [] => rfl
  | x :: l => by simp [List.filterMap_cons, hfg, filterMap_eq_map' f g hfg l]

/-- The decoded certificate is a prefix of `decL`. -/
theorem ic_filterMap {γ : Type} [Fintype γ] [Nonempty γ] (X : Str) (N t : ℕ) (ht : t ≤ N) :
    (DP.ic (Fintype.card γ) (Fintype.equivFin γ (Classical.arbitrary γ)) X t).filterMap (sym γ) =
      (decL (γ := γ) N (Fintype.card γ) X).take t := by
  unfold DP.ic decL
  rw [List.filterMap_map, ← List.map_take, List.take_range, Nat.min_eq_left ht]
  refine filterMap_eq_map' _ _ (fun s => ?_) _
  simp only [Function.comp]
  have hb : ((List.range (Fintype.card γ)).map fun j => (X.drop (s * Fintype.card γ)).getD j false) =
      (List.range (Fintype.card γ)).map fun j => X.getD (s * Fintype.card γ + j) false := by
    congr 1; funext j
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [fi_eq_firstIdx, hb]
  unfold decSym
  rcases hf : firstIdx ((List.range (Fintype.card γ)).map fun j => X.getD (s * Fintype.card γ + j) false) with _ | j
  · simp [sym]
  · have hj : j < Fintype.card γ := by
      have := fi_lt (Fintype.card γ) (X.drop (s * Fintype.card γ)) j (by rw [fi_eq_firstIdx, hb, hf])
      exact this
    simp [sym, hj]

/-! ## Honest witness codes -/

/-- The witness: the circuit codes as one bit-pair code. -/
def Wenc (Gs : List Str) : Str := Gs.flatMap fun G => dbl G ++ [true, true]

theorem segIt_Wenc (Gs : List Str) : ∀ m, segIt (Wenc Gs) m = Wenc (Gs.drop m)
  | 0 => rfl
  | m + 1 => by
    rw [segIt, segIt_Wenc Gs m]
    rcases h : Gs.drop m with _ | ⟨G, rest⟩
    · have : Gs.drop (m + 1) = [] := by rw [← List.drop_drop, h]; rfl
      rw [this]; rfl
    · have : Gs.drop (m + 1) = rest := by rw [← List.drop_drop, h]; rfl
      rw [this]
      simp only [Wenc, List.flatMap_cons, List.append_assoc]
      rw [show [true, true] ++ rest.flatMap (fun G => dbl G ++ [true, true]) =
        true :: true :: rest.flatMap (fun G => dbl G ++ [true, true]) from rfl, seg_dbl_sep]

theorem sel_Wenc (Gs : List Str) (m : ℕ) (hm : m < Gs.length) :
    (seg (segIt (Wenc Gs) m)).1 = Gs[m] := by
  rw [segIt_Wenc, List.drop_eq_getElem_cons hm]
  simp only [Wenc, List.flatMap_cons, List.append_assoc]
  rw [show [true, true] ++ (Gs.drop (m + 1)).flatMap (fun G => dbl G ++ [true, true]) =
    true :: true :: (Gs.drop (m + 1)).flatMap (fun G => dbl G ++ [true, true]) from rfl, seg_dbl_sep]

theorem length_Wenc (Gs : List Str) (B : ℕ) (h : ∀ G ∈ Gs, G.length ≤ B) :
    (Wenc Gs).length ≤ Gs.length * (2 * B + 2) := by
  induction Gs with
  | nil => simp [Wenc]
  | cons G Gs ih =>
    have h1 := h G (by simp)
    have ih' := ih (fun G' hG' => h G' (by simp [hG']))
    simp only [Wenc, List.flatMap_cons, List.length_append, List.length_cons] at ih' ⊢
    have : (dbl G).length = 2 * G.length := by simp [dbl]; ring
    rw [this]
    have e2 : (Gs.length + 1) * (2 * B + 2) = Gs.length * (2 * B + 2) + (2 * B + 2) := by ring
    simp only [List.length_nil] at *
    omega

/-! ## The instantiated program -/

section Inst

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β]
  [DecidableEq γ]

/-- The truncated-unary code of a symbol of the inner decider's alphabet. -/
def tuL (Nc : ℕ) (ix : (α ⊕ Option β) ⊕ Option γ → ℕ) (g : (α ⊕ Option β) ⊕ Option γ) : Str :=
  FromTM2.tu Nc (ix g)

/-- The program data. -/
def mkPar (Nc : ℕ) (ix : (α ⊕ Option β) ⊕ Option γ → ℕ) (q0 : Prog) (p Q : Polynomial ℕ) : Par where
  kA := Fintype.card α
  kB := Fintype.card β
  kC := Fintype.card γ
  dA := Fintype.card α
  dB := Fintype.card β
  dC := if h : Nonempty γ then Fintype.equivFin γ (@Classical.arbitrary γ h) else 0
  BA := Nc + Fintype.card (α ⊕ Option β)
  BB := Nc + Fintype.card (α ⊕ Option β)
  BC := Nc
  SA := fun j => (oF (sym α) (fun a => tuL Nc ix (.inl (.inl a))) j).reverse
  TA := fun j => (oF (sym α) (fun a => blkV (Sum.inl a : α ⊕ Option β)) j).reverse
  SB := fun j => (oF (sym β) (fun y => tuL Nc ix (.inl (.inr (some y)))) j).reverse
  TB := fun j => (oF (sym β) (fun y => blkV (Sum.inr (some y) : α ⊕ Option β)) j).reverse
  SC := fun j => (oF (sym γ) (fun c => tuL (β := β) Nc ix (.inr (some c))) j).reverse
  sWB := tuL Nc ix (.inl (.inr none))
  sC := tuL (β := β) Nc ix (.inr none)
  bS := blkV (Sum.inr none : α ⊕ Option β)
  p := p
  Q := Q
  q := q0

theorem length_tuL {Nc : ℕ} {ix : (α ⊕ Option β) ⊕ Option γ → ℕ} (hix : ∀ g, ix g < Nc) (g) :
    (tuL Nc ix g).length ≤ Nc :=
  FromNP.tu_length_le.trans (hix g)

theorem length_oF_le {δ : Type} (o : ℕ → Option δ) (G : δ → Str) (B : ℕ) (hG : ∀ a, (G a).length ≤ B)
    (j : ℕ) : (oF o G j).length ≤ B := by
  unfold oF; split
  · exact hG _
  · simp

theorem mkPar_ok {Nc : ℕ} {ix : (α ⊕ Option β) ⊕ Option γ → ℕ} (hix : ∀ g, ix g < Nc) (q0 : Prog)
    (p Q : Polynomial ℕ) : (mkPar Nc ix q0 p Q).Ok := by
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩
  · simp only [mkPar, List.length_reverse]
    have := length_oF_le (sym α) (fun a => tuL Nc ix (.inl (.inl a))) Nc
      (fun a => length_tuL hix _) j
    have := length_oF_le (sym α) (fun a => blkV (Sum.inl a : α ⊕ Option β))
      (Fintype.card (α ⊕ Option β)) (fun a => (length_blkV _).le) j
    omega
  · simp only [mkPar, List.length_reverse]
    have := length_oF_le (sym β) (fun y => tuL Nc ix (.inl (.inr (some y)))) Nc
      (fun a => length_tuL hix _) j
    have := length_oF_le (sym β) (fun y => blkV (Sum.inr (some y) : α ⊕ Option β))
      (Fintype.card (α ⊕ Option β)) (fun a => (length_blkV _).le) j
    omega
  · simp only [mkPar, List.length_reverse, List.length_nil, Nat.add_zero]
    exact length_oF_le (sym γ) (fun c => tuL (β := β) Nc ix (.inr (some c))) Nc
      (fun a => length_tuL hix _) j

/-- The nested pair encoding of the inner decider. -/
abbrev e3 (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] :
    Computability.FinEncoding ((List α × List β) × List γ) :=
  Millennium.pair_encoding (Millennium.pair_encoding (Millennium.fin_encoding_string α)
    (Millennium.fin_encoding_string β)) (Millennium.fin_encoding_string γ)

/-- The symbols of the nested pair code `(w#b)#c`. -/
def code3 (w : List α) (b : List β) (c : List γ) : List ((α ⊕ Option β) ⊕ Option γ) :=
  (w.map Sum.inl ++ Sum.inr none :: b.map (fun y => Sum.inr (some y))).map Sum.inl ++
    Sum.inr none :: c.map (fun g => Sum.inr (some g))

theorem e3_encode (w : List α) (b : List β) (c : List γ) :
    (e3 α β γ).encode ((w, b), c) = code3 w b c := rfl

theorem xc_mkPar (Nc : ℕ) (ix : (α ⊕ Option β) ⊕ Option γ → ℕ) (q0 : Prog) (p Q : Polynomial ℕ)
    (iw ib ic : List ℕ) :
    xc (mkPar Nc ix q0 p Q) iw ib ic =
      (code3 (iw.filterMap (sym α)) (ib.filterMap (sym β)) (ic.filterMap (sym γ))).flatMap
        (tuL Nc ix) := by
  simp only [xc, mkPar]
  rw [rev_flatMap_rev (oF (sym α) fun a => tuL Nc ix (.inl (.inl a))),
    rev_flatMap_rev (oF (sym β) fun y => tuL Nc ix (.inl (.inr (some y)))),
    rev_flatMap_rev (oF (sym γ) fun c => tuL (β := β) Nc ix (.inr (some c))),
    flatMap_oF, flatMap_oF, flatMap_oF]
  simp only [code3, List.map_append, List.map_cons, List.map_map,
    List.flatMap_append, List.flatMap_cons, List.flatMap_map, List.append_assoc]
  rfl

end Inst

/-! ## Codes of the inner predicate's inputs -/

section Code

variable {α β : Type} [Fintype α] [Fintype β]

/-- Index of a symbol. -/
abbrev eI {δ : Type} [Fintype δ] (a : δ) : ℕ := (Fintype.equivFin δ a : ℕ)

/-- The bit code of the symbols of `((w, W), b)`. -/
def cD : (α ⊕ Option Bool) ⊕ Option β → Str
  | .inl (.inl a) => false :: oneB (Fintype.card α) (eI a)
  | .inl (.inr none) => [true]
  | .inl (.inr (some x)) => [false, x]
  | .inr none => [true, true]
  | .inr (some y) => false :: oneB (Fintype.card β) (eI y)

/-- The symbols of `((w, W), b)`. -/
def code4 (w : List α) (W : List Bool) (b : List β) : List ((α ⊕ Option Bool) ⊕ Option β) :=
  (w.map Sum.inl ++ Sum.inr none :: W.map (fun x => Sum.inr (some x))).map Sum.inl ++
    Sum.inr none :: b.map (fun y => Sum.inr (some y))

theorem flatMap_code4 (w : List α) (W : List Bool) (b : List β) :
    (code4 w W b).flatMap cD = ((w.map eI).flatMap fun i => false :: oneB (Fintype.card α) i) ++
      true :: (dbl W ++ true :: true :: (((b.map eI).flatMap fun i => false :: oneB (Fintype.card β) i) ++ [])) := by
  simp only [code4, List.map_append, List.map_cons, List.map_map, List.flatMap_append,
    List.flatMap_cons, List.flatMap_map, List.append_nil]
  have hd : ∀ W : List Bool, (W.flatMap fun x => cD (β := β) (α := α) (Sum.inl (Sum.inr (some x)))) = dbl W := by
    intro W; induction W with
    | nil => rfl
    | cons x W ih => simp only [List.flatMap_cons, ih]; rfl
  simp only [Function.comp_def]
  rw [hd]
  simp [cD, List.append_assoc]

theorem eI_lt {δ : Type} [Fintype δ] (a : δ) : eI a < Fintype.card δ := (Fintype.equivFin δ a).isLt

end Code

section Sem

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β]
  [DecidableEq γ]

theorem flatMap_blkV_pe2 (w : List α) (b : List β) :
    (pe2 w b).flatMap blkV = w.flatMap (fun a => blkV (Sum.inl a : α ⊕ Option β)) ++
      blkV (Sum.inr none : α ⊕ Option β) ++ b.flatMap (fun y => blkV (Sum.inr (some y) : α ⊕ Option β)) := by
  simp [pe2, List.flatMap_append, List.flatMap_map, List.append_assoc]

/-- **The computed predicate on codes.** -/
theorem dsem_code (Nc : ℕ) (ix : (α ⊕ Option β) ⊕ Option γ → ℕ) (q0 : Prog) (p Q : Polynomial ℕ)
    (ans : List ℕ → List ℕ → List ℕ → Bool) (w : List α) (W : List Bool) (b : List β) :
    Dsem (mkPar Nc ix q0 p Q) ans ((code4 w W b).flatMap cD) ↔
      p.eval w.length < b.length ∨ ∃ t ≤ Q.eval (w.length + 1 + b.length),
        ans (w.map eI) (b.map eI) (DP.ic (Fintype.card γ) (mkPar Nc ix q0 p Q).dC
          (evalD (seg (segIt W b.length)).1 (List.ofFn (oneHot (w.length + 1 + b.length) (pe2 w b)))
            [] false false).reverse t) = false := by
  set π := mkPar Nc ix q0 p Q
  set z := (code4 w W b).flatMap cD
  have hw : ∀ i ∈ w.map eI, i < Fintype.card α := by
    intro i hi; obtain ⟨a, -, rfl⟩ := List.mem_map.1 hi; exact eI_lt a
  have hb : ∀ i ∈ b.map eI, i < Fintype.card β := by
    intro i hi; obtain ⟨a, -, rfl⟩ := List.mem_map.1 hi; exact eI_lt a
  have h1 : r1 π z = (w.map eI, dbl W ++ true :: true ::
      (((b.map eI).flatMap fun i => false :: oneB (Fintype.card β) i) ++ [])) := by
    simp only [r1, z, flatMap_code4, π, mkPar]
    rw [sl_blocks _ _ _ _ hw, sl_true]
    simp
  have h2 : r2 π z = (W, ((b.map eI).flatMap fun i => false :: oneB (Fintype.card β) i) ++ []) := by
    simp only [r2, h1, seg_dbl_sep]
  have h3 : r3 π z = (b.map eI, []) := by
    simp only [r3, h2]
    simp only [π, mkPar]
    rw [sl_blocks _ _ _ _ hb, sl_nil]
    simp
  have hV : vS π z = List.ofFn (oneHot (w.length + 1 + b.length) (pe2 w b)) := by
    rw [← length_pe2, ofFn_oneHot, flatMap_blkV_pe2]
    simp only [vS, h1, h3]
    simp only [π, mkPar]
    rw [rev_flatMap_rev (oF (sym α) fun a => blkV (Sum.inl a : α ⊕ Option β)),
      rev_flatMap_rev (oF (sym β) fun y => blkV (Sum.inr (some y) : α ⊕ Option β)),
      flatMap_oF, flatMap_oF, filterMap_sym, filterMap_sym]
  have hN : nS π z = Q.eval (w.length + 1 + b.length) := by
    simp only [nS, h1, h3, List.length_map]
    simp only [π, mkPar]
    congr 1; omega
  unfold Dsem
  rw [hN]
  simp only [xS, gS, hV, h1, h2, h3, List.length_map]
  rfl

end Sem

/-! ## The collapse -/

/-- The nested pair encoding of the inputs `((w, W), b)` of the inner predicate. -/
abbrev e4 (α β : Type) [Fintype α] [Fintype β] :
    Computability.FinEncoding ((List α × List Bool) × List β) :=
  Millennium.pair_encoding (Millennium.pair_encoding (Millennium.fin_encoding_string α)
    (Millennium.fin_encoding_string Bool)) (Millennium.fin_encoding_string β)

theorem e4_encode {α β : Type} [Fintype α] [Fintype β] (w : List α) (W : List Bool) (b : List β) :
    (e4 α β).encode ((w, W), b) = code4 w W b := rfl

/-- **The official Karp–Lipton collapse.**  If `NP ⊆ P/poly`, then every language of the official
class `Π₂ᴾ` (strings over a finite nonempty alphabet) is in the official class `Σ₂ᴾ`. -/
theorem pi2_subset_sigma2 (hNP : NPSubsetPPoly) {α : Type} [Fintype α] [DecidableEq α]
    [Nonempty α] [Primcodable α] {L : Millennium.Language (List α)}
    (hL : Millennium.polynomial_hierarchy_pi_level 2 (Millennium.fin_encoding_string α) L) :
    Millennium.polynomial_hierarchy_sigma_level 2 (Millennium.fin_encoding_string α) L := by
  obtain ⟨T, hT⟩ := smallExistentials_iff.1.2 (smallExistentials_iff.2.2 hNP)
  obtain ⟨β, _, _, L', hL', p, hp⟩ := hL
  obtain ⟨γ, _, _, L'', hL'', q, hq⟩ := hL'
  obtain ⟨q0, Nc, ix, K, -, -, hix, hrun⟩ :=
    OfficialCode.decide_of_inPolynomialTime (e3 α β γ) hL''
  let ix' : (α ⊕ Option β) ⊕ Option γ → ℕ := ix
  have hix' : ∀ g, ix' g < Nc := hix
  set Q : Polynomial ℕ := if Nonempty γ then q else 0 with hQ
  set π := mkPar (α := α) (β := β) (γ := γ) Nc ix' q0 p Q with hπdef
  have hπ : π.Ok := mkPar_ok hix' q0 p Q
  set ans : List ℕ → List ℕ → List ℕ → Bool := fun iw ib ic =>
    decide (Millennium.complement L'' ((iw.filterMap (sym α), ib.filterMap (sym β)),
      ic.filterMap (sym γ))) with hans
  have hq0 : ∀ iw ib ic : List ℕ, runFor ∅ π.q (tb K (xc π iw ib ic).length)
      (.run (init [xc π iw ib ic])) = .done (ans iw ib ic) := by
    intro iw ib ic
    rw [hπdef, xc_mkPar, ← e3_encode]
    exact hrun _
  have hS := dsem_mem_P π hπ K ans hq0
  let D : Millennium.Language ((List α × List Bool) × List β) := fun t =>
    Dsem π ans (((e4 α β).encode t).flatMap cD)
  have hD : Millennium.InPolynomialTime (e4 α β) D :=
    Pnp.TM2Hom.inPolynomialTime_of_code (e4 α β) cD _ hS D (fun t => Iff.rfl)
  -- the inner predicate on codes
  have hDs : ∀ (w : List α) (W : List Bool) (b : List β), D ((w, W), b) ↔
      p.eval w.length < b.length ∨ ∃ t ≤ Q.eval (w.length + 1 + b.length),
        L'' ((w, b), (DP.ic (Fintype.card γ) π.dC
          (evalD (seg (segIt W b.length)).1 (List.ofFn (oneHot (w.length + 1 + b.length) (pe2 w b)))
            [] false false).reverse t).filterMap (sym γ)) := by
    intro w W b
    show Dsem π ans (((e4 α β).encode ((w, W), b)).flatMap cD) ↔ _
    refine Iff.trans (dsem_code (α := α) (β := β) (γ := γ) Nc ix' q0 p Q ans w W b) ?_
    simp only [hans, filterMap_sym, decide_eq_false_iff_not, Millennium.complement, not_not]
    exact Iff.rfl
  have hlenwb : ∀ (w : List α) (b : List β), ((Millennium.pair_encoding (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string β)).encode (w, b)).length = w.length + 1 + b.length := by
    intro w b; rw [Millennium.pair_encoding.length_eq]; rfl
  have hlenwW : ∀ (w : List α) (W : List Bool), ((Millennium.pair_encoding (Millennium.fin_encoding_string α)
      (Millennium.fin_encoding_string Bool)).encode (w, W)).length = w.length + 1 + W.length := by
    intro w W; rw [Millennium.pair_encoding.length_eq]; rfl
  -- soundness, for both cases
  have hsound : ∀ (w : List α) (W : List Bool),
      (∀ b : List β, b.length ≤ p.eval (w.length + 1 + W.length) → D ((w, W), b)) → L w := by
    intro w W hall
    by_contra hLw
    obtain ⟨b, hb, hL'b⟩ := (hp w).1 hLw
    have hb' : b.length ≤ p.eval w.length := hb
    have hmono : p.eval w.length ≤ p.eval (w.length + 1 + W.length) :=
      Pnp.TM2Proj.polynomial_eval_mono _ (by omega)
    rcases (hDs w W b).1 (hall b (hb'.trans hmono)) with h | ⟨t, ht, hL''t⟩
    · omega
    · refine (hq (w, b)).2 ⟨_, ?_, hL''t⟩ hL'b
      rw [hlenwb]
      refine (length_filterMap_le _ _).trans ?_
      rw [length_ic]
      by_cases hγ : Nonempty γ
      · rw [hQ, if_pos hγ] at ht; exact ht
      · rw [hQ, if_neg hγ, Polynomial.eval_zero] at ht; omega
  by_cases hγ : Nonempty γ
  · -- the main case: dense witness codes
    obtain ⟨r, hr⟩ := dense_search hT L'' hL'' q
    choose G hGl hG using hr
    let pW : Polynomial ℕ := (p + 1) * (2 * r.comp (Polynomial.X + p) + 2)
    refine Pnp.Derand.sigma2_intro (Millennium.fin_encoding_string α) L Bool β D hD pW p
      (fun w => ⟨fun hLw => ?_, fun ⟨W, _, hall⟩ => hsound w W (by rwa [hlenwW] at hall)⟩)
    set n := w.length
    let Gs : List Str := (List.range (p.eval n + 1)).map (G n)
    refine ⟨Wenc Gs, ?_, fun b hb => ?_⟩
    · -- the witness length
      have hGs : ∀ g ∈ Gs, g.length ≤ r.eval (n + p.eval n) := by
        intro g hg
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hg
        rw [List.mem_range] at hm
        exact (hGl n m).trans (Pnp.TM2Proj.polynomial_eval_mono _ (by omega))
      refine (length_Wenc Gs _ hGs).trans (le_of_eq ?_)
      simp [pW, Gs, Polynomial.eval_comp, n]
      rfl
    · rw [hDs]
      by_cases hbm : p.eval n < b.length
      · exact Or.inl hbm
      right
      have hL'b : ¬ L' (w, b) := fun h => (hp w).2 ⟨b, Nat.le_of_not_lt hbm, h⟩ hLw
      obtain ⟨c, hc, hcL⟩ := (hq (w, b)).1 hL'b
      rw [hlenwb] at hc
      have hsel : (seg (segIt (Wenc Gs) b.length)).1 = G n b.length := by
        rw [sel_Wenc Gs b.length (by simp [Gs]; omega)]
        simp [Gs]
      obtain ⟨m', hm', hm'L⟩ := hG n b.length w b rfl rfl ⟨c, hc, hcL⟩
      refine ⟨m', ?_, ?_⟩
      · rw [hQ, if_pos hγ]; exact hm'
      · rw [hsel]
        have hdC : π.dC = Fintype.equivFin γ (Classical.arbitrary γ) := by
          simp [hπdef, mkPar, dif_pos hγ]
        rw [hdC, ic_filterMap _ _ _ hm']
        exact hm'L
  · -- no certificate symbols: the certificate is empty
    refine Pnp.Derand.sigma2_intro (Millennium.fin_encoding_string α) L Bool β D hD 0 p
      (fun w => ⟨fun hLw => ⟨[], by simp, fun b hb => ?_⟩,
        fun ⟨W, _, hall⟩ => hsound w W (by rwa [hlenwW] at hall)⟩)
    rw [hDs]
    by_cases hbm : p.eval w.length < b.length
    · exact Or.inl hbm
    right
    have hL'b : ¬ L' (w, b) := fun h => (hp w).2 ⟨b, Nat.le_of_not_lt hbm, h⟩ hLw
    obtain ⟨c, -, hcL⟩ := (hq (w, b)).1 hL'b
    have hc : c = [] := by
      cases c with
      | nil => rfl
      | cons g _ => exact absurd ⟨g⟩ hγ
    refine ⟨0, Nat.zero_le _, ?_⟩
    simp only [DP.ic, List.range_zero, List.map_nil, List.filterMap_nil]
    rw [← hc]; exact hcL

end

end Pnp.KarpLipton.Collapse
