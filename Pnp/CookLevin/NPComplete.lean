import Pnp.CookLevin.TabInst
import Pnp.CookLevin.FunBridge
import Pnp.CookLevin.Generator

/-!
# M33e: SAT is NP-complete (uniform Cook–Levin), assembly

For an official `NP` language `L'` with verifier machine `tm`, the reduction maps `b` to the
tableau formula `(shape (dat …)).formula (gsOf b)`.  Correctness is `tab_sat_iff`; computability
comes from a formula generator (`GenSpec`) and `computable_of_cmd_code`.
-/

namespace Pnp.CookLevin.NPC

open Turing Polynomial Pnp.PPoly Pnp.CookLevin Pnp.CookLevin.Uniform Pnp.CookLevin.Tab
open Pnp.Relativize Pnp.Relativize.Struct Classical

/-- The specification of the formula generator program. -/
def GenSpec : Prop :=
  ∀ sh : Shape, ∃ (c : Cmd) (kOut K : ℕ) (g : Str → List SatSym),
    (∀ x : Str, ∃ σ', ExecLe c (init [x]).stk (.norm σ') (tb K x.length) ∧
      σ' kOut = ((g x).flatMap ic).reverse) ∧
    ∀ gs, g (gs.flatMap (oneHotW sh.W)) = sh.formula gs

section Verifier

variable {β : Type} (eb : Computability.FinEncoding β) {Γ₁ : Type} [Fintype Γ₁]
  (k : ℕ) {f : β × List Γ₁ → Bool}
  (comp : TM2ComputableInPolyTime
    (Millennium.pair_encoding eb (Millennium.fin_encoding_string Γ₁)).encode
    Computability.finEncodingBoolBool.encode f)

/-- The tableau data of the verifier machine. -/
noncomputable def dat : Data comp.tm where
  W := Fintype.card eb.Γ
  inSym g := comp.inputAlphabet.symm (Sum.inl ((Fintype.equivFin eb.Γ).symm g))
  sepSym := comp.inputAlphabet.symm (Sum.inr none)
  ok x := ∃ γ : Γ₁, x = comp.inputAlphabet.symm (Sum.inr (some γ))
  yes := comp.outputAlphabet.symm true
  PM := X ^ k
  PT := comp.time.comp (X + 1 + X ^ k)
  PB := X + 2 + X ^ k + comp.time.comp (X + 1 + X ^ k) * C (Dp comp.tm)

/-- The input word, as a list of `Fin W`. -/
noncomputable def gsOf (b : β) : List (Fin (Fintype.card eb.Γ)) :=
  (eb.encode b).map (Fintype.equivFin eb.Γ)

/-- Certificate symbols on the machine tape. -/
noncomputable def cert (γ : Γ₁) : comp.tm.Γ comp.tm.k₀ := comp.inputAlphabet.symm (Sum.inr (some γ))

variable {eb k comp}

theorem length_gsOf (b : β) : (gsOf eb b).length = (eb.encode b).length := by simp [gsOf]

theorem inWord_eq (b : β) (y : List Γ₁) :
    inWord (dat eb k comp) (gsOf eb b) (y.map (cert eb comp)) =
      List.map comp.inputAlphabet.invFun
        ((Millennium.pair_encoding eb (Millennium.fin_encoding_string Γ₁)).encode (b, y)) := by
  simp only [inWord, dat, gsOf, Millennium.pair_encoding, Millennium.fin_encoding_string,
    List.map_append, List.map_map, List.map_cons, id]
  congr 1
  apply List.map_congr_left; intro x _; (simp [Equiv.invFun_as_coe]; rfl)

theorem ok_iff (ys : List (comp.tm.Γ comp.tm.k₀)) :
    (∀ y ∈ ys, (dat eb k comp).ok y) ↔ ∃ y : List Γ₁, ys = y.map (cert eb comp) := by
  constructor
  · intro h
    induction ys with
    | nil => exact ⟨[], rfl⟩
    | cons x xs ih =>
      obtain ⟨γ, rfl⟩ := h x (List.mem_cons_self ..)
      obtain ⟨y, rfl⟩ := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
      exact ⟨γ :: y, rfl⟩
  · rintro ⟨y, rfl⟩ x hx
    obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hx
    exact ⟨γ, rfl⟩

/-- The verifier run, as iterated total steps. -/
theorem run_eq (b : β) (y : List Γ₁) (hy : y.length ≤ (eb.encode b).length ^ k) :
    (step' comp.tm)^[(dat eb k comp).PT.eval (gsOf eb b).length]
        (initList comp.tm (inWord (dat eb k comp) (gsOf eb b) (y.map (cert eb comp)))) =
      haltList comp.tm [comp.outputAlphabet.symm (f (b, y))] := by
  have ho := comp.outputsFun (b, y)
  rw [← inWord_eq] at ho
  obtain ⟨hT, -⟩ := outputsInTime_step' comp.tm ho
  have hlen : ((Millennium.pair_encoding eb (Millennium.fin_encoding_string Γ₁)).encode
      (b, y)).length = (eb.encode b).length + 1 + y.length := by
    simp [Millennium.pair_encoding, Millennium.fin_encoding_string]; omega
  have hle : comp.time.eval ((Millennium.pair_encoding eb
      (Millennium.fin_encoding_string Γ₁)).encode (b, y)).length ≤
      (dat eb k comp).PT.eval (gsOf eb b).length := by
    rw [hlen, length_gsOf]
    simp only [dat, eval_comp, eval_add, eval_X, eval_one, eval_pow]
    exact Pnp.TM2Proj.polynomial_eval_mono _ (by omega)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, add_comm, Function.iterate_add_apply, hT]
  exact Function.iterate_fixed (step'_of_halted comp.tm (haltList_l comp.tm _)) d

theorem acc_halt (v : comp.tm.Γ comp.tm.k₁) :
    Tab.Acc (dat eb k comp) (haltList comp.tm [v]) ↔ v = comp.outputAlphabet.symm true := by
  unfold Tab.Acc
  rw [haltList_stk, dif_pos rfl]
  simp [haltList_l, dat]

/-- **Correctness of the reduction.** -/
theorem reduce_iff (R : β → List Γ₁ → Prop) (hf : ∀ p, R p.1 p.2 ↔ f p = true) (b : β) :
    (∃ y : List Γ₁, y.length ≤ (eb.encode b).length ^ k ∧ R b y) ↔
      SATLang ((shape (dat eb k comp)).formula (gsOf eb b)) := by
  rw [tab_sat_iff (by simp [dat])]
  constructor
  · rintro ⟨y, hy, hR⟩
    refine ⟨y.map (cert eb comp), (ok_iff _).2 ⟨y, rfl⟩, ?_, ?_⟩
    · simp only [List.length_map, dat, eval_pow, eval_X, length_gsOf]; exact hy
    · erw [run_eq (comp := comp) b y hy, acc_halt (comp := comp)]
      rw [(hf (b, y))] at hR; rw [hR]
  · rintro ⟨ys, hok, hyl, hacc⟩
    obtain ⟨y, rfl⟩ := (ok_iff _).1 hok
    have hy : y.length ≤ (eb.encode b).length ^ k := by
      simpa [dat, length_gsOf] using hyl
    refine ⟨y, hy, ?_⟩
    erw [run_eq (comp := comp) b y hy, acc_halt (comp := comp)] at hacc
    rw [hf (b, y)]
    exact comp.outputAlphabet.symm.injective hacc

end Verifier

/-- **Cook–Levin, hardness**: every official `NP` language reduces to `SATLang`. -/
theorem sat_np_hard (hgen : GenSpec) {β : Type} (eb : Computability.FinEncoding β)
    (L' : Millennium.Language β) (hL : Millennium.InNondeterministicPolynomialTime eb L') :
    Millennium.PolynomialTimeReducible eb (Millennium.fin_encoding_string SatSym) L' SATLang := by
  obtain ⟨Γ₁, _, R, k, ⟨f, comp, hf⟩, hL⟩ := hL
  let d := dat eb k comp
  obtain ⟨c, kOut, K, g, hg, hgf⟩ := hgen (shape d)
  let F : β → List SatSym := fun b => (shape d).formula (gsOf eb b)
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code eb
    (fun x => oneHotW (Fintype.card eb.Γ) (Fintype.equivFin eb.Γ x)) c kOut K g hg F
    (fun b => by
      show (shape d).formula (gsOf eb b) = _
      rw [← hgf]; congr 1
      show List.flatMap _ ((eb.encode b).map _) = _
      induction eb.encode b with
      | nil => rfl
      | cons x xs ih => rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]; rfl)
  refine ⟨F, hc, fun b => ?_⟩
  rw [hL b]
  exact reduce_iff R (fun p => hf p) b

/-- **Cook–Levin**: `SATLang` is NP-complete (official definitions), given the generator. -/
theorem sat_np_complete_of_gen (hgen : GenSpec) :
    Millennium.NondeterministicPolynomialTimeComplete (Millennium.fin_encoding_string SatSym)
      SATLang :=
  ⟨sat_in_np, fun eb L' hL => sat_np_hard hgen eb L' hL⟩

/-- **Cook–Levin (uniform)**: `SATLang` is NP-complete for the official definitions. -/
theorem sat_np_complete :
    Millennium.NondeterministicPolynomialTimeComplete (Millennium.fin_encoding_string SatSym)
      SATLang :=
  sat_np_complete_of_gen Uniform.generator

end Pnp.CookLevin.NPC
