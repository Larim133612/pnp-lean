import Pnp.CookLevin.ShapeSat
import Pnp.CookLevin.TabLocal

/-!
# The Cook–Levin tableau of a `FinTM2` as a shaped formula (M33)

`Data tm` fixes how an input `gs : List (Fin W)` becomes the input word of the machine `tm`
(`inSym`, then the separator `sepSym`, then a free certificate over the allowed symbols `ok`),
the accepted output symbol `yes` and the polynomials `PM` (certificate capacity), `PT` (time),
`PB` (cells).  `shape d` is the `Shape` (see `Pnp/CookLevin/Shape.lean`) of the tableau formula:
slice `t` of the variables is the encoding `sliceOf` (`Pnp/CookLevin/TabLocal.lean`) of the
configuration at time `t`.

`tab_sat_iff`: the formula is satisfiable iff some certificate of allowed symbols of length
`≤ M` makes the configuration after `T` total steps halted with `yes` on top of the output stack.
-/

namespace Pnp.CookLevin.Tab

open Turing Turing.TM2 Function Pnp.PPoly Pnp.CookLevin Pnp.CookLevin.Uniform SatSym

variable (tm : FinTM2)

attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin FinTM2.kFin

open Classical

/-! ### Patterns -/

/-- The unit clause `x_i = v` (relative position `i`). -/
def unitP (i : ℕ) (v : Bool) : List SatSym := zs i ++ [litOf v]

theorem clauseSat_unitP (z : ℕ → Bool) (a i : ℕ) (v : Bool) :
    ClauseSat z (zs a ++ unitP i v) ↔ z (a + i) = v := by
  unfold unitP
  rw [clauseSat_zs_append, clauseSat_zs_append, clauseSat_litOf]
  simp

/-- All bit lists of length `n`. -/
def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBits n).flatMap fun l => [false :: l, true :: l]

theorem mem_allBits : ∀ {n : ℕ} {l : List Bool}, l ∈ allBits n ↔ l.length = n
  | 0, l => by cases l <;> simp [allBits]
  | n + 1, l => by
    cases l with
    | nil => simp [allBits]
    | cons b l =>
      simp only [allBits, List.mem_flatMap, List.mem_cons, List.length_cons,
        Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨l', hl', h | h | h⟩
        · obtain ⟨-, rfl⟩ := List.cons.inj h; exact mem_allBits.1 hl'
        · obtain ⟨-, rfl⟩ := List.cons.inj h; exact mem_allBits.1 hl'
        · simp at h
      · intro h
        exact ⟨l, mem_allBits.2 h, by cases b <;> simp⟩

/-- A family of step clauses over all assignments of a block forces the target bit. -/
theorem stepFam_iff (z : ℕ → Bool) (a L g : ℕ) (G : List Bool → Bool) :
    (∀ α ∈ allBits L, ClauseSat z (zs a ++ negPat α ++ zs g ++ [litOf (G α)])) ↔
      z (a + L + g) = G (blk (fun i => z (a + i)) L) := by
  have key : ∀ α : List Bool, α.length = L →
      (ClauseSat z (zs a ++ negPat α ++ zs g ++ [litOf (G α)]) ↔
        blk (fun i => z (a + i)) L ≠ α ∨ z (a + L + g) = G α) := by
    intro α hα
    have hl : (negPat α).length = L := by simp [negPat, hα]
    simp only [List.append_assoc]
    rw [clauseSat_zs_append, Uniform.clauseSat_append, clauseSat_negPat, clauseSat_zs_append,
      clauseSat_litOf, hl, hα]
    simp only [Nat.add_zero, Nat.add_assoc]
  constructor
  · intro h
    have hl := length_blk (fun i => z (a + i)) L
    have := (key _ hl).1 (h _ (mem_allBits.2 hl))
    simpa using this
  · intro h α hα
    rw [key α (mem_allBits.1 hα)]
    by_cases he : blk (fun i => z (a + i)) L = α
    · right; rw [h, he]
    · left; exact he

/-- Two-block version. -/
theorem stepFam₂_iff (z : ℕ → Bool) (a L₁ g₁ L₂ g₂ : ℕ) (G : List Bool → List Bool → Bool) :
    (∀ α₁ ∈ allBits L₁, ∀ α₂ ∈ allBits L₂,
      ClauseSat z (zs a ++ negPat α₁ ++ zs g₁ ++ negPat α₂ ++ zs g₂ ++ [litOf (G α₁ α₂)])) ↔
      z (a + L₁ + g₁ + L₂ + g₂) =
        G (blk (fun i => z (a + i)) L₁) (blk (fun i => z (a + L₁ + g₁ + i)) L₂) := by
  have key : ∀ α₁ α₂ : List Bool, α₁.length = L₁ → α₂.length = L₂ →
      (ClauseSat z (zs a ++ negPat α₁ ++ zs g₁ ++ negPat α₂ ++ zs g₂ ++ [litOf (G α₁ α₂)]) ↔
        blk (fun i => z (a + i)) L₁ ≠ α₁ ∨ blk (fun i => z (a + L₁ + g₁ + i)) L₂ ≠ α₂ ∨
          z (a + L₁ + g₁ + L₂ + g₂) = G α₁ α₂) := by
    intro α₁ α₂ h₁ h₂
    have hl₁ : (negPat α₁).length = L₁ := by simp [negPat, h₁]
    have hl₂ : (negPat α₂).length = L₂ := by simp [negPat, h₂]
    simp only [List.append_assoc]
    rw [clauseSat_zs_append, Uniform.clauseSat_append, clauseSat_negPat, clauseSat_zs_append,
      Uniform.clauseSat_append, clauseSat_negPat, clauseSat_zs_append, clauseSat_litOf, hl₁, hl₂, h₁, h₂]
    simp only [Nat.add_zero, Nat.add_assoc]
  constructor
  · intro h
    have hl₁ := length_blk (fun i => z (a + i)) L₁
    have hl₂ := length_blk (fun i => z (a + L₁ + g₁ + i)) L₂
    have := (key _ _ hl₁ hl₂).1 (h _ (mem_allBits.2 hl₁) _ (mem_allBits.2 hl₂))
    simpa using this
  · intro h α₁ hα₁ α₂ hα₂
    rw [key α₁ α₂ (mem_allBits.1 hα₁) (mem_allBits.1 hα₂)]
    by_cases he₁ : blk (fun i => z (a + i)) L₁ = α₁
    · by_cases he₂ : blk (fun i => z (a + L₁ + g₁ + i)) L₂ = α₂
      · right; right; rw [h, he₁, he₂]
      · right; left; exact he₂
    · left; exact he₁

/-! ### The shape of the tableau -/

/-- How inputs become machine words, and what is accepted. -/
structure Data where
  W : ℕ
  inSym : Fin W → tm.Γ tm.k₀
  sepSym : tm.Γ tm.k₀
  ok : tm.Γ tm.k₀ → Prop
  yes : tm.Γ tm.k₁
  PM : Polynomial ℕ
  PT : Polynomial ℕ
  PB : Polynomial ℕ

/-- Position of the bit `o` of stack `k₀` inside a column. -/
noncomputable def pk (o : Option (A tm tm.k₀)) : ℕ := eC tm ⟨tm.k₀, o⟩

/-- Unit clauses inside a column. -/
noncomputable def colUnits (P : CI tm → Option Bool) : List (List SatSym) :=
  (Finset.univ.toList : List (CI tm)).filterMap fun β => (P β).map (unitP (eC tm β))

/-- Unit clauses inside the `k₀` block of a column. -/
noncomputable def k0Units (P : Option (A tm tm.k₀) → Option Bool) : List (List SatSym) :=
  (Finset.univ.toList : List (Option (A tm tm.k₀))).filterMap fun o => (P o).map (unitP (pk tm o))

theorem forall_colUnits (P : CI tm → Option Bool) (Q : List SatSym → Prop) :
    (∀ c ∈ colUnits tm P, Q c) ↔ ∀ β v, P β = some v → Q (unitP (eC tm β) v) := by
  simp only [colUnits, List.mem_filterMap, Finset.mem_toList, Finset.mem_univ, true_and,
    Option.map_eq_some_iff]
  constructor
  · intro h β v hv; exact h _ ⟨β, v, hv, rfl⟩
  · rintro h c ⟨β, v, hv, rfl⟩; exact h β v hv

theorem forall_k0Units (P : Option (A tm tm.k₀) → Option Bool) (Q : List SatSym → Prop) :
    (∀ c ∈ k0Units tm P, Q c) ↔ ∀ o v, P o = some v → Q (unitP (pk tm o) v) := by
  simp only [k0Units, List.mem_filterMap, Finset.mem_toList, Finset.mem_univ, true_and,
    Option.map_eq_some_iff]
  constructor
  · intro h o v hv; exact h _ ⟨o, v, hv, rfl⟩
  · rintro h c ⟨o, v, hv, rfl⟩; exact h o v hv

variable {tm} (d : Data tm)

/-- Allowed certificate cells. -/
def okO (o : Option (A tm tm.k₀)) : Prop := ∀ x ∈ o, d.ok x.val

/-- The all-`none` cells. -/
def noneCells : ∀ k, Option (tm.Γ k) := fun _ => none

/-- Cells with `x` on stack `k₀` only. -/
def k0Cells (x : Option (tm.Γ tm.k₀)) : ∀ k, Option (tm.Γ k) :=
  fun k => if h : k = tm.k₀ then h ▸ x else none

variable (tm) in
/-- At-least-one clause over the allowed values of the `k₀` block. -/
noncomputable def aloP (d : Data tm) : List SatSym :=
  (List.range (w tm)).map fun b => if ∃ o, okO d o ∧ pk tm o = b then pos else zero

variable (tm) in
/-- At-most-one clauses of the `k₀` block. -/
noncomputable def amoP : List (List SatSym) :=
  (Finset.univ.toList : List (Option (A tm tm.k₀) × Option (A tm tm.k₀))).filterMap fun p =>
    if pk tm p.1 < pk tm p.2 then
      some (zs (pk tm p.1) ++ [neg] ++ zs (pk tm p.2 - pk tm p.1 - 1) ++ [neg])
    else none

variable (tm) in
/-- `none` in this column implies `none` in the next column. -/
noncomputable def propP : List SatSym := zs (pk tm none) ++ [neg] ++ zs (w tm - 1) ++ [pos]

/-- **The shape of the tableau formula.** -/
noncomputable def shape : Shape where
  W := d.W
  w := w tm
  L1 := L1 tm
  D := Dp tm
  PM := d.PM
  PT := d.PT
  PB := d.PB
  init0 := (List.range (c0 tm)).map fun i => unitP i (encCtrl tm (some tm.main) tm.initialState i)
  initCol := colUnits tm fun β => if β.1 ≠ tm.k₀ then some (encCol tm noneCells (eC tm β)) else none
  inCol g := k0Units tm fun o => some (decide (o = code tm (some (d.inSym g))))
  sepCol := k0Units tm fun o => some (decide (o = code tm (some d.sepSym)))
  certCol := k0Units tm (fun o => if okO d o then none else some false) ++ [aloP tm d] ++
    amoP tm ++ [propP tm]
  boundCol := [unitP (pk tm none) true]
  sliceCls := (List.range (Dp tm * w tm)).map (fun i => unitP (L1 tm + i) false) ++
    (List.range (Dp tm * w tm)).flatMap fun i =>
      [zs (c0 tm + i) ++ [neg] ++ zs (2 * Dp tm * w tm - 1) ++ [pos],
       zs (c0 tm + i) ++ [pos] ++ zs (2 * Dp tm * w tm - 1) ++ [neg]]
  rpadCls := (List.range (Dp tm * w tm)).map fun i => unitP i (encCol tm noneCells (i % w tm))
  stepC := (Finset.univ.toList : List (CtI tm)).flatMap fun e =>
    (allBits (L1 tm)).map fun α => (negPat α, 2 * Dp tm * w tm + eT tm e, litOf (gC tm e α))
  stepX := (Finset.univ.toList : List (CI tm)).flatMap fun β =>
    (allBits (L1 tm)).flatMap fun α₁ => (allBits ((2 * Dp tm + 1) * w tm)).map fun α₂ =>
      (negPat α₁, negPat α₂, L1 tm + (Dp tm - 1) * w tm + eC tm β, litOf (gX tm β.1 β.2 α₁ α₂))
  acc := unitP (eT tm (.inl none)) true ::
    (if h : d.yes ∈ A tm tm.k₁ then [unitP (L1 tm + Dp tm * w tm + eC tm ⟨tm.k₁, some ⟨d.yes, h⟩⟩) true]
     else [[]])

/-! ### No separators inside the patterns -/

theorem sep_nmem_unitP (i : ℕ) (v : Bool) : sep ∉ unitP i v := by
  simp only [unitP, List.mem_append, List.mem_replicate, List.mem_singleton, not_or]
  exact ⟨by simp, by cases v <;> simp [litOf]⟩

theorem sep_nmem_negPat (α : List Bool) : sep ∉ negPat α := by
  simp only [negPat, List.mem_map, not_exists, not_and]
  intro b _; cases b <;> simp

theorem litOf_ne_sep (v : Bool) : litOf v ≠ sep := by cases v <;> simp [litOf]

theorem shape_noSep : (shape d).NoSep := by
  have hcu : ∀ P, ∀ c ∈ colUnits tm P, sep ∉ c := fun P =>
    (forall_colUnits tm P (fun c => sep ∉ c)).2 fun β v _ => sep_nmem_unitP _ _
  have hku : ∀ P, ∀ c ∈ k0Units tm P, sep ∉ c := fun P =>
    (forall_k0Units tm P (fun c => sep ∉ c)).2 fun o v _ => sep_nmem_unitP _ _
  refine ⟨?_, hcu _, fun g => hku _, hku _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [shape, List.mem_map, List.mem_range]
    rintro c ⟨i, -, rfl⟩; exact sep_nmem_unitP _ _
  · intro c hc
    simp only [shape, List.mem_append, List.mem_singleton] at hc
    rcases hc with ((hc | rfl) | hc) | rfl
    · exact hku _ c hc
    · simp only [aloP, List.mem_map, not_exists, not_and]
      intro b _; split_ifs <;> simp
    · simp only [amoP, List.mem_filterMap] at hc
      obtain ⟨p, -, hp⟩ := hc
      split_ifs at hp
      obtain rfl := Option.some.inj hp
      simp [List.mem_replicate]
    · simp [propP, List.mem_replicate]
  · simp only [shape, List.mem_singleton]; rintro c rfl; exact sep_nmem_unitP _ _
  · intro c hc
    simp only [shape, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
      List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with ⟨i, -, rfl⟩ | ⟨i, -, rfl | rfl⟩
    · exact sep_nmem_unitP _ _
    · simp [List.mem_replicate]
    · simp [List.mem_replicate]
  · simp only [shape, List.mem_map, List.mem_range]
    rintro c ⟨i, -, rfl⟩; exact sep_nmem_unitP _ _
  · simp only [shape, List.mem_flatMap, List.mem_map]
    rintro p ⟨e, -, α, -, rfl⟩; exact ⟨sep_nmem_negPat _, litOf_ne_sep _⟩
  · simp only [shape, List.mem_flatMap, List.mem_map]
    rintro p ⟨β, -, α₁, -, α₂, -, rfl⟩
    exact ⟨sep_nmem_negPat _, sep_nmem_negPat _, litOf_ne_sep _⟩
  · intro c hc
    simp only [shape, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact sep_nmem_unitP _ _
    · split_ifs at hc <;> simp_all [sep_nmem_unitP]

/-! ### The clause families, evaluated -/

section Fam

variable (z : ℕ → Bool)

theorem fam_init0 : (∀ c ∈ (shape d).init0, ClauseSat z (zs 0 ++ c)) ↔
    ∀ i < c0 tm, z i = encCtrl tm (some tm.main) tm.initialState i := by
  simp only [shape, List.forall_mem_map, List.mem_range, clauseSat_unitP, zero_add]

theorem fam_initCol (a : ℕ) : (∀ c ∈ (shape d).initCol, ClauseSat z (zs a ++ c)) ↔
    ∀ β : CI tm, β.1 ≠ tm.k₀ → z (a + eC tm β) = encCol tm noneCells (eC tm β) := by
  simp only [shape]
  rw [forall_colUnits]
  simp only [clauseSat_unitP]
  constructor
  · intro h β hβ; exact h β _ (by simp [hβ])
  · intro h β v hv
    split_ifs at hv with hβ
    obtain rfl := Option.some.inj hv
    exact h β hβ

theorem fam_k0 (a : ℕ) (P : Option (A tm tm.k₀) → Option Bool) :
    (∀ c ∈ k0Units tm P, ClauseSat z (zs a ++ c)) ↔ ∀ o v, P o = some v → z (a + pk tm o) = v := by
  rw [forall_k0Units]; simp only [clauseSat_unitP]

theorem fam_inCol (a : ℕ) (g : Fin d.W) : (∀ c ∈ (shape d).inCol g, ClauseSat z (zs a ++ c)) ↔
    ∀ o, z (a + pk tm o) = decide (o = code tm (some (d.inSym g))) := by
  simp only [shape]
  rw [fam_k0]
  exact ⟨fun h o => h o _ rfl, fun h o v hv => (Option.some.inj hv) ▸ h o⟩

theorem fam_sepCol (a : ℕ) : (∀ c ∈ (shape d).sepCol, ClauseSat z (zs a ++ c)) ↔
    ∀ o, z (a + pk tm o) = decide (o = code tm (some d.sepSym)) := by
  simp only [shape]
  rw [fam_k0]
  exact ⟨fun h o => h o _ rfl, fun h o v hv => (Option.some.inj hv) ▸ h o⟩

theorem pk_lt (o : Option (A tm tm.k₀)) : pk tm o < w tm := (eC tm _).isLt

theorem pk_injective : Function.Injective (pk tm) := by
  intro o o' h
  have := (eC tm).injective (Fin.ext h)
  simpa using this

/-- Exactly-one and propagation constraints of a certificate column. -/
structure CertOK (a : ℕ) : Prop where
  forbid : ∀ o, ¬ okO d o → z (a + pk tm o) = false
  alo : ∃ o, okO d o ∧ z (a + pk tm o) = true
  amo : ∀ o o', z (a + pk tm o) = true → z (a + pk tm o') = true → o = o'
  prop : z (a + pk tm none) = true → z (a + w tm + pk tm none) = true

theorem fam_cert (a : ℕ) : (∀ c ∈ (shape d).certCol, ClauseSat z (zs a ++ c)) ↔ CertOK d z a := by
  simp only [shape, List.forall_mem_append, List.forall_mem_singleton, fam_k0]
  have halo : ClauseSat z (zs a ++ aloP tm d) ↔ ∃ o, okO d o ∧ z (a + pk tm o) = true := by
    rw [clauseSat_zs_append, clauseSat_iff_getElem]
    simp only [aloP, List.length_map, List.length_range, List.getElem_map, List.getElem_range]
    constructor
    · rintro ⟨j, hj, h⟩
      split_ifs at h with hc
      · obtain ⟨o, ho, rfl⟩ := hc; exact ⟨o, ho, h⟩
      · exact absurd h (by simp [litTrue])
    · rintro ⟨o, ho, h⟩
      exact ⟨pk tm o, pk_lt o, by rw [if_pos ⟨o, ho, rfl⟩]; exact h⟩
  have hamo : (∀ c ∈ amoP tm, ClauseSat z (zs a ++ c)) ↔
      ∀ o o', z (a + pk tm o) = true → z (a + pk tm o') = true → o = o' := by
    have hc : ∀ o o', pk tm o < pk tm o' →
        (ClauseSat z (zs a ++ (zs (pk tm o) ++ [neg] ++ zs (pk tm o' - pk tm o - 1) ++ [neg])) ↔
          z (a + pk tm o) = false ∨ z (a + pk tm o') = false) := by
      intro o o' hlt
      simp only [List.append_assoc]
      rw [clauseSat_zs_append, clauseSat_zs_append, Uniform.clauseSat_append,
        clauseSat_zs_append]
      have e1 : ClauseSat (fun i => z (a + (pk tm o + i))) [neg] ↔ z (a + pk tm o) = false := by
        rw [show [neg] = [litOf false] from rfl, clauseSat_litOf]
        simp only [Nat.add_zero]
      rw [e1, List.length_singleton]
      have e2 : ClauseSat (fun i => z (a + (pk tm o + (1 + (pk tm o' - pk tm o - 1 + i))))) [neg] ↔
          z (a + pk tm o') = false := by
        rw [show [neg] = [litOf false] from rfl, clauseSat_litOf]
        simp only [Nat.add_zero]
        rw [show pk tm o + (1 + (pk tm o' - pk tm o - 1)) = pk tm o' by omega]
      exact or_congr Iff.rfl e2
    simp only [amoP, List.mem_filterMap, Finset.mem_toList, Finset.mem_univ, true_and]
    constructor
    · intro h o o' h1 h2
      by_contra hne
      rcases lt_trichotomy (pk tm o) (pk tm o') with hlt | heq | hgt
      · have := (hc o o' hlt).1 (h _ ⟨(o, o'), by simp only [if_pos hlt]⟩)
        rcases this with h' | h'
        · rw [h1] at h'; exact Bool.noConfusion h'
        · rw [h2] at h'; exact Bool.noConfusion h'
      · exact hne (pk_injective heq)
      · have := (hc o' o hgt).1 (h _ ⟨(o', o), by simp only [if_pos hgt]⟩)
        rcases this with h' | h'
        · rw [h2] at h'; exact Bool.noConfusion h'
        · rw [h1] at h'; exact Bool.noConfusion h'
    · rintro h c ⟨⟨o, o'⟩, hp⟩
      split_ifs at hp with hlt
      obtain rfl := Option.some.inj hp
      rw [hc o o' hlt]
      rcases Bool.eq_false_or_eq_true (z (a + pk tm o)) with h1 | h1
      · rcases Bool.eq_false_or_eq_true (z (a + pk tm o')) with h2 | h2
        · have := h o o' h1 h2; subst this; exact absurd hlt (lt_irrefl _)
        · exact Or.inr h2
      · exact Or.inl h1
  have hprop : ClauseSat z (zs a ++ propP tm) ↔
      (z (a + pk tm none) = true → z (a + w tm + pk tm none) = true) := by
    unfold propP
    simp only [List.append_assoc]
    rw [clauseSat_zs_append, clauseSat_zs_append, Uniform.clauseSat_append, clauseSat_zs_append,
      show [neg] = [litOf false] from rfl, show [pos] = [litOf true] from rfl, clauseSat_litOf,
      clauseSat_litOf, List.length_singleton]
    have hw := w_pos tm
    simp only [Nat.add_zero]
    rw [show pk tm none + (1 + (w tm - 1)) = w tm + pk tm none by omega, ← Nat.add_assoc]
    cases z (a + pk tm none) <;> simp
  rw [halo, hamo, hprop]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨fun o ho => h1 o false (by simp [ho]), h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨fun o v hv => ?_, h2⟩, h3⟩, h4⟩
    split_ifs at hv with ho
    obtain rfl := Option.some.inj hv
    exact h1 o ho

theorem fam_bound (a : ℕ) : (∀ c ∈ (shape d).boundCol, ClauseSat z (zs a ++ c)) ↔
    z (a + pk tm none) = true := by
  simp [shape, clauseSat_unitP]

theorem fam_slice (a : ℕ) : (∀ c ∈ (shape d).sliceCls, ClauseSat z (zs a ++ c)) ↔
    (∀ i < Dp tm * w tm, z (a + (L1 tm + i)) = false) ∧
    (∀ i < Dp tm * w tm, z (a + (c0 tm + i)) = z (a + (c0 tm + i + 2 * Dp tm * w tm))) := by
  have hpos : 0 < Dp tm * w tm := Nat.mul_pos (by unfold Dp; omega) (w_pos tm)
  have h2 : 2 * Dp tm * w tm = 2 * (Dp tm * w tm) := by ring
  simp only [shape, List.forall_mem_append, List.forall_mem_map, List.forall_mem_flatMap,
    List.mem_range, List.forall_mem_cons, clauseSat_unitP]
  refine and_congr Iff.rfl (forall₂_congr fun i hi => ?_)
  have key : ∀ v : Bool, ClauseSat z (zs a ++ (zs (c0 tm + i) ++ [litOf v] ++
      zs (2 * Dp tm * w tm - 1) ++ [litOf (!v)])) ↔
      z (a + (c0 tm + i)) = v ∨ z (a + (c0 tm + i + 2 * Dp tm * w tm)) = !v := by
    intro v
    simp only [List.append_assoc]
    rw [clauseSat_zs_append, clauseSat_zs_append, Uniform.clauseSat_append, clauseSat_zs_append,
      clauseSat_litOf, clauseSat_litOf, List.length_singleton]
    simp only [Nat.add_zero]
    rw [show c0 tm + i + (1 + (2 * Dp tm * w tm - 1)) = c0 tm + i + 2 * Dp tm * w tm by omega]
  have k1 := key false
  have k2 := key true
  simp only [Bool.not_false, Bool.not_true] at k1 k2
  rw [show [neg] = [litOf false] from rfl, show [pos] = [litOf true] from rfl, k1, k2]
  cases z (a + (c0 tm + i)) <;> cases z (a + (c0 tm + i + 2 * Dp tm * w tm)) <;> simp

theorem fam_rpad (a : ℕ) : (∀ c ∈ (shape d).rpadCls, ClauseSat z (zs a ++ c)) ↔
    ∀ i < Dp tm * w tm, z (a + i) = encCol tm noneCells (i % w tm) := by
  simp [shape, clauseSat_unitP]

theorem fam_stepC (a B : ℕ) : (∀ p ∈ (shape d).stepC,
      ClauseSat z (zs a ++ p.1 ++ zs (B * w tm + p.2.1) ++ [p.2.2])) ↔
    ∀ e : CtI tm, z (a + L1 tm + (B * w tm + (2 * Dp tm * w tm + eT tm e))) =
      gC tm e (blk (fun i => z (a + i)) (L1 tm)) := by
  simp only [shape, List.forall_mem_flatMap, List.forall_mem_map, Finset.mem_toList,
    Finset.mem_univ, true_imp_iff]
  refine forall_congr' fun e => ?_
  have := stepFam_iff z a (L1 tm) (B * w tm + (2 * Dp tm * w tm + eT tm e)) (gC tm e)
  simpa [Nat.add_assoc] using this

theorem fam_stepX (a j B : ℕ) : (∀ p ∈ (shape d).stepX,
      ClauseSat z (zs a ++ p.1 ++ zs (j * w tm) ++ p.2.1 ++ zs (B * w tm + p.2.2.1) ++ [p.2.2.2])) ↔
    ∀ β : CI tm, z (a + L1 tm + j * w tm + (2 * Dp tm + 1) * w tm +
        (B * w tm + (L1 tm + (Dp tm - 1) * w tm + eC tm β))) =
      gX tm β.1 β.2 (blk (fun i => z (a + i)) (L1 tm))
        (blk (fun i => z (a + L1 tm + j * w tm + i)) ((2 * Dp tm + 1) * w tm)) := by
  simp only [shape, List.forall_mem_flatMap, List.forall_mem_map, Finset.mem_toList,
    Finset.mem_univ, true_imp_iff]
  refine forall_congr' fun β => ?_
  exact stepFam₂_iff z a (L1 tm) (j * w tm) ((2 * Dp tm + 1) * w tm)
    (B * w tm + (L1 tm + (Dp tm - 1) * w tm + eC tm β)) (gX tm β.1 β.2)

theorem fam_acc (a : ℕ) : (∀ c ∈ (shape d).acc, ClauseSat z (zs a ++ c)) ↔
    z (a + eT tm (.inl none)) = true ∧
      ∃ h : d.yes ∈ A tm tm.k₁,
        z (a + (L1 tm + Dp tm * w tm + eC tm ⟨tm.k₁, some ⟨d.yes, h⟩⟩)) = true := by
  simp only [shape, List.forall_mem_cons, clauseSat_unitP]
  refine and_congr Iff.rfl ?_
  split_ifs with h
  · simp [clauseSat_unitP, h]
  · simp only [List.forall_mem_singleton, List.append_nil, h, IsEmpty.exists_iff, iff_false]
    exact clauseSat_zs z a

end Fam

/-! ### Slices of an assignment -/

section Slices

variable (tm)

/-- Slice length. -/
noncomputable def SL (B : ℕ) : ℕ := L1 tm + (B + 2 * Dp tm) * w tm

theorem SL_eq (B : ℕ) : SL tm B = L1 tm + B * w tm + 2 * Dp tm * w tm := by
  unfold SL; ring

theorem one_le_Dp : 1 ≤ Dp tm := by unfold Dp; omega

/-- Slice `t` of `z` is the encoding of `c`. -/
def SliceEq (z : ℕ → Bool) (B t : ℕ) (c : tm.Cfg) : Prop :=
  ∀ i < SL tm B, z (t * SL tm B + i) = sliceOf tm c i

variable {tm}

theorem cellsAt_none {c : tm.Cfg} {B j : ℕ} (hlen : ∀ k, ((c : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤ B)
    (hj : B ≤ j) : cellsAt tm c j = noneCells := by
  funext k
  unfold cellsAt noneCells
  exact List.getElem?_eq_none (by have := hlen k; omega)

theorem colOf_right {c : tm.Cfg} {B q : ℕ}
    (hlen : ∀ k, ((c : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤ B) (hq : Dp tm + B ≤ q) :
    colOf tm c q = encCol tm noneCells := by
  unfold colOf
  rw [if_pos (by omega), cellsAt_none hlen (by omega)]

theorem colOf_left {c : tm.Cfg} {q : ℕ} (hq : q < Dp tm) : colOf tm c q = fun _ => false := by
  unfold colOf; rw [if_neg (by omega)]

/-- Decomposition of a position in the column area. -/
theorem col_decomp (i : ℕ) : i = i / w tm * w tm + i % w tm := by
  rw [Nat.mul_comm]; exact (Nat.div_add_mod i (w tm)).symm

theorem mod_lt' (i : ℕ) : i % w tm < w tm := Nat.mod_lt _ (w_pos tm)

/-- Slice equality from the columns. -/
theorem sliceEq_of_cols {z : ℕ → Bool} {B t : ℕ} {c : tm.Cfg}
    (hctrl : ∀ i < c0 tm, z (t * SL tm B + i) = sliceOf tm c i)
    (hcol : ∀ q < B + 2 * Dp tm, ∀ b < w tm, z (t * SL tm B + (L1 tm + q * w tm + b)) = colOf tm c q b)
    (hcopy : ∀ i < Dp tm * w tm, z (t * SL tm B + (c0 tm + i)) =
      z (t * SL tm B + (c0 tm + i + 2 * Dp tm * w tm))) :
    SliceEq tm z B t c := by
  intro i hi
  by_cases h0 : i < c0 tm
  · exact hctrl i h0
  by_cases h1 : i < L1 tm
  · -- copy columns
    obtain ⟨i', rfl⟩ : ∃ i', i = c0 tm + i' := ⟨i - c0 tm, by omega⟩
    have hi' : i' < Dp tm * w tm := by unfold L1 at h1; omega
    rw [hcopy i' hi']
    have hq : i' / w tm < Dp tm := by
      rw [Nat.div_lt_iff_lt_mul (w_pos tm)]; exact hi'
    have e := col_decomp (tm := tm) i'
    have hpos : c0 tm + i' + 2 * Dp tm * w tm = L1 tm + (Dp tm + i' / w tm) * w tm + i' % w tm := by
      unfold L1
      have : (Dp tm + i' / w tm) * w tm = Dp tm * w tm + i' / w tm * w tm := by ring
      have h2 : 2 * Dp tm * w tm = Dp tm * w tm + Dp tm * w tm := by ring
      omega
    rw [hpos, hcol _ (by omega) _ (mod_lt' _),
      show c0 tm + i' = c0 tm + i' / w tm * w tm + i' % w tm by omega,
      sliceOf_copy tm c hq (mod_lt' _)]
  · obtain ⟨i', rfl⟩ : ∃ i', i = L1 tm + i' := ⟨i - L1 tm, by omega⟩
    have hq : i' / w tm < B + 2 * Dp tm := by
      rw [Nat.div_lt_iff_lt_mul (w_pos tm)]; unfold SL at hi; omega
    have e := col_decomp (tm := tm) i'
    rw [show L1 tm + i' = L1 tm + i' / w tm * w tm + i' % w tm by omega,
      hcol _ hq _ (mod_lt' _), sliceOf_col tm c _ (mod_lt' _)]

/-- The columns of a slice from the families `initCol`-like data. -/
theorem cols_of {z : ℕ → Bool} {B t : ℕ} {c : tm.Cfg}
    (hlen : ∀ k, ((c : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤ B)
    (hreal : ∀ j < B, ∀ β : CI tm, z (t * SL tm B + (L1 tm + (Dp tm + j) * w tm + eC tm β)) =
      decide (code tm (cellsAt tm c j β.1) = β.2))
    (hleft : ∀ i < Dp tm * w tm, z (t * SL tm B + (L1 tm + i)) = false)
    (hright : ∀ i < Dp tm * w tm,
      z (t * SL tm B + (L1 tm + (Dp tm + B) * w tm) + i) = encCol tm noneCells (i % w tm)) :
    ∀ q < B + 2 * Dp tm, ∀ b < w tm, z (t * SL tm B + (L1 tm + q * w tm + b)) = colOf tm c q b := by
  intro q hq b hb
  by_cases h1 : q < Dp tm
  · rw [colOf_left h1, Nat.add_assoc, hleft _ ?_]
    have := Nat.mul_le_mul_right (w tm) (Nat.succ_le_of_lt h1)
    rw [Nat.succ_mul] at this; omega
  by_cases h2 : q < Dp tm + B
  · obtain ⟨j, rfl⟩ : ∃ j, q = Dp tm + j := ⟨q - Dp tm, by omega⟩
    have := hreal j (by omega) ((eC tm).symm ⟨b, hb⟩)
    simp only [Equiv.apply_symm_apply] at this
    rw [this]
    unfold colOf
    rw [if_pos (by omega), Nat.add_sub_cancel_left]
    unfold encCol
    rw [dif_pos hb]
  · obtain ⟨r, rfl⟩ : ∃ r, q = Dp tm + B + r := ⟨q - (Dp tm + B), by omega⟩
    have hr : r < Dp tm := by omega
    have hlt : r * w tm + b < Dp tm * w tm := by
      have := Nat.mul_le_mul_right (w tm) (Nat.succ_le_of_lt hr)
      rw [Nat.succ_mul] at this; omega
    have := hright _ hlt
    rw [show t * SL tm B + (L1 tm + (Dp tm + B) * w tm) + (r * w tm + b) =
      t * SL tm B + (L1 tm + (Dp tm + B + r) * w tm + b) by ring] at this
    rw [this, colOf_right hlen (by omega)]
    congr 1
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem pos_ctrl (B t e : ℕ) : t * SL tm B + L1 tm + (B * w tm + (2 * Dp tm * w tm + e)) =
    (t + 1) * SL tm B + e := by
  rw [SL_eq]; ring

theorem pos_cell (B t j b : ℕ) : t * SL tm B + L1 tm + j * w tm + (2 * Dp tm + 1) * w tm +
      (B * w tm + (L1 tm + (Dp tm - 1) * w tm + b)) =
    (t + 1) * SL tm B + (L1 tm + (Dp tm + j) * w tm + b) := by
  rw [SL_eq]
  obtain ⟨D', hD⟩ : ∃ D', Dp tm = D' + 1 := ⟨D tm, rfl⟩
  rw [hD, Nat.add_sub_cancel]; ring

theorem blk_slice {z : ℕ → Bool} {B t : ℕ} {c : tm.Cfg} (h : SliceEq tm z B t c) :
    blk (fun i => z (t * SL tm B + i)) (L1 tm) = blk₁ tm c := by
  unfold blk blk₁
  refine List.map_congr_left fun i hi => h i ?_
  rw [List.mem_range] at hi; unfold SL; omega

theorem win_slice {z : ℕ → Bool} {B t : ℕ} {c : tm.Cfg} (h : SliceEq tm z B t c) {j : ℕ}
    (hj : j < B) :
    blk (fun i => z (t * SL tm B + L1 tm + j * w tm + i)) ((2 * Dp tm + 1) * w tm) = win tm c j := by
  unfold blk win
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [show t * SL tm B + L1 tm + j * w tm + i = t * SL tm B + (L1 tm + j * w tm + i) by ring]
  refine h _ ?_
  have : (j + (2 * Dp tm + 1)) * w tm ≤ (B + 2 * Dp tm) * w tm :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (j + (2 * Dp tm + 1)) * w tm = j * w tm + (2 * Dp tm + 1) * w tm := by ring
  unfold SL; omega

/-- **Forward step**: the step clauses force slice `t + 1` (control and real cells). -/
theorem step_fwd {z : ℕ → Bool} {B t : ℕ} {c : tm.Cfg} (h : SliceEq tm z B t c) (hc : Valid tm c)
    (hC : ∀ e : CtI tm, z (t * SL tm B + L1 tm + (B * w tm + (2 * Dp tm * w tm + eT tm e))) =
      gC tm e (blk (fun i => z (t * SL tm B + i)) (L1 tm)))
    (hX : ∀ j < B, ∀ β : CI tm, z (t * SL tm B + L1 tm + j * w tm + (2 * Dp tm + 1) * w tm +
        (B * w tm + (L1 tm + (Dp tm - 1) * w tm + eC tm β))) =
      gX tm β.1 β.2 (blk (fun i => z (t * SL tm B + i)) (L1 tm))
        (blk (fun i => z (t * SL tm B + L1 tm + j * w tm + i)) ((2 * Dp tm + 1) * w tm))) :
    (∀ i < c0 tm, z ((t + 1) * SL tm B + i) = sliceOf tm (step' tm c) i) ∧
    (∀ j < B, ∀ β : CI tm, z ((t + 1) * SL tm B + (L1 tm + (Dp tm + j) * w tm + eC tm β)) =
      decide (code tm (cellsAt tm (step' tm c) j β.1) = β.2)) := by
  constructor
  · intro i hi
    have := hC ((eT tm).symm ⟨i, hi⟩)
    simp only [Equiv.apply_symm_apply] at this
    rw [pos_ctrl, blk_slice h, gC_slice tm hc] at this
    simpa using this
  · intro j hj β
    have := hX j hj β
    rw [pos_cell, blk_slice h, win_slice h hj, gX_slice tm hc] at this
    rw [this, sliceOf_col tm _ _ (eC tm β).isLt]
    unfold colOf
    rw [if_pos (by omega), Nat.add_sub_cancel_left, encCol_eC]

/-- **Backward step**: consecutive encoded slices satisfy the step clauses. -/
theorem step_bwd {z : ℕ → Bool} {B t : ℕ} {c : tm.Cfg} (h : SliceEq tm z B t c) (hc : Valid tm c)
    (h' : SliceEq tm z B (t + 1) (step' tm c)) :
    (∀ e : CtI tm, z (t * SL tm B + L1 tm + (B * w tm + (2 * Dp tm * w tm + eT tm e))) =
      gC tm e (blk (fun i => z (t * SL tm B + i)) (L1 tm))) ∧
    (∀ j < B, ∀ β : CI tm, z (t * SL tm B + L1 tm + j * w tm + (2 * Dp tm + 1) * w tm +
        (B * w tm + (L1 tm + (Dp tm - 1) * w tm + eC tm β))) =
      gX tm β.1 β.2 (blk (fun i => z (t * SL tm B + i)) (L1 tm))
        (blk (fun i => z (t * SL tm B + L1 tm + j * w tm + i)) ((2 * Dp tm + 1) * w tm))) := by
  constructor
  · intro e
    rw [pos_ctrl, blk_slice h, gC_slice tm hc]
    refine h' _ ?_
    have := (eT tm e).isLt; unfold SL L1; omega
  · intro j hj β
    rw [pos_cell, blk_slice h, win_slice h hj, gX_slice tm hc]
    refine h' _ ?_
    have := (eC tm β).isLt
    have h2 : (Dp tm + j + 1) * w tm ≤ (B + 2 * Dp tm) * w tm := Nat.mul_le_mul_right _ (by omega)
    have e : (Dp tm + j + 1) * w tm = (Dp tm + j) * w tm + w tm := by ring
    unfold SL; omega

end Slices

/-! ### Certificates read from cells -/

theorem prefixList_getElem?_of {β : Type*} : ∀ (N : ℕ) (f : ℕ → Option β) (X : ℕ), N < X →
    (∀ m, m + 1 < X → f m = none → f (m + 1) = none) → f N = none →
    ∀ m < X, (prefixList f N)[m]? = f m := by
  have hall : ∀ (f : ℕ → Option β) (X : ℕ), (∀ m, m + 1 < X → f m = none → f (m + 1) = none) →
      f 0 = none → ∀ m < X, f m = none := by
    intro f X hmono h0 m hm
    induction m with
    | zero => exact h0
    | succ m ih => exact hmono m hm (ih (by omega))
  intro N
  induction N with
  | zero =>
    intro f X _ hmono h0 m hm
    rw [hall f X hmono h0 m hm]; rfl
  | succ N ih =>
    intro f X hX hmono hN m hm
    simp only [prefixList]
    cases h0 : f 0 with
    | none => rw [hall f X hmono h0 m hm]; rfl
    | some a =>
      simp only
      cases m with
      | zero => simp [h0]
      | succ m =>
        rw [List.getElem?_cons_succ]
        exact ih (fun i => f (i + 1)) (X - 1) (by omega) (fun m' hm' h => hmono (m' + 1) (by omega) h)
          hN m (by omega)

theorem length_prefixList {β : Type*} : ∀ (N : ℕ) (f : ℕ → Option β), (prefixList f N).length ≤ N
  | 0, _ => le_rfl
  | N + 1, f => by
    simp only [prefixList]
    cases f 0 with
    | none => simp
    | some a => simp only [List.length_cons]; have := length_prefixList N (fun i => f (i + 1)); omega

theorem mem_prefixList {β : Type*} : ∀ (N : ℕ) (f : ℕ → Option β) (y : β), y ∈ prefixList f N →
    ∃ m, f m = some y
  | 0, _, _, h => by simp [prefixList] at h
  | N + 1, f, y, h => by
    simp only [prefixList] at h
    cases h0 : f 0 with
    | none => rw [h0] at h; simp at h
    | some a =>
      rw [h0] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨0, h0⟩
      · obtain ⟨m, hm⟩ := mem_prefixList N _ y h
        exact ⟨m + 1, hm⟩

theorem code_some_val {k : tm.K} (x : A tm k) : code tm (some x.val) = some x := by
  simp [code, x.property]

theorem code_eq_none {k : tm.K} {o : Option (tm.Γ k)} (h : ∀ x ∈ o, x ∈ A tm k) :
    code tm o = none ↔ o = none := by
  cases o with
  | none => simp [code]
  | some x => simp [code, h x rfl]

/-! ### The main theorem -/

section Main

variable (d : Data tm) (gs : List (Fin d.W))

/-- The machine input for the certificate `ys`. -/
def inWord (ys : List (tm.Γ tm.k₀)) : List (tm.Γ tm.k₀) := gs.map d.inSym ++ d.sepSym :: ys

/-- Halted with `yes` on top of the output stack. -/
def Acc (c : tm.Cfg) : Prop :=
  (c : Cfg tm.Γ tm.Λ tm.σ).l = none ∧ ((c : Cfg tm.Γ tm.Λ tm.σ).stk tm.k₁)[0]? = some d.yes

@[simp] theorem shape_w : (shape d).w = w tm := rfl
@[simp] theorem shape_S (B : ℕ) : (shape d).S B = SL tm B := rfl
@[simp] theorem shape_col (j : ℕ) : (shape d).col j = L1 tm + (Dp tm + j) * w tm := rfl
@[simp] theorem shape_PM : (shape d).PM = d.PM := rfl
@[simp] theorem shape_PT : (shape d).PT = d.PT := rfl
@[simp] theorem shape_PB : (shape d).PB = d.PB := rfl
@[simp] theorem shape_W : (shape d).W = d.W := rfl

theorem cellsAt_init (s : List (tm.Γ tm.k₀)) (j : ℕ) (k : tm.K) :
    cellsAt tm (initList tm s) j k = if h : k = tm.k₀ then h ▸ s[j]? else none := by
  unfold cellsAt
  rw [Pnp.PPoly.initList_stk]
  split_ifs with h
  · subst h; rfl
  · rfl

theorem inWord_getElem?_lt (ys : List (tm.Γ tm.k₀)) {i : ℕ} {g : Fin d.W} (h : gs[i]? = some g) :
    (inWord d gs ys)[i]? = some (d.inSym g) := by
  have hi : i < gs.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; simp at h
  unfold inWord
  rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map, h]; rfl

theorem inWord_getElem?_sep (ys : List (tm.Γ tm.k₀)) :
    (inWord d gs ys)[gs.length]? = some d.sepSym := by
  unfold inWord
  rw [List.getElem?_append_right (by simp)]; simp

theorem inWord_getElem?_cert (ys : List (tm.Γ tm.k₀)) (m : ℕ) :
    (inWord d gs ys)[gs.length + 1 + m]? = ys[m]? := by
  unfold inWord
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map, show gs.length + 1 + m - gs.length = m + 1 by omega,
    List.getElem?_cons_succ]

theorem length_inWord (ys : List (tm.Γ tm.k₀)) :
    (inWord d gs ys).length = gs.length + 1 + ys.length := by
  simp [inWord]; omega

/-- All clause families, evaluated. -/
theorem allSat_shape (z : ℕ → Bool) :
    (∀ c ∈ (shape d).cls gs, ClauseSat z c) ↔
      let n := gs.length
      let M := d.PM.eval n
      let T := d.PT.eval n
      let B := d.PB.eval n
      (∀ i < c0 tm, z i = encCtrl tm (some tm.main) tm.initialState i) ∧
      (∀ j < B, ∀ β : CI tm, β.1 ≠ tm.k₀ →
        z (L1 tm + (Dp tm + j) * w tm + eC tm β) = encCol tm noneCells (eC tm β)) ∧
      (∀ (i : ℕ) (g : Fin d.W), gs[i]? = some g → ∀ o,
        z (L1 tm + (Dp tm + i) * w tm + pk tm o) = decide (o = code tm (some (d.inSym g)))) ∧
      (∀ o, z (L1 tm + (Dp tm + n) * w tm + pk tm o) = decide (o = code tm (some d.sepSym))) ∧
      (∀ m < B - n - 1, CertOK d z (L1 tm + (Dp tm + (n + 1 + m)) * w tm)) ∧
      z (L1 tm + (Dp tm + (n + 1 + M)) * w tm + pk tm none) = true ∧
      (∀ t ≤ T,
        ((∀ i < Dp tm * w tm, z (t * SL tm B + (L1 tm + i)) = false) ∧
          (∀ i < Dp tm * w tm, z (t * SL tm B + (c0 tm + i)) =
            z (t * SL tm B + (c0 tm + i + 2 * Dp tm * w tm)))) ∧
        ∀ i < Dp tm * w tm,
          z (t * SL tm B + (L1 tm + (Dp tm + B) * w tm) + i) = encCol tm noneCells (i % w tm)) ∧
      (∀ t < T,
        (∀ e : CtI tm, z (t * SL tm B + L1 tm + (B * w tm + (2 * Dp tm * w tm + eT tm e))) =
          gC tm e (blk (fun i => z (t * SL tm B + i)) (L1 tm))) ∧
        (∀ j < B, ∀ β : CI tm, z (t * SL tm B + L1 tm + j * w tm + (2 * Dp tm + 1) * w tm +
            (B * w tm + (L1 tm + (Dp tm - 1) * w tm + eC tm β))) =
          gX tm β.1 β.2 (blk (fun i => z (t * SL tm B + i)) (L1 tm))
            (blk (fun i => z (t * SL tm B + L1 tm + j * w tm + i)) ((2 * Dp tm + 1) * w tm)))) ∧
      (z (T * SL tm B + eT tm (.inl none)) = true ∧
        ∃ h : d.yes ∈ A tm tm.k₁,
          z (T * SL tm B + (L1 tm + Dp tm * w tm + eC tm ⟨tm.k₁, some ⟨d.yes, h⟩⟩)) = true) := by
  rw [Shape.allSat_iff]
  simp only [shape_w, shape_S, shape_col, shape_PM, shape_PT, shape_PB, fam_init0, fam_initCol,
    fam_inCol, fam_sepCol, fam_cert, fam_bound, fam_slice, fam_rpad, fam_stepC, fam_stepX, fam_acc]
  exact Iff.rfl

theorem colOf_real (c : tm.Cfg) (j : ℕ) (β : CI tm) :
    colOf tm c (Dp tm + j) (eC tm β) = decide (code tm (cellsAt tm c j β.1) = β.2) := by
  unfold colOf; rw [if_pos (by omega), Nat.add_sub_cancel_left, encCol_eC]

theorem SL_pos (B : ℕ) : 0 < SL tm B := by
  have := w_pos tm; have := one_le_Dp tm
  have : 0 < (B + 2 * Dp tm) * w tm := Nat.mul_pos (by omega) (w_pos tm)
  unfold SL; omega

theorem col_lt_SL {B q b : ℕ} (hq : q < B + 2 * Dp tm) (hb : b < w tm) :
    L1 tm + q * w tm + b < SL tm B := by
  have := Nat.mul_le_mul_right (w tm) (Nat.succ_le_of_lt hq)
  rw [Nat.succ_mul] at this; unfold SL; omega

/-- Columns of an encoded slice. -/
theorem colEq_of_sliceEq {z : ℕ → Bool} {B t : ℕ} {c : tm.Cfg} (h : SliceEq tm z B t c) :
    ∀ q < B + 2 * Dp tm, ∀ b < w tm, z (t * SL tm B + (L1 tm + q * w tm + b)) = colOf tm c q b :=
  fun q hq b hb => by rw [h _ (col_lt_SL hq hb), sliceOf_col tm c q hb]

/-- The copy / padding families hold on an encoded slice. -/
theorem slice_fam_of {z : ℕ → Bool} {B t : ℕ} {c : tm.Cfg} (h : SliceEq tm z B t c)
    (hlen : ∀ k, ((c : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤ B) :
    ((∀ i < Dp tm * w tm, z (t * SL tm B + (L1 tm + i)) = false) ∧
      (∀ i < Dp tm * w tm, z (t * SL tm B + (c0 tm + i)) =
        z (t * SL tm B + (c0 tm + i + 2 * Dp tm * w tm)))) ∧
    ∀ i < Dp tm * w tm,
      z (t * SL tm B + (L1 tm + (Dp tm + B) * w tm) + i) = encCol tm noneCells (i % w tm) := by
  have hcol := colEq_of_sliceEq h
  have hq : ∀ i < Dp tm * w tm, i / w tm < Dp tm := fun i hi => by
    rw [Nat.div_lt_iff_lt_mul (w_pos tm)]; exact hi
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, fun i hi => ?_⟩
  · have e := col_decomp (tm := tm) i
    rw [show L1 tm + i = L1 tm + i / w tm * w tm + i % w tm by omega,
      hcol _ (by have := hq i hi; omega) _ (mod_lt' _), colOf_left (hq i hi)]
  · have e := col_decomp (tm := tm) i
    have hpos : c0 tm + i + 2 * Dp tm * w tm = L1 tm + (Dp tm + i / w tm) * w tm + i % w tm := by
      unfold L1
      have : (Dp tm + i / w tm) * w tm = Dp tm * w tm + i / w tm * w tm := by ring
      have h2 : 2 * Dp tm * w tm = Dp tm * w tm + Dp tm * w tm := by ring
      omega
    rw [hpos, hcol _ (by have := hq i hi; omega) _ (mod_lt' _), h _ (by unfold SL L1; omega),
      show c0 tm + i = c0 tm + i / w tm * w tm + i % w tm by omega,
      sliceOf_copy tm c (hq i hi) (mod_lt' _)]
  · have e := col_decomp (tm := tm) i
    rw [show t * SL tm B + (L1 tm + (Dp tm + B) * w tm) + i =
        t * SL tm B + (L1 tm + (Dp tm + B + i / w tm) * w tm + i % w tm) by
      have : (Dp tm + B + i / w tm) * w tm = (Dp tm + B) * w tm + i / w tm * w tm := by ring
      omega, hcol _ (by have := hq i hi; omega) _ (mod_lt' _), colOf_right hlen (Nat.le_add_right _ _)]

variable {d gs}

/-- **Completeness**: an accepted certificate gives a satisfying assignment. -/
theorem sat_of_acc
    (hB : gs.length + 2 + d.PM.eval gs.length + d.PT.eval gs.length * Dp tm ≤ d.PB.eval gs.length)
    (ys : List (tm.Γ tm.k₀)) (hok : ∀ y ∈ ys, d.ok y) (hyl : ys.length ≤ d.PM.eval gs.length)
    (hacc : Acc d ((step' tm)^[d.PT.eval gs.length] (initList tm (inWord d gs ys)))) :
    ∃ z : ℕ → Bool, ∀ c ∈ (shape d).cls gs, ClauseSat z c := by
  set n := gs.length with hn
  set M := d.PM.eval n with hM
  set T := d.PT.eval n with hT
  set B := d.PB.eval n with hBdef
  set S := SL tm B with hS
  let c : ℕ → tm.Cfg := fun t => (step' tm)^[t] (initList tm (inWord d gs ys))
  have hc0 : c 0 = initList tm (inWord d gs ys) := rfl
  have hcs : ∀ t, c (t + 1) = step' tm (c t) := fun t => iterate_succ_apply' _ _ _
  have hv : ∀ t, Valid tm (c t) := fun t => iterate_step'_stkInA tm _ t
  have hlen : ∀ t ≤ T, ∀ k, (((c t) : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤ B := by
    intro t ht k
    have h1 := iterate_step'_length_le tm (inWord d gs ys) t k
    rw [length_inWord] at h1
    have h2 : t * D tm ≤ T * Dp tm := Nat.mul_le_mul ht (by unfold Dp; omega)
    exact h1.trans (by omega)
  let z : ℕ → Bool := fun p => if p / S ≤ T then sliceOf tm (c (p / S)) (p % S) else false
  have hSpos : 0 < S := SL_pos B
  have hDp := one_le_Dp tm
  have hz : ∀ t ≤ T, SliceEq tm z B t (c t) := by
    intro t ht i hi
    have e1 : (t * S + i) / S = t := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hSpos, Nat.div_eq_of_lt hi, zero_add]
    have e2 : (t * S + i) % S = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    rw [← hS]; show (if (t * S + i) / S ≤ T then _ else _) = _
    rw [e1, e2, if_pos ht]
  have hz0 := colEq_of_sliceEq (hz 0 (Nat.zero_le _))
  simp only [zero_mul, zero_add] at hz0
  -- real cells at time 0
  have hreal0 : ∀ j < B + Dp tm, ∀ β : CI tm, z (L1 tm + (Dp tm + j) * w tm + eC tm β) =
      decide (code tm (cellsAt tm (c 0) j β.1) = β.2) := fun j hj β => by
    rw [hz0 _ (by omega) _ (eC tm β).isLt, colOf_real]
  have hk0 : ∀ j < B + Dp tm, ∀ o, z (L1 tm + (Dp tm + j) * w tm + pk tm o) =
      decide (code tm ((inWord d gs ys)[j]?) = o) := fun j hj o => by
    rw [pk, hreal0 j hj, hc0, cellsAt_init, dif_pos rfl]
  refine ⟨z, (allSat_shape d gs z).2 ?_⟩
  dsimp only
  simp only [← hn, ← hM, ← hT, ← hBdef, ← hS]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hz 0 (Nat.zero_le _) i (by unfold SL L1; omega)
    simp only [zero_mul, zero_add] at this
    rw [this, sliceOf_ctrl tm _ hi, hc0]; rfl
  · intro j hj β hβ
    have hj' : j < B := hj
    rw [hreal0 j (by omega), hc0, cellsAt_init, dif_neg hβ, encCol_eC]; rfl
  · intro i g hg o
    have hi : i < n := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
    rw [hk0 i (by omega), inWord_getElem?_lt d gs ys hg]
    exact decide_eq_decide.mpr eq_comm
  · intro o
    rw [hk0 n (by omega), inWord_getElem?_sep]
    exact decide_eq_decide.mpr eq_comm
  · intro m hm
    have hv' : ∀ o, z (L1 tm + (Dp tm + (n + 1 + m)) * w tm + pk tm o) =
        decide (code tm ys[m]? = o) := fun o => by
      rw [hk0 _ (by omega), inWord_getElem?_cert]
    have hokv : okO d (code tm ys[m]?) := by
      intro x hx
      cases hy : ys[m]? with
      | none => rw [hy] at hx; simp [code] at hx
      | some y =>
        rw [hy] at hx
        have : code tm (some y) = some ⟨y, Or.inr rfl⟩ := code_some_val ⟨y, Or.inr rfl⟩
        rw [this] at hx
        obtain rfl := Option.some.inj hx
        exact hok y (List.mem_of_getElem? hy)
    refine ⟨fun o ho => ?_, ⟨_, hokv, by rw [hv']; simp⟩, fun o o' h1 h2 => ?_, fun h1 => ?_⟩
    · rw [hv']; simp only [decide_eq_false_iff_not]; rintro rfl; exact ho hokv
    · rw [hv'] at h1 h2; simp only [decide_eq_true_eq] at h1 h2; exact h1.symm.trans h2
    · rw [hv'] at h1
      simp only [decide_eq_true_eq] at h1
      have hnone : ys[m]? = none := by
        rw [code_eq_none] at h1
        · exact h1
        · intro x _; exact Or.inr rfl
      have hnone' : ys[m + 1]? = none := by
        rw [List.getElem?_eq_none_iff] at hnone ⊢; omega
      rw [show L1 tm + (Dp tm + (n + 1 + m)) * w tm + w tm + pk tm none =
          L1 tm + (Dp tm + (n + 1 + (m + 1))) * w tm + pk tm none by ring,
        hk0 _ (by omega), inWord_getElem?_cert, hnone']
      simp [code]
  · rw [hk0 _ (by omega), inWord_getElem?_cert, List.getElem?_eq_none (by omega)]
    simp [code]
  · intro t ht
    exact slice_fam_of (hz t ht) (hlen t ht)
  · intro t ht
    have := step_bwd (hz t ht.le) (hv t) (by rw [← hcs]; exact hz (t + 1) ht)
    exact this
  · have hT' := hz T le_rfl
    obtain ⟨hl, hy⟩ := hacc
    have hyA : d.yes ∈ A tm tm.k₁ := hv T _ _ (List.mem_of_getElem? hy)
    refine ⟨?_, hyA, ?_⟩
    · rw [hT' _ (by have := (eT tm (.inl none)).isLt; unfold SL L1; omega),
        sliceOf_ctrl tm _ (eT tm _).isLt, encCtrl_eT]
      simp only [decide_eq_true_eq]
      exact hl
    · have := colEq_of_sliceEq hT' (Dp tm) (by omega) _ (eC tm ⟨tm.k₁, some ⟨d.yes, hyA⟩⟩).isLt
      simp only [← hS] at this
      rw [this, show Dp tm = Dp tm + 0 from rfl, colOf_real]
      simp only [cellsAt, decide_eq_true_eq]
      erw [hy]
      exact code_some_val ⟨d.yes, hyA⟩

/-- **Soundness**: a satisfying assignment yields an accepted certificate. -/
theorem acc_of_sat
    (hB : gs.length + 2 + d.PM.eval gs.length + d.PT.eval gs.length * Dp tm ≤ d.PB.eval gs.length)
    (z : ℕ → Bool) (hsat : ∀ c ∈ (shape d).cls gs, ClauseSat z c) :
    ∃ ys : List (tm.Γ tm.k₀), (∀ y ∈ ys, d.ok y) ∧ ys.length ≤ d.PM.eval gs.length ∧
      Acc d ((step' tm)^[d.PT.eval gs.length] (initList tm (inWord d gs ys))) := by
  have H := (allSat_shape d gs z).1 hsat
  set n := gs.length with hn
  set M := d.PM.eval n with hM
  set T := d.PT.eval n with hT
  set B := d.PB.eval n with hBdef
  dsimp only at H
  simp only [← hM, ← hT, ← hBdef] at H
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := H
  have hDp := one_le_Dp tm
  set X := B - n - 1 with hX
  have hMX : M < X := by omega
  let a : ℕ → ℕ := fun m => L1 tm + (Dp tm + (n + 1 + m)) * w tm
  let val : ℕ → Option (A tm tm.k₀) := fun m => decOH (fun o => z (a m + pk tm o)) none
  have hval : ∀ m < X, ∀ o, z (a m + pk tm o) = true ↔ o = val m := by
    intro m hm o
    obtain ⟨o₀, -, ho₀⟩ := (h5 m hm).alo
    have hspec : ∀ o, z (a m + pk tm o) = true ↔ o = o₀ := fun o =>
      ⟨fun h => (h5 m hm).amo o o₀ h ho₀, fun h => h ▸ ho₀⟩
    rw [show val m = o₀ from decOH_spec none hspec]; exact hspec o
  have hvalok : ∀ m < X, okO d (val m) := by
    intro m hm
    obtain ⟨o₀, hok, ho₀⟩ := (h5 m hm).alo
    rwa [← (hval m hm o₀).1 ho₀]
  let dec : ℕ → Option (tm.Γ tm.k₀) := fun m => (val m).map Subtype.val
  have hcode : ∀ m, code tm (dec m) = val m := by
    intro m
    show code tm ((val m).map Subtype.val) = val m
    cases val m with
    | none => rfl
    | some x => exact code_some_val x
  have hnone : ∀ m, dec m = none ↔ val m = none := fun m => by simp [dec]
  have hprop : ∀ m, m + 1 < X → dec m = none → dec (m + 1) = none := by
    intro m hm h
    rw [hnone] at h ⊢
    have h0 : z (a m + pk tm none) = true := (hval m (by omega) none).2 h.symm
    have h1' := (h5 m (by omega)).prop h0
    rw [show a m + w tm + pk tm none = a (m + 1) + pk tm none by simp only [a]; ring] at h1'
    exact ((hval (m + 1) hm none).1 h1').symm
  have hdecM : dec M = none := by
    rw [hnone]; exact ((hval M hMX none).1 h6).symm
  set ys := prefixList dec M with hys
  have hysget : ∀ m < X, ys[m]? = dec m := prefixList_getElem?_of M dec X hMX hprop hdecM
  have hyslen : ys.length ≤ M := length_prefixList M dec
  have hok : ∀ y ∈ ys, d.ok y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have := hysget i (by omega)
    rw [List.getElem?_eq_getElem hi] at this
    have hv := hvalok i (by omega)
    cases hvi : val i with
    | none => simp [dec, hvi] at this
    | some x =>
      simp only [dec, hvi, Option.map_some, Option.some.injEq] at this
      rw [this]; exact hv x hvi
  refine ⟨ys, hok, hyslen, ?_⟩
  let c : ℕ → tm.Cfg := fun t => (step' tm)^[t] (initList tm (inWord d gs ys))
  have hcs : ∀ t, c (t + 1) = step' tm (c t) := fun t => iterate_succ_apply' _ _ _
  have hv : ∀ t, Valid tm (c t) := fun t => iterate_step'_stkInA tm _ t
  have hlen : ∀ t ≤ T, ∀ k, (((c t) : Cfg tm.Γ tm.Λ tm.σ).stk k).length ≤ B := by
    intro t ht k
    have h1 := iterate_step'_length_le tm (inWord d gs ys) t k
    rw [length_inWord] at h1
    have h2 : t * D tm ≤ T * Dp tm := Nat.mul_le_mul ht (by unfold Dp; omega)
    exact h1.trans (by omega)
  have hreal0 : ∀ j < B, ∀ β : CI tm, z (0 * SL tm B + (L1 tm + (Dp tm + j) * w tm + eC tm β)) =
      decide (code tm (cellsAt tm (c 0) j β.1) = β.2) := by
    intro j hj β
    obtain ⟨k, o⟩ := β
    rw [zero_mul, zero_add]
    show _ = decide (code tm (cellsAt tm (initList tm (inWord d gs ys)) j k) = o)
    rw [cellsAt_init]
    by_cases hk : k = tm.k₀
    · subst hk
      rw [dif_pos rfl]
      show z (L1 tm + (Dp tm + j) * w tm + pk tm o) = decide (code tm (inWord d gs ys)[j]? = o)
      rcases lt_trichotomy j n with hjn | rfl | hjn
      · obtain ⟨g, hg⟩ : ∃ g, gs[j]? = some g := ⟨gs[j], List.getElem?_eq_getElem hjn⟩
        rw [h3 j g hg o, inWord_getElem?_lt d gs ys hg]; exact decide_eq_decide.mpr eq_comm
      · rw [h4 o, inWord_getElem?_sep]; exact decide_eq_decide.mpr eq_comm
      · obtain ⟨m, rfl⟩ : ∃ m, j = n + 1 + m := ⟨j - n - 1, by omega⟩
        have hm : m < X := by omega
        rw [inWord_getElem?_cert, hysget m hm, hcode, Bool.eq_iff_iff, decide_eq_true_iff]
        exact (hval m hm o).trans eq_comm
    · rw [dif_neg hk, h2 j hj ⟨k, o⟩ hk, encCol_eC]; rfl
  have hslice : ∀ t ≤ T, SliceEq tm z B t (c t) := by
    intro t
    induction t with
    | zero =>
      intro _
      have hcols := cols_of (hlen 0 (Nat.zero_le _)) hreal0 (h7 0 (Nat.zero_le _)).1.1
        (h7 0 (Nat.zero_le _)).2
      refine sliceEq_of_cols ?_ hcols (h7 0 (Nat.zero_le _)).1.2
      intro i hi
      rw [zero_mul, zero_add, h1 i hi, sliceOf_ctrl tm _ hi]; rfl
    | succ t ih =>
      intro ht
      have ih := ih (by omega)
      obtain ⟨hC, hR⟩ := step_fwd ih (hv t) (h8 t (by omega)).1 (h8 t (by omega)).2
      rw [← hcs] at hC hR
      have hcols := cols_of (hlen (t + 1) ht) hR (h7 (t + 1) ht).1.1 (h7 (t + 1) ht).2
      exact sliceEq_of_cols hC hcols (h7 (t + 1) ht).1.2
  have hT' := hslice T le_rfl
  obtain ⟨hctl, hyA, hyes⟩ := h9
  constructor
  · rw [hT' _ (by have := (eT tm (.inl none)).isLt; unfold SL L1; omega),
      sliceOf_ctrl tm _ (eT tm _).isLt, encCtrl_eT] at hctl
    simp only [decide_eq_true_eq] at hctl
    exact hctl
  · have hc := colEq_of_sliceEq hT' (Dp tm) (by omega) _ (eC tm ⟨tm.k₁, some ⟨d.yes, hyA⟩⟩).isLt
    have e := colOf_real (c T) 0 ⟨tm.k₁, some ⟨d.yes, hyA⟩⟩
    rw [Nat.add_zero] at e
    rw [hc, e] at hyes
    simp only [decide_eq_true_eq] at hyes
    unfold cellsAt at hyes
    have := congrArg (Option.map Subtype.val) hyes
    rw [map_code tm (fun x hx => hv T _ _ (List.mem_of_getElem? hx))] at this
    simpa [cellsAt] using this

/-- **The tableau formula is satisfiable iff some admissible certificate is accepted.** -/
theorem tab_sat_iff
    (hB : gs.length + 2 + d.PM.eval gs.length + d.PT.eval gs.length * Dp tm ≤ d.PB.eval gs.length) :
    SATLang ((shape d).formula gs) ↔
      ∃ ys : List (tm.Γ tm.k₀), (∀ y ∈ ys, d.ok y) ∧ ys.length ≤ d.PM.eval gs.length ∧
        Acc d ((step' tm)^[d.PT.eval gs.length] (initList tm (inWord d gs ys))) := by
  rw [Shape.formula_sat_iff _ (shape_noSep d)]
  constructor
  · rintro ⟨z, hz⟩; exact acc_of_sat hB z hz
  · rintro ⟨ys, hok, hyl, hacc⟩; exact sat_of_acc hB ys hok hyl hacc

end Main

end Pnp.CookLevin.Tab
