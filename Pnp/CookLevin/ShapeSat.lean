import Pnp.CookLevin.Shape

/-!
# Satisfiability of shaped formulas, clause by clause (M33)

`Shape.formula sh gs` is a concatenation of clauses, each terminated by `sep`.  If no pattern of
the shape contains `sep` (`Shape.NoSep`), the formula is satisfiable iff one assignment satisfies
every clause family (`formula_sat_iff`, with the families spelled out in `Shape.Sat`).  We also
give the clause-level calculus used to evaluate the families: `clauseSat_append`, zeros, negated
patterns `negPat` and single literals `litOf`.
-/

namespace Pnp.CookLevin.Uniform

open SatSym

/-! ### Clause calculus -/

theorem clauseSat_iff_getElem (a : ℕ → Bool) (l : List SatSym) :
    ClauseSat a l ↔ ∃ j, ∃ h : j < l.length, litTrue a j l[j] := by
  unfold ClauseSat
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, by simpa [List.getD_eq_getElem?_getD, hj] using h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, by simpa [List.getD_eq_getElem?_getD, hj] using h⟩

theorem litTrue_shift (a : ℕ → Bool) (m j : ℕ) (s : SatSym) :
    litTrue a (m + j) s ↔ litTrue (fun i => a (m + i)) j s := by
  cases s <;> rfl

theorem clauseSat_append (a : ℕ → Bool) (c₁ c₂ : List SatSym) :
    ClauseSat a (c₁ ++ c₂) ↔ ClauseSat a c₁ ∨ ClauseSat (fun i => a (c₁.length + i)) c₂ := by
  simp only [clauseSat_iff_getElem, List.length_append]
  constructor
  · rintro ⟨j, hj, h⟩
    by_cases h1 : j < c₁.length
    · left; exact ⟨j, h1, by rwa [List.getElem_append_left h1] at h⟩
    · right
      refine ⟨j - c₁.length, by omega, ?_⟩
      rw [List.getElem_append_right (by omega)] at h
      rw [← litTrue_shift]
      rwa [show c₁.length + (j - c₁.length) = j by omega]
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
    · exact ⟨j, by omega, by rwa [List.getElem_append_left hj]⟩
    · refine ⟨c₁.length + j, by omega, ?_⟩
      rw [List.getElem_append_right (by omega), litTrue_shift]
      simpa using h

theorem clauseSat_zs (a : ℕ → Bool) (g : ℕ) : ¬ ClauseSat a (zs g) := by
  rintro ⟨j, hj, h⟩
  simp only [List.length_replicate] at hj
  simp [List.getD_eq_getElem?_getD, hj, litTrue] at h

theorem clauseSat_zs_append (a : ℕ → Bool) (g : ℕ) (c : List SatSym) :
    ClauseSat a (zs g ++ c) ↔ ClauseSat (fun i => a (g + i)) c := by
  rw [clauseSat_append]; simp [clauseSat_zs]

/-- The literal of value `v`. -/
def litOf (v : Bool) : SatSym := if v then pos else neg

/-- The clause falsified exactly by the assignment `α` (of the block). -/
def negPat (α : List Bool) : List SatSym := α.map fun b => if b then neg else pos

theorem clauseSat_litOf (a : ℕ → Bool) (v : Bool) : ClauseSat a [litOf v] ↔ a 0 = v := by
  simp only [clauseSat_iff_getElem, List.length_singleton]
  constructor
  · rintro ⟨j, hj, h⟩
    obtain rfl : j = 0 := by omega
    cases v <;> simpa [litOf, litTrue] using h
  · intro h; exact ⟨0, by omega, by cases v <;> simpa [litOf, litTrue] using h⟩

/-- The values of `a` on `0, …, L-1`. -/
def blk (a : ℕ → Bool) (L : ℕ) : List Bool := (List.range L).map a

theorem length_blk (a : ℕ → Bool) (L : ℕ) : (blk a L).length = L := by simp [blk]

theorem clauseSat_negPat (a : ℕ → Bool) (α : List Bool) :
    ClauseSat a (negPat α) ↔ blk a α.length ≠ α := by
  simp only [clauseSat_iff_getElem, negPat, List.length_map, List.getElem_map, ne_eq]
  constructor
  · rintro ⟨j, hj, h⟩ he
    have : a j = α[j] := by
      have := congrArg (fun l => l[j]?) he
      simpa [blk, List.getElem?_map, List.getElem?_range hj, hj] using this
    cases hα : α[j] <;> simp_all [litTrue]
  · intro hne
    by_contra hc
    push Not at hc
    apply hne
    refine List.ext_getElem (length_blk _ _) fun j h1 h2 => ?_
    have := hc j h2
    simp only [blk, List.getElem_map, List.getElem_range]
    cases hα : α[j] <;> simp_all [litTrue]

/-! ### Clause lists of formulas -/

theorem clausesAux_append_sep : ∀ (c cur rest : List SatSym), sep ∉ c →
    clausesAux (c ++ sep :: rest) cur = (cur.reverse ++ c) :: clausesAux rest []
  | [], cur, rest, _ => by simp [clausesAux]
  | s :: c, cur, rest, h => by
    have hs : s ≠ sep := fun e => h (e ▸ List.mem_cons_self)
    have ih := clausesAux_append_sep c (s :: cur) rest (fun e => h (List.mem_cons_of_mem _ e))
    cases s <;> first | exact absurd rfl hs | simp [clausesAux, ih]

theorem clauses_flatMap : ∀ (L : List (List SatSym)), (∀ c ∈ L, sep ∉ c) →
    clauses (L.flatMap (· ++ [sep])) = L
  | [], _ => rfl
  | c :: L, h => by
    have := clausesAux_append_sep c [] (L.flatMap (· ++ [sep])) (h c List.mem_cons_self)
    simp only [List.flatMap_cons, List.append_assoc, List.singleton_append, clauses] at this ⊢
    rw [this]
    simp only [List.reverse_nil, List.nil_append]
    exact congrArg _ (clauses_flatMap L fun c hc => h c (List.mem_cons_of_mem _ hc))

theorem satLang_flatMap (L : List (List SatSym)) (h : ∀ c ∈ L, sep ∉ c) :
    SATLang (L.flatMap (· ++ [sep])) ↔ ∃ a : ℕ → Bool, ∀ c ∈ L, ClauseSat a c := by
  rw [clauses_sat_iff, clauses_flatMap L h]

/-! ### The clause list of a shaped formula -/

namespace Shape

variable (sh : Shape)

/-- Clauses of `place a cs`. -/
def pcls (a : ℕ) (cs : List (List SatSym)) : List (List SatSym) := cs.map (zs a ++ ·)

theorem place_eq (a : ℕ) (cs : List (List SatSym)) :
    place a cs = (pcls a cs).flatMap (· ++ [sep]) := by
  simp only [place, pcls, List.flatMap_map]
  congr 1

/-- Clauses of `inPart`. -/
def inCls : ℕ → List (Fin sh.W) → List (List SatSym)
  | _, [] => []
  | i, g :: gs => pcls (sh.col i) (sh.inCol g) ++ inCls (i + 1) gs

theorem inPart_eq : ∀ (i : ℕ) (gs : List (Fin sh.W)),
    sh.inPart i gs = (sh.inCls i gs).flatMap (· ++ [sep])
  | _, [] => rfl
  | i, g :: gs => by
    simp only [inPart, inCls, List.flatMap_append, place_eq, inPart_eq (i + 1) gs]

/-- Clauses of `slicePart`. -/
def sliceCls' (B t : ℕ) : List (List SatSym) :=
  pcls (t * sh.S B) sh.sliceCls ++ pcls (t * sh.S B + sh.col B) sh.rpadCls

/-- Clauses of `stepPart`. -/
def stepCls (B t : ℕ) : List (List SatSym) :=
  sh.stepC.map (fun p => zs (t * sh.S B) ++ p.1 ++ zs (B * sh.w + p.2.1) ++ [p.2.2]) ++
  (List.range B).flatMap fun j =>
    sh.stepX.map fun p =>
      zs (t * sh.S B) ++ p.1 ++ zs (j * sh.w) ++ p.2.1 ++ zs (B * sh.w + p.2.2.1) ++ [p.2.2.2]

/-- All clauses of the formula. -/
noncomputable def cls (gs : List (Fin sh.W)) : List (List SatSym) :=
  let n := gs.length
  let M := sh.PM.eval n
  let T := sh.PT.eval n
  let B := sh.PB.eval n
  pcls 0 sh.init0 ++
  (List.range B).flatMap (fun j => pcls (sh.col j) sh.initCol) ++
  sh.inCls 0 gs ++
  pcls (sh.col n) sh.sepCol ++
  (List.range (B - n - 1)).flatMap (fun m => pcls (sh.col (n + 1 + m)) sh.certCol) ++
  pcls (sh.col (n + 1 + M)) sh.boundCol ++
  (List.range T).flatMap (fun t => sh.sliceCls' B t ++ sh.stepCls B t) ++
  sh.sliceCls' B T ++
  pcls (T * sh.S B) sh.acc

theorem formula_eq (gs : List (Fin sh.W)) :
    sh.formula gs = (sh.cls gs).flatMap (· ++ [sep]) := by
  simp only [formula, cls, slicePart, stepPart, sliceCls', stepCls, List.flatMap_append,
    place_eq, inPart_eq, List.flatMap_assoc, List.flatMap_map]
  simp

/-- No pattern of the shape contains `sep`. -/
def NoSep : Prop :=
  (∀ c ∈ sh.init0, sep ∉ c) ∧ (∀ c ∈ sh.initCol, sep ∉ c) ∧ (∀ g, ∀ c ∈ sh.inCol g, sep ∉ c) ∧
  (∀ c ∈ sh.sepCol, sep ∉ c) ∧ (∀ c ∈ sh.certCol, sep ∉ c) ∧ (∀ c ∈ sh.boundCol, sep ∉ c) ∧
  (∀ c ∈ sh.sliceCls, sep ∉ c) ∧ (∀ c ∈ sh.rpadCls, sep ∉ c) ∧
  (∀ p ∈ sh.stepC, sep ∉ p.1 ∧ p.2.2 ≠ sep) ∧
  (∀ p ∈ sh.stepX, sep ∉ p.1 ∧ sep ∉ p.2.1 ∧ p.2.2.2 ≠ sep) ∧ (∀ c ∈ sh.acc, sep ∉ c)

theorem sep_not_mem_zs (a : ℕ) : sep ∉ zs a := by simp [List.mem_replicate]

theorem cls_noSep (h : sh.NoSep) (gs : List (Fin sh.W)) : ∀ c ∈ sh.cls gs, sep ∉ c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have hp : ∀ a cs, (∀ c ∈ cs, sep ∉ c) → ∀ c ∈ pcls a cs, sep ∉ c := by
    intro a cs hcs c hc
    simp only [pcls, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    simp only [List.mem_append, not_or]
    exact ⟨sep_not_mem_zs a, hcs d hd⟩
  have hin : ∀ i gs', ∀ c ∈ sh.inCls i gs', sep ∉ c := by
    intro i gs'
    induction gs' generalizing i with
    | nil => simp [inCls]
    | cons g gs' ih =>
      intro c hc
      simp only [inCls, List.mem_append] at hc
      rcases hc with hc | hc
      · exact hp _ _ (h3 g) c hc
      · exact ih _ c hc
  have hsl : ∀ B t, ∀ c ∈ sh.sliceCls' B t, sep ∉ c := by
    intro B t c hc
    simp only [sliceCls', List.mem_append] at hc
    rcases hc with hc | hc
    · exact hp _ _ h7 c hc
    · exact hp _ _ h8 c hc
  have hst : ∀ B t, ∀ c ∈ sh.stepCls B t, sep ∉ c := by
    intro B t c hc
    simp only [stepCls, List.mem_append, List.mem_map, List.mem_flatMap] at hc
    rcases hc with ⟨p, hp', rfl⟩ | ⟨j, -, p, hp', rfl⟩
    · have := h9 p hp'
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨⟨⟨sep_not_mem_zs _, this.1⟩, sep_not_mem_zs _⟩, this.2.symm⟩
    · have := h10 p hp'
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨⟨⟨⟨⟨sep_not_mem_zs _, this.1⟩, sep_not_mem_zs _⟩, this.2.1⟩, sep_not_mem_zs _⟩,
        this.2.2.symm⟩
  intro c hc
  simp only [cls, List.mem_append, List.mem_flatMap] at hc
  rcases hc with ((((((((hc | ⟨j, -, hc⟩) | hc) | hc) | ⟨m, -, hc⟩) | hc) | ⟨t, -, hc⟩) | hc) | hc)
  · exact hp _ _ h1 c hc
  · exact hp _ _ h2 c hc
  · exact hin _ _ c hc
  · exact hp _ _ h4 c hc
  · exact hp _ _ h5 c hc
  · exact hp _ _ h6 c hc
  · rcases hc with hc | hc
    · exact hsl _ _ c hc
    · exact hst _ _ c hc
  · exact hsl _ _ c hc
  · exact hp _ _ h11 c hc

/-- **Satisfiability of a shaped formula** = one assignment satisfies all clauses. -/
theorem formula_sat_iff (h : sh.NoSep) (gs : List (Fin sh.W)) :
    SATLang (sh.formula gs) ↔ ∃ a : ℕ → Bool, ∀ c ∈ sh.cls gs, ClauseSat a c := by
  rw [formula_eq]; exact satLang_flatMap _ (sh.cls_noSep h gs)

theorem forall_pcls (a : ℕ) (cs : List (List SatSym)) (P : List SatSym → Prop) :
    (∀ c ∈ pcls a cs, P c) ↔ ∀ c ∈ cs, P (zs a ++ c) := by
  simp [pcls]

theorem forall_inCls (z : ℕ → Bool) : ∀ (i : ℕ) (gs : List (Fin sh.W)),
    (∀ c ∈ sh.inCls i gs, ClauseSat z c) ↔
      ∀ (m : ℕ) (g : Fin sh.W), gs[m]? = some g → ∀ c ∈ sh.inCol g,
        ClauseSat z (zs (sh.col (i + m)) ++ c)
  | _, [] => by simp [inCls]
  | i, g :: gs => by
    simp only [inCls, List.mem_append, or_imp, forall_and, forall_pcls, forall_inCls z (i + 1) gs]
    constructor
    · rintro ⟨h1, h2⟩ m g' hm
      cases m with
      | zero => simp at hm; subst hm; simpa using h1
      | succ m =>
        simp only [List.getElem?_cons_succ] at hm
        have := h2 m g' hm
        rwa [show i + 1 + m = i + (m + 1) by omega] at this
    · intro h
      refine ⟨fun c hc => by simpa using h 0 g rfl c hc, fun m g' hm c hc => ?_⟩
      have := h (m + 1) g' (by simpa using hm) c hc
      rwa [show i + (m + 1) = i + 1 + m by omega] at this

/-- **All clauses, by families.** -/
theorem allSat_iff (z : ℕ → Bool) (gs : List (Fin sh.W)) :
    (∀ c ∈ sh.cls gs, ClauseSat z c) ↔
      let n := gs.length
      let M := sh.PM.eval n
      let T := sh.PT.eval n
      let B := sh.PB.eval n
      (∀ c ∈ sh.init0, ClauseSat z (zs 0 ++ c)) ∧
      (∀ j < B, ∀ c ∈ sh.initCol, ClauseSat z (zs (sh.col j) ++ c)) ∧
      (∀ (i : ℕ) (g : Fin sh.W), gs[i]? = some g → ∀ c ∈ sh.inCol g,
        ClauseSat z (zs (sh.col i) ++ c)) ∧
      (∀ c ∈ sh.sepCol, ClauseSat z (zs (sh.col n) ++ c)) ∧
      (∀ m < B - n - 1, ∀ c ∈ sh.certCol, ClauseSat z (zs (sh.col (n + 1 + m)) ++ c)) ∧
      (∀ c ∈ sh.boundCol, ClauseSat z (zs (sh.col (n + 1 + M)) ++ c)) ∧
      (∀ t ≤ T, (∀ c ∈ sh.sliceCls, ClauseSat z (zs (t * sh.S B) ++ c)) ∧
        (∀ c ∈ sh.rpadCls, ClauseSat z (zs (t * sh.S B + sh.col B) ++ c))) ∧
      (∀ t < T,
        (∀ p ∈ sh.stepC, ClauseSat z (zs (t * sh.S B) ++ p.1 ++ zs (B * sh.w + p.2.1) ++ [p.2.2])) ∧
        (∀ j < B, ∀ p ∈ sh.stepX, ClauseSat z
          (zs (t * sh.S B) ++ p.1 ++ zs (j * sh.w) ++ p.2.1 ++ zs (B * sh.w + p.2.2.1) ++
            [p.2.2.2]))) ∧
      (∀ c ∈ sh.acc, ClauseSat z (zs (sh.PT.eval gs.length * sh.S B) ++ c)) := by
  dsimp only
  simp only [cls, sliceCls', stepCls, List.forall_mem_append, List.forall_mem_flatMap,
    List.forall_mem_map, List.mem_range, forall_pcls, forall_inCls, zero_add]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8, h8'⟩, h9⟩
    refine ⟨h1, h2, h3, h4, h5, h6, fun t ht => ?_, fun t ht => (h7 t ht).2, h9⟩
    rcases Nat.lt_or_eq_of_le ht with ht | rfl
    · exact (h7 t ht).1
    · exact ⟨h8, h8'⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, fun t ht => ⟨h7 t ht.le, h8 t ht⟩⟩,
      (h7 _ le_rfl).1, (h7 _ le_rfl).2⟩, h9⟩

end Shape

end Pnp.CookLevin.Uniform
