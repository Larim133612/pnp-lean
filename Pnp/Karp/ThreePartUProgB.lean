import Pnp.Karp.ThreePartUProgA

/-!
# Unary 3-PARTITION reduction program, part B: stacks, specifications, the transformer

Stacks (fields of `tpup_S`): `0` output `R`; `1` the input rows `Mn`; `2`, `3`, `7`
temporaries; `4` `QQ = false^q`; `5` `PRE = false^t`, `6` `SUF = false^(M-1-t)` (the tag);
`8` the row buffer; `9, 10, 11` the suffixes and `14, 16, 17` the prefixes of the blocks
`A, B, C` of a triple row; `12`, `13` the prefix/suffix of a gadget element; `15` a counter;
the constants (field `K`): `18` `false^(L+1)`, `19` `false^(2L-q)`, `20` `false^(2L-M)`,
`21` `false^(3L)`, `22` `[false]`, `23` `false^M`, `24` `false^L`, `25` `false^R`, and
`26 + j` (`j < 9`) the printed `R ^ j` copies of `pos`.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.ThreePartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.BinPacking Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

/-! ## Stack layout -/

structure tpup_S where
  R : Str
  Mn : Str
  T : Str
  X : Str
  QQ : Str
  PRE : Str
  SUF : Str
  T1 : Str
  RW : Str
  A : Str
  B : Str
  C : Str
  GP : Str
  GS : Str
  AP : Str
  CN : Str
  BP : Str
  CP : Str
  K : ℕ → Str

def tpup_S.st (s : tpup_S) : ℕ → Str := fun j =>
  if j = 0 then s.R else if j = 1 then s.Mn else if j = 2 then s.T else if j = 3 then s.X else if j = 4 then s.QQ else if j = 5 then s.PRE else if j = 6 then s.SUF else if j = 7 then s.T1 else if j = 8 then s.RW else if j = 9 then s.A else if j = 10 then s.B else if j = 11 then s.C else if j = 12 then s.GP else if j = 13 then s.GS else if j = 14 then s.AP else if j = 15 then s.CN else if j = 16 then s.BP else if j = 17 then s.CP else s.K j

theorem tpup_st_big (s : tpup_S) (j : ℕ) (h : 18 ≤ j) : s.st j = s.K j := by
  unfold tpup_S.st; repeat rw [if_neg (by omega)]

local macro "tpupx" : tactic =>
  `(tactic| (funext j; by_cases h : j < 18
             · interval_cases j <;> rfl
             · rw [update_of_ne (by omega), tpup_st_big _ _ (by omega), tpup_st_big _ _ (by omega)]))

section St
variable (s : tpup_S) (v : Str)
@[simp] theorem tpup_st0 : s.st 0 = s.R := rfl
@[simp] theorem tpup_st1 : s.st 1 = s.Mn := rfl
@[simp] theorem tpup_st2 : s.st 2 = s.T := rfl
@[simp] theorem tpup_st3 : s.st 3 = s.X := rfl
@[simp] theorem tpup_st4 : s.st 4 = s.QQ := rfl
@[simp] theorem tpup_st5 : s.st 5 = s.PRE := rfl
@[simp] theorem tpup_st6 : s.st 6 = s.SUF := rfl
@[simp] theorem tpup_st7 : s.st 7 = s.T1 := rfl
@[simp] theorem tpup_st8 : s.st 8 = s.RW := rfl
@[simp] theorem tpup_st9 : s.st 9 = s.A := rfl
@[simp] theorem tpup_st10 : s.st 10 = s.B := rfl
@[simp] theorem tpup_st11 : s.st 11 = s.C := rfl
@[simp] theorem tpup_st12 : s.st 12 = s.GP := rfl
@[simp] theorem tpup_st13 : s.st 13 = s.GS := rfl
@[simp] theorem tpup_st14 : s.st 14 = s.AP := rfl
@[simp] theorem tpup_st15 : s.st 15 = s.CN := rfl
@[simp] theorem tpup_st16 : s.st 16 = s.BP := rfl
@[simp] theorem tpup_st17 : s.st 17 = s.CP := rfl
@[simp] theorem tpup_u0 : update s.st 0 v = {s with R := v}.st := by tpupx
@[simp] theorem tpup_u1 : update s.st 1 v = {s with Mn := v}.st := by tpupx
@[simp] theorem tpup_u2 : update s.st 2 v = {s with T := v}.st := by tpupx
@[simp] theorem tpup_u3 : update s.st 3 v = {s with X := v}.st := by tpupx
@[simp] theorem tpup_u4 : update s.st 4 v = {s with QQ := v}.st := by tpupx
@[simp] theorem tpup_u5 : update s.st 5 v = {s with PRE := v}.st := by tpupx
@[simp] theorem tpup_u6 : update s.st 6 v = {s with SUF := v}.st := by tpupx
@[simp] theorem tpup_u7 : update s.st 7 v = {s with T1 := v}.st := by tpupx
@[simp] theorem tpup_u8 : update s.st 8 v = {s with RW := v}.st := by tpupx
@[simp] theorem tpup_u9 : update s.st 9 v = {s with A := v}.st := by tpupx
@[simp] theorem tpup_u10 : update s.st 10 v = {s with B := v}.st := by tpupx
@[simp] theorem tpup_u11 : update s.st 11 v = {s with C := v}.st := by tpupx
@[simp] theorem tpup_u12 : update s.st 12 v = {s with GP := v}.st := by tpupx
@[simp] theorem tpup_u13 : update s.st 13 v = {s with GS := v}.st := by tpupx
@[simp] theorem tpup_u14 : update s.st 14 v = {s with AP := v}.st := by tpupx
@[simp] theorem tpup_u15 : update s.st 15 v = {s with CN := v}.st := by tpupx
@[simp] theorem tpup_u16 : update s.st 16 v = {s with BP := v}.st := by tpupx
@[simp] theorem tpup_u17 : update s.st 17 v = {s with CP := v}.st := by tpupx
end St

/-- The record of a state. -/
def tpup_ofF (σ : ℕ → Str) : tpup_S :=
  ⟨σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6, σ 7, σ 8, σ 9, σ 10, σ 11, σ 12, σ 13, σ 14, σ 15, σ 16,
    σ 17, σ⟩

theorem tpup_ofF_st (σ : ℕ → Str) : (tpup_ofF σ).st = σ := by
  funext j; by_cases h : j < 18
  · interval_cases j <;> rfl
  · rw [tpup_st_big _ _ (by omega)]; rfl

/-! ## Constants -/

/-- The constant stacks. -/
def tpup_KH (K : ℕ → Str) (q M : ℕ) : Prop :=
  K 18 = List.replicate (uL M + 1) false ∧ K 19 = List.replicate (2 * uL M - q) false ∧
  K 20 = List.replicate (2 * uL M - M) false ∧ K 21 = List.replicate (3 * uL M) false ∧
  K 22 = [false] ∧ ∀ j < 9, K (26 + j) = rv (List.replicate (uR M ^ j) pos)

/-- The fixed counts. -/
def tpup_fc (q M : ℕ) (j : ℕ) : ℕ :=
  if j = 18 then uL M + 1 else if j = 19 then 2 * uL M - q else if j = 20 then 2 * uL M - M
  else if j = 21 then 3 * uL M else 1

/-- The counts of a triple row. -/
def tpup_rc (q M t : ℕ) (A B C : List Bool) (j : ℕ) : ℕ :=
  if j = 14 then tpup_pf A else if j = 9 then (tpup_sf A).length
  else if j = 16 then tpup_pf B else if j = 10 then (tpup_sf B).length
  else if j = 17 then tpup_pf C else if j = 11 then (tpup_sf C).length
  else if j = 5 then t else if j = 6 then M - 1 - t else tpup_fc q M j

/-- The counts of a gadget element. -/
def tpup_gc (q M t e : ℕ) (j : ℕ) : ℕ :=
  if j = 12 then e else if j = 13 then q - 1 - e
  else if j = 5 then t else if j = 6 then M - 1 - t else tpup_fc q M j

theorem tpup_uL_le (M : ℕ) : 3 * uL M + 1 ≤ uR M := by unfold uR; omega

theorem tpup_M_le (M : ℕ) : M + 1 ≤ uR M := by unfold uR uL; omega

theorem tpup_R_pos (M : ℕ) : 1 ≤ uR M := by unfold uR; omega

theorem tpup_pow_le (M j : ℕ) (hj : j < 9) : uR M ^ j ≤ uR M ^ 8 :=
  Nat.pow_le_pow_right (tpup_R_pos M) (by omega)

theorem tpup_R_le_W (M : ℕ) : uR M ≤ 2 * uR M ^ 8 := by
  have := Nat.pow_le_pow_right (tpup_R_pos M) (show 1 ≤ 8 by norm_num)
  rw [pow_one] at this; omega

theorem tpup_QH_of {σ K : ℕ → Str} {q M V : ℕ} (hK : tpup_KH K q M)
    (hσ : ∀ j, 18 ≤ j → σ j = K j) (hV : 2 * uR M ^ 8 ≤ V) : tpup_QH σ (uR M) V :=
  fun j hj => ⟨by rw [hσ _ (by omega)]; exact hK.2.2.2.2.2 j hj,
    by have := tpup_pow_le M j hj; omega⟩

theorem tpup_FH_of {cnt : ℕ → ℕ} {q M : ℕ} (h : ∀ j, 18 ≤ j → j ≤ 22 → cnt j = tpup_fc q M j) :
    tpup_FH cnt q M := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [h _ (by norm_num) (by norm_num)] <;> simp [tpup_fc]

/-! ## Item specifications: stacks -/

theorem tpup_cs_mem {cn : ℕ} {pu : ℕ × ℕ} : ∀ (s : Sh) (j : ℕ), j ∈ tpup_cs cn pu s →
    j = 18 ∨ j = 21 ∨ j = cn ∨ j = pu.1 ∨ j = pu.2
  | .z, j, h => by simp [tpup_cs] at h
  | .o _, j, h => by simp [tpup_cs] at h; tauto
  | .c _, j, h => by simp [tpup_cs] at h; tauto
  | .a, j, h => by simp [tpup_cs] at h; tauto

theorem tpup_cs_len {cn : ℕ} {pu : ℕ × ℕ} : ∀ s : Sh, (tpup_cs cn pu s).length ≤ 2
  | .z => by simp [tpup_cs]
  | .o _ => by simp [tpup_cs]
  | .c _ => by simp [tpup_cs]
  | .a => by simp [tpup_cs]

theorem tpup_sp_len (ip : ℕ → ℕ × ℕ) (x : El) : (tpup_sp ip x).length = 9 := rfl

theorem tpup_sp_mem (ip : ℕ → ℕ × ℕ) (x : El) : ∀ d ∈ tpup_sp ip x, d.length ≤ 3 ∧ ∀ j ∈ d,
    (18 ≤ j ∧ j ≤ 22) ∨ j = 5 ∨ j = 6 ∨ ∃ c' < 3, j = (ip c').1 ∨ j = (ip c').2 := by
  intro d hd
  simp only [tpup_sp, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨by have := tpup_cs_len (cn := 19) (pu := ip 0) (shI x 0); omega, fun j hj => by
        rcases tpup_cs_mem _ j hj with h | h | h | h | h <;> subst h <;>
          first | (left; omega) | (right; right; right; exact ⟨0, by norm_num, by tauto⟩)⟩
    | exact ⟨by have := tpup_cs_len (cn := 19) (pu := ip 1) (shI x 1); omega, fun j hj => by
        rcases tpup_cs_mem _ j hj with h | h | h | h | h <;> subst h <;>
          first | (left; omega) | (right; right; right; exact ⟨1, by norm_num, by tauto⟩)⟩
    | exact ⟨by have := tpup_cs_len (cn := 19) (pu := ip 2) (shI x 2); omega, fun j hj => by
        rcases tpup_cs_mem _ j hj with h | h | h | h | h <;> subst h <;>
          first | (left; omega) | (right; right; right; exact ⟨2, by norm_num, by tauto⟩)⟩
    | exact ⟨by have := tpup_cs_len (cn := 20) (pu := (5, 6)) (shL x 0); omega, fun j hj => by
        rcases tpup_cs_mem _ j hj with h | h | h | h | h <;> subst h <;> simp⟩
    | exact ⟨by have := tpup_cs_len (cn := 20) (pu := (5, 6)) (shL x 1); omega, fun j hj => by
        rcases tpup_cs_mem _ j hj with h | h | h | h | h <;> subst h <;> simp⟩
    | exact ⟨by have := tpup_cs_len (cn := 20) (pu := (5, 6)) (shL x 2); omega, fun j hj => by
        rcases tpup_cs_mem _ j hj with h | h | h | h | h <;> subst h <;> simp⟩
    | exact ⟨by split <;> simp, fun j hj => by split at hj <;> simp at hj; subst hj; simp⟩
    | exact ⟨by simp, fun j hj => by simp at hj; subst hj; simp⟩

/-- The count hypotheses of an item specification. -/
theorem tpup_CH_sp {σ K : ℕ → Str} {cnt : ℕ → ℕ} {q M V : ℕ} (ip : ℕ → ℕ × ℕ) (x : El)
    (hK : tpup_KH K q M) (hσ : ∀ j, 18 ≤ j → σ j = K j)
    (hc : ∀ j, 18 ≤ j → j ≤ 22 → cnt j = tpup_fc q M j) (hV : uR M ≤ V)
    (h5 : (σ 5).length = cnt 5 ∧ cnt 5 ≤ V) (h6 : (σ 6).length = cnt 6 ∧ cnt 6 ≤ V)
    (hip : ∀ c' < 3, tpup_ok (ip c').1 ∧ (σ (ip c').1).length = cnt (ip c').1 ∧
      cnt (ip c').1 ≤ V ∧ tpup_ok (ip c').2 ∧ (σ (ip c').2).length = cnt (ip c').2 ∧
      cnt (ip c').2 ≤ V) :
    tpup_CH σ cnt V (tpup_sp ip x) := by
  intro d hd
  obtain ⟨hl, hm⟩ := tpup_sp_mem ip x d hd
  refine ⟨hl, fun j hj => ?_⟩
  have hL := tpup_uL_le M
  rcases hm j hj with ⟨h1, h2⟩ | rfl | rfl | ⟨c', hc', rfl | rfl⟩
  · refine ⟨⟨by omega, by omega, by omega⟩, ?_, ?_⟩
    · rw [hσ j h1, hc j h1 h2]
      obtain ⟨k18, k19, k20, k21, k22, -⟩ := hK
      interval_cases j <;> simp [tpup_fc, k18, k19, k20, k21, k22]
    · rw [hc j h1 h2]; unfold tpup_fc; split_ifs <;> omega
  · exact ⟨⟨by omega, by omega, by omega⟩, h5⟩
  · exact ⟨⟨by omega, by omega, by omega⟩, h6⟩
  · obtain ⟨a1, a2, a3, -, -, -⟩ := hip c' hc'; exact ⟨a1, a2, a3⟩
  · obtain ⟨-, -, -, a1, a2, a3⟩ := hip c' hc'; exact ⟨a1, a2, a3⟩

/-! ## The specifications of the printed items -/

/-- The prefix/suffix stacks of the blocks of a triple row. -/
def tpup_ipR (c : ℕ) : ℕ × ℕ := if c = 0 then (14, 9) else if c = 1 then (16, 10) else (17, 11)

/-- The twelve items of a triple row. -/
def tpup_rowSp : List (List (List ℕ)) := (triBlk 0 (0, 0, 0)).map (tpup_sp tpup_ipR)

/-- The three items of a gadget element of coordinate `c`. -/
def tpup_gadSp (c : ℕ) : List (List (List ℕ)) := (gadBlk 0 0 c 0).map (tpup_sp fun _ => (12, 13))

/-- The bound row. -/
def tpup_bSp : List (List (List ℕ)) := [[[21], [21], [21], [21], [21], [21], [22], [22], [22, 22, 22]]]

/-! ## The transformer -/

/-- The printed items of row `r` (tag `t`). -/
def tpup_rowO (q M : ℕ) (r : List SatSym) (t : ℕ) : List SatSym :=
  let RW := (r.map tpp_bb).reverse
  tpup_blkO (tpup_rc q M t ((RW.drop q).drop q).reverse ((RW.drop q).take q).reverse
    (RW.take q).reverse) (uR M) tpup_rowSp

def tpup_rowsO (q M : ℕ) : List (List SatSym) → ℕ → List SatSym
  | [], _ => []
  | r :: rs, t => tpup_rowO q M r t ++ tpup_rowsO q M rs (t + 1)

def tpup_gadO (q K M c : ℕ) : List SatSym :=
  (List.range q).flatMap fun e =>
    tpup_blkO (tpup_gc q M (K + c * q + e) e) (uR M) (tpup_gadSp c)

def tpup_bO (q M : ℕ) : List SatSym := tpup_blkO (tpup_fc q M) (uR M) tpup_bSp

/-- The transformer on the rows `cl`. -/
def tpup_Fc (cl : List (List SatSym)) : List SatSym :=
  let q := (cl.headD []).length
  let rows := cl.tail
  let K := rows.length
  let M := K + 3 * q
  tpup_rowsO q M rows 0 ++ tpup_gadO q K M 0 ++ tpup_gadO q K M 1 ++ tpup_gadO q K M 2 ++
    tpup_bO q M

/-- **The transformer.** -/
def tpup_F (w : List SatSym) : List SatSym := tpup_Fc (clauses w)

end Pnp.Karp.ThreePartU
