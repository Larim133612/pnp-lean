import Pnp.Karp.ThreePart
import Pnp.Karp.ThreeDMProg
import Pnp.Karp.FeedbackArcProg

/-!
# The 3-PARTITION reduction program and SAT ≤ₚ 3-PARTITION

`TPI w` is computed as the composition of the 3DM printer `DMI` (`mg_computable`,
`Pnp/Karp/ThreeDMProg.lean`) with the transformer `tpp_F` (computed by `tpp_redCmd`), which
satisfies `tpp_F (DMI w) = TPI w` (`tpp_F_DMI`).

`tpp_redCmd` parses its input into the rows `hdr :: rows` (`q = |hdr|`, `K = |rows|`,
`M = K + 3 q`), and then prints, for every row `l` (split into its three blocks `A, B, C` of
length `q`), its twelve item rows, every digit block being a copy, complement, all-ones or
all-zeros image of one of `A, B, C` or of the tag block `tagB M l`; then the gadget items
(tags `K + c q + e`), and the bound row.  Stacks (fields of `tpp_S`): `0` output `R`; `1` the
input rows `Mn`; `2`, `3` temporaries; `4` `QQ = false^q`; `5` `PRE = false^t`; `6`
`SUF = false^(M-1-t)`; `7` the tag block `TG`; `8` the row buffer `RW`; `9, 10, 11` the blocks
`A, B, C`; `12, 13, 14` `GP = false^e`, `GS = false^(q-1-e)`, `GE = tagB q e`; `15` a counter.
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.ThreePart

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.BinPacking Pnp.Karp.ThreeDM

/-! ## Stack layout -/

structure tpp_S where
  R : Str
  Mn : Str
  T : Str
  X : Str
  QQ : Str
  PRE : Str
  SUF : Str
  TG : Str
  RW : Str
  A : Str
  B : Str
  C : Str
  GP : Str
  GS : Str
  GE : Str
  CN : Str

def tpp_S.st (s : tpp_S) : ℕ → Str := fun j =>
  if j = 0 then s.R else if j = 1 then s.Mn else if j = 2 then s.T else if j = 3 then s.X else
  if j = 4 then s.QQ else if j = 5 then s.PRE else if j = 6 then s.SUF else
  if j = 7 then s.TG else if j = 8 then s.RW else if j = 9 then s.A else
  if j = 10 then s.B else if j = 11 then s.C else if j = 12 then s.GP else
  if j = 13 then s.GS else if j = 14 then s.GE else if j = 15 then s.CN else []

theorem tpp_st_big (s : tpp_S) (j : ℕ) (h : 16 ≤ j) : s.st j = [] := by
  unfold tpp_S.st; repeat rw [if_neg (by omega)]

local macro "tppx" : tactic =>
  `(tactic| (funext j; by_cases h : j < 16
             · interval_cases j <;> rfl
             · rw [update_of_ne (by omega), tpp_st_big _ _ (by omega), tpp_st_big _ _ (by omega)]))

section St
variable (s : tpp_S) (v : Str)
@[simp] theorem tpp_st0 : s.st 0 = s.R := rfl
@[simp] theorem tpp_st1 : s.st 1 = s.Mn := rfl
@[simp] theorem tpp_st2 : s.st 2 = s.T := rfl
@[simp] theorem tpp_st3 : s.st 3 = s.X := rfl
@[simp] theorem tpp_st4 : s.st 4 = s.QQ := rfl
@[simp] theorem tpp_st5 : s.st 5 = s.PRE := rfl
@[simp] theorem tpp_st6 : s.st 6 = s.SUF := rfl
@[simp] theorem tpp_st7 : s.st 7 = s.TG := rfl
@[simp] theorem tpp_st8 : s.st 8 = s.RW := rfl
@[simp] theorem tpp_st9 : s.st 9 = s.A := rfl
@[simp] theorem tpp_st10 : s.st 10 = s.B := rfl
@[simp] theorem tpp_st11 : s.st 11 = s.C := rfl
@[simp] theorem tpp_st12 : s.st 12 = s.GP := rfl
@[simp] theorem tpp_st13 : s.st 13 = s.GS := rfl
@[simp] theorem tpp_st14 : s.st 14 = s.GE := rfl
@[simp] theorem tpp_st15 : s.st 15 = s.CN := rfl
@[simp] theorem tpp_u0 : update s.st 0 v = {s with R := v}.st := by tppx
@[simp] theorem tpp_u1 : update s.st 1 v = {s with Mn := v}.st := by tppx
@[simp] theorem tpp_u2 : update s.st 2 v = {s with T := v}.st := by tppx
@[simp] theorem tpp_u3 : update s.st 3 v = {s with X := v}.st := by tppx
@[simp] theorem tpp_u4 : update s.st 4 v = {s with QQ := v}.st := by tppx
@[simp] theorem tpp_u5 : update s.st 5 v = {s with PRE := v}.st := by tppx
@[simp] theorem tpp_u6 : update s.st 6 v = {s with SUF := v}.st := by tppx
@[simp] theorem tpp_u7 : update s.st 7 v = {s with TG := v}.st := by tppx
@[simp] theorem tpp_u8 : update s.st 8 v = {s with RW := v}.st := by tppx
@[simp] theorem tpp_u9 : update s.st 9 v = {s with A := v}.st := by tppx
@[simp] theorem tpp_u10 : update s.st 10 v = {s with B := v}.st := by tppx
@[simp] theorem tpp_u11 : update s.st 11 v = {s with C := v}.st := by tppx
@[simp] theorem tpp_u12 : update s.st 12 v = {s with GP := v}.st := by tppx
@[simp] theorem tpp_u13 : update s.st 13 v = {s with GS := v}.st := by tppx
@[simp] theorem tpp_u14 : update s.st 14 v = {s with GE := v}.st := by tppx
@[simp] theorem tpp_u15 : update s.st 15 v = {s with CN := v}.st := by tppx
end St

/-! ## Printing digit blocks -/

/-- A printed base-4 digit `b ∈ {0,1}`. -/
def tpp_g (b : Bool) : List SatSym := [if b then pos else zero, zero]

/-- The digit selector (`bf` for a stored `false`, `bt` for a stored `true`). -/
def tpp_sl (bf bt b : Bool) : Bool := if b then bt else bf

/-- The digits of a stored block `β`, through the selector. -/
def tpp_dg (bf bt : Bool) (β : List Bool) : List SatSym :=
  β.flatMap fun b => tpp_g (tpp_sl bf bt b)

/-- Print the symbols `L` on stack `0`. -/
def tpp_em (L : List SatSym) : Cmd := pushList 0 (rv L)

theorem tpp_ex_em (L E : List SatSym) (σ : ℕ → Str) (h : σ 0 = rv E) :
    ExecLe (tpp_em L) σ (.norm (update σ 0 (rv (E ++ L)))) (2 * L.length + 1) := by
  refine (ExecLe.of (exec_pushList 0 (rv L) σ)).cast ?_
    (by simp only [rv, List.length_reverse, length_flatMap_ic]; omega)
  rw [h, rv_append]

def tpp_prL (bf bt : Bool) : Cmd := .loop (.pop 2 .brk (tpp_em (tpp_g bf)) (tpp_em (tpp_g bt)))

theorem tpp_ex_prL (bf bt : Bool) : ∀ (β : List Bool) (σ : ℕ → Str) (E : List SatSym),
    σ 2 = β → σ 0 = rv E →
    ExecLe (tpp_prL bf bt) σ (.norm (update (update σ 2 []) 0 (rv (E ++ tpp_dg bf bt β))))
      (6 * β.length + 2)
  | [], σ, E, h2, h0 => (ExecLe.loop_brk (ExecLe.pop_nil h2 (ExecLe.brk _))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [tpp_dg])
      (by simp)
  | b :: β, σ, E, h2, h0 => by
    have h1 : ExecLe (.pop 2 .brk (tpp_em (tpp_g bf)) (tpp_em (tpp_g bt))) σ
        (.norm (update (update σ 2 β) 0 (rv (E ++ tpp_g (tpp_sl bf bt b))))) 6 := by
      refine ExecLe.pop_cons h2 ?_
      have e : update σ 2 β 0 = rv E := by rw [update_of_ne (by norm_num), h0]
      cases b
      · exact (tpp_ex_em _ E _ e).cast rfl (by simp [tpp_g])
      · exact (tpp_ex_em _ E _ e).cast rfl (by simp [tpp_g])
    have ih := tpp_ex_prL bf bt β (update (update σ 2 β) 0 (rv (E ++ tpp_g (tpp_sl bf bt b))))
      (E ++ tpp_g (tpp_sl bf bt b)) (by simp) (by simp)
    refine (ExecLe.loop_norm h1 ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all [tpp_dg]

/-- Print the digits of stack `k` through the selector (via temporaries `2`, `3`). -/
def tpp_prB (k : ℕ) (bf bt : Bool) : Cmd := .seq (copyVia k 2 3) (tpp_prL bf bt)

theorem tpp_ex_prB {k : ℕ} (_hk0 : k ≠ 0) (hk2 : k ≠ 2) (hk3 : k ≠ 3) (bf bt : Bool)
    (σ : ℕ → Str) (E : List SatSym) (h2 : σ 2 = []) (h3 : σ 3 = []) (h0 : σ 0 = rv E) :
    ExecLe (tpp_prB k bf bt) σ (.norm (update σ 0 (rv (E ++ tpp_dg bf bt (σ k)))))
      (11 * (σ k).length + 6) := by
  have p1 := ExecLe.of (exec_copyVia (a := k) (b := 2) (t := 3) hk2 hk3 (by norm_num) σ h3)
  rw [h2, List.append_nil] at p1
  have p2 := tpp_ex_prL bf bt (σ k) (update σ 2 (σ k)) E (by simp)
    (by rw [update_of_ne (by norm_num), h0])
  refine (p1.seq_norm p2).cast ?_ (by omega)
  congr 1; funext j; simp only [update_apply]
  split_ifs <;> simp_all

/-! ## Items and blocks of items -/

/-- An item: digit blocks `(bf, bt, k)` and constant trailing symbols `cs`. -/
def tpp_itC : List (Bool × Bool × ℕ) → List SatSym → Cmd
  | [], cs => tpp_em cs
  | p :: ps, cs => .seq (tpp_prB p.2.2 p.1 p.2.1) (tpp_itC ps cs)

def tpp_itO (v : ℕ → List Bool) (sp : List (Bool × Bool × ℕ)) (cs : List SatSym) :
    List SatSym := sp.flatMap (fun p => tpp_dg p.1 p.2.1 (v p.2.2)) ++ cs

/-- Admissible stack index of a digit block. -/
def tpp_ok (k : ℕ) : Prop := k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 3

theorem tpp_ex_itC (Z : ℕ) : ∀ (sp : List (Bool × Bool × ℕ)) (cs : List SatSym)
    (σ : ℕ → Str) (E : List SatSym), σ 2 = [] → σ 3 = [] → σ 0 = rv E →
    (∀ p ∈ sp, tpp_ok p.2.2 ∧ (σ p.2.2).length ≤ Z) →
    ExecLe (tpp_itC sp cs) σ (.norm (update σ 0 (rv (E ++ tpp_itO σ sp cs))))
      (sp.length * (11 * Z + 6) + 2 * cs.length + 1)
  | [], cs, σ, E, h2, h3, h0, _ => (tpp_ex_em cs E σ h0).cast (by simp [tpp_itO]) (by simp)
  | p :: ps, cs, σ, E, h2, h3, h0, hp => by
    obtain ⟨⟨a0, a2, a3⟩, hz⟩ := hp p List.mem_cons_self
    have p1 := tpp_ex_prB a0 a2 a3 p.1 p.2.1 σ E h2 h3 h0
    have ih := tpp_ex_itC Z ps cs (update σ 0 (rv (E ++ tpp_dg p.1 p.2.1 (σ p.2.2))))
      (E ++ tpp_dg p.1 p.2.1 (σ p.2.2)) (by simp [h2]) (by simp [h3]) (by simp)
      (fun p' hp' => by
        obtain ⟨⟨b0, b2, b3⟩, hz'⟩ := hp p' (List.mem_cons_of_mem _ hp')
        exact ⟨⟨b0, b2, b3⟩, by rw [update_of_ne b0]; exact hz'⟩)
    refine (p1.seq_norm ih).cast ?_ ?_
    · congr 1; rw [update_idem]; congr 2
      have e : ∀ p' ∈ ps, update σ 0 (rv (E ++ tpp_dg p.1 p.2.1 (σ p.2.2))) p'.2.2 = σ p'.2.2 :=
        fun p' hp' => update_of_ne (hp p' (List.mem_cons_of_mem _ hp')).1.1 _ _
      simp only [tpp_itO, List.flatMap_cons, List.append_assoc]
      congr 2
      congr 1
      apply List.flatMap_congr; intro p' hp'; rw [e p' hp']
    · simp only [List.length_cons]; nlinarith

def tpp_blkC : List (List (Bool × Bool × ℕ) × List SatSym) → Cmd
  | [] => .skip
  | p :: ps => .seq (tpp_itC p.1 p.2) (tpp_blkC ps)

def tpp_blkO (v : ℕ → List Bool) (its : List (List (Bool × Bool × ℕ) × List SatSym)) :
    List SatSym := its.flatMap fun p => tpp_itO v p.1 p.2

theorem tpp_ex_blkC (Z : ℕ) : ∀ (its : List (List (Bool × Bool × ℕ) × List SatSym))
    (σ : ℕ → Str) (E : List SatSym), σ 2 = [] → σ 3 = [] → σ 0 = rv E →
    (∀ p ∈ its, p.1.length ≤ 6 ∧ p.2.length ≤ 7 ∧ ∀ x ∈ p.1, tpp_ok x.2.2 ∧ (σ x.2.2).length ≤ Z) →
    ExecLe (tpp_blkC its) σ (.norm (update σ 0 (rv (E ++ tpp_blkO σ its))))
      (its.length * (66 * Z + 51) + 1)
  | [], σ, E, h2, h3, h0, _ => (ExecLe.skip σ).cast
      (by congr 1; simp [tpp_blkO, ← h0]) (by simp)
  | p :: ps, σ, E, h2, h3, h0, hp => by
    obtain ⟨l1, l2, hx⟩ := hp p List.mem_cons_self
    have p1 := tpp_ex_itC Z p.1 p.2 σ E h2 h3 h0 hx
    have ih := tpp_ex_blkC Z ps (update σ 0 (rv (E ++ tpp_itO σ p.1 p.2)))
      (E ++ tpp_itO σ p.1 p.2) (by simp [h2]) (by simp [h3]) (by simp)
      (fun p' hp' => by
        obtain ⟨m1, m2, hx'⟩ := hp p' (List.mem_cons_of_mem _ hp')
        exact ⟨m1, m2, fun x hx0 => ⟨(hx' x hx0).1,
          by rw [update_of_ne (hx' x hx0).1.1]; exact (hx' x hx0).2⟩⟩)
    refine (p1.seq_norm ih).cast ?_ ?_
    · congr 1; rw [update_idem]; congr 2
      have e : ∀ p' ∈ ps, tpp_itO (update σ 0 (rv (E ++ tpp_itO σ p.1 p.2))) p'.1 p'.2 =
          tpp_itO σ p'.1 p'.2 := fun p' hp' => by
        unfold tpp_itO; congr 1
        apply List.flatMap_congr; intro x hx0
        rw [update_of_ne ((hp p' (List.mem_cons_of_mem _ hp')).2.2 x hx0).1.1]
      simp only [tpp_blkO, List.flatMap_cons, List.append_assoc]
      congr 2
      apply List.flatMap_congr; intro p' hp'; rw [e p' hp']
    · simp only [List.length_cons]; nlinarith

theorem tpp_blkO_congr {v v' : ℕ → List Bool} (its : List (List (Bool × Bool × ℕ) × List SatSym))
    (h : ∀ p ∈ its, ∀ x ∈ p.1, v x.2.2 = v' x.2.2) : tpp_blkO v its = tpp_blkO v' its := by
  unfold tpp_blkO tpp_itO
  apply List.flatMap_congr; intro p hp
  congr 1; apply List.flatMap_congr; intro x hx; rw [h p hp x hx]

/-! ## Reading, counting, splitting, building -/

/-- Read one symbol from stack `k` and branch on it. -/
def tpp_rd (k : ℕ) (cs c0 cp cn : Cmd) : Cmd :=
  .pop k .brk (.pop k .brk cs c0) (.pop k .brk cp cn)

def tpp_sel (cs c0 cp cn : Cmd) : SatSym → Cmd
  | sep => cs
  | zero => c0
  | pos => cp
  | neg => cn

theorem tpp_ex_rd {k : ℕ} {cs c0 cp cn : Cmd} (e : SatSym) (σ : ℕ → Str) (M' : Str)
    (hM : σ k = ic e ++ M') {r : Res} {T : ℕ}
    (h : ExecLe (tpp_sel cs c0 cp cn e) (update σ k M') r T) :
    ExecLe (tpp_rd k cs c0 cp cn) σ r (T + 2) := by
  cases e <;> simp only [ic, List.cons_append, List.nil_append] at hM
  · refine ExecLe.pop_cons (b := true) (s := false :: M') hM ?_
    simp only [↓reduceIte]
    exact ExecLe.pop_cons (b := false) (s := M') (by simp) (by rw [update_idem]; exact h)
  · refine ExecLe.pop_cons (b := true) (s := true :: M') hM ?_
    simp only [↓reduceIte]
    exact ExecLe.pop_cons (b := true) (s := M') (by simp) (by rw [update_idem]; exact h)
  · refine ExecLe.pop_cons (b := false) (s := true :: M') hM ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ExecLe.pop_cons (b := true) (s := M') (by simp) (by rw [update_idem]; exact h)
  · refine ExecLe.pop_cons (b := false) (s := false :: M') hM ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ExecLe.pop_cons (b := false) (s := M') (by simp) (by rw [update_idem]; exact h)

/-- Read a row from stack `1`, pushing `f` of each symbol onto stack `k`. -/
def tpp_rdL (k : ℕ) (f : SatSym → Bool) : Cmd :=
  .loop (tpp_rd 1 .brk (.push k (f zero)) (.push k (f pos)) (.push k (f neg)))

theorem tpp_ex_rdL {k : ℕ} (hk : k ≠ 1) (f : SatSym → Bool) : ∀ (r : List SatSym) (rest : Str)
    (σ : ℕ → Str), sep ∉ r → σ 1 = (r ++ [sep]).flatMap ic ++ rest →
    ExecLe (tpp_rdL k f) σ (.norm (update (update σ 1 rest) k ((r.map f).reverse ++ σ k)))
      (4 * r.length + 4)
  | [], rest, σ, _, h1 => by
    have h := tpp_ex_rd (cs := .brk) (c0 := .push k (f zero)) (cp := .push k (f pos))
      (cn := .push k (f neg)) sep σ rest (by simpa using h1) (ExecLe.brk _)
    exact (ExecLe.loop_brk h).cast (by simp [update_of_ne hk]) (by simp)
  | e :: r, rest, σ, hs, h1 => by
    have he : e ≠ sep := fun h => hs (h ▸ List.mem_cons_self ..)
    have hs' : sep ∉ r := fun h => hs (List.mem_cons_of_mem _ h)
    have hb := tpp_ex_rd (k := 1) (cs := .brk) (c0 := .push k (f zero)) (cp := .push k (f pos))
      (cn := .push k (f neg)) e σ ((r ++ [sep]).flatMap ic ++ rest) (by simp [h1])
      (r := .norm (update (update σ 1 ((r ++ [sep]).flatMap ic ++ rest)) k
        (f e :: σ k))) (T := 1)
      (by
        have := ExecLe.push k (f e) (update σ 1 ((r ++ [sep]).flatMap ic ++ rest))
        rw [update_of_ne hk] at this
        cases e <;> first | exact absurd rfl he | exact this)
    have ih := tpp_ex_rdL hk f r rest
      (update (update σ 1 ((r ++ [sep]).flatMap ic ++ rest)) k (f e :: σ k)) hs'
      (by rw [update_of_ne (Ne.symm hk), update_self])
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all

/-- Count the `sep`s of stack `2` (pushing `false` onto stack `6` for each). -/
def tpp_cnL : Cmd :=
  .loop (.pop 2 .brk (.pop 2 .brk (.push 6 false) .skip) (.pop 2 .brk .skip .skip))

theorem tpp_ex_cnL : ∀ (L : List SatSym) (σ : ℕ → Str), σ 2 = L.flatMap ic →
    ExecLe tpp_cnL σ (.norm (update (update σ 2 []) 6
      (List.replicate (L.count sep) false ++ σ 6))) (3 * L.length + 2)
  | [], σ, h => (ExecLe.loop_brk (ExecLe.pop_nil h (ExecLe.brk _))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all) (by simp)
  | e :: L, σ, h => by
    have hb : ExecLe (.pop 2 .brk (.pop 2 .brk (.push 6 false) .skip) (.pop 2 .brk .skip .skip)) σ
        (.norm (update (update σ 2 (L.flatMap ic)) 6
          (List.replicate (if e = sep then 1 else 0) false ++ σ 6))) 3 := by
      cases e <;> simp only [ic, List.flatMap_cons, List.cons_append, List.nil_append] at h <;>
      · refine ExecLe.pop_cons h ?_
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine ExecLe.pop_cons (s := L.flatMap ic) (by rw [update_self]) ?_
        rw [update_idem]
        simp only [Bool.false_eq_true, ↓reduceIte]
        first
        | exact (ExecLe.push 6 false _).cast
            (by simp [update_of_ne (show (6 : ℕ) ≠ 2 by norm_num)]) le_rfl
        | exact (ExecLe.skip _).cast (by simp) le_rfl
    have ih := tpp_ex_cnL L (update (update σ 2 (L.flatMap ic)) 6
      (List.replicate (if e = sep then 1 else 0) false ++ σ 6)) (by simp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]
    split_ifs with h1 h2 <;> simp_all [List.count_cons, List.replicate_add]

/-- Move up to `n` (the length of the counter `15`) bits of stack `8` onto stack `k`. -/
def tpp_spL (k : ℕ) : Cmd :=
  .loop (.pop 15 .brk (.pop 8 .skip (.push k false) (.push k true))
    (.pop 8 .skip (.push k false) (.push k true)))

theorem tpp_ex_spL {k : ℕ} (hk8 : k ≠ 8) (hk15 : k ≠ 15) : ∀ (n : ℕ) (l : Str) (σ : ℕ → Str),
    σ 15 = List.replicate n false → σ 8 = l →
    ExecLe (tpp_spL k) σ (.norm (update (update (update σ 15 []) 8 (l.drop n)) k
      ((l.take n).reverse ++ σ k))) (3 * n + 2)
  | 0, l, σ, h15, h8 => (ExecLe.loop_brk (ExecLe.pop_nil (by simpa using h15) (ExecLe.brk _))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all) (by simp)
  | n + 1, [], σ, h15, h8 => by
    have hb : ExecLe (.pop 15 .brk (.pop 8 .skip (.push k false) (.push k true))
        (.pop 8 .skip (.push k false) (.push k true))) σ
        (.norm (update σ 15 (List.replicate n false))) 3 :=
      ExecLe.pop_same (b := false) (by simpa [List.replicate_succ] using h15)
        (ExecLe.pop_nil (by simp [h8]) (ExecLe.skip _))
    have ih := tpp_ex_spL hk8 hk15 n [] (update σ 15 (List.replicate n false)) (by simp)
      (by simp [h8])
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all
  | n + 1, b :: l, σ, h15, h8 => by
    have hb : ExecLe (.pop 15 .brk (.pop 8 .skip (.push k false) (.push k true))
        (.pop 8 .skip (.push k false) (.push k true))) σ
        (.norm (update (update (update σ 15 (List.replicate n false)) 8 l) k (b :: σ k))) 3 := by
      refine ExecLe.pop_same (b := false) (by simpa [List.replicate_succ] using h15) ?_
      refine ExecLe.pop_cons (b := b) (s := l) (by simp [h8]) ?_
      have e : update (update σ 15 (List.replicate n false)) 8 l k = σ k := by
        rw [update_of_ne hk8, update_of_ne hk15]
      cases b
      · exact (ExecLe.push k false _).cast (by rw [e]) le_rfl
      · exact (ExecLe.push k true _).cast (by rw [e]) le_rfl
    have ih := tpp_ex_spL hk8 hk15 n l
      (update (update (update σ 15 (List.replicate n false)) 8 l) k (b :: σ k))
      (by simp [hk15, Ne.symm hk15])
      (by simp [Ne.symm hk8])
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all

/-- Split off `q` (the length of `QQ`) bits of stack `8` onto stack `k`. -/
def tpp_spC (k : ℕ) : Cmd := .seq (copyVia 4 15 3) (tpp_spL k)

/-- Stack `d` becomes `σ p ++ true :: σ s ++ σ d`. -/
def tpp_bldC (d p s : ℕ) : Cmd := .seq (copyVia s d 3) (.seq (.push d true) (copyVia p d 3))

theorem tpp_ex_bldC {d p s : ℕ} (hdp : d ≠ p) (hds : d ≠ s) (hd3 : d ≠ 3) (hp3 : p ≠ 3)
    (hs3 : s ≠ 3) (σ : ℕ → Str) (h3 : σ 3 = []) :
    ExecLe (tpp_bldC d p s) σ (.norm (update σ d (σ p ++ true :: σ s ++ σ d)))
      (5 * (σ p).length + 5 * (σ s).length + 9) := by
  have p1 := ExecLe.of (exec_copyVia (a := s) (b := d) (t := 3) (Ne.symm hds) hs3 hd3 σ h3)
  have p2 := ExecLe.push d true (update σ d (σ s ++ σ d))
  have p3 := ExecLe.of (exec_copyVia (a := p) (b := d) (t := 3) (Ne.symm hdp) hp3 hd3
    (update (update σ d (σ s ++ σ d)) d (true :: update σ d (σ s ++ σ d) d)) (by simp [hd3.symm, h3]))
  refine (p1.seq_norm (p2.seq_norm p3)).cast ?_ ?_
  · congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all
  · simp [update_of_ne (Ne.symm hdp)]; omega

/-- Pop one bit (if any). -/
def tpp_pop1 (k : ℕ) : Cmd := .pop k .skip .skip .skip

theorem tpp_ex_pop1 (k n : ℕ) (σ : ℕ → Str) (h : σ k = List.replicate n false) :
    ExecLe (tpp_pop1 k) σ (.norm (update σ k (List.replicate (n - 1) false))) 2 := by
  rcases n with _ | n
  · exact (ExecLe.pop_nil (by simpa using h) (ExecLe.skip _)).cast
      (by congr 1; rw [← h]; simp) le_rfl
  · exact (ExecLe.pop_same (b := false) (by simpa [List.replicate_succ] using h)
      (ExecLe.skip _)).cast (by simp) le_rfl

theorem tpp_ex_spC {k : ℕ} (hk8 : k ≠ 8) (hk15 : k ≠ 15) (_hk3 : k ≠ 3) (_hk4 : k ≠ 4) (q : ℕ)
    (l : Str) (σ : ℕ → Str) (h3 : σ 3 = []) (h15 : σ 15 = []) (h4 : σ 4 = List.replicate q false)
    (h8 : σ 8 = l) :
    ExecLe (tpp_spC k) σ (.norm (update (update σ 8 (l.drop q)) k ((l.take q).reverse ++ σ k)))
      (8 * q + 6) := by
  have p1 := ExecLe.of (exec_copyVia (a := 4) (b := 15) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) σ h3)
  rw [h15, h4, List.append_nil] at p1
  have p2 := tpp_ex_spL hk8 hk15 q l (update σ 15 (List.replicate q false)) (by simp)
    (by simp [h8])
  refine (p1.seq_norm p2).cast ?_ (by simp; omega)
  congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all

/-! ## The specification of the printed items -/

/-- Digit blocks: copy, complement, all zeros, all ones of stack `k`. -/
abbrev tpp_c (k : ℕ) : Bool × Bool × ℕ := (false, true, k)
abbrev tpp_n (k : ℕ) : Bool × Bool × ℕ := (true, false, k)
abbrev tpp_z (k : ℕ) : Bool × Bool × ℕ := (false, false, k)
abbrev tpp_o (k : ℕ) : Bool × Bool × ℕ := (true, true, k)

/-- The trailing symbols of an item: state digits, leading digit `1`, `sep`. -/
def tpp_cs (s1 s2 : Bool) : List SatSym :=
  [if s1 then pos else zero, zero, if s2 then pos else zero, zero, pos, zero, sep]

/-- The twelve items of a triple row (`A, B, C` in stacks `9, 10, 11`, the tag in `7`). -/
def tpp_rowSpec : List (List (Bool × Bool × ℕ) × List SatSym) :=
  [([tpp_c 9, tpp_z 10, tpp_z 11, tpp_z 7, tpp_z 7, tpp_z 7], tpp_cs false false),
   ([tpp_z 9, tpp_c 10, tpp_z 11, tpp_z 7, tpp_z 7, tpp_z 7], tpp_cs true false),
   ([tpp_z 9, tpp_z 10, tpp_c 11, tpp_z 7, tpp_z 7, tpp_z 7], tpp_cs false true),
   ([tpp_z 9, tpp_z 10, tpp_o 11, tpp_c 7, tpp_n 7, tpp_z 7], tpp_cs false false),
   ([tpp_z 9, tpp_z 10, tpp_o 11, tpp_c 7, tpp_n 7, tpp_z 7], tpp_cs true false),
   ([tpp_o 9, tpp_z 10, tpp_z 11, tpp_z 7, tpp_c 7, tpp_n 7], tpp_cs true false),
   ([tpp_o 9, tpp_z 10, tpp_z 11, tpp_z 7, tpp_c 7, tpp_n 7], tpp_cs false true),
   ([tpp_z 9, tpp_o 10, tpp_z 11, tpp_n 7, tpp_z 7, tpp_c 7], tpp_cs false true),
   ([tpp_z 9, tpp_o 10, tpp_z 11, tpp_n 7, tpp_z 7, tpp_c 7], tpp_cs false false),
   ([tpp_n 9, tpp_o 10, tpp_z 11, tpp_n 7, tpp_c 7, tpp_o 7], tpp_cs false true),
   ([tpp_z 9, tpp_n 10, tpp_o 11, tpp_o 7, tpp_n 7, tpp_c 7], tpp_cs false false),
   ([tpp_o 9, tpp_z 10, tpp_n 11, tpp_c 7, tpp_o 7, tpp_n 7], tpp_cs true false)]

theorem tpp_rowSpec_idx : ∀ p ∈ tpp_rowSpec, p.1.length ≤ 6 ∧ p.2.length ≤ 7 ∧
    ∀ x ∈ p.1, x.2.2 = 9 ∨ x.2.2 = 10 ∨ x.2.2 = 11 ∨ x.2.2 = 7 := by
  simp [tpp_rowSpec, tpp_cs]

/-- Index block `c'` of a gadget item of coordinate `c`. -/
def tpp_ib (c c' : ℕ) (x y z : Bool × Bool) (k : ℕ) : Bool × Bool × ℕ :=
  if c' = c then (x.1, x.2, k) else if c' = (c + 1) % 3 then (y.1, y.2, k) else (z.1, z.2, k)

/-- The three gadget items of coordinate `c` (the element block in `14`, the tag in `7`). -/
def tpp_gadSpec (c : ℕ) : List (List (Bool × Bool × ℕ) × List SatSym) :=
  [([tpp_ib c 0 (false, true) (false, false) (false, false) 14,
     tpp_ib c 1 (false, true) (false, false) (false, false) 14,
     tpp_ib c 2 (false, true) (false, false) (false, false) 14,
     tpp_z 7, tpp_z 7, tpp_z 7], tpp_cs (c = 0) (c = 1)),
   ([tpp_ib c 0 (false, false) (false, false) (true, true) 14,
     tpp_ib c 1 (false, false) (false, false) (true, true) 14,
     tpp_ib c 2 (false, false) (false, false) (true, true) 14,
     tpp_ib c 0 (false, true) (true, false) (false, false) 7,
     tpp_ib c 1 (false, true) (true, false) (false, false) 7,
     tpp_ib c 2 (false, true) (true, false) (false, false) 7], tpp_cs (c = 0) (c = 1)),
   ([tpp_ib c 0 (true, false) (true, true) (false, false) 14,
     tpp_ib c 1 (true, false) (true, true) (false, false) 14,
     tpp_ib c 2 (true, false) (true, true) (false, false) 14,
     tpp_ib c 0 (true, false) (false, true) (true, true) 7,
     tpp_ib c 1 (true, false) (false, true) (true, true) 7,
     tpp_ib c 2 (true, false) (false, true) (true, true) 7], tpp_cs (c = 2) (c = 0))]

theorem tpp_ib_k (c c' : ℕ) (x y z : Bool × Bool) (k : ℕ) : (tpp_ib c c' x y z k).2.2 = k := by
  unfold tpp_ib; split_ifs <;> rfl

theorem tpp_gadSpec_idx (c : ℕ) : ∀ p ∈ tpp_gadSpec c, p.1.length ≤ 6 ∧ p.2.length ≤ 7 ∧
    ∀ x ∈ p.1, x.2.2 = 14 ∨ x.2.2 = 7 := by
  intro p hp
  simp only [tpp_gadSpec, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> refine ⟨by simp, by simp [tpp_cs], ?_⟩ <;> intro x hx <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [tpp_ib_k]

/-- The bound row (`QQ` in `4`, `PRE` in `5`). -/
def tpp_bSpec : List (List (Bool × Bool × ℕ) × List SatSym) :=
  [([tpp_o 4, tpp_o 4, tpp_o 4, tpp_o 5, tpp_o 5, tpp_o 5], [pos, zero, pos, zero, pos, pos, sep])]

/-! ## The printed word -/

/-- The bit of a symbol. -/
def tpp_bb : SatSym → Bool
  | pos => true
  | _ => false

/-- The tag block `false^e true false^(n-1-e)`. -/
def tagB (n e : ℕ) : List Bool := List.replicate e false ++ true :: List.replicate (n - 1 - e) false

/-- The row valuation. -/
def tpp_vR (A B C TG : List Bool) : ℕ → List Bool := fun k =>
  if k = 9 then A else if k = 10 then B else if k = 11 then C else TG

/-- The printed items of row `r` with tag block `TG`. -/
def tpp_rowO (q : ℕ) (r : List SatSym) (TG : List Bool) : List SatSym :=
  let RW := (r.map tpp_bb).reverse
  tpp_blkO (tpp_vR ((RW.drop q).drop q).reverse ((RW.drop q).take q).reverse (RW.take q).reverse TG)
    tpp_rowSpec

def tpp_rowsO (q M : ℕ) : List (List SatSym) → ℕ → List SatSym
  | [], _ => []
  | r :: rs, t => tpp_rowO q r (tagB M t) ++ tpp_rowsO q M rs (t + 1)

/-- The gadget valuation. -/
def tpp_vG (GE TG : List Bool) : ℕ → List Bool := fun k => if k = 14 then GE else TG

def tpp_gadO (q K M c : ℕ) : List SatSym :=
  (List.range q).flatMap fun e =>
    tpp_blkO (tpp_vG (tagB q e) (tagB M (K + c * q + e))) (tpp_gadSpec c)

def tpp_bO (q M : ℕ) : List SatSym :=
  tpp_blkO (fun k => if k = 4 then List.replicate q false else List.replicate M false) tpp_bSpec

/-- The transformer on the rows `cl`. -/
def tpp_Fc (cl : List (List SatSym)) : List SatSym :=
  let q := (cl.headD []).length
  let rows := cl.tail
  let K := rows.length
  let M := K + 3 * q
  tpp_rowsO q M rows 0 ++ tpp_gadO q K M 0 ++ tpp_gadO q K M 1 ++ tpp_gadO q K M 2 ++ tpp_bO q M

/-- **The transformer.** -/
def tpp_F (w : List SatSym) : List SatSym := tpp_Fc (clauses w)

/-! ## One triple row -/

def tpp_rowB : Cmd :=
  .seq (tpp_rdL 8 tpp_bb) (.seq (tpp_spC 11) (.seq (tpp_spC 10) (.seq (move 8 9)
    (.seq (tpp_bldC 7 5 6) (.seq (tpp_blkC tpp_rowSpec) (.seq (drain 7) (.seq (drain 9)
    (.seq (drain 10) (.seq (drain 11) (.seq (.push 5 false) (tpp_pop1 6)))))))))))

def tpp_rowT (Z : ℕ) : ℕ := 1000 * Z + 1000

theorem tpp_ex_rowB (q t u Z : ℕ) (r : List SatSym) (rest : Str) (s : tpp_S) (E : List SatSym)
    (hs : sep ∉ r) (hM : s.Mn = (r ++ [sep]).flatMap ic ++ rest) (hT : s.T = []) (hX : s.X = [])
    (hQ : s.QQ = List.replicate q false) (hP : s.PRE = List.replicate t false)
    (hS : s.SUF = List.replicate u false) (hTG : s.TG = []) (hRW : s.RW = []) (hA : s.A = [])
    (hB : s.B = []) (hC : s.C = []) (hCN : s.CN = []) (hR : s.R = rv E)
    (hZ1 : r.length ≤ Z) (hZ2 : t + u + 1 ≤ Z) (hZ3 : q ≤ Z) :
    ExecLe tpp_rowB s.st (.norm {s with Mn := rest, PRE := List.replicate (t + 1) false, SUF := List.replicate (u - 1) false, R := rv (E ++ tpp_rowO q r (List.replicate t false ++ true :: List.replicate u false))}.st)
      (tpp_rowT Z) := by
  obtain ⟨R0, Mn0, T0, X0, QQ0, PRE0, SUF0, TG0, RW0', A0, B0, C0, GP0, GS0, GE0, CN0⟩ := s
  simp only at hM hT hX hQ hP hS hTG hRW hA hB hC hCN hR
  subst hM hT hX hQ hP hS hTG hRW hA hB hC hCN hR
  set s : tpp_S := ⟨rv E, (r ++ [sep]).flatMap ic ++ rest, [], [], List.replicate q false,
    List.replicate t false, List.replicate u false, [], [], [], [], [], GP0, GS0, GE0, []⟩ with hs0
  have hM : s.Mn = (r ++ [sep]).flatMap ic ++ rest := rfl
  have hRW : s.RW = [] := rfl
  have hT : s.T = [] := rfl
  have hX : s.X = [] := rfl
  have hCN : s.CN = [] := rfl
  have hQ : s.QQ = List.replicate q false := rfl
  have hC : s.C = [] := rfl
  have hB : s.B = [] := rfl
  have hA : s.A = [] := rfl
  have hTG : s.TG = [] := rfl
  have hP : s.PRE = List.replicate t false := rfl
  have hS : s.SUF = List.replicate u false := rfl
  have hR : s.R = rv E := rfl
  set RW0 := (r.map tpp_bb).reverse with hRW0
  have p1 := tpp_ex_rdL (k := 8) (by norm_num) tpp_bb r rest s.st hs hM
  simp only [tpp_u1, tpp_st8, hRW, List.append_nil, tpp_u8] at p1
  set s1 : tpp_S := {s with Mn := rest, RW := RW0}
  have p2 := tpp_ex_spC (k := 11) (by norm_num) (by norm_num) (by norm_num) (by norm_num) q RW0
    s1.st (by simp [s1, hX]) (by simp [s1, hCN]) (by simp [s1, hQ]) (by simp [s1])
  simp only [tpp_u8, tpp_u11, tpp_st11, s1, hC, List.append_nil] at p2
  set s2 : tpp_S := {s with Mn := rest, RW := RW0.drop q, C := (RW0.take q).reverse}
  have p3 := tpp_ex_spC (k := 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) q
    (RW0.drop q) s2.st (by simp [s2, hX]) (by simp [s2, hCN]) (by simp [s2, hQ]) (by simp [s2])
  simp only [tpp_u8, tpp_u10, tpp_st10, s2, hB, List.append_nil] at p3
  set s3 : tpp_S := {s with Mn := rest, RW := (RW0.drop q).drop q, C := (RW0.take q).reverse, B := ((RW0.drop q).take q).reverse}
  have p4 := exec_move (a := 8) (b := 9) (by norm_num) _ s3.st rfl
  simp only [tpp_u8, tpp_u9, tpp_st9, tpp_st8, s3, hA, List.append_nil] at p4
  set A := ((RW0.drop q).drop q).reverse
  set TG := List.replicate t false ++ true :: List.replicate u false
  set s4 : tpp_S := {s with Mn := rest, RW := [], C := (RW0.take q).reverse, B := ((RW0.drop q).take q).reverse, A := A}
  have p5 := tpp_ex_bldC (d := 7) (p := 5) (s := 6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) s4.st (by simp [s4, hX])
  simp only [tpp_u7, tpp_st7, tpp_st5, tpp_st6, s4, hTG, hP, hS, List.append_nil] at p5
  set s5 : tpp_S := {s with Mn := rest, RW := [], C := (RW0.take q).reverse, B := ((RW0.drop q).take q).reverse, A := A, TG := TG}
  have hl : ∀ x ∈ tpp_rowSpec, ∀ y ∈ x.1, tpp_ok y.2.2 ∧ (s5.st y.2.2).length ≤ Z := by
    intro x hx y hy
    rcases (tpp_rowSpec_idx x hx).2.2 y hy with h | h | h | h <;> rw [h] <;>
      refine ⟨by unfold tpp_ok; omega, ?_⟩ <;>
      simp [s5, A, TG, RW0] <;> omega
  have p6 := tpp_ex_blkC Z tpp_rowSpec s5.st E (by simp [s5, hT]) (by simp [s5, hX])
    (by simp [s5, hR]) (fun x hx => ⟨(tpp_rowSpec_idx x hx).1, (tpp_rowSpec_idx x hx).2.1,
      hl x hx⟩)
  simp only [tpp_u0] at p6
  have eO : tpp_blkO s5.st tpp_rowSpec = tpp_rowO q r TG := by
    unfold tpp_rowO
    apply tpp_blkO_congr
    intro x hx y hy
    rcases (tpp_rowSpec_idx x hx).2.2 y hy with h | h | h | h <;> rw [h] <;>
      simp [s5, tpp_vR, A, RW0]
  rw [eO] at p6
  set s6 : tpp_S := {s5 with R := rv (E ++ tpp_rowO q r TG)}
  have p7 := exec_drain 7 _ s6.st rfl
  have p8 := exec_drain 9 _ (update s6.st 7 []) rfl
  have p9 := exec_drain 10 _ (update (update s6.st 7 []) 9 []) rfl
  have p10 := exec_drain 11 _ (update (update (update s6.st 7 []) 9 []) 10 []) rfl
  have p11 := ExecLe.push 5 false (update (update (update (update s6.st 7 []) 9 []) 10 []) 11 [])
  have p12 := tpp_ex_pop1 6 u (update (update (update (update (update s6.st 7 []) 9 []) 10 [])
    11 []) 5 (false :: (update (update (update (update s6.st 7 []) 9 []) 10 []) 11 []) 5))
    (by simp [s6, s5, hS])
  refine (p1.seq_norm (p2.seq_norm (p3.seq_norm ((ExecLe.of p4).seq_norm (p5.seq_norm
    (p6.seq_norm ((ExecLe.of p7).seq_norm ((ExecLe.of p8).seq_norm ((ExecLe.of p9).seq_norm
    ((ExecLe.of p10).seq_norm (p11.seq_norm p12))))))))))).cast ?_ ?_
  · congr 1
    simp only [tpp_u5, tpp_u6, tpp_u7, tpp_u9, tpp_u10, tpp_u11, tpp_st5, s6, s5, s, TG]
    rfl
  · have h12 : tpp_rowSpec.length = 12 := rfl
    simp [s6, s5, s4, s3, A, TG, RW0, hP, hS, h12]
    unfold tpp_rowT
    omega

/-! ## The row loop -/

/-- Peek at stack `k`: break if empty, else restore the bit and run `c`. -/
def tpp_pk (k : ℕ) (c : Cmd) : Cmd := .pop k .brk (.seq (.push k false) c) (.seq (.push k true) c)

theorem tpp_ex_pk {k : ℕ} {c : Cmd} (σ : ℕ → Str) {b : Bool} {M' : Str} (hk : σ k = b :: M')
    {r : Res} {T : ℕ} (h : ExecLe c σ r T) : ExecLe (tpp_pk k c) σ r (T + 2) := by
  have e : update (update σ k M') k (b :: update σ k M' k) = σ := by
    funext j; simp only [update_apply]; split_ifs with h1 <;> simp_all
  refine ExecLe.pop_cons hk ?_
  cases b
  · exact ((ExecLe.push k false _).seq_norm (by rw [e]; exact h)).cast rfl (by omega)
  · exact ((ExecLe.push k true _).seq_norm (by rw [e]; exact h)).cast rfl (by omega)

def tpp_rowL : Cmd := .loop (tpp_pk 1 tpp_rowB)

theorem tpp_ex_rowL (q M Z : ℕ) (hMZ : M ≤ Z) (hqZ : q ≤ Z) :
    ∀ (rows : List (List SatSym)) (t : ℕ) (s : tpp_S) (E : List SatSym),
    (∀ r ∈ rows, sep ∉ r ∧ r.length ≤ Z) → t + rows.length ≤ M →
    s.Mn = (rows.flatMap (· ++ [sep])).flatMap ic → s.T = [] → s.X = [] →
    s.QQ = List.replicate q false → s.PRE = List.replicate t false →
    s.SUF = List.replicate (M - 1 - t) false → s.TG = [] → s.RW = [] → s.A = [] →
    s.B = [] → s.C = [] → s.CN = [] → s.R = rv E →
    ExecLe tpp_rowL s.st (.norm {s with Mn := [], PRE := List.replicate (t + rows.length) false, SUF := List.replicate (M - 1 - (t + rows.length)) false, R := rv (E ++ tpp_rowsO q M rows t)}.st)
      (rows.length * (tpp_rowT Z + 2) + 2)
  | [], t, s, E, _, _, hM, _, _, _, _, _, _, _, _, _, _, _, hR =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hM]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all [tpp_rowsO]) (by simp)
  | r :: rs, t, s, E, hr, ht, hM, hT, hX, hQ, hP, hS, hTG, hRW, hA, hB, hC, hCN, hR => by
    have hM1 : s.Mn = (r ++ [sep]).flatMap ic ++ (rs.flatMap (· ++ [sep])).flatMap ic := by
      rw [hM]; simp
    have hne : s.Mn ≠ [] := by rw [hM1]; simp [ic]
    obtain ⟨b, M', hbm⟩ := List.exists_cons_of_ne_nil hne
    have hl : List.length (r :: rs) = rs.length + 1 := rfl
    have hrow := tpp_ex_rowB q t (M - 1 - t) Z r _ s E (hr r List.mem_cons_self).1 hM1 hT hX hQ hP
      hS hTG hRW hA hB hC hCN hR (hr r List.mem_cons_self).2 (by omega) hqZ
    have hb := tpp_ex_pk (k := 1) s.st (by simpa using hbm) hrow
    have ih := tpp_ex_rowL q M Z hMZ hqZ rs (t + 1) {s with Mn := (rs.flatMap (· ++ [sep])).flatMap ic, PRE := List.replicate (t + 1) false, SUF := List.replicate (M - 1 - t - 1) false, R := rv (E ++ tpp_rowO q r (List.replicate t false ++ true :: List.replicate (M - 1 - t) false))}
      (E ++ tpp_rowO q r (List.replicate t false ++ true :: List.replicate (M - 1 - t) false))
      (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr')) (by omega) rfl hT hX hQ rfl
      (by simp; omega) hTG hRW hA hB hC hCN rfl
    refine (ExecLe.loop_norm hb ih).cast ?_ (by rw [hl]; ring_nf; omega)
    congr 1; cases s
    simp [tpp_rowsO, tagB, show t + 1 + rs.length = t + (rs.length + 1) by omega]

/-! ## The gadget loops -/

def tpp_gB (c : ℕ) : Cmd :=
  .seq (tpp_bldC 14 12 13) (.seq (tpp_bldC 7 5 6) (.seq (tpp_blkC (tpp_gadSpec c))
    (.seq (drain 14) (.seq (drain 7) (.seq (.push 12 false) (.seq (tpp_pop1 13)
    (.seq (.push 5 false) (tpp_pop1 6))))))))

theorem tpp_ex_gB (c q M Z e P : ℕ) (s : tpp_S) (E : List SatSym) (hT : s.T = []) (hX : s.X = [])
    (hP : s.PRE = List.replicate P false) (hS : s.SUF = List.replicate (M - 1 - P) false)
    (hGP : s.GP = List.replicate e false) (hGS : s.GS = List.replicate (q - 1 - e) false)
    (hTG : s.TG = []) (hGE : s.GE = []) (hR : s.R = rv E)
    (heq : e < q) (hPM : P < M) (hqZ : q ≤ Z) (hMZ : M ≤ Z) :
    ExecLe (tpp_gB c) s.st (.norm {s with GP := List.replicate (e + 1) false, GS := List.replicate (q - 1 - (e + 1)) false, PRE := List.replicate (P + 1) false, SUF := List.replicate (M - 1 - (P + 1)) false, R := rv (E ++ tpp_blkO (tpp_vG (tagB q e) (tagB M P)) (tpp_gadSpec c))}.st)
      (tpp_rowT Z) := by
  obtain ⟨R0, Mn0, T0, X0, QQ0, PRE0, SUF0, TG0, RW0, A0, B0, C0, GP0, GS0, GE0, CN0⟩ := s
  simp only at hT hX hP hS hGP hGS hTG hGE hR
  subst hT hX hP hS hGP hGS hTG hGE hR
  set s : tpp_S := ⟨rv E, Mn0, [], [], QQ0, List.replicate P false, List.replicate (M - 1 - P) false, [], RW0, A0, B0, C0, List.replicate e false, List.replicate (q - 1 - e) false, [], CN0⟩ with hs0
  have p1 := tpp_ex_bldC (d := 14) (p := 12) (s := 13) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) s.st rfl
  simp only [tpp_u14, tpp_st14, tpp_st12, tpp_st13, s, List.append_nil] at p1
  set GE := List.replicate e false ++ true :: List.replicate (q - 1 - e) false
  set s1 : tpp_S := {s with GE := GE}
  have p2 := tpp_ex_bldC (d := 7) (p := 5) (s := 6) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) s1.st rfl
  simp only [tpp_u7, tpp_st7, tpp_st5, tpp_st6, s1, s, List.append_nil] at p2
  set TG := List.replicate P false ++ true :: List.replicate (M - 1 - P) false
  set s2 : tpp_S := {s with GE := GE, TG := TG}
  have hl : ∀ x ∈ tpp_gadSpec c, ∀ y ∈ x.1, tpp_ok y.2.2 ∧ (s2.st y.2.2).length ≤ Z := by
    intro x hx y hy
    rcases (tpp_gadSpec_idx c x hx).2.2 y hy with h | h <;> rw [h] <;>
      refine ⟨by unfold tpp_ok; omega, ?_⟩ <;>
      simp [s2, GE, TG] <;> omega
  have p3 := tpp_ex_blkC Z (tpp_gadSpec c) s2.st E rfl rfl rfl
    (fun x hx => ⟨(tpp_gadSpec_idx c x hx).1, (tpp_gadSpec_idx c x hx).2.1, hl x hx⟩)
  simp only [tpp_u0] at p3
  have eO : tpp_blkO s2.st (tpp_gadSpec c) = tpp_blkO (tpp_vG (tagB q e) (tagB M P))
      (tpp_gadSpec c) := by
    apply tpp_blkO_congr
    intro x hx y hy
    rcases (tpp_gadSpec_idx c x hx).2.2 y hy with h | h <;> rw [h] <;>
      simp [s2, tpp_vG, GE, TG, tagB]
  rw [eO] at p3
  set s3 : tpp_S := {s2 with R := rv (E ++ tpp_blkO (tpp_vG (tagB q e) (tagB M P)) (tpp_gadSpec c))}
  have p4 := exec_drain 14 _ s3.st rfl
  have p5 := exec_drain 7 _ (update s3.st 14 []) rfl
  have p6 := ExecLe.push 12 false (update (update s3.st 14 []) 7 [])
  have p7 := tpp_ex_pop1 13 (q - 1 - e) (update (update (update s3.st 14 []) 7 []) 12
    (false :: (update (update s3.st 14 []) 7 []) 12)) (by simp [s3, s2, s])
  have p8 := ExecLe.push 5 false (update (update (update (update s3.st 14 []) 7 []) 12
    (false :: (update (update s3.st 14 []) 7 []) 12)) 13 (List.replicate (q - 1 - e - 1) false))
  have p9 := tpp_ex_pop1 6 (M - 1 - P) (update (update (update (update (update s3.st 14 []) 7 []) 12
    (false :: (update (update s3.st 14 []) 7 []) 12)) 13 (List.replicate (q - 1 - e - 1) false)) 5
    (false :: (update (update (update (update s3.st 14 []) 7 []) 12
    (false :: (update (update s3.st 14 []) 7 []) 12)) 13 (List.replicate (q - 1 - e - 1) false)) 5))
    (by simp [s3, s2, s])
  refine (p1.seq_norm (p2.seq_norm (p3.seq_norm ((ExecLe.of p4).seq_norm ((ExecLe.of p5).seq_norm
    (p6.seq_norm (p7.seq_norm (p8.seq_norm p9)))))))).cast ?_ ?_
  · congr 1
    simp only [tpp_u5, tpp_u6, tpp_u7, tpp_u12, tpp_u13, tpp_u14, tpp_st5, tpp_st12, s3, s2, s]
    simp [List.replicate_succ, show q - 1 - e - 1 = q - 1 - (e + 1) by omega,
      show M - 1 - P - 1 = M - 1 - (P + 1) by omega]
  · have h3 : (tpp_gadSpec c).length = 3 := rfl
    simp [s3, s2, GE, TG, h3]
    unfold tpp_rowT
    omega

def tpp_gL (c : ℕ) : Cmd := .loop (.pop 15 .brk (tpp_gB c) (tpp_gB c))

theorem tpp_ex_gL (c q M Z P0 : ℕ) (hqZ : q ≤ Z) (hMZ : M ≤ Z) : ∀ (n e : ℕ) (s : tpp_S)
    (E : List SatSym), s.CN = List.replicate n false → e + n ≤ q → P0 + e + n ≤ M →
    s.T = [] → s.X = [] → s.PRE = List.replicate (P0 + e) false →
    s.SUF = List.replicate (M - 1 - (P0 + e)) false → s.GP = List.replicate e false →
    s.GS = List.replicate (q - 1 - e) false → s.TG = [] → s.GE = [] → s.R = rv E →
    ExecLe (tpp_gL c) s.st (.norm {s with CN := [], GP := List.replicate (e + n) false, GS := List.replicate (q - 1 - (e + n)) false, PRE := List.replicate (P0 + e + n) false, SUF := List.replicate (M - 1 - (P0 + e + n)) false, R := rv (E ++ (List.range n).flatMap fun i => tpp_blkO (tpp_vG (tagB q (e + i)) (tagB M (P0 + e + i))) (tpp_gadSpec c))}.st)
      (n * (tpp_rowT Z + 1) + 2)
  | 0, e, s, E, hCN, _, _, _, _, hP, hS, hGP, hGS, _, _, hR =>
    (ExecLe.loop_brk (ExecLe.pop_nil (by simp [hCN]) (ExecLe.brk _))).cast
      (by congr 1; cases s; simp_all) (by simp)
  | n + 1, e, s, E, hCN, hen, hPn, hT, hX, hP, hS, hGP, hGS, hTG, hGE, hR => by
    have hb := tpp_ex_gB c q M Z e (P0 + e) {s with CN := List.replicate n false} E hT hX hP hS
      hGP hGS hTG hGE hR (by omega) (by omega) hqZ hMZ
    have hb' : ExecLe (.pop 15 .brk (tpp_gB c) (tpp_gB c)) s.st _ (tpp_rowT Z + 1) :=
      ExecLe.pop_same (b := false) (s := List.replicate n false) (by simp [hCN, List.replicate_succ])
        (by rw [tpp_u15]; exact hb)
    have ih := tpp_ex_gL c q M Z P0 hqZ hMZ n (e + 1) {s with CN := List.replicate n false, GP := List.replicate (e + 1) false, GS := List.replicate (q - 1 - (e + 1)) false, PRE := List.replicate (P0 + e + 1) false, SUF := List.replicate (M - 1 - (P0 + e + 1)) false, R := rv (E ++ tpp_blkO (tpp_vG (tagB q e) (tagB M (P0 + e))) (tpp_gadSpec c))}
      _ rfl (by omega) (by omega) hT hX (by simp [Nat.add_assoc]) (by simp [Nat.add_assoc])
      rfl rfl hTG hGE rfl
    refine (ExecLe.loop_norm hb' ih).cast ?_ (by rw [Nat.succ_mul]; omega)
    congr 1; cases s
    simp only [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_zero,
      List.append_assoc]
    simp [show e + 1 + n = e + (n + 1) by omega, show P0 + e + 1 + n = P0 + e + (n + 1) by omega,
      Nat.add_assoc, Nat.add_comm 1]

def tpp_gadC (c : ℕ) : Cmd :=
  .seq (drain 12) (.seq (copyVia 4 13 3) (.seq (tpp_pop1 13) (.seq (copyVia 4 15 3) (tpp_gL c))))

theorem tpp_ex_gadC (c q M Z P0 g : ℕ) (hqZ : q ≤ Z) (hMZ : M ≤ Z) (hgZ : g ≤ Z) (s : tpp_S)
    (E : List SatSym) (hCN : s.CN = []) (hPM : P0 + q ≤ M) (hT : s.T = []) (hX : s.X = [])
    (hQ : s.QQ = List.replicate q false)
    (hP : s.PRE = List.replicate P0 false) (hS : s.SUF = List.replicate (M - 1 - P0) false)
    (hGP : s.GP = List.replicate g false) (hGS : s.GS = []) (hTG : s.TG = []) (hGE : s.GE = [])
    (hR : s.R = rv E) :
    ExecLe (tpp_gadC c) s.st (.norm {s with GP := List.replicate q false, PRE := List.replicate (P0 + q) false, SUF := List.replicate (M - 1 - (P0 + q)) false, R := rv (E ++ (List.range q).flatMap fun i => tpp_blkO (tpp_vG (tagB q i) (tagB M (P0 + i))) (tpp_gadSpec c))}.st)
      (q * (tpp_rowT Z + 1) + 12 * Z + 20) := by
  obtain ⟨R0, Mn0, T0, X0, QQ0, PRE0, SUF0, TG0, RW0, A0, B0, C0, GP0, GS0, GE0, CN0⟩ := s
  simp only at hCN hT hX hQ hP hS hGP hGS hTG hGE hR
  subst hCN hT hX hQ hP hS hGP hGS hTG hGE hR
  set s : tpp_S := ⟨rv E, Mn0, [], [], List.replicate q false, List.replicate P0 false, List.replicate (M - 1 - P0) false, [], RW0, A0, B0, C0, List.replicate g false, [], [], []⟩ with hs0
  have hX : s.X = [] := rfl
  have hT : s.T = [] := rfl
  have hTG : s.TG = [] := rfl
  have hGE : s.GE = [] := rfl
  have hR : s.R = rv E := rfl
  have hP : s.PRE = List.replicate P0 false := rfl
  have hS : s.SUF = List.replicate (M - 1 - P0) false := rfl
  have hGP : s.GP = List.replicate g false := rfl
  have hQ : s.QQ = List.replicate q false := rfl
  have hGS : s.GS = [] := rfl
  have hCN : s.CN = [] := rfl
  have p1 := exec_drain 12 _ s.st rfl
  rw [tpp_u12] at p1
  have p2 := ExecLe.of (exec_copyVia (a := 4) (b := 13) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) {s with GP := []}.st (by simp [hX]))
  simp only [tpp_u13, tpp_st4, tpp_st13, hQ, hGS, List.append_nil] at p2
  have p3 := tpp_ex_pop1 13 q {s with GP := [], GS := List.replicate q false}.st rfl
  rw [tpp_u13] at p3
  have p4 := ExecLe.of (exec_copyVia (a := 4) (b := 15) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) {s with GP := [], GS := List.replicate (q - 1) false}.st (by simp [hX]))
  simp only [tpp_u15, tpp_st4, tpp_st15, hQ, hCN, List.append_nil] at p4
  have p5 := tpp_ex_gL c q M Z P0 hqZ hMZ q 0 {s with GP := [], GS := List.replicate (q - 1) false, CN := List.replicate q false} E rfl (by omega) (by omega) hT hX (by simp [hP])
    (by simp [hS]) rfl (by simp) hTG hGE hR
  refine ((ExecLe.of p1).seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm p5)))).cast ?_ ?_
  · congr 1; simp [s]
  · rw [tpp_st12, hGP]; simp; omega

/-! ## The main phase -/

def tpp_hdC : Cmd := tpp_rdL 4 fun _ => false
def tpp_cnC : Cmd := .seq (copyVia 1 2 3) tpp_cnL
def tpp_setC : Cmd :=
  .seq (copyVia 4 6 3) (.seq (copyVia 4 6 3) (.seq (copyVia 4 6 3) (tpp_pop1 6)))

def tpp_main : Cmd :=
  .seq tpp_hdC (.seq tpp_cnC (.seq tpp_setC (.seq tpp_rowL (.seq (tpp_gadC 0)
    (.seq (tpp_gadC 1) (.seq (tpp_gadC 2) (tpp_blkC tpp_bSpec)))))))

def tpp_s0 (Mn : Str) : tpp_S := ⟨[], Mn, [], [], [], [], [], [], [], [], [], [], [], [], [], []⟩

theorem tpp_count_sep : ∀ L : List (List SatSym), (∀ c ∈ L, sep ∉ c) →
    (L.flatMap (· ++ [sep])).count sep = L.length
  | [], _ => rfl
  | c :: L, h => by
    rw [List.flatMap_cons, List.count_append, tpp_count_sep L (fun c' hc' => h c'
      (List.mem_cons_of_mem _ hc')), List.count_append, List.count_eq_zero_of_not_mem
      (h c List.mem_cons_self)]
    simp; omega

theorem tpp_len_le : ∀ (L : List (List SatSym)), ∀ r ∈ L, r.length + 1 ≤ (L.flatMap (· ++ [sep])).length
  | [], r, h => by simp at h
  | c :: L, r, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := tpp_len_le L r h; simp only [List.flatMap_cons, List.length_append] at this ⊢; omega

theorem tpp_cnt_le : ∀ (L : List (List SatSym)), L.length ≤ (L.flatMap (· ++ [sep])).length
  | [] => le_rfl
  | c :: L => by
    have := tpp_cnt_le L; simp only [List.flatMap_cons, List.length_append, List.length_cons] at this ⊢
    omega

def tpp_Tm (N : ℕ) : ℕ := (4 * N + 10) * (tpp_rowT (5 * N + 5) + 2) + 2000 * N + 2000

theorem tpp_ex_main (cl : List (List SatSym)) (hsep : ∀ r ∈ cl, sep ∉ r) (N : ℕ)
    (hN : (cl.flatMap (· ++ [sep])).length ≤ N) :
    ∃ s : tpp_S, ExecLe tpp_main (tpp_s0 ((cl.flatMap (· ++ [sep])).flatMap ic)).st (.norm s.st)
      (tpp_Tm N) ∧ s.R = rv (tpp_Fc cl) := by
  set q := (cl.headD []).length with hq
  set rows := cl.tail with hrows
  set K := rows.length with hK
  set M := K + 3 * q with hMd
  set Z := 5 * N + 5 with hZ
  have hrows_sep : ∀ r ∈ rows, sep ∉ r := fun r hr => hsep r (List.mem_of_mem_tail hr)
  have hcl : cl = [] ∨ cl = (cl.headD []) :: rows := by
    rcases cl with _ | ⟨c, L⟩
    · left; rfl
    · right; rfl
  have hqN : q ≤ N := by
    rcases hcl with h | h
    · simp [hq, h]
    · have := tpp_len_le cl (cl.headD []) (by rw [h]; exact List.mem_cons_self); omega
  have hKN : K ≤ N := by
    have := tpp_cnt_le cl
    have : K ≤ cl.length := by simp [hK, hrows]
    omega
  have hLr : ((rows.flatMap (· ++ [sep])).length) ≤ N := by
    rcases hcl with h | h
    · simp [hrows, h]
    · rw [h] at hN; simp only [List.flatMap_cons, List.length_append] at hN; omega
  have hrZ : ∀ r ∈ rows, sep ∉ r ∧ r.length ≤ Z := fun r hr =>
    ⟨hrows_sep r hr, by have := tpp_len_le rows r hr; omega⟩
  -- header
  set s1 : tpp_S := {tpp_s0 ((rows.flatMap (· ++ [sep])).flatMap ic) with QQ := List.replicate q false}
  have p1 : ExecLe tpp_hdC (tpp_s0 ((cl.flatMap (· ++ [sep])).flatMap ic)).st (.norm s1.st)
      (4 * N + 4) := by
    rcases hcl with h | h
    · have e : ((cl.flatMap (· ++ [sep])).flatMap ic) = [] := by rw [h]; rfl
      rw [e]
      refine (ExecLe.loop_brk (ExecLe.pop_nil rfl (ExecLe.brk _))).cast ?_ (by omega)
      congr 1; simp [s1, tpp_s0, hrows, hq, h]
    · have e : (cl.flatMap (· ++ [sep])).flatMap ic =
          (cl.headD [] ++ [sep]).flatMap ic ++ (rows.flatMap (· ++ [sep])).flatMap ic := by
        conv_lhs => rw [h]
        simp
      have := tpp_ex_rdL (k := 4) (by norm_num) (fun _ => false) (cl.headD [])
        ((rows.flatMap (· ++ [sep])).flatMap ic) (tpp_s0 ((cl.flatMap (· ++ [sep])).flatMap ic)).st
        (hsep _ (by rw [h]; exact List.mem_cons_self)) e
      refine this.cast ?_ (by omega)
      congr 1; simp [s1, tpp_s0, hq]
  -- counting
  set L := rows.flatMap (· ++ [sep])
  have p2a := ExecLe.of (exec_copyVia (a := 1) (b := 2) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) s1.st rfl)
  have p2b := tpp_ex_cnL L (update s1.st 2 (s1.st 1 ++ s1.st 2)) (by simp [s1, tpp_s0, L])
  rw [tpp_count_sep rows hrows_sep] at p2b
  set s2 : tpp_S := {s1 with SUF := List.replicate K false}
  have p2 : ExecLe tpp_cnC s1.st (.norm s2.st) (15 * N + 10) := by
    refine (p2a.seq_norm p2b).cast ?_ ?_
    · congr 1; simp [s2, s1, tpp_s0]; rfl
    · have : (s1.st 1).length = 2 * L.length := length_flatMap_ic L
      rw [this]; omega
  -- setup
  have p3a := ExecLe.of (exec_copyVia (a := 4) (b := 6) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) s2.st rfl)
  have p3b := ExecLe.of (exec_copyVia (a := 4) (b := 6) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) (update s2.st 6 (s2.st 4 ++ s2.st 6)) (by simp [s2, s1, tpp_s0]))
  have p3c := ExecLe.of (exec_copyVia (a := 4) (b := 6) (t := 3) (by norm_num) (by norm_num)
    (by norm_num) (update (update s2.st 6 (s2.st 4 ++ s2.st 6)) 6
      ((update s2.st 6 (s2.st 4 ++ s2.st 6)) 4 ++ (update s2.st 6 (s2.st 4 ++ s2.st 6)) 6))
    (by simp [s2, s1, tpp_s0]))
  have p3d := tpp_ex_pop1 6 M (update (update (update s2.st 6 (s2.st 4 ++ s2.st 6)) 6
      ((update s2.st 6 (s2.st 4 ++ s2.st 6)) 4 ++ (update s2.st 6 (s2.st 4 ++ s2.st 6)) 6)) 6
      ((update (update s2.st 6 (s2.st 4 ++ s2.st 6)) 6
      ((update s2.st 6 (s2.st 4 ++ s2.st 6)) 4 ++ (update s2.st 6 (s2.st 4 ++ s2.st 6)) 6)) 4 ++
      (update (update s2.st 6 (s2.st 4 ++ s2.st 6)) 6
      ((update s2.st 6 (s2.st 4 ++ s2.st 6)) 4 ++ (update s2.st 6 (s2.st 4 ++ s2.st 6)) 6)) 6))
    (by simp [s2, s1, tpp_s0, hMd]; try ring_nf)
  set s3 : tpp_S := {s1 with SUF := List.replicate (M - 1 - 0) false}
  have p3 : ExecLe tpp_setC s2.st (.norm s3.st) (15 * N + 20) := by
    refine (p3a.seq_norm (p3b.seq_norm (p3c.seq_norm p3d))).cast ?_ ?_
    · congr 1; simp [s3, s2, s1, tpp_s0]
    · simp [s2, s1]; omega
  -- rows
  have hMZ : M ≤ Z := by omega
  have p4 := tpp_ex_rowL q M Z hMZ (by omega) rows 0 s3 [] hrZ (by omega) rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  set E1 := tpp_rowsO q M rows 0
  set s4 : tpp_S := {s3 with Mn := [], PRE := List.replicate (0 + rows.length) false, SUF := List.replicate (M - 1 - (0 + rows.length)) false, R := rv ([] ++ E1)}
  -- gadgets
  have p5 := tpp_ex_gadC 0 q M Z (K + 0 * q) 0 (by omega) hMZ (by omega) s4 ([] ++ E1) rfl
    (by omega) rfl rfl rfl (by simp [s4, hK]) (by simp [s4, hK]) rfl rfl rfl rfl rfl
  set E2 := (List.range q).flatMap fun i => tpp_blkO (tpp_vG (tagB q i) (tagB M (K + 0 * q + i))) (tpp_gadSpec 0)
  set s5 : tpp_S := {s4 with GP := List.replicate q false, PRE := List.replicate (K + 0 * q + q) false, SUF := List.replicate (M - 1 - (K + 0 * q + q)) false, R := rv ([] ++ E1 ++ E2)}
  have p6 := tpp_ex_gadC 1 q M Z (K + 1 * q) q (by omega) hMZ (by omega) s5 ([] ++ E1 ++ E2) rfl
    (by omega) rfl rfl rfl (by simp [s5]; try ring_nf) (by simp [s5]; try ring_nf) rfl rfl rfl rfl rfl
  set E3 := (List.range q).flatMap fun i => tpp_blkO (tpp_vG (tagB q i) (tagB M (K + 1 * q + i))) (tpp_gadSpec 1)
  set s6 : tpp_S := {s5 with GP := List.replicate q false, PRE := List.replicate (K + 1 * q + q) false, SUF := List.replicate (M - 1 - (K + 1 * q + q)) false, R := rv ([] ++ E1 ++ E2 ++ E3)}
  have p7 := tpp_ex_gadC 2 q M Z (K + 2 * q) q (by omega) hMZ (by omega) s6 ([] ++ E1 ++ E2 ++ E3)
    rfl (by omega) rfl rfl rfl (by simp [s6]; try ring_nf) (by simp [s6]; try ring_nf) rfl rfl rfl rfl rfl
  set E4 := (List.range q).flatMap fun i => tpp_blkO (tpp_vG (tagB q i) (tagB M (K + 2 * q + i))) (tpp_gadSpec 2)
  set s7 : tpp_S := {s6 with GP := List.replicate q false, PRE := List.replicate (K + 2 * q + q) false, SUF := List.replicate (M - 1 - (K + 2 * q + q)) false, R := rv ([] ++ E1 ++ E2 ++ E3 ++ E4)}
  -- bound row
  have hbi : ∀ p ∈ tpp_bSpec, p.1.length ≤ 6 ∧ p.2.length ≤ 7 ∧ ∀ x ∈ p.1, x.2.2 = 4 ∨ x.2.2 = 5 := by
    simp [tpp_bSpec]
  have p8 := tpp_ex_blkC Z tpp_bSpec s7.st ([] ++ E1 ++ E2 ++ E3 ++ E4) rfl rfl rfl
    (fun p hp => ⟨(hbi p hp).1, (hbi p hp).2.1, fun x hx => by
      rcases (hbi p hp).2.2 x hx with h | h <;> rw [h] <;>
        exact ⟨by unfold tpp_ok; omega, by simp [s7, s6, s5, s4, s3, s1, tpp_s0]; omega⟩⟩)
  have eB : tpp_blkO s7.st tpp_bSpec = tpp_bO q M := by
    unfold tpp_bO
    apply tpp_blkO_congr
    intro p hp x hx
    rcases (hbi p hp).2.2 x hx with h | h <;> rw [h] <;> simp [s7, s6, s5, s4, s3, s1, tpp_s0]
    omega
  rw [eB] at p8
  refine ⟨_, (p1.seq_norm (p2.seq_norm (p3.seq_norm (p4.seq_norm (p5.seq_norm (p6.seq_norm
    (p7.seq_norm p8))))))).cast (by rw [tpp_u0]) ?_, ?_⟩
  · have h1 : tpp_bSpec.length = 1 := rfl
    rw [h1]
    have hK' : rows.length = K := rfl
    have b1 : K * (tpp_rowT Z + 2) ≤ N * (tpp_rowT Z + 2) := Nat.mul_le_mul_right _ hKN
    have b2 : q * (tpp_rowT Z + 1) ≤ N * (tpp_rowT Z + 2) := Nat.mul_le_mul hqN (by omega)
    unfold tpp_Tm
    rw [← hZ, hK']
    nlinarith
  · show _ = rv (tpp_rowsO q M rows 0 ++ tpp_gadO q K M 0 ++ tpp_gadO q K M 1 ++
      tpp_gadO q K M 2 ++ tpp_bO q M)
    simp only [s7, E1, E2, E3, E4, tpp_gadO, List.nil_append, List.append_assoc]

/-! ## The program -/

/-- The transformer program. -/
def tpp_redCmd : Cmd := .seq parseLoop (.seq (trimC 4) (.seq (move 4 1) tpp_main))

theorem tpp_exec_redCmd (x : Str) : ∃ σ', ExecLe tpp_redCmd (init [x]).stk (.norm σ')
    (100000 * (x.length + 2) ^ 2) ∧ σ' 0 = ((tpp_F (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ₁ := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := exec_trimC_word 4 w σ₁ (by simp [σ₁, he 4 (by decide)])
  set σ₂ := update σ₁ 4 (((trunc w).flatMap ic).reverse)
  have p3 := exec_move (a := 4) (b := 1) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 4 []) 1 ((σ₂ 4).reverse ++ σ₂ 1) =
      (tpp_s0 (((clauses w).flatMap (· ++ [sep])).flatMap ic)).st := by
    funext j
    by_cases hj : j < 16
    · interval_cases j <;> simp [σ₂, σ₁, he, trunc, tpp_S.st, tpp_s0]
    · rw [tpp_st_big _ _ (by omega)]
      simp [σ₂, σ₁, he j (by omega), show j ≠ 0 by omega, show j ≠ 1 by omega,
        show j ≠ 4 by omega]
  rw [hσ] at p3
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  obtain ⟨s, p4, hs⟩ := tpp_ex_main (clauses w) (sep_not_mem_clauses w) x.length
    (by have : (trunc w).length = ((clauses w).flatMap (· ++ [sep])).length := rfl; omega)
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm p4))).cast rfl ?_, ?_⟩
  · have htl : (σ₂ 4).length = 2 * (trunc w).length := by
      simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
    rw [htl]
    unfold tpp_Tm tpp_rowT
    nlinarith
  · rw [tpp_st0, hs]; rfl

theorem tpp_T_le (n : ℕ) : 100000 * (n + 2) ^ 2 ≤ tb 20 n := by
  unfold tb
  have h7 : 2 ^ 18 ≤ (n + 2) ^ 18 := Nat.pow_le_pow_left (by omega) 18
  have e : (n + 2) ^ 20 = (n + 2) ^ 18 * (n + 2) ^ 2 := by ring
  rw [e]
  exact Nat.mul_le_mul_right _ (le_trans (by norm_num) h7)

/-- `tpp_F` is polynomial-time computable. -/
theorem tpp_F_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    tpp_F) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    tpp_redCmd 0 20 (fun x => tpp_F (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := tpp_exec_redCmd x
      exact ⟨σ', h1.mono (tpp_T_le _), h2⟩)
    tpp_F (fun t => (congrArg tpp_F (FunBridge.dec2_flatMap_ic t)).symm)

/-! ## `tpp_F (DMI w) = TPI w` -/

theorem tpp_map_c (l : List Bool) : l.map (tpp_sl false true) = l := by
  conv_rhs => rw [← List.map_id l]
  congr 1; funext b; cases b <;> rfl

theorem tpp_map_z (l : List Bool) : l.map (tpp_sl false false) = List.replicate l.length false := by
  rw [← List.map_const']; congr 1; funext b; cases b <;> rfl

theorem tpp_map_o (l : List Bool) : l.map (tpp_sl true true) = List.replicate l.length true := by
  rw [← List.map_const']; congr 1; funext b; cases b <;> rfl

theorem tpp_map_n (n e : ℕ) : (ohB n e).map (tpp_sl true false) = coB n e := by
  simp only [ohB, coB, List.map_map]
  congr 1; funext i; by_cases h : i = e <;> simp [h, tpp_sl]

@[simp] theorem tpp_len_ohB (n e : ℕ) : (ohB n e).length = n := by simp [ohB]
@[simp] theorem tpp_len_coB (n e : ℕ) : (coB n e).length = n := by simp [coB]

theorem tpp_tagB (n e : ℕ) (h : e < n) : tagB n e = ohB n e := by
  apply List.ext_getElem
  · simp [tagB]; omega
  · intro i h1 h2
    simp only [ohB, List.getElem_map, List.getElem_range, tagB, List.getElem_append,
      List.length_replicate, List.getElem_cons, List.getElem_replicate]
    split_ifs <;> simp_all <;> omega

theorem tpp_dg_eq (bf bt : Bool) (β : List Bool) :
    tpp_dg bf bt β = (β.map (tpp_sl bf bt)).flatMap tpp_g := by
  simp [tpp_dg, List.flatMap_map]

theorem tpp_item {q M : ℕ} (v : ℕ → List Bool) (sp : List (Bool × Bool × ℕ)) (s1 s2 : Bool) (x : El)
    (h : sp.flatMap (fun p => (v p.2.2).map (tpp_sl p.1 p.2.1)) =
      blkI q x 0 ++ blkI q x 1 ++ blkI q x 2 ++ blkL M x 0 ++ blkL M x 1 ++ blkL M x 2)
    (h1 : st1 x = s1) (h2 : st2 x = s2) :
    tpp_itO v sp (tpp_cs s1 s2) = elRow q M x ++ [sep] := by
  have e1 : sp.flatMap (fun p => tpp_dg p.1 p.2.1 (v p.2.2)) =
      (sp.flatMap (fun p => (v p.2.2).map (tpp_sl p.1 p.2.1))).flatMap tpp_g := by
    rw [List.flatMap_assoc]; simp only [tpp_dg_eq]
  unfold tpp_itO elRow digs
  rw [e1, h, ← h1, ← h2]
  simp only [List.flatMap_append, List.append_assoc]
  congr 1

theorem tpp_blkO_eq {q M : ℕ} (v : ℕ → List Bool) :
    ∀ (its : List (List (Bool × Bool × ℕ) × List SatSym)) (xs : List El),
    List.Forall₂ (fun p x => tpp_itO v p.1 p.2 = elRow q M x ++ [sep]) its xs →
    tpp_blkO v its = (xs.map (elRow q M)).flatMap (· ++ [sep])
  | [], [], _ => rfl
  | p :: ps, x :: xs, h => by
    rcases List.forall₂_cons.1 h with ⟨h1, h2⟩
    simp only [tpp_blkO, List.flatMap_cons, List.map_cons] at h1 ⊢
    rw [h1]
    exact congrArg _ (tpp_blkO_eq v ps xs h2)

theorem tpp_oh_bb (q a : ℕ) : (oh q a).map tpp_bb = ohB q a := by
  simp only [oh, ohB, List.map_map]
  congr 1; funext i; by_cases h : i = a <;> simp [h, tpp_bb]

theorem tpp_row_eq (q M t : ℕ) (ht : t < M) (x : ℕ × ℕ × ℕ) :
    tpp_rowO q (triRow q x) (tagB M t) = ((triBlk t x).map (elRow q M)).flatMap (· ++ [sep]) := by
  obtain ⟨a, b, c⟩ := x
  have hr : (triRow q (a, b, c)).map tpp_bb = ohB q a ++ ohB q b ++ ohB q c := by
    simp [triRow, tpp_oh_bb]
  have hR : ((triRow q (a, b, c)).map tpp_bb).reverse =
      (ohB q c).reverse ++ (ohB q b).reverse ++ (ohB q a).reverse := by
    rw [hr]; simp
  have eC : (((triRow q (a, b, c)).map tpp_bb).reverse.take q).reverse = ohB q c := by
    rw [hR, List.append_assoc, List.take_left' (by simp)]; simp
  have eB : ((((triRow q (a, b, c)).map tpp_bb).reverse.drop q).take q).reverse = ohB q b := by
    rw [hR, List.append_assoc, List.drop_left' (by simp), List.take_left' (by simp)]; simp
  have eA : ((((triRow q (a, b, c)).map tpp_bb).reverse.drop q).drop q).reverse = ohB q a := by
    rw [hR, List.append_assoc, List.drop_left' (by simp), List.drop_left' (by simp)]; simp
  unfold tpp_rowO
  simp only []
  rw [eA, eB, eC, tpp_tagB M t ht]
  apply tpp_blkO_eq
  simp only [tpp_rowSpec, triBlk, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply tpp_item <;>
    simp [tpp_vR, blkI, blkL, st1, st2, tpp_map_c, tpp_map_z, tpp_map_o, tpp_map_n] <;>
    first | omega | simp only [List.replicate_add, List.append_assoc]

theorem tpp_gad_eq (q K M c e : ℕ) (hc : c < 3) (he : e < q) (hP : K + c * q + e < M) :
    tpp_blkO (tpp_vG (tagB q e) (tagB M (K + c * q + e))) (tpp_gadSpec c) =
      ((gadBlk q K c e).map (elRow q M)).flatMap (· ++ [sep]) := by
  rw [tpp_tagB q e he, tpp_tagB M _ hP]
  apply tpp_blkO_eq
  interval_cases c <;>
  simp only [tpp_gadSpec, gadBlk, List.forall₂_cons, List.Forall₂.nil, and_true] <;>
  refine ⟨?_, ?_, ?_⟩ <;>
    apply tpp_item <;>
    simp [tpp_vG, tpp_ib, blkI, blkL, st1, st2, tpp_map_c, tpp_map_z, tpp_map_o, tpp_map_n] <;>
    first | omega | simp only [List.replicate_add, List.append_assoc]

theorem tpp_gadO_eq (q K M c : ℕ) (hc : c < 3) (hM : K + 3 * q ≤ M) :
    tpp_gadO q K M c = (((List.range q).flatMap fun e => gadBlk q K c e).map (elRow q M)).flatMap
      (· ++ [sep]) := by
  unfold tpp_gadO
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro e he
  rw [List.mem_range] at he
  apply tpp_gad_eq q K M c e hc he
  have : c * q + q ≤ 3 * q := by
    have := Nat.mul_le_mul_right q (show c + 1 ≤ 3 by omega); rw [Nat.add_mul] at this; omega
  omega

theorem tpp_range3 (q K : ℕ) : ((List.range (3 * q)).flatMap fun u => gadBlk q K (u / q) (u % q)) =
    ((List.range q).flatMap fun e => gadBlk q K 0 e) ++
      ((List.range q).flatMap fun e => gadBlk q K 1 e) ++
      ((List.range q).flatMap fun e => gadBlk q K 2 e) := by
  rw [show 3 * q = q + q + q by ring, List.range_add, List.range_add, List.flatMap_append,
    List.flatMap_append]
  simp only [List.flatMap_map]
  congr 1; congr 1
  · apply List.flatMap_congr; intro e he; rw [List.mem_range] at he
    rw [Nat.div_eq_of_lt he, Nat.mod_eq_of_lt he]
  · apply List.flatMap_congr; intro e he; rw [List.mem_range] at he
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega), Nat.add_mod_left, Nat.mod_eq_of_lt he]
  · apply List.flatMap_congr; intro e he; rw [List.mem_range] at he
    rw [Nat.div_eq_of_lt_le (k := 2) (by omega) (by omega), Nat.add_assoc, Nat.add_mod_left,
      Nat.add_mod_left, Nat.mod_eq_of_lt he]

theorem tpp_dg_oo : ∀ n : ℕ, tpp_dg true true (List.replicate n false) =
    (List.replicate n [pos, zero]).flatten
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, ← tpp_dg_oo n]; rfl

theorem tpp_bO_eq (q M : ℕ) : tpp_bO q M = bRow q M ++ [sep] := by
  simp only [tpp_bO, tpp_blkO, tpp_bSpec, tpp_itO, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, tpp_o, bRow]
  simp only [eq_false (show (5 : ℕ) ≠ 4 by omega), if_true, if_false, tpp_dg_oo]
  rw [show 3 * q + 3 * M + 2 = q + q + q + M + M + M + 1 + 1 by ring]
  simp only [List.replicate_add, List.flatten_append, List.append_assoc]
  rfl

theorem tpp_rows_eq (q M : ℕ) : ∀ (ts : List (ℕ × ℕ × ℕ)) (t : ℕ), t + ts.length ≤ M →
    tpp_rowsO q M (ts.map (triRow q)) t =
      (((List.range ts.length).flatMap fun l => triBlk (t + l) (ts.getD l (0, 0, 0))).map
        (elRow q M)).flatMap (· ++ [sep])
  | [], t, _ => rfl
  | x :: ts, t, h => by
    have ih := tpp_rows_eq q M ts (t + 1) (by simp at h; omega)
    simp only [List.map_cons, tpp_rowsO, List.length_cons, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map, List.getD_cons_zero, List.getD_cons_succ,
      Nat.add_zero, List.map_append, List.flatMap_append]
    have hf : (fun a => triBlk (t + (a + 1)) (ts.getD a (0, 0, 0))) =
        fun l => triBlk (t + 1 + l) (ts.getD l (0, 0, 0)) :=
      funext fun l => by rw [show t + (l + 1) = t + 1 + l by omega]
    rw [hf, ih, tpp_row_eq q M t (by simp at h; omega), List.flatMap_map, List.flatMap_map]

/-- **The transformer maps the 3DM instance to the 3-PARTITION instance.** -/
theorem tpp_F_DMI (w : List SatSym) : tpp_F (DMI w) = TPI w := by
  have hc : clauses (DMI w) = List.replicate (qB w) zero :: triRows w := by
    unfold DMI
    apply Pnp.Karp.Clique.clauses_flatMap
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · simp
    · simp only [triRows, List.mem_map] at hc
      obtain ⟨t, -, rfl⟩ := hc
      simp only [triRow, oh, List.mem_append, List.mem_map, not_or]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro ⟨i, -, hi⟩ <;> split_ifs at hi
  unfold tpp_F tpp_Fc
  rw [hc]
  simp only [List.headD_cons, List.tail_cons, List.length_replicate, triRows, List.length_map]
  unfold TPI TPW els mT
  set q := qB w
  set ts := tris w
  rw [tpp_rows_eq q _ ts 0 (by omega), tpp_range3, tpp_gadO_eq q _ _ 0 (by omega) le_rfl,
    tpp_gadO_eq q _ _ 1 (by omega) le_rfl, tpp_gadO_eq q _ _ 2 (by omega) le_rfl, tpp_bO_eq]
  simp only [List.map_append, List.flatMap_append, Nat.zero_add, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-! ## The reduction -/

/-- **SAT ≤ₚ 3-PARTITION** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `TPI`. -/
theorem sat_le_tp_of (h : ∀ w, SATLang w ↔ TPLang (TPI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang TPLang := by
  obtain ⟨hd⟩ := mg_computable 1 (by norm_num) DMI mg_DMI
  obtain ⟨ht⟩ := tpp_F_computable
  refine ⟨tpp_F ∘ DMI, Pnp.TM2Comp.comp hd ht, fun w => ?_⟩
  rw [Function.comp_apply, tpp_F_DMI]
  exact h w

end Pnp.Karp.ThreePart
