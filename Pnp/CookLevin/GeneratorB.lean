import Pnp.CookLevin.GeneratorA

/-!
# The emission phases of the formula generator (M33d, part 2)

Register map (stacks `≥ 3`, unary): `3` = `n`, `4` = `M`, `5` = `T`, `6` = `B`, `7, 8, 9`
temporaries, `10` = `S B`, `11` = `B·w`, `12` = `col B`, `13` = loop counter, `14` = current
column, `15` = `t · S B`, `16` = time counter, `17` = `j · w`, `18` = `w`, `19` = bound column.

Each phase emits one part of `Shape.formula` and restores all registers.
-/

namespace Pnp.CookLevin.Uniform

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

/-- State equality for register files built by `update`. -/
macro "steq" : tactic =>
  `(tactic| (apply st_congr; intro j _; simp only [update_apply]; split_ifs <;> simp_all))

/-- Lines placing each pattern of `cs` at the column held by register `k`. -/
def plc (k : ℕ) (cs : List (List SatSym)) : List (List It) :=
  cs.map fun c => [.reg k, .lit (c ++ [sep])]

theorem linesSem_plc (v : ℕ → ℕ) (k : ℕ) (cs : List (List SatSym)) :
    linesSem v (plc k cs) = place (v k) cs := by
  simp [linesSem, plc, lineSem, It.sem, place, List.flatMap_map]
  congr 1; funext c; simp [at_]

theorem plc_ok {v : ℕ → ℕ} {Λ k : ℕ} (cs : List (List SatSym)) (hk : 3 ≤ k) (hk7 : k ≠ 7)
    (hv : v k ≤ Λ) : ∀ l ∈ plc k cs, ∀ it ∈ l, it.Ok v Λ := by
  intro l hl it hit
  simp only [plc, List.mem_map] at hl
  obtain ⟨c, _, rfl⟩ := hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl
  · exact ⟨hk, hk7, hv⟩
  · trivial

theorem em_plc {v : ℕ → ℕ} {Λ k : ℕ} (cs : List (List SatSym)) (h7 : v 7 = 0) (hk : 3 ≤ k)
    (hk7 : k ≠ 7) (hv : v k ≤ Λ) :
    Em (linesCmd (plc k cs)) v (place (v k) cs) (linesCost (plc k cs) * (Λ + 1)) := by
  have := linesCmd_em h7 (plc k cs) (plc_ok cs hk hk7 hv)
  rwa [linesSem_plc] at this

theorem U_le (Λ : ℕ) : Λ + 1 ≤ (Λ + 1) ^ 2 := by nlinarith

theorem lin_U2 {a Λ : ℕ} (h : a ≤ Λ) (k b : ℕ) : k * a + b ≤ (k + b) * (Λ + 1) ^ 2 := by
  have := U_le Λ
  have : k * a ≤ k * (Λ + 1) ^ 2 := Nat.mul_le_mul_left _ (by omega)
  have : b ≤ b * (Λ + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  nlinarith

theorem const_U2 (b Λ : ℕ) : b ≤ b * (Λ + 1) ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)

theorem lin_U2' (k Λ : ℕ) : k * (Λ + 1) ≤ k * (Λ + 1) ^ 2 := Nat.mul_le_mul_left _ (U_le Λ)

variable (sh : Shape)

/-! ## Phase 1: the clauses at offset `0` -/

def init0Cmd : Cmd := linesCmd (plc 9 sh.init0)

theorem em_init0 {v : ℕ → ℕ} (Λ : ℕ) (h7 : v 7 = 0) (h9 : v 9 = 0) :
    Em (init0Cmd sh) v (place 0 sh.init0) (linesCost (plc 9 sh.init0) * (Λ + 1)) := by
  have := em_plc (Λ := Λ) sh.init0 h7 (by norm_num) (by norm_num) (by omega : v 9 ≤ Λ)
  rwa [h9] at this

/-! ## Phase 2: the clauses of every real column of slice `0` -/

def initBody : Cmd := .seq (linesCmd (plc 14 sh.initCol)) (pushList 14 (List.replicate sh.w true))

def initCmd : Cmd :=
  .seq (pushList 14 (List.replicate (sh.L1 + sh.D * sh.w) true))
    (.seq (copyVia 6 13 7) (.seq (forLoop 13 (initBody sh)) (drain 14)))

theorem col_eq (j : ℕ) : sh.col j = sh.L1 + sh.D * sh.w + j * sh.w := by
  unfold Shape.col; ring

theorem em_init : ∃ A, ∀ (Λ : ℕ) (v : ℕ → ℕ), v 7 = 0 → v 13 = 0 → v 14 = 0 → v 6 ≤ Λ →
    sh.L1 + sh.D * sh.w + v 6 * sh.w ≤ Λ →
    Em (initCmd sh) v ((List.range (v 6)).flatMap fun j => place (sh.col j) sh.initCol)
      (A * (Λ + 1) ^ 2) := by
  refine ⟨linesCost (plc 14 sh.initCol) + sh.w + 20, fun Λ v h7 h13 h14 hB hC i X o => ?_⟩
  set c := sh.L1 + sh.D * sh.w with hc
  set B := v 6 with hBdef
  set lc := linesCost (plc 14 sh.initCol)
  have h1 := ex_pushList_reg (i := i) (X := X) (o := o) (r := 14) (by norm_num) c v
  have h2 := ex_copy (i := i) (X := X) (o := o) (a := 6) (b := 13) (t := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (update v 14 (v 14 + c)) (by simp [h7])
  set f : ℕ → ℕ → ℕ := fun k => update (update v 14 (c + k * sh.w)) 13 (B - k) with hf
  have h3 := ex_forLoop (K := 13) (by norm_num) (body := initBody sh) (i := i) (X := X) B f
    (fun k => place (sh.col k) sh.initCol) (lc * (Λ + 1) + (sh.w + 1))
    (fun k _ => by simp [f])
    (fun k hk o' => by
      have hu7 : update (f k) 13 (B - k - 1) 7 = 0 := by simp [f, h7]
      have hu14 : update (f k) 13 (B - k - 1) 14 = sh.col k := by simp [f, col_eq, c]
      have hl := em_plc (Λ := Λ) sh.initCol hu7 (k := 14) (by norm_num) (by norm_num)
        (by rw [hu14, col_eq]; nlinarith)
      rw [hu14] at hl
      have hp := ex_pushList_reg (i := i) (X := X) (o := rv (place (sh.col k) sh.initCol) ++ o')
        (r := 14) (by norm_num) sh.w (update (f k) 13 (B - k - 1))
      refine ((hl i X o').seq_norm hp).cast ?_ le_rfl
      congr 1; apply st_congr; intro j _
      simp only [f, update_apply]; split_ifs <;> simp_all [col_eq] <;> first | omega | ring)
    o
  have h4 := ex_drain (i := i) (X := X) (o := rv ((List.range B).flatMap
    fun k => place (sh.col k) sh.initCol) ++ o) (r := 14) (by norm_num) (f B)
  have e2 : st i X o (update (update v 14 (v 14 + c)) 13
      (update v 14 (v 14 + c) 13 + update v 14 (v 14 + c) 6)) = st i X o (f 0) := by
    simp only [f]; steq
  rw [e2] at h2
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm h4))).cast ?_ ?_
  · congr 1; simp only [f]; steq
  · have hf14 : f B 14 = c + B * sh.w := by simp [f]
    rw [hf14]
    have hBU : B ≤ Λ + 1 := by omega
    have hcU : c + B * sh.w ≤ Λ + 1 := by omega
    have : B * (lc * (Λ + 1) + (sh.w + 1) + 1) ≤ (Λ + 1) * (lc * (Λ + 1) + (sh.w + 1) + 1) :=
      Nat.mul_le_mul_right _ hBU
    have h5 : (sh.w + 20) * (Λ + 1) ≤ (sh.w + 20) * (Λ + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (by nlinarith)
    have e6 : update v 14 (v 14 + c) 6 = B := by simp [B]
    rw [e6]
    have : B * (lc * (Λ + 1) + (sh.w + 1) + 1) ≤ lc * (Λ + 1) ^ 2 + (sh.w + 2) * (Λ + 1) := by
      nlinarith
    nlinarith

/-! ## Phase 3: the input clauses, the separator, the certificate and the bound -/

/-- The input clauses of symbol index `j` (none for `j ≥ W`). -/
def inColN (j : ℕ) : List (List SatSym) := if h : j < sh.W then sh.inCol ⟨j, h⟩ else []

/-- Input clauses for the indices `js`, starting at column offset `c`. -/
def inPartN (c : ℕ) (js : List ℕ) : List SatSym := pN (fun c j => place c ((inColN sh) j)) sh.w c js

def inAct (j : ℕ) : Cmd := .seq (linesCmd (plc 14 ((inColN sh) j))) (pushList 14 (List.replicate sh.w true))

/-- A bound for the line costs of the input actions. -/
def Cin : ℕ := ∑ j ∈ Finset.range sh.W, linesCost (plc 14 ((inColN sh) j)) + 1

theorem lc_inColN_le (j : ℕ) : linesCost (plc 14 ((inColN sh) j)) ≤ (Cin sh) := by
  unfold Cin
  by_cases h : j < sh.W
  · have := Finset.single_le_sum (f := fun j => linesCost (plc 14 ((inColN sh) j)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 h)
    omega
  · simp [inColN, h, plc, linesCost]

/-- Width parameter of the blocks (`W - 1`; blocks of width `1` if `W = 0`). -/
def rW : ℕ := sh.W - 1

def inCmdA : Cmd :=
  .seq (pushList 14 (List.replicate (sh.L1 + sh.D * sh.w) true)) (parseLoop (rW sh) (inAct sh))

theorem ex_inCmdA : ∃ A, ∀ (Λ : ℕ) (v : ℕ → ℕ) (i x o : Str), v 7 = 0 → v 14 = 0 →
    x.length ≤ Λ → sh.L1 + sh.D * sh.w + x.length * sh.w ≤ Λ →
    ExecLe (inCmdA sh) (st i x o v)
      (.norm (st i [] (rv ((inPartN sh) (sh.col 0) (blocks (rW sh) x)) ++ o)
        (update v 14 (sh.col (blocks (rW sh) x).length)))) (A * (Λ + 1) ^ 2) := by
  refine ⟨(Cin sh) + 2 * (rW sh) + sh.w + 10, fun Λ v i x o h7 h14 hx hc => ?_⟩
  set c := sh.L1 + sh.D * sh.w with hc'
  have h1 := ex_pushList_reg (i := i) (X := x) (o := o) (r := 14) (by norm_num) c v
  rw [h14, Nat.zero_add] at h1
  have h2 := ex_parseLoop (rW sh) (inAct sh) (fun c j => place c ((inColN sh) j)) sh.w Λ
    ((Cin sh) * (Λ + 1) + (sh.w + 1)) (i := i) (fun c => update v 14 c) (fun c' hc' j X o' => by
      have hl := em_plc (v := update v 14 c') (Λ := Λ) ((inColN sh) j) (by simp [h7])
        (k := 14) (by norm_num) (by norm_num) (by simp [hc'])
      simp only [update_self] at hl
      have hp := ex_pushList_reg (i := i) (X := X) (o := rv (place c' ((inColN sh) j)) ++ o')
        (r := 14) (by norm_num) sh.w (update v 14 c')
      refine ((hl i X o').seq_norm hp).cast ?_ ?_
      · simp
      · have := Nat.mul_le_mul_right (Λ + 1) ((lc_inColN_le sh) j); omega) x c o hc
  refine (h1.seq_norm h2).cast ?_ ?_
  · congr 2; simp [col_eq, c]
  · have hx' : x.length ≤ Λ + 1 := by omega
    have : x.length * (2 * (rW sh) + ((Cin sh) * (Λ + 1) + (sh.w + 1)) + 3) ≤
        (Λ + 1) * (2 * (rW sh) + ((Cin sh) * (Λ + 1) + (sh.w + 1)) + 3) := Nat.mul_le_mul_right _ hx'
    have hU := U_le Λ
    have := Nat.mul_le_mul_left (2 * rW sh + sh.w + 4) hU
    have : c ≤ Λ := by omega
    nlinarith

def certBody : Cmd := .seq (linesCmd (plc 14 sh.certCol)) (pushList 14 (List.replicate sh.w true))

def inCmdB : Cmd :=
  .seq (linesCmd (plc 14 sh.sepCol)) (.seq (pushList 14 (List.replicate sh.w true))
  (.seq (copyVia 14 19 7) (.seq (mul 4 18 19 7 8) (.seq (copyVia 6 13 7) (.seq (subCmd 13 3 7)
  (.seq (decK 13) (.seq (forLoop 13 (certBody sh)) (.seq (linesCmd (plc 19 sh.boundCol))
  (.seq (drain 14) (drain 19))))))))))

set_option maxHeartbeats 2000000 in
theorem ex_inCmdB : ∃ A, ∀ (Λ : ℕ) (v : ℕ → ℕ) (n : ℕ) (i X o : Str), v 7 = 0 → v 8 = 0 →
    v 13 = 0 → v 19 = 0 → v 18 = sh.w → v 3 = n → n ≤ Λ → v 4 ≤ Λ → v 6 ≤ Λ →
    sh.L1 + sh.D * sh.w + (n + 1 + v 4 + v 6) * sh.w ≤ Λ →
    ExecLe (inCmdB sh) (st i X o (update v 14 (sh.col n)))
      (.norm (st i X (rv (place (sh.col n) sh.sepCol ++
        (List.range (v 6 - n - 1)).flatMap (fun m => place (sh.col (n + 1 + m)) sh.certCol) ++
        place (sh.col (n + 1 + v 4)) sh.boundCol) ++ o) (update v 14 0))) (A * (Λ + 1) ^ 2) := by
  refine ⟨linesCost (plc 14 sh.sepCol) + linesCost (plc 14 sh.certCol) +
    linesCost (plc 19 sh.boundCol) + 7 * sh.w + 55,
    fun Λ v n i X o h7 h8 h13 h19 h18 h3 hn hM hB hc => ?_⟩
  set c := sh.L1 + sh.D * sh.w with hc'
  set M := v 4 with hMdef
  set B := v 6 with hBdef
  set lcS := linesCost (plc 14 sh.sepCol)
  set lcC := linesCost (plc 14 sh.certCol)
  set lcB := linesCost (plc 19 sh.boundCol)
  have ecol : ∀ k, sh.col k = c + k * sh.w := fun k => by rw [col_eq]
  have hnw : n * sh.w ≤ (n + 1 + M + B) * sh.w := Nat.mul_le_mul_right _ (by omega)
  have hn1w : (n + 1) * sh.w ≤ (n + 1 + M + B) * sh.w := Nat.mul_le_mul_right _ (by omega)
  have hMw : (n + 1 + M) * sh.w ≤ (n + 1 + M + B) * sh.w := Nat.mul_le_mul_right _ (by omega)
  have hU := U_le Λ
  -- the separator column
  have s1 := (em_plc (v := update v 14 (sh.col n)) (Λ := Λ) sh.sepCol (by simp [h7]) (k := 14)
    (by norm_num) (by norm_num) (by simp [ecol]; omega) i X o).mono (lin_U2' lcS Λ)
  simp only [update_self] at s1
  set o1 := rv (place (sh.col n) sh.sepCol) ++ o
  have s2 := (ex_pushList_reg (i := i) (X := X) (o := o1) (r := 14) (by norm_num) sh.w
    (update v 14 (sh.col n))).mono (const_U2 (sh.w + 1) Λ)
  set w2 := update v 14 (c + (n + 1) * sh.w)
  have e2 : update (update v 14 (sh.col n)) 14 (update v 14 (sh.col n) 14 + sh.w) = w2 := by
    simp only [update_self, update_idem, w2, ecol]; congr 1; ring
  rw [e2] at s2
  have s3 := (ex_copy (i := i) (X := X) (o := o1) (a := 14) (b := 19) (t := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) w2
    (by simp [w2, h7])).mono (lin_U2 (Λ := Λ) (a := w2 14) (by simp [w2]; omega) 5 4)
  set w3 := update w2 19 (c + (n + 1) * sh.w)
  have e3 : update w2 19 (w2 19 + w2 14) = w3 := by simp [w2, w3, h19]
  rw [e3] at s3
  have s4 := (ex_mul (i := i) (X := X) (o := o1) (a := 4) (b := 18) (c := 19) (ta := 7) (tm := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) w3 (by simp [w3, w2, h7])
    (by simp [w3, w2, h8])).mono (show _ ≤ (5 * sh.w + 12) * (Λ + 1) ^ 2 by
      have e : w3 4 * (5 * w3 18 + 8) + 4 = (5 * sh.w + 8) * M + 4 := by
        simp [w3, w2, h18, M]; ring
      rw [e, show 5 * sh.w + 12 = (5 * sh.w + 8) + 4 by ring]
      exact lin_U2 (Λ := Λ) hM _ _)
  set w4 := update w2 19 (c + (n + 1 + M) * sh.w)
  have e4 : update w3 19 (w3 19 + w3 4 * w3 18) = w4 := by
    simp only [w3, w4, update_idem, update_self]
    congr 1; simp [w2, h18, M]; ring
  rw [e4] at s4
  have s5 := (ex_copy (i := i) (X := X) (o := o1) (a := 6) (b := 13) (t := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) w4
    (by simp [w4, w2, h7])).mono (show _ ≤ (5 + 4) * (Λ + 1) ^ 2 by
      have e : w4 6 = B := by simp [w4, w2, B]
      rw [e]; exact lin_U2 (Λ := Λ) hB 5 4)
  have e5 : update w4 13 (w4 13 + w4 6) = update w4 13 B := by simp [w4, w2, h13, B]
  rw [e5] at s5
  have s6 := (ex_sub (i := i) (X := X) (o := o1) (K := 13) (N := 3) (t := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (update w4 13 B)
    (by simp [w4, w2, h7])).mono (show _ ≤ (6 + 4) * (Λ + 1) ^ 2 by
      have e : update w4 13 B 3 = n := by simp [w4, w2, h3]
      rw [e]; exact lin_U2 (Λ := Λ) hn 6 4)
  have e6 : update (update w4 13 B) 13 (update w4 13 B 13 - update w4 13 B 3) =
      update w4 13 (B - n) := by simp [w4, w2, h3]
  rw [e6] at s6
  have s7 := (ex_decK (i := i) (X := X) (o := o1) (K := 13) (by norm_num)
    (update w4 13 (B - n))).mono (const_U2 2 Λ)
  set m := B - n - 1 with hm
  set f : ℕ → ℕ → ℕ := fun k =>
    update (update (update v 14 (c + (n + 1 + k) * sh.w)) 19 (c + (n + 1 + M) * sh.w)) 13 (m - k)
    with hf
  have e7 : update (update w4 13 (B - n)) 13 (update w4 13 (B - n) 13 - 1) = f 0 := by
    simp only [update_idem, update_self, f, w4, w2, Nat.add_zero, Nat.sub_zero]; rfl
  rw [e7] at s7
  have s8 := (ex_forLoop (K := 13) (by norm_num) (body := certBody sh) (i := i) (X := X) m f
    (fun k => place (sh.col (n + 1 + k)) sh.certCol)
    (lcC * (Λ + 1) + (sh.w + 1))
    (fun k _ => by simp [f])
    (fun k hk o' => by
      have hu7 : update (f k) 13 (m - k - 1) 7 = 0 := by simp [f, h7]
      have hu14 : update (f k) 13 (m - k - 1) 14 = sh.col (n + 1 + k) := by simp [f, ecol]
      have hkB : (n + 1 + k) * sh.w ≤ (n + 1 + M + B) * sh.w :=
        Nat.mul_le_mul_right _ (by omega)
      have hl := em_plc (Λ := Λ) sh.certCol hu7 (k := 14) (by norm_num) (by norm_num)
        (by rw [hu14, ecol]; omega)
      rw [hu14] at hl
      have hp := ex_pushList_reg (i := i) (X := X)
        (o := rv (place (sh.col (n + 1 + k)) sh.certCol) ++ o')
        (r := 14) (by norm_num) sh.w (update (f k) 13 (m - k - 1))
      refine ((hl i X o').seq_norm hp).cast ?_ le_rfl
      congr 1; apply st_congr; intro j _
      simp only [f, update_apply]; split_ifs <;> simp_all <;> first | omega | ring)
    o1).mono (show _ ≤ (lcC + sh.w + 4) * (Λ + 1) ^ 2 by
      have : m * (lcC * (Λ + 1) + (sh.w + 1) + 1) ≤ (Λ + 1) * (lcC * (Λ + 1) + (sh.w + 1) + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have := Nat.mul_le_mul_left (sh.w + 4) hU
      nlinarith)
  set o2 := rv ((List.range m).flatMap fun k => place (sh.col (n + 1 + k)) sh.certCol) ++ o1
  have s9 := (em_plc (v := f m) (Λ := Λ) sh.boundCol (by simp [f, h7]) (k := 19) (by norm_num)
    (by norm_num) (by simp [f]; omega) i X o2).mono (lin_U2' lcB Λ)
  have e19 : f m 19 = sh.col (n + 1 + M) := by simp [f, ecol]
  rw [e19] at s9
  set o3 := rv (place (sh.col (n + 1 + M)) sh.boundCol) ++ o2
  have s10 := (ex_drain (i := i) (X := X) (o := o3) (r := 14) (by norm_num) (f m)).mono
    (show _ ≤ (2 + 2) * (Λ + 1) ^ 2 by
      have hkB : (n + 1 + m) * sh.w ≤ (n + 1 + M + B) * sh.w :=
        Nat.mul_le_mul_right _ (by omega)
      exact lin_U2 (Λ := Λ) (a := f m 14) (by simp [f]; omega) 2 2)
  have s11 := (ex_drain (i := i) (X := X) (o := o3) (r := 19) (by norm_num)
    (update (f m) 14 0)).mono (show _ ≤ (2 + 2) * (Λ + 1) ^ 2 by
      exact lin_U2 (Λ := Λ) (a := update (f m) 14 0 19) (by simp [f]; omega) 2 2)
  refine (s1.seq_norm (s2.seq_norm (s3.seq_norm (s4.seq_norm (s5.seq_norm (s6.seq_norm
    (s7.seq_norm (s8.seq_norm (s9.seq_norm (s10.seq_norm s11)))))))))).cast ?_ (le_of_eq ?_)
  · congr 1; simp only [o3, o2, o1, rv_append, List.append_assoc]
    apply st_congr; intro j _; simp only [f, update_apply]; split_ifs <;> simp_all
  · ring

end Pnp.CookLevin.Uniform
