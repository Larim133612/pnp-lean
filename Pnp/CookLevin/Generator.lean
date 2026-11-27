import Pnp.CookLevin.GeneratorC
import Pnp.Oracle.OfficialP

/-!
# A polynomial-time program printing the uniform Cook–Levin formula (M33d)

`generator sh`: a stack program (`Pnp/Oracle/Struct.lean`) that, on every bit string `x` on
stack `0`, terminates within `(|x|+2)^K` steps and leaves the internal 2-bit code of `g x` on
stack `2` (last symbol on top); on valid inputs (concatenations of one-hot blocks of width `W`)
`g x` is `Shape.formula sh gs`.

The program (`genCmd`):
1. `preCmd`: copy the input to stack `1`, count its blocks `n` (blocks of width `max W 1`),
   compute `M`, `T`, `B` in unary (Horner), and the registers `w`, `B·w`, `S B`, `col B`;
2. the emission phases of `Pnp/CookLevin/GeneratorB.lean` and `Pnp/CookLevin/GeneratorC.lean`,
   in the order of `Shape.formula`; the input clauses are emitted during a second pass over the
   input copy, block by block, by a table look-up on the first `true` of each block
   (`Pnp/CookLevin/GeneratorA.lean`).
-/

namespace Pnp.CookLevin.Uniform

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

/-! ## Polynomially bounded functions of the input -/

/-- `f x ≤ C (|x|+2)^E` for some constants. -/
def PolyB (f : Str → ℕ) : Prop := ∃ C E : ℕ, ∀ x : Str, f x ≤ C * (x.length + 2) ^ E

theorem PolyB.mono {f g : Str → ℕ} (hg : PolyB g) (h : ∀ x, f x ≤ g x) : PolyB f := by
  obtain ⟨C, E, hC⟩ := hg; exact ⟨C, E, fun x => (h x).trans (hC x)⟩

theorem PolyB.const (c : ℕ) : PolyB fun _ => c := ⟨c, 0, fun x => by simp⟩

theorem PolyB.len : PolyB fun x => x.length := ⟨1, 1, fun x => by simp⟩

theorem pow_le_pow_add (N a b : ℕ) : (N + 2) ^ a ≤ (N + 2) ^ (a + b) :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem PolyB.add {f g : Str → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB fun x => f x + g x := by
  obtain ⟨C, E, hC⟩ := hf
  obtain ⟨D, F, hD⟩ := hg
  refine ⟨C + D, E + F, fun x => ?_⟩
  have h1 := Nat.mul_le_mul_left C (pow_le_pow_add x.length E F)
  have h2 := Nat.mul_le_mul_left D (pow_le_pow_add x.length F E)
  rw [Nat.add_comm F E] at h2
  have := hC x; have := hD x
  nlinarith

theorem PolyB.mul {f g : Str → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB fun x => f x * g x := by
  obtain ⟨C, E, hC⟩ := hf
  obtain ⟨D, F, hD⟩ := hg
  refine ⟨C * D, E + F, fun x => ?_⟩
  calc f x * g x ≤ (C * (x.length + 2) ^ E) * (D * (x.length + 2) ^ F) :=
        Nat.mul_le_mul (hC x) (hD x)
    _ = C * D * (x.length + 2) ^ (E + F) := by ring

/-- A polynomial evaluated at a value `≤ |x|`. -/
theorem PolyB.eval (q : Polynomial ℕ) {n : Str → ℕ} (hn : ∀ x, n x ≤ x.length) :
    PolyB fun x => q.eval (n x) := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i, q.natDegree, fun x => ?_⟩
  show q.eval (n x) ≤ _
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
  rw [Finset.mem_range] at hi
  calc n x ^ i ≤ (x.length + 2) ^ i := Nat.pow_le_pow_left (by have := hn x; omega) _
    _ ≤ (x.length + 2) ^ q.natDegree := Nat.pow_le_pow_right (by omega) (by omega)

theorem PolyB.polyT (q : Polynomial ℕ) {n : Str → ℕ} (hn : ∀ x, n x ≤ x.length) :
    PolyB fun x => polyT q (n x) := by
  obtain ⟨C, E, h⟩ := polyT_le q
  refine ⟨C, E, fun x => (h (n x)).trans (Nat.mul_le_mul_left _ ?_)⟩
  exact Nat.pow_le_pow_left (by have := hn x; omega) _

theorem PolyB.tb {f : Str → ℕ} (hf : PolyB f) : ∃ K, ∀ x, f x ≤ tb K x.length := by
  obtain ⟨C, E, h⟩ := hf
  refine ⟨C + 0 + E, fun x => ?_⟩
  have := OfficialP.absorb C 0 E x.length
  have := h x
  simp only [Pnp.Relativize.tb]; omega

/-! ## The precomputation -/

variable (sh : Shape)

/-- Number of input blocks. -/
def nX (x : Str) : ℕ := (blocks (rW sh) x).length

theorem nX_le (x : Str) : nX sh x ≤ x.length := blocks_length_le _ x

/-- The register file after the precomputation, for `n` blocks. -/
noncomputable def vP (n : ℕ) : ℕ → ℕ :=
  update (update (update (update (update (update (update (update (fun _ => 0) 3 n) 4
    (sh.PM.eval n)) 5 (sh.PT.eval n)) 6 (sh.PB.eval n)) 18 sh.w) 11 (sh.PB.eval n * sh.w)) 10
    (sh.S (sh.PB.eval n))) 12 (sh.col (sh.PB.eval n))

noncomputable def preCmd : Cmd :=
  .seq (copyVia 0 1 7) (.seq (cntLoop (rW sh)) (.seq (polyCmd 3 4 7 8 9 sh.PM)
  (.seq (polyCmd 3 5 7 8 9 sh.PT) (.seq (polyCmd 3 6 7 8 9 sh.PB)
  (.seq (pushList 18 (List.replicate sh.w true)) (.seq (mul 6 18 11 7 8)
  (.seq (pushList 10 (List.replicate (sh.L1 + 2 * sh.D * sh.w) true)) (.seq (copyVia 11 10 7)
  (.seq (pushList 12 (List.replicate (sh.L1 + sh.D * sh.w) true)) (copyVia 11 12 7))))))))))

/-- Cost of the precomputation. -/
noncomputable def Tpre (x : Str) : ℕ :=
  (5 * x.length + 4) + (x.length * (rW sh + 4) + 2) + polyT sh.PM (nX sh x) +
    polyT sh.PT (nX sh x) + polyT sh.PB (nX sh x) + (sh.w + 1) +
    (sh.PB.eval (nX sh x) * (5 * sh.w + 8) + 4) + (sh.L1 + 2 * sh.D * sh.w + 1) +
    (5 * (sh.PB.eval (nX sh x) * sh.w) + 4) + (sh.L1 + sh.D * sh.w + 1) +
    (5 * (sh.PB.eval (nX sh x) * sh.w) + 4)

set_option maxHeartbeats 1000000 in
theorem ex_pre (x : Str) :
    ExecLe (preCmd sh) (st x [] [] fun _ => 0) (.norm (st [] x [] (vP sh (nX sh x)))) (Tpre sh x) := by
  set n := nX sh x with hn
  set v0 : ℕ → ℕ := fun _ => 0
  have q1 := ExecLe.of (exec_copyVia (a := 0) (b := 1) (t := 7) (by decide) (by decide)
    (by decide) (st x [] [] v0) (by rw [st_reg (by norm_num)]; rfl))
  rw [st_zero, st_one, List.append_nil, upd_one] at q1
  have q2 := ex_cntLoop (rW sh) x [] x v0
  set u1 := update v0 3 n
  have e2 : update v0 3 (v0 3 + (blocks (rW sh) x).length) = u1 := by simp [u1, v0, n, nX]
  rw [e2] at q2
  have q3 := ex_poly (i := []) (X := x) (o := []) (xs := 3) (acc := 4) (nxt := 7) (ta := 8) (tm := 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) sh.PM u1 (by simp [u1, v0]) (by simp [u1, v0]) (by simp [u1, v0])
    (by simp [u1, v0])
  have e1 : u1 3 = n := by simp [u1]
  rw [e1] at q3
  set u2 := update u1 4 (sh.PM.eval n)
  have q4 := ex_poly (i := []) (X := x) (o := []) (xs := 3) (acc := 5) (nxt := 7) (ta := 8) (tm := 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) sh.PT u2 (by simp [u2, u1, v0]) (by simp [u2, u1, v0])
    (by simp [u2, u1, v0]) (by simp [u2, u1, v0])
  have e3 : u2 3 = n := by simp [u2, u1]
  rw [e3] at q4
  set u3 := update u2 5 (sh.PT.eval n)
  have q5 := ex_poly (i := []) (X := x) (o := []) (xs := 3) (acc := 6) (nxt := 7) (ta := 8) (tm := 9)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) sh.PB u3 (by simp [u3, u2, u1, v0]) (by simp [u3, u2, u1, v0])
    (by simp [u3, u2, u1, v0]) (by simp [u3, u2, u1, v0])
  have e4 : u3 3 = n := by simp [u3, u2, u1]
  rw [e4] at q5
  set B := sh.PB.eval n
  set u4 := update u3 6 B
  have q6 := ex_pushList_reg (i := []) (X := x) (o := []) (r := 18) (by norm_num) sh.w u4
  have e6 : u4 18 + sh.w = sh.w := by simp [u4, u3, u2, u1, v0]
  rw [e6] at q6
  set u5 := update u4 18 sh.w
  have q7 := (ex_mul (i := []) (X := x) (o := []) (a := 6) (b := 18) (c := 11) (ta := 7) (tm := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) u5 (by simp [u5, u4, u3, u2, u1, v0])
    (by simp [u5, u4, u3, u2, u1, v0])).mono (show _ ≤ B * (5 * sh.w + 8) + 4 by
      simp [u5, u4])
  have e7 : u5 11 + u5 6 * u5 18 = B * sh.w := by simp [u5, u4, u3, u2, u1, v0]
  rw [e7] at q7
  set u6 := update u5 11 (B * sh.w)
  have q8 := ex_pushList_reg (i := []) (X := x) (o := []) (r := 10) (by norm_num)
    (sh.L1 + 2 * sh.D * sh.w) u6
  have e8 : u6 10 + (sh.L1 + 2 * sh.D * sh.w) = sh.L1 + 2 * sh.D * sh.w := by
    simp [u6, u5, u4, u3, u2, u1, v0]
  rw [e8] at q8
  set u6' := update u6 10 (sh.L1 + 2 * sh.D * sh.w)
  have q9 := (ex_copy (i := []) (X := x) (o := []) (a := 11) (b := 10) (t := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) u6'
    (by simp [u6', u6, u5, u4, u3, u2, u1, v0])).mono
    (show _ ≤ 5 * (B * sh.w) + 4 by simp [u6', u6])
  have e9 : u6' 10 + u6' 11 = sh.S B := by
    simp [u6', u6]; unfold Shape.S; ring
  rw [e9] at q9
  set u7 := update u6' 10 (sh.S B)
  have q10 := ex_pushList_reg (i := []) (X := x) (o := []) (r := 12) (by norm_num)
    (sh.L1 + sh.D * sh.w) u7
  have e10 : u7 12 + (sh.L1 + sh.D * sh.w) = sh.L1 + sh.D * sh.w := by
    simp [u7, u6', u6, u5, u4, u3, u2, u1, v0]
  rw [e10] at q10
  set u7' := update u7 12 (sh.L1 + sh.D * sh.w)
  have q11 := (ex_copy (i := []) (X := x) (o := []) (a := 11) (b := 12) (t := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) u7'
    (by simp [u7', u7, u6', u6, u5, u4, u3, u2, u1, v0])).mono
    (show _ ≤ 5 * (B * sh.w) + 4 by simp [u7', u7, u6', u6])
  have e11 : u7' 12 + u7' 11 = sh.col B := by
    simp [u7', u7, u6', u6]; rw [col_eq]; try ring
  rw [e11] at q11
  refine (q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm (q5.seq_norm (q6.seq_norm
    (q7.seq_norm (q8.seq_norm (q9.seq_norm (q10.seq_norm q11)))))))))).cast ?_ ?_
  · refine congrArg Res.norm (st_eq rfl fun j _ => ?_)
    simp only [u7', u7, u6', u6, u5, u4, u3, u2, u1, vP, update_apply]
    split_ifs <;> simp_all <;> first | rfl | (left; rfl)
  · simp only [Tpre, ← hn]
    have hB : B = sh.PB.eval n := rfl
    rw [← hB]
    omega

/-! ## The whole program -/

noncomputable def genCmd : Cmd :=
  .seq (preCmd sh) (.seq (init0Cmd sh) (.seq (initCmd sh) (.seq (inCmdA sh) (.seq (inCmdB sh)
    (tCmd sh)))))

/-- The printed formula, for any input. -/
noncomputable def gOut (x : Str) : List SatSym :=
  place 0 sh.init0 ++
  (List.range (sh.PB.eval (nX sh x))).flatMap (fun j => place (sh.col j) sh.initCol) ++
  inPartN sh (sh.col 0) (blocks (rW sh) x) ++
  place (sh.col (nX sh x)) sh.sepCol ++
  (List.range (sh.PB.eval (nX sh x) - nX sh x - 1)).flatMap
    (fun m => place (sh.col (nX sh x + 1 + m)) sh.certCol) ++
  place (sh.col (nX sh x + 1 + sh.PM.eval (nX sh x))) sh.boundCol ++
  (List.range (sh.PT.eval (nX sh x))).flatMap
    (fun t => sh.slicePart (sh.PB.eval (nX sh x)) t ++ sh.stepPart (sh.PB.eval (nX sh x)) t) ++
  sh.slicePart (sh.PB.eval (nX sh x)) (sh.PT.eval (nX sh x)) ++
  place (sh.PT.eval (nX sh x) * sh.S (sh.PB.eval (nX sh x))) sh.acc

/-- A bound for all register values and loop counts. -/
noncomputable def Lam (x : Str) : ℕ :=
  x.length + nX sh x + sh.PM.eval (nX sh x) + sh.PT.eval (nX sh x) + sh.PB.eval (nX sh x) +
    (sh.L1 + sh.D * sh.w + (x.length + 1 + sh.PM.eval (nX sh x) + sh.PB.eval (nX sh x)) * sh.w) +
    sh.PT.eval (nX sh x) * sh.S (sh.PB.eval (nX sh x)) + sh.S (sh.PB.eval (nX sh x)) +
    sh.col (sh.PB.eval (nX sh x)) + sh.PB.eval (nX sh x) * sh.w

theorem init_st (x : Str) : (init [x]).stk = st x [] [] fun _ => 0 := by
  funext j
  rcases j with _ | _ | _ | j
  · rfl
  · rfl
  · rfl
  · simp [init, st]

theorem U_mono3 (a Λ : ℕ) (h : a ≤ 3) : (Λ + 1) ^ a ≤ (Λ + 1) ^ 3 :=
  Nat.pow_le_pow_right (by omega) h

set_option maxHeartbeats 2000000 in
theorem ex_gen : ∃ A, ∀ x : Str, ExecLe (genCmd sh) (init [x]).stk
    (.norm (st [] [] (rv (gOut sh x)) (vP sh (nX sh x)))) (Tpre sh x + A * (Lam sh x + 1) ^ 3) := by
  obtain ⟨A2, h2⟩ := em_init sh
  obtain ⟨A3, h3⟩ := ex_inCmdA sh
  obtain ⟨A4, h4⟩ := ex_inCmdB sh
  obtain ⟨A5, h5⟩ := em_tCmd sh
  refine ⟨linesCost (plc 9 sh.init0) + A2 + A3 + A4 + A5, fun x => ?_⟩
  rw [init_st]
  set n := nX sh x with hn
  set Λ := Lam sh x with hΛ
  set v := vP sh n with hv
  have hnx : n ≤ x.length := nX_le sh x
  have hL : Λ = x.length + n + sh.PM.eval n + sh.PT.eval n + sh.PB.eval n +
      (sh.L1 + sh.D * sh.w + (x.length + 1 + sh.PM.eval n + sh.PB.eval n) * sh.w) +
      sh.PT.eval n * sh.S (sh.PB.eval n) + sh.S (sh.PB.eval n) +
      sh.col (sh.PB.eval n) + sh.PB.eval n * sh.w := rfl
  have hxw : (x.length + 1 + sh.PM.eval n + sh.PB.eval n) * sh.w ≤ Λ := by omega
  have hcB : sh.col (sh.PB.eval n) ≤ Λ := by omega
  have hv4 : v 4 = sh.PM.eval n := by simp [v, vP]
  have hv6 : v 6 = sh.PB.eval n := by simp [v, vP]
  have hv5 : v 5 = sh.PT.eval n := by simp [v, vP]
  have q0 := ex_pre sh x
  rw [← hn] at q0
  have q1 := ((em_init0 sh (v := v) Λ (by simp [v, vP]) (by simp [v, vP])) [] x []).mono
    ((lin_U2' _ Λ).trans (Nat.mul_le_mul_left _ (U_mono3 2 Λ (by norm_num))))
  have q2 := ((h2 Λ v (by simp [v, vP]) (by simp [v, vP]) (by simp [v, vP])
    (by rw [hv6]; omega)
    (by
      have : sh.PB.eval n * sh.w ≤ (x.length + 1 + sh.PM.eval n + sh.PB.eval n) * sh.w :=
        Nat.mul_le_mul_right _ (by omega)
      rw [hv6]; omega)) [] x (rv (place 0 sh.init0) ++ [])).mono
    (Nat.mul_le_mul_left _ (U_mono3 2 Λ (by norm_num)))
  set o2 := rv ((List.range (v 6)).flatMap fun j => place (sh.col j) sh.initCol) ++
    (rv (place 0 sh.init0) ++ [])
  have q3 := (h3 Λ v [] x o2 (by simp [v, vP]) (by simp [v, vP]) (by omega)
    (by
      have : x.length * sh.w ≤ (x.length + 1 + sh.PM.eval n + sh.PB.eval n) * sh.w :=
        Nat.mul_le_mul_right _ (by omega)
      omega)).mono (Nat.mul_le_mul_left _ (U_mono3 2 Λ (by norm_num)))
  rw [show (blocks (rW sh) x).length = n from rfl] at q3
  set o3 := rv (inPartN sh (sh.col 0) (blocks (rW sh) x)) ++ o2
  have q4 := (h4 Λ v n [] [] o3 (by simp [v, vP]) (by simp [v, vP]) (by simp [v, vP])
    (by simp [v, vP]) (by simp [v, vP]) (by simp [v, vP]) (by omega)
    (by rw [hv4]; omega) (by rw [hv6]; omega)
    (by
      rw [hv4, hv6]
      have : (n + 1 + sh.PM.eval n + sh.PB.eval n) * sh.w ≤
          (x.length + 1 + sh.PM.eval n + sh.PB.eval n) * sh.w :=
        Nat.mul_le_mul_right _ (by omega)
      omega)).mono (Nat.mul_le_mul_left _ (U_mono3 2 Λ (by norm_num)))
  have e14 : update v 14 0 = v := by
    rw [update_eq_self_iff]; simp [v, vP]
  rw [e14, hv4, hv6] at q4
  have q5 := h5 Λ v (by simp [v, vP]) (by simp [v, vP]) (by simp [v, vP]) (by simp [v, vP])
    (by simp [v, vP]) (by simp [v, vP]) (by simp [v, vP]) (by simp [v, vP]) (by simp [v, vP])
    (by rw [hv5]; omega) (by rw [hv6]; omega)
    (by rw [hv5, hv6]; omega)
    (by rw [hv6]; omega) (by rw [hv6]; exact hcB)
    (by rw [hv6]; omega) [] [] (rv (place (sh.col n) sh.sepCol ++
        (List.range (sh.PB.eval n - n - 1)).flatMap (fun m => place (sh.col (n + 1 + m)) sh.certCol) ++
        place (sh.col (n + 1 + sh.PM.eval n)) sh.boundCol) ++ o3)
  rw [hv5, hv6] at q5
  refine (q0.seq_norm (q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm q5))))).cast ?_
    (le_of_eq (by ring))
  refine congrArg Res.norm (st_eq ?_ fun _ _ => rfl)
  simp only [o3, o2, hv6, gOut, ← hn, rv_append, List.append_assoc, List.append_nil]

/-! ## The time bound -/

theorem polyB_Lam : PolyB (Lam sh) := by
  have hn := nX_le sh
  have pn : PolyB (nX sh) := PolyB.len.mono hn
  have pM := PolyB.eval sh.PM hn
  have pT := PolyB.eval sh.PT hn
  have pB := PolyB.eval sh.PB hn
  have pS : PolyB fun x => sh.S (sh.PB.eval (nX sh x)) := by
    unfold Shape.S
    exact (PolyB.const _).add ((pB.add (PolyB.const _)).mul (PolyB.const _))
  have pc : PolyB fun x => sh.col (sh.PB.eval (nX sh x)) := by
    unfold Shape.col
    exact (PolyB.const _).add (((PolyB.const _).add pB).mul (PolyB.const _))
  have p1 : PolyB fun x => sh.L1 + sh.D * sh.w +
      (x.length + 1 + sh.PM.eval (nX sh x) + sh.PB.eval (nX sh x)) * sh.w :=
    ((PolyB.const _).add (PolyB.const _)).add
      ((((PolyB.len.add (PolyB.const 1)).add pM).add pB).mul (PolyB.const _))
  unfold Lam
  exact ((((((((PolyB.len.add pn).add pM).add pT).add pB).add p1).add (pT.mul pS)).add pS).add
    pc).add (pB.mul (PolyB.const _))

theorem polyB_Tpre : PolyB (Tpre sh) := by
  have hn := nX_le sh
  have pB := PolyB.eval sh.PB hn
  have pBw : PolyB fun x => 5 * (sh.PB.eval (nX sh x) * sh.w) + 4 :=
    ((PolyB.const 5).mul (pB.mul (PolyB.const _))).add (PolyB.const 4)
  unfold Tpre
  exact ((((((((((((PolyB.const 5).mul PolyB.len).add (PolyB.const 4)).add
    ((PolyB.len.mul (PolyB.const _)).add (PolyB.const 2))).add (PolyB.polyT sh.PM hn)).add
    (PolyB.polyT sh.PT hn)).add (PolyB.polyT sh.PB hn)).add (PolyB.const _)).add
    ((pB.mul (PolyB.const _)).add (PolyB.const 4))).add (PolyB.const _)).add pBw).add
    (PolyB.const _)).add pBw

theorem polyB_total (A : ℕ) : PolyB fun x => Tpre sh x + A * (Lam sh x + 1) ^ 3 := by
  have pL := (polyB_Lam sh).add (PolyB.const 1)
  exact (polyB_Tpre sh).add (((PolyB.const A).mul ((pL.mul pL).mul pL)).mono
    fun x => le_of_eq (by ring))

/-! ## Valid inputs -/

theorem oneHotW_eq (W : ℕ) (g : Fin W) :
    oneHotW W g = List.replicate g false ++ true :: List.replicate (W - 1 - g) false := by
  apply List.ext_getElem
  · simp [oneHotW]; omega
  · intro k h1 h2
    simp only [oneHotW, List.getElem_ofFn, List.getElem_append, List.length_replicate,
      List.getElem_replicate]
    split_ifs with h
    · simp [Fin.ext_iff]; omega
    · rw [List.getElem_cons]
      split_ifs with h'
      · simp [Fin.ext_iff]; omega
      · simp [Fin.ext_iff]; omega

theorem blocks_ne (r : ℕ) {z : Str} (hz : z ≠ []) :
    blocks r z = (fi (r + 1) z).getD 0 :: blocks r (z.drop (r + 1)) := by
  cases z with
  | nil => exact absurd rfl hz
  | cons b l => rw [blocks_cons]; rfl

theorem blocks_valid : ∀ gs : List (Fin sh.W),
    blocks (rW sh) (gs.flatMap (oneHotW sh.W)) = gs.map Fin.val
  | [] => by simp [blocks_nil]
  | g :: gs => by
    have hW : rW sh + 1 = sh.W := by unfold rW; have := g.isLt; omega
    have hlen : (oneHotW sh.W g).length = sh.W := by simp [oneHotW]
    rw [List.flatMap_cons, blocks_ne _ (by
      intro h; have := congrArg List.length h; simp [hlen] at this; have := g.isLt; omega)]
    rw [hW, List.drop_left' hlen, blocks_valid gs, List.map_cons]
    congr 1
    rw [oneHotW_eq, fi_block g sh.W _ g.isLt]; rfl

theorem inPartN_eq : ∀ (gs : List (Fin sh.W)) (k : ℕ),
    inPartN sh (sh.col k) (gs.map Fin.val) = sh.inPart k gs
  | [], k => rfl
  | g :: gs, k => by
    have := inPartN_eq gs (k + 1)
    simp only [inPartN, List.map_cons, pN, Shape.inPart] at this ⊢
    rw [show sh.col k + sh.w = sh.col (k + 1) by rw [col_eq, col_eq]; ring, this]
    congr 2
    simp [inColN, g.isLt]

theorem gOut_valid (gs : List (Fin sh.W)) :
    gOut sh (gs.flatMap (oneHotW sh.W)) = sh.formula gs := by
  have hb := blocks_valid sh gs
  have hn : nX sh (gs.flatMap (oneHotW sh.W)) = gs.length := by
    simp [nX, hb]
  simp only [gOut, hn, hb, inPartN_eq, Shape.formula]

/-! ## The generator -/

/-- **A polynomial-time stack program printing the uniform Cook–Levin formula.**  On every bit
string `x` the program `c` terminates within `(|x|+2)^K` steps and leaves the internal code of
the symbols of `g x` on stack `kOut` (last symbol on top); on concatenations of one-hot blocks
`g x` is the formula `Shape.formula sh gs`. -/
theorem generator (sh : Shape) : ∃ (c : Cmd) (kOut K : ℕ) (g : Str → List SatSym),
    (∀ x : Str, ∃ σ', ExecLe c (init [x]).stk (.norm σ') (tb K x.length) ∧
        σ' kOut = ((g x).flatMap ic).reverse) ∧
    ∀ gs : List (Fin sh.W), g (gs.flatMap (oneHotW sh.W)) = sh.formula gs := by
  obtain ⟨A, hA⟩ := ex_gen sh
  obtain ⟨K, hK⟩ := (polyB_total sh A).tb
  refine ⟨genCmd sh, 2, K, gOut sh, fun x => ⟨_, (hA x).mono (hK x), ?_⟩, gOut_valid sh⟩
  simp [rv]

end Pnp.CookLevin.Uniform
