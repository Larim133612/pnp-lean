import Pnp.CookLevin.GeneratorB

/-!
# The time loop of the formula generator (M33d, part 3)

Phase 4 of the generator: for every `t < T` the fixed clauses of slice `t` and the step clauses
from slice `t` to slice `t + 1`, then the clauses of slice `T` and the acceptance clauses.
Registers as in `Pnp/CookLevin/GeneratorB.lean`.
-/

namespace Pnp.CookLevin.Uniform

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

variable (sh : Shape)

def sliceLines : List (List It) :=
  plc 15 sh.sliceCls ++ sh.rpadCls.map fun c => [.reg 15, .reg 12, .lit (c ++ [sep])]

def stepCLines : List (List It) :=
  sh.stepC.map fun p => [.reg 15, .lit p.1, .reg 11, .lit (zs p.2.1 ++ [p.2.2, sep])]

def stepXLines : List (List It) :=
  sh.stepX.map fun p =>
    [.reg 15, .lit p.1, .reg 17, .lit p.2.1, .reg 11, .lit (zs p.2.2.1 ++ [p.2.2.2, sep])]

theorem linesSem_append (v : ℕ → ℕ) (l₁ l₂ : List (List It)) :
    linesSem v (l₁ ++ l₂) = linesSem v l₁ ++ linesSem v l₂ := by
  simp [linesSem]

theorem sem_slice (v : ℕ → ℕ) (B t : ℕ) (h15 : v 15 = t * sh.S B) (h12 : v 12 = sh.col B) :
    linesSem v (sliceLines sh) = sh.slicePart B t := by
  rw [sliceLines, linesSem_append, linesSem_plc, h15, Shape.slicePart]
  congr 1
  simp only [linesSem, lineSem, List.flatMap_map, place]
  congr 1; funext c
  simp only [It.sem, h12, h15, at_, zs, List.replicate_add, List.append_assoc, List.append_nil,
    List.flatMap_cons, List.flatMap_nil]

theorem sem_stepC (v : ℕ → ℕ) (B t : ℕ) (h15 : v 15 = t * sh.S B) (h11 : v 11 = B * sh.w) :
    linesSem v (stepCLines sh) =
      sh.stepC.flatMap (fun p => zs (t * sh.S B) ++ p.1 ++ zs (B * sh.w + p.2.1) ++ [p.2.2, sep]) := by
  simp only [stepCLines, linesSem, lineSem, List.flatMap_map]
  congr 1; funext p
  simp only [It.sem, h15, h11, zs, List.replicate_add, List.append_assoc, List.append_nil,
    List.flatMap_cons, List.flatMap_nil]

theorem sem_stepX (v : ℕ → ℕ) (B t j : ℕ) (h15 : v 15 = t * sh.S B) (h11 : v 11 = B * sh.w)
    (h17 : v 17 = j * sh.w) :
    linesSem v (stepXLines sh) =
      sh.stepX.flatMap fun p =>
        zs (t * sh.S B) ++ p.1 ++ zs (j * sh.w) ++ p.2.1 ++ zs (B * sh.w + p.2.2.1) ++
          [p.2.2.2, sep] := by
  simp only [stepXLines, linesSem, lineSem, List.flatMap_map]
  congr 1; funext p
  simp only [It.sem, h15, h11, h17, zs, List.replicate_add, List.append_assoc, List.append_nil,
    List.flatMap_cons, List.flatMap_nil]

theorem st_eq {i X o o' : Str} {v v' : ℕ → ℕ} (ho : o = o') (hv : ∀ j, 3 ≤ j → v j = v' j) :
    st i X o v = st i X o' v' := by
  subst ho; exact st_congr hv

theorem U_le3 (Λ : ℕ) : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)

theorem ok_reg {v : ℕ → ℕ} {Λ r : ℕ} (h : 3 ≤ r ∧ r ≠ 7 ∧ v r ≤ Λ) : (It.reg r).Ok v Λ := h

/-! ## The inner loop over the columns -/

def jBody : Cmd := .seq (linesCmd (stepXLines sh)) (copyVia 18 17 7)

def jCmd : Cmd := .seq (copyVia 6 13 7) (.seq (forLoop 13 (jBody sh)) (drain 17))

/-- The step clauses with a gap, for all columns `j < B`. -/
def stepXPart (B t : ℕ) : List SatSym :=
  (List.range B).flatMap fun j =>
    sh.stepX.flatMap fun p =>
      zs (t * sh.S B) ++ p.1 ++ zs (j * sh.w) ++ p.2.1 ++ zs (B * sh.w + p.2.2.1) ++
        [p.2.2.2, sep]

theorem em_jCmd : ∃ A, ∀ (Λ : ℕ) (u : ℕ → ℕ) (t : ℕ), u 7 = 0 → u 13 = 0 → u 17 = 0 →
    u 18 = sh.w → u 15 = t * sh.S (u 6) → u 11 = u 6 * sh.w → u 6 ≤ Λ → u 15 ≤ Λ →
    u 6 * sh.w ≤ Λ →
    Em (jCmd sh) u (stepXPart sh (u 6) t) (A * (Λ + 1) ^ 2) := by
  refine ⟨linesCost (stepXLines sh) + 5 * sh.w + 20,
    fun Λ u t h7 h13 h17 h18 h15 h11 hB hT hBw i X o => ?_⟩
  set B := u 6 with hBdef
  set lc := linesCost (stepXLines sh)
  have hU := U_le Λ
  have s1 := (ex_copy (i := i) (X := X) (o := o) (a := 6) (b := 13) (t := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) u h7).mono
    (lin_U2 (Λ := Λ) (a := u 6) hB 5 4)
  set g : ℕ → ℕ → ℕ := fun k => update (update u 17 (k * sh.w)) 13 (B - k) with hg
  have e1 : update u 13 (u 13 + u 6) = g 0 := by
    funext j; simp only [g, update_apply]; split_ifs <;> simp_all
  rw [e1] at s1
  have s2 := (ex_forLoop (K := 13) (by norm_num) (body := jBody sh) (i := i) (X := X) B g
    (fun j => sh.stepX.flatMap fun p =>
      zs (t * sh.S B) ++ p.1 ++ zs (j * sh.w) ++ p.2.1 ++ zs (B * sh.w + p.2.2.1) ++
        [p.2.2.2, sep])
    (lc * (Λ + 1) + (5 * sh.w + 4))
    (fun k _ => by simp [g])
    (fun k hk o' => by
      set y := update (g k) 13 (B - k - 1) with hy
      have hkw : k * sh.w ≤ B * sh.w := Nat.mul_le_mul_right _ (by omega)
      have hl := linesCmd_em (v := y) (Λ := Λ) (by simp [y, g, h7]) (stepXLines sh) (by
        intro l hl it hit
        simp only [stepXLines, List.mem_map] at hl
        obtain ⟨p, _, rfl⟩ := hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
        rcases hit with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | (refine ⟨by norm_num, by norm_num, ?_⟩; simp [y, g]; omega) | trivial)
      rw [sem_stepX sh y B t k (by simp [y, g, h15]) (by simp [y, g, h11]) (by simp [y, g])] at hl
      have hc := ex_copy (i := i) (X := X) (o := rv (sh.stepX.flatMap fun p =>
          zs (t * sh.S B) ++ p.1 ++ zs (k * sh.w) ++ p.2.1 ++ zs (B * sh.w + p.2.2.1) ++
            [p.2.2.2, sep]) ++ o') (a := 18) (b := 17) (t := 7) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y
        (by simp [y, g, h7])
      refine ((hl i X o').seq_norm hc).cast ?_ (by simp [y, g, h18, lc])
      congr 1; apply st_congr; intro j _
      simp only [y, g, update_apply]; split_ifs <;> simp_all <;> first | omega | ring)
    o).mono (show _ ≤ (lc + 5 * sh.w + 7) * (Λ + 1) ^ 2 by
      have : B * (lc * (Λ + 1) + (5 * sh.w + 4) + 1) ≤
          (Λ + 1) * (lc * (Λ + 1) + (5 * sh.w + 4) + 1) := Nat.mul_le_mul_right _ (by omega)
      have := Nat.mul_le_mul_left (5 * sh.w + 7) hU
      nlinarith)
  have s3 := (ex_drain (i := i) (X := X) (o := rv (stepXPart sh B t) ++ o) (r := 17) (by norm_num) (g B)).mono
    (lin_U2 (Λ := Λ) (a := g B 17) (by simp [g]; omega) 2 2)
  refine (s1.seq_norm (s2.seq_norm s3)).cast ?_ (le_of_eq (by ring))
  congr 1; apply st_congr; intro j _; simp only [g, update_apply]; split_ifs <;> simp_all

/-! ## The time loop -/

def tBody : Cmd :=
  .seq (linesCmd (sliceLines sh)) (.seq (linesCmd (stepCLines sh)) (.seq (jCmd sh) (copyVia 10 15 7)))

def tCmd : Cmd :=
  .seq (copyVia 5 16 7) (.seq (forLoop 16 (tBody sh)) (.seq (linesCmd (sliceLines sh))
    (.seq (linesCmd (plc 15 sh.acc)) (drain 15))))

theorem ok_slice {v : ℕ → ℕ} {Λ : ℕ} (h15 : v 15 ≤ Λ) (h12 : v 12 ≤ Λ) :
    ∀ l ∈ sliceLines sh, ∀ it ∈ l, it.Ok v Λ := by
  intro l hl it hit
  simp only [sliceLines, List.mem_append] at hl
  rcases hl with hl | hl
  · exact plc_ok sh.sliceCls (by norm_num) (by norm_num) h15 l hl it hit
  · simp only [List.mem_map] at hl
    obtain ⟨c, _, rfl⟩ := hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl | rfl
    · exact ⟨by norm_num, by norm_num, h15⟩
    · exact ⟨by norm_num, by norm_num, h12⟩
    · trivial

theorem ok_stepC {v : ℕ → ℕ} {Λ : ℕ} (h15 : v 15 ≤ Λ) (h11 : v 11 ≤ Λ) :
    ∀ l ∈ stepCLines sh, ∀ it ∈ l, it.Ok v Λ := by
  intro l hl it hit
  simp only [stepCLines, List.mem_map] at hl
  obtain ⟨p, _, rfl⟩ := hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, by norm_num, h15⟩
  · trivial
  · exact ⟨by norm_num, by norm_num, h11⟩
  · trivial

theorem t_step (v : ℕ → ℕ) (S T t : ℕ) (h10 : v 10 = S) :
    update (update (update (update v 15 (t * S)) 16 (T - t)) 16 (T - t - 1)) 15
      (update (update (update v 15 (t * S)) 16 (T - t)) 16 (T - t - 1) 15 +
        update (update (update v 15 (t * S)) 16 (T - t)) 16 (T - t - 1) 10) =
    update (update v 15 ((t + 1) * S)) 16 (T - (t + 1)) := by
  funext j; simp only [update_apply]; split_ifs <;> simp_all <;> first | omega | ring

set_option maxHeartbeats 1000000 in
theorem em_tCmd : ∃ A, ∀ (Λ : ℕ) (v : ℕ → ℕ), v 7 = 0 → v 13 = 0 → v 15 = 0 → v 16 = 0 →
    v 17 = 0 → v 18 = sh.w → v 10 = sh.S (v 6) → v 11 = v 6 * sh.w → v 12 = sh.col (v 6) →
    v 5 ≤ Λ → v 6 ≤ Λ → v 5 * sh.S (v 6) ≤ Λ → sh.S (v 6) ≤ Λ → sh.col (v 6) ≤ Λ →
    v 6 * sh.w ≤ Λ →
    Em (tCmd sh) v ((List.range (v 5)).flatMap (fun t => sh.slicePart (v 6) t ++ sh.stepPart (v 6) t)
      ++ sh.slicePart (v 6) (v 5) ++ place (v 5 * sh.S (v 6)) sh.acc) (A * (Λ + 1) ^ 3) := by
  obtain ⟨Aj, hj⟩ := em_jCmd sh
  refine ⟨9 + (linesCost (sliceLines sh) + linesCost (stepCLines sh) + Aj + 12) +
    linesCost (sliceLines sh) + linesCost (plc 15 sh.acc) + 4,
    fun Λ v h7 h13 h15 h16 h17 h18 h10 h11 h12 hT hB hTS hS hcB hBw i X o => ?_⟩
  set T := v 5 with hTdef
  set B := v 6 with hBdef
  set S := sh.S B with hSdef
  set lcS := linesCost (sliceLines sh)
  set lcC := linesCost (stepCLines sh)
  set lcA := linesCost (plc 15 sh.acc)
  have hU := U_le Λ
  have hU3 := U_le3 Λ
  have s1 := (ex_copy (i := i) (X := X) (o := o) (a := 5) (b := 16) (t := 7) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) v h7).mono
    ((lin_U2 (Λ := Λ) (a := v 5) hT 5 4).trans (Nat.mul_le_mul_left _ hU3))
  set f : ℕ → ℕ → ℕ := fun t => update (update v 15 (t * S)) 16 (T - t) with hf
  have e1 : update v 16 (v 16 + v 5) = f 0 := by
    funext j; simp only [f, update_apply]; split_ifs <;> simp_all
  rw [e1] at s1
  have s2 := (ex_forLoop (K := 16) (by norm_num) (body := tBody sh) (i := i) (X := X) T f
    (fun t => sh.slicePart B t ++ sh.stepPart B t)
    ((lcS + lcC + Aj + 9) * (Λ + 1) ^ 2)
    (fun k _ => by simp [f])
    (fun t ht o' => by
      set y := update (f t) 16 (T - t - 1) with hy
      have htS : t * S ≤ T * S := Nat.mul_le_mul_right _ (by omega)
      have y15 : y 15 = t * S := by simp [y, f]
      have a1 := linesCmd_em (v := y) (Λ := Λ) (by simp [y, f, h7]) (sliceLines sh)
        (ok_slice sh (by rw [y15]; omega) (by simp [y, f, h12]; omega))
      rw [sem_slice sh y B t y15 (by simp [y, f, h12])] at a1
      have a2 := linesCmd_em (v := y) (Λ := Λ) (by simp [y, f, h7]) (stepCLines sh)
        (ok_stepC sh (by rw [y15]; omega) (by simp [y, f, h11]; omega))
      rw [sem_stepC sh y B t y15 (by simp [y, f, h11])] at a2
      have hy6 : y 6 = B := by
        show update (update (update v 15 (t * S)) 16 (T - t)) 16 (T - t - 1) 6 = v 6
        simp
      have a3 := hj Λ y t (by simp [y, f, h7]) (by simp [y, f, h13]) (by simp [y, f, h17])
        (by simp [y, f, h18]) (by rw [y15, hy6]) (by rw [hy6]; simp [y, f, h11])
        (by rw [hy6]; omega) (by rw [y15]; omega) (by rw [hy6]; omega)
      rw [hy6] at a3
      have a4 := ex_copy (i := i) (X := X) (o := rv (stepXPart sh B t) ++ (rv (sh.stepC.flatMap
        (fun p => zs (t * S) ++ p.1 ++ zs (B * sh.w + p.2.1) ++ [p.2.2, sep])) ++
        (rv (sh.slicePart B t) ++ o'))) (a := 10) (b := 15) (t := 7) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) y
        (by simp [y, f, h7])
      refine ((a1 i X o').seq_norm ((a2 i X _).seq_norm ((a3 i X _).seq_norm a4))).cast ?_ ?_
      · refine congrArg Res.norm (st_eq ?_ ?_)
        · simp only [Shape.stepPart, stepXPart, rv_append, List.append_assoc]; rfl
        · intro j _; exact congrFun (t_step v S T t h10) j
      · have e : y 10 = S := by simp [y, f, h10]
        rw [e]
        have := lin_U2' lcS Λ
        have := lin_U2' lcC Λ
        have := lin_U2 (Λ := Λ) hS 5 4
        nlinarith)
    o).mono (show _ ≤ (lcS + lcC + Aj + 12) * (Λ + 1) ^ 3 by
      have : T * ((lcS + lcC + Aj + 9) * (Λ + 1) ^ 2 + 1) ≤
          (Λ + 1) * ((lcS + lcC + Aj + 9) * (Λ + 1) ^ 2 + 1) := Nat.mul_le_mul_right _ (by omega)
      have e : (Λ + 1) ^ 3 = (Λ + 1) * (Λ + 1) ^ 2 := by ring
      rw [e]
      have := Nat.mul_le_mul_left (Λ + 1) hU
      nlinarith)
  set o2 := rv ((List.range T).flatMap fun t => sh.slicePart B t ++ sh.stepPart B t) ++ o
  have fT15 : f T 15 = T * S := by simp [f]
  have s3 := (linesCmd_em (v := f T) (Λ := Λ) (by simp [f, h7]) (sliceLines sh)
    (ok_slice sh (by rw [fT15]; omega) (by simp [f, h12]; omega)) i X o2).mono
    ((lin_U2' lcS Λ).trans (Nat.mul_le_mul_left _ hU3))
  rw [sem_slice sh (f T) B T fT15 (by simp [f, h12])] at s3
  have s4 := (em_plc (v := f T) (Λ := Λ) sh.acc (by simp [f, h7]) (k := 15) (by norm_num)
    (by norm_num) (by rw [fT15]; omega) i X (rv (sh.slicePart B T) ++ o2)).mono
    ((lin_U2' lcA Λ).trans (Nat.mul_le_mul_left _ hU3))
  rw [fT15] at s4
  have s5 := (ex_drain (i := i) (X := X) (o := rv (place (T * S) sh.acc) ++
    (rv (sh.slicePart B T) ++ o2)) (r := 15) (by norm_num) (f T)).mono
    ((lin_U2 (Λ := Λ) (a := f T 15) (by rw [fT15]; omega) 2 2).trans
      (Nat.mul_le_mul_left _ hU3))
  refine (s1.seq_norm (s2.seq_norm (s3.seq_norm (s4.seq_norm s5)))).cast ?_ (le_of_eq (by ring))
  refine congrArg Res.norm (st_eq ?_ ?_)
  · simp only [o2, rv_append, List.append_assoc]
  · clear s1 s2 s3 s4 s5 hj e1
    intro j _; simp only [f, update_apply, Nat.sub_self]; split_ifs <;> simp_all

end Pnp.CookLevin.Uniform
