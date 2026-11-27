import Pnp.Karp.ThreeSAT

/-!
# 3-SAT is in NP (official definition)

The checking relation is `R3 w y := Is3 w ∧ SatRel w y`.  The verifier program extends the SAT
verifier `satCmd` of `Pnp/CookLevin/SAT.lean`:

1. `phaseA` and `move 2 3` as in `satCmd` (the internal code of `w` is on stack `3`);
2. `copyVia 3 6 7`: copy it to the spare stack `6`;
3. `chkLoop`: scan stack `6`, counting the literals of the current clause in unary on stack
   `8`; at every `sep`, halt `false` if the count is `≥ 4` (`ge4`), otherwise the count is reset
   (this computes `chk w 0`, i.e. `Is3 w`);
4. `phaseC` as in `satCmd`.
-/

namespace Pnp.Karp.ThreeSAT

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym

/-! ## The counter check -/

/-- Pop stack `8` (doing nothing if it is empty), then run `c`. -/
def p8 (c : Cmd) : Cmd := .pop 8 .skip c c

/-- At a separator: halt `false` if stack `8` holds at least four marks, otherwise empty it. -/
def ge4 : Cmd := p8 (p8 (p8 (p8 (.halt false))))

/-- Loop body of `chkLoop` (reads one 2-bit symbol code from stack `6`). -/
def bodyK : Cmd :=
  .pop 6 .brk (.pop 6 .brk ge4 .skip) (.pop 6 .brk (.push 8 true) (.push 8 true))

/-- Compute `chk` on the code on stack `6`. -/
def chkLoop : Cmd := .loop bodyK

/-- Final literal count of `chk`. -/
def cnt : List SatSym → ℕ → ℕ
  | [], k => k
  | sep :: w, _ => cnt w 0
  | zero :: w, k => cnt w k
  | pos :: w, k => cnt w (k + 1)
  | neg :: w, k => cnt w (k + 1)

theorem p8_nil {c : Cmd} {σ : ℕ → Str} (h : σ 8 = []) : ExecLe (p8 c) σ (.norm σ) 2 :=
  (ExecLe.pop_nil h (ExecLe.skip σ)).cast rfl le_rfl

theorem p8_cons {c : Cmd} {σ : ℕ → Str} {s : Str} {r : Res} {T : ℕ} (h : σ 8 = true :: s)
    (hc : ExecLe c (update σ 8 s) r T) : ExecLe (p8 c) σ r (T + 1) :=
  ExecLe.pop_same h hc

theorem exec_ge4 (σ : ℕ → Str) (k : ℕ) (h : σ 8 = List.replicate k true) :
    ExecLe ge4 σ (if k ≤ 3 then .norm (update σ 8 []) else .halt false) 5 := by
  match k, h with
  | 0, h =>
    have h' : σ 8 = [] := h
    exact (p8_nil h).cast (by rw [if_pos (by omega), ← h', update_eq_self]) (by omega)
  | 1, h => exact (p8_cons (s := []) h (p8_nil (by simp))).cast (by simp) (by omega)
  | 2, h => exact (p8_cons (s := [true]) h (p8_cons (s := []) (by simp)
      (p8_nil (by simp)))).cast (by simp) (by omega)
  | 3, h => exact (p8_cons (s := [true, true]) h (p8_cons (s := [true]) (by simp)
      (p8_cons (s := []) (by simp) (p8_nil (by simp))))).cast (by simp) (by omega)
  | k + 4, h =>
    have h' : σ 8 = true :: true :: true :: true :: List.replicate k true := by
      rw [h]; simp [List.replicate_succ]
    exact (p8_cons h' (p8_cons (s := true :: true :: List.replicate k true) (by simp)
      (p8_cons (s := true :: List.replicate k true) (by simp)
      (p8_cons (s := List.replicate k true) (by simp)
      (ExecLe.halt false _))))).cast (by rw [if_neg (by omega)]) le_rfl

/-- What `chkLoop` produces. -/
def ckRes (σ : ℕ → Str) (w : List SatSym) (k : ℕ) : Res :=
  if chk w k then .norm (update (update σ 6 []) 8 (List.replicate (cnt w k) true)) else .halt false

theorem ckRes_congr {σ σ' : ℕ → Str} (h : ∀ j, j ≠ 6 → j ≠ 8 → σ' j = σ j) (w : List SatSym)
    (k : ℕ) : ckRes σ' w k = ckRes σ w k := by
  unfold ckRes
  split_ifs
  · congr 1; funext j; simp only [update_apply]; split_ifs with h1 h2 <;> try rfl
    exact h j h2 h1
  · rfl

theorem loopK {σ σ' : ℕ → Str} {r : Res} {T₁ T₂ T : ℕ} (hb : ExecLe bodyK σ (.norm σ') T₁)
    (ih : ExecLe chkLoop σ' r T₂) (hT : T₁ + T₂ ≤ T) : ExecLe chkLoop σ r T :=
  (ExecLe.loop_norm hb ih).cast rfl hT

theorem exec_chkLoop : ∀ (w : List SatSym) (σ : ℕ → Str) (k : ℕ),
    σ 6 = w.flatMap ic → σ 8 = List.replicate k true →
    ExecLe chkLoop σ (ckRes σ w k) (7 * w.length + 2)
  | [], σ, k, h6, h8 => (ExecLe.loop_brk (ExecLe.pop_nil h6 (ExecLe.brk σ))).cast
      (by
        simp only [ckRes, chk, cnt, if_true]
        congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all) (by simp)
  | sep :: w, σ, k, h6, h8 => by
    have h6' : σ 6 = false :: false :: w.flatMap ic := by simp [h6, ic]
    by_cases hk : k ≤ 3
    · let σ' := update (update σ 6 (w.flatMap ic)) 8 []
      have hg := exec_ge4 (update (update σ 6 (false :: w.flatMap ic)) 6 (w.flatMap ic)) k
        (by simp [h8])
      rw [if_pos hk] at hg
      have hb : ExecLe bodyK σ (.norm σ') (5 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h6' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
          (by simp) (hg.cast (by simp only [σ', update_idem]) le_rfl))
      have ih := exec_chkLoop w σ' 0 (by simp [σ']) (by simp [σ'])
      refine loopK hb (ih.cast ?_ le_rfl) (by simp; omega)
      rw [ckRes_congr (σ := σ) (fun j h1 h2 => by simp [σ', h1, h2])]
      simp [ckRes, chk, cnt, hk]
    · have hg := exec_ge4 (update (update σ 6 (false :: w.flatMap ic)) 6 (w.flatMap ic)) k
        (by simp [h8])
      rw [if_neg hk] at hg
      have hb : ExecLe bodyK σ (.halt false) (5 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h6' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
          (by simp) (hg.cast rfl le_rfl))
      exact (ExecLe.loop_halt hb).cast (by simp [ckRes, chk, hk]) (by simp; omega)
  | zero :: w, σ, k, h6, h8 => by
    have h6' : σ 6 = false :: true :: w.flatMap ic := by simp [h6, ic]
    let σ' := update σ 6 (w.flatMap ic)
    have hb : ExecLe bodyK σ (.norm σ') (1 + 1 + 1) :=
      ExecLe.pop_cons (b := false) h6' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
        (by simp) ((ExecLe.skip _).cast (by rw [update_idem]) le_rfl))
    have ih := exec_chkLoop w σ' k (by simp [σ']) (by simp [σ', h8])
    refine loopK hb (ih.cast ?_ le_rfl) (by simp; omega)
    rw [ckRes_congr (σ := σ) (fun j h1 h2 => by simp [σ', h1])]
    simp [ckRes, chk, cnt]
  | pos :: w, σ, k, h6, h8 => by
    have h6' : σ 6 = true :: false :: w.flatMap ic := by simp [h6, ic]
    let σ' := update (update σ 6 (w.flatMap ic)) 8 (true :: σ 8)
    have hb : ExecLe bodyK σ (.norm σ') (1 + 1 + 1) :=
      ExecLe.pop_cons (b := true) h6' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
        (by simp) ((ExecLe.push 8 true _).cast (by simp [σ', update_idem]) le_rfl))
    have ih := exec_chkLoop w σ' (k + 1) (by simp [σ']) (by simp [σ', h8, List.replicate_succ])
    refine loopK hb (ih.cast ?_ le_rfl) (by simp; omega)
    rw [ckRes_congr (σ := σ) (fun j h1 h2 => by simp [σ', h1, h2])]
    simp [ckRes, chk, cnt]
  | neg :: w, σ, k, h6, h8 => by
    have h6' : σ 6 = true :: true :: w.flatMap ic := by simp [h6, ic]
    let σ' := update (update σ 6 (w.flatMap ic)) 8 (true :: σ 8)
    have hb : ExecLe bodyK σ (.norm σ') (1 + 1 + 1) :=
      ExecLe.pop_cons (b := true) h6' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
        (by simp) ((ExecLe.push 8 true _).cast (by simp [σ', update_idem]) le_rfl))
    have ih := exec_chkLoop w σ' (k + 1) (by simp [σ']) (by simp [σ', h8, List.replicate_succ])
    refine loopK hb (ih.cast ?_ le_rfl) (by simp; omega)
    rw [ckRes_congr (σ := σ) (fun j h1 h2 => by simp [σ', h1, h2])]
    simp [ckRes, chk, cnt]

/-! ## The whole verifier -/

/-- The 3-SAT verifier program. -/
def sat3Cmd : Cmd := .seq phaseA (.seq (move 2 3) (.seq (copyVia 3 6 7) (.seq chkLoop phaseC)))

/-- Time bound of the verifier. -/
def Tsat3 (n : ℕ) : ℕ := Tsat n + (5 * n + 4) + (7 * n + 2)

theorem exec_sat3Cmd (z : Str) :
    ExecLe sat3Cmd (init [z]).stk
      (.halt (chk (dec z).1 0 && run (dec z).1 (dec z).2 [] false)) (Tsat3 z.length) := by
  have hl := dec_length z
  set w := (dec z).1
  set Y := (dec z).2
  have h0 : (init [z]).stk 0 = z := rfl
  have he : ∀ j, j ≠ 0 → (init [z]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have hA := exec_phaseA z (init [z]).stk h0
  set σ₁ := update (update (init [z]).stk 0 Y) 2 ((w.flatMap ic).reverse ++ (init [z]).stk 2)
  have hM := exec_move (a := 2) (b := 3) (by decide) _ σ₁ rfl
  set σ₂ := update (update σ₁ 2 []) 3 ((σ₁ 2).reverse ++ σ₁ 3)
  have h23 : σ₂ 3 = w.flatMap ic := by
    simp [σ₂, σ₁, he 3 (by decide), he 2 (by decide)]
  have hCp := exec_copyVia (a := 3) (b := 6) (t := 7) (by decide) (by decide) (by decide) σ₂
    (by simp [σ₂, σ₁, he 7 (by decide)])
  set σ₃ := update σ₂ 6 (σ₂ 3 ++ σ₂ 6)
  have hK := exec_chkLoop w σ₃ 0
    (by simp only [σ₃, update_self]; rw [h23]; simp [σ₂, σ₁, he 6 (by decide)])
    (by simp [σ₃, σ₂, σ₁, he 8 (by decide)])
  have hw : (w.flatMap ic).length = 2 * w.length := length_flatMap_ic w
  have hlen2 : (σ₂ 3).length = 2 * w.length := by rw [h23, hw]
  have hwz : w.length ≤ z.length := by omega
  have hTA : 3 * z.length + 4 + (2 * (σ₁ 2).length + 2) + (5 * (σ₂ 3).length + 4) +
      (7 * w.length + 2) ≤ 3 * z.length + 4 + (2 * z.length + 2) + (5 * z.length + 4) +
      (7 * z.length + 2) := by
    simp only [σ₁, update_self, List.length_append, List.length_reverse, hw, he 2 (by decide),
      List.length_nil, hlen2]
    omega
  cases hc : chk w 0
  · have hK' : ExecLe chkLoop σ₃ (.halt false) (7 * w.length + 2) := hK.cast
      (by simp [ckRes, hc]) le_rfl
    refine (ExecLe.seq_norm hA (ExecLe.seq_norm (ExecLe.of hM) (ExecLe.seq_norm (ExecLe.of hCp)
      (ExecLe.seq_halt hK')))).cast (by simp) ?_
    unfold Tsat3 Tsat; omega
  · set σ₄ := update (update σ₃ 6 []) 8 (List.replicate (cnt w 0) true)
    have hK' : ExecLe chkLoop σ₃ (.norm σ₄) (7 * w.length + 2) := hK.cast
      (by simp [ckRes, hc, σ₄]) le_rfl
    have hC := exec_phaseC Y.length w σ₄ Y [] false
      (by simp [σ₄, σ₃, h23]) (by simp [σ₄, σ₃, σ₂, σ₁])
      (by simp [σ₄, σ₃, σ₂, σ₁, he 5 (by decide)])
      (by simp [σ₄, σ₃, σ₂, σ₁, he 4 (by decide), CookLevin.fl]) (by simp)
    refine (ExecLe.seq_norm hA (ExecLe.seq_norm (ExecLe.of hM) (ExecLe.seq_norm (ExecLe.of hCp)
      (ExecLe.seq_norm hK' hC)))).cast (by simp) ?_
    have : Y.length ≤ z.length := by omega
    have : w.length * (2 * Y.length + 8) + 2 ≤ z.length * (2 * z.length + 8) + 2 := by
      nlinarith
    unfold Tsat3 Tsat; omega

theorem Tsat3_le (n : ℕ) : Tsat3 n ≤ tb 4 n := by
  unfold Tsat3 Tsat tb
  have h4 : 2 ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have : (n + 2) ^ 4 = (n + 2) ^ 2 * (n + 2) ^ 2 := by ring
  nlinarith

/-! ## Transfer to the official class -/

/-- The checking relation of 3-SAT. -/
def R3 (w : List SatSym) (y : List Bool) : Prop := Is3 w ∧ SatRel w y

theorem sat3Lang_iff (w : List SatSym) :
    SAT3Lang w ↔ ∃ y : List Bool, y.length ≤ w.length ∧ R3 w y := by
  unfold SAT3Lang R3
  rw [satLang_iff]
  constructor
  · rintro ⟨h3, y, hy, hR⟩; exact ⟨y, hy, h3, hR⟩
  · rintro ⟨y, hy, h3, hR⟩; exact ⟨h3, y, hy, hR⟩

/-- **3-SAT ∈ NP** for the official class `NP` (`Millennium.InNondeterministicPolynomialTime`). -/
theorem sat3_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      SAT3Lang := by
  classical
  have hrun := fun z => ((exec_sat3Cmd z).mono (Tsat3_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg sat3Cmd) (tb 4 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg sat3Cmd, 4, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) R3 := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq, Bool.and_eq_true]
    rw [run_eq y w y [] false 0 (by simp) (by simp) (by simp), ← is3_iff_chk]
    rfl
  refine ⟨Bool, inferInstance, R3, 1, hR, fun w => ?_⟩
  rw [sat3Lang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.ThreeSAT
