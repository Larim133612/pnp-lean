import Pnp.Karp.NAE
import Pnp.Karp.ThreeSATNP

/-!
# NAE-3SAT is in NP (official definition)

The checking relation is `nav_R w y := Is3 w ∧ SatRel w y ∧ SatRel (w.map swp) y`: the
certificate `y` (an assignment `a = y.getD · false`) satisfies `w`, and also `w` with all
literals complemented (i.e. `!a` satisfies `w`).

The verifier extends the 3-SAT verifier `sat3Cmd`: `phaseA`, `move 2 3`, `copyVia 3 6 7`,
`chkLoop` as there, and then `nav_phaseN`, a variant of `phaseC` evaluating `w` and its
complemented version in one pass, with two clause flags (stacks `4` and `9`).
-/

namespace Pnp.Karp.NAE

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.ThreeSAT

/-! ## The language side -/

theorem nav_evalF_swp (a : ℕ → Bool) : ∀ (w : List SatSym) (j : ℕ) (F : Bool),
    evalF a (w.map swp) j F = evalF (fun i => !a i) w j F
  | [], _, _ => rfl
  | sep :: w, j, F => by
    simp only [List.map_cons, swp, evalF, nav_evalF_swp a w 0 false]
  | zero :: w, j, F => by
    simp only [List.map_cons, swp, evalF, nav_evalF_swp a w (j + 1) F]
  | pos :: w, j, F => by
    simp only [List.map_cons, swp, evalF, nav_evalF_swp a w (j + 1)]
  | neg :: w, j, F => by
    simp only [List.map_cons, swp, evalF, nav_evalF_swp a w (j + 1), Bool.not_not]

theorem nav_evalF_iff (a : ℕ → Bool) (w : List SatSym) :
    evalF a w 0 false = true ↔ ∀ c ∈ clauses w, ClauseSat a c := by
  have := evalF_eq_clauses a w [] false (by simp [ClauseSat])
  simpa [clauses] using this

/-- The checking relation of NAE-3SAT. -/
def nav_R (w : List SatSym) (y : List Bool) : Prop :=
  Is3 w ∧ SatRel w y ∧ SatRel (w.map swp) y

theorem nav_nae_iff_eval (a : ℕ → Bool) (w : List SatSym) :
    (∀ c ∈ clauses w, NAESat a c) ↔
      evalF a w 0 false = true ∧ evalF a (w.map swp) 0 false = true := by
  rw [nav_evalF_swp, nav_evalF_iff, nav_evalF_iff]
  unfold NAESat
  constructor
  · intro h; exact ⟨fun c hc => (h c hc).1, fun c hc => (h c hc).2⟩
  · rintro ⟨h1, h2⟩ c hc; exact ⟨h1 c hc, h2 c hc⟩

theorem nav_lang_iff (w : List SatSym) :
    NAE3Lang w ↔ ∃ y : List Bool, y.length ≤ w.length ∧ nav_R w y := by
  unfold NAE3Lang nav_R SatRel
  constructor
  · rintro ⟨h3, a, ha⟩
    rw [nav_nae_iff_eval] at ha
    refine ⟨(List.range w.length).map a, by simp, h3, ?_, ?_⟩
    · rw [← ha.1]
      refine evalF_congr w 0 false (fun i hi => ?_)
      simp only [zero_add] at hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    · rw [← ha.2]
      refine evalF_congr _ 0 false (fun i hi => ?_)
      simp only [zero_add, List.length_map] at hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  · rintro ⟨y, -, h3, h1, h2⟩
    exact ⟨h3, _, (nav_nae_iff_eval _ w).2 ⟨h1, h2⟩⟩

/-! ## The two-flag evaluation loop -/

/-- Set the flag stack `9` to `[true]`. -/
def nav_setG : Cmd := .pop 9 (.push 9 true) (.push 9 true) (.push 9 true)

/-- Loop body of `nav_phaseN`. -/
def nav_bodyN : Cmd :=
  .pop 3 (.halt true)
    (.pop 3 (.halt true)
      (.pop 4 (.halt false) (.halt false) (.pop 9 (.halt false) (.halt false) (move 5 0)))
      (.pop 0 .skip (.push 5 false) (.push 5 true)))
    (.pop 3 (.halt true)
      (.pop 0 nav_setG (.seq (.push 5 false) nav_setG) (.seq (.push 5 true) setF))
      (.pop 0 setF (.seq (.push 5 false) setF) (.seq (.push 5 true) nav_setG)))

/-- Evaluate the formula on stack `3` and its complemented version. -/
def nav_phaseN : Cmd := .loop nav_bodyN

/-- What `nav_phaseN` computes. -/
def nav_runN : List SatSym → Str → Str → Bool → Bool → Bool
  | [], _, _, _, _ => true
  | sep :: w, Y, U, F, G => F && G && nav_runN w (U.reverse ++ Y) [] false false
  | zero :: w, [], U, F, G => nav_runN w [] U F G
  | zero :: w, b :: Y, U, F, G => nav_runN w Y (b :: U) F G
  | pos :: w, [], U, F, _ => nav_runN w [] U F true
  | pos :: w, b :: Y, U, F, G => nav_runN w Y (b :: U) (F || b) (G || !b)
  | neg :: w, [], U, _, G => nav_runN w [] U true G
  | neg :: w, b :: Y, U, F, G => nav_runN w Y (b :: U) (F || !b) (G || b)

theorem nav_runN_eq : ∀ (w : List SatSym) (Y U : Str) (F G : Bool),
    nav_runN w Y U F G = (run w Y U F && run (w.map swp) Y U G)
  | [], _, _, _, _ => rfl
  | sep :: w, Y, U, F, G => by
    simp only [nav_runN, List.map_cons, swp, run, nav_runN_eq w]
    cases F <;> cases G <;> simp
  | zero :: w, [], U, F, G => by simp only [nav_runN, List.map_cons, swp, run, nav_runN_eq w]
  | zero :: w, b :: Y, U, F, G => by
    simp only [nav_runN, List.map_cons, swp, run, nav_runN_eq w]
  | pos :: w, [], U, F, G => by simp only [nav_runN, List.map_cons, swp, run, nav_runN_eq w]
  | pos :: w, b :: Y, U, F, G => by
    simp only [nav_runN, List.map_cons, swp, run, nav_runN_eq w]
  | neg :: w, [], U, F, G => by simp only [nav_runN, List.map_cons, swp, run, nav_runN_eq w]
  | neg :: w, b :: Y, U, F, G => by
    simp only [nav_runN, List.map_cons, swp, run, nav_runN_eq w]

theorem nav_exec_setG (G : Bool) (σ : ℕ → Str) (h : σ 9 = CookLevin.fl G) :
    ExecLe nav_setG σ (.norm (update σ 9 [true])) 2 := by
  cases G
  · exact (ExecLe.pop_nil h (ExecLe.push 9 true σ)).cast (by simp [h, CookLevin.fl]) le_rfl
  · exact (ExecLe.pop_cons h (ExecLe.push 9 true _)).cast (by simp) le_rfl

theorem nav_loopN {σ σ' : ℕ → Str} {r : Res} {T₁ T₂ T : ℕ} (hb : ExecLe nav_bodyN σ (.norm σ') T₁)
    (ih : ExecLe nav_phaseN σ' r T₂) (hT : T₁ + T₂ ≤ T) : ExecLe nav_phaseN σ r T :=
  (ExecLe.loop_norm hb ih).cast rfl hT

theorem nav_exec_phaseN (N : ℕ) : ∀ (w : List SatSym) (σ : ℕ → Str) (Y U : Str) (F G : Bool),
    σ 3 = w.flatMap ic → σ 0 = Y → σ 5 = U → σ 4 = CookLevin.fl F → σ 9 = CookLevin.fl G →
    U.length + Y.length ≤ N →
    ExecLe nav_phaseN σ (.halt (nav_runN w Y U F G)) (w.length * (2 * N + 8) + 2)
  | [], σ, Y, U, F, G, h3, _, _, _, _, _ =>
    (ExecLe.loop_halt (ExecLe.pop_nil h3 (ExecLe.halt true σ))).cast (by simp [nav_runN])
      (by simp)
  | sep :: w, σ, Y, U, F, G, h3, h0, h5, h4, h9, hN => by
    have h3' : σ 3 = false :: false :: w.flatMap ic := by simp [h3, ic]
    cases F
    · have hb : ExecLe nav_bodyN σ (.halt false) (1 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_nil (by simpa [CookLevin.fl] using h4) (ExecLe.halt false _)))
      exact (ExecLe.loop_halt hb).cast (by simp [nav_runN]) (by simp; nlinarith)
    cases G
    · have hb : ExecLe nav_bodyN σ (.halt false) (1 + 1 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_cons (b := true) (s := []) (by simpa [CookLevin.fl] using h4)
            (ExecLe.pop_nil (by simpa [CookLevin.fl] using h9) (ExecLe.halt false _))))
      exact (ExecLe.loop_halt hb).cast (by simp [nav_runN]) (by simp; nlinarith)
    · let σ' := update (update (update (update (update σ 3 (w.flatMap ic)) 4 []) 9 []) 5 [])
        0 (U.reverse ++ Y)
      have hb : ExecLe nav_bodyN σ (.norm σ') (2 * U.length + 2 + 1 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_cons (b := true) (s := []) (by simpa [CookLevin.fl] using h4)
            (ExecLe.pop_cons (b := true) (s := []) (by simpa [CookLevin.fl] using h9)
            ((ExecLe.of (exec_move (a := 5) (b := 0) (by decide) U _ (by simp [h5]))).cast
              (by simp only [σ']; ueq) le_rfl))))
      have ih := nav_exec_phaseN N w σ' (U.reverse ++ Y) [] false false (by simp [σ'])
        (by simp [σ']) (by simp [σ']) (by simp [σ', CookLevin.fl]) (by simp [σ', CookLevin.fl]) (by simp; omega)
      exact nav_loopN hb (ih.cast (by simp [nav_runN]) le_rfl) (by simp; nlinarith)
  | zero :: w, σ, Y, U, F, G, h3, h0, h5, h4, h9, hN => by
    have h3' : σ 3 = false :: true :: w.flatMap ic := by simp [h3, ic]
    cases Y with
    | nil =>
      let σ' := update σ 3 (w.flatMap ic)
      have hb : ExecLe nav_bodyN σ (.norm σ') (1 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_nil (by simp [h0])
            ((ExecLe.skip _).cast (by simp only [σ']; ueq) le_rfl)))
      have ih := nav_exec_phaseN N w σ' [] U F G (by simp [σ']) (by simp [σ', h0])
        (by simp [σ', h5]) (by simp [σ', h4]) (by simp [σ', h9]) (by simpa using hN)
      exact nav_loopN hb (ih.cast (by simp [nav_runN]) le_rfl) (by simp; nlinarith)
    | cons b Y =>
      let σ' := update (update (update σ 3 (w.flatMap ic)) 0 Y) 5 (b :: U)
      have hb : ExecLe nav_bodyN σ (.norm σ') (1 + 1 + 1 + 1) := by
        refine ExecLe.pop_cons (b := false) h3' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_cons (b := b) (s := Y) (by simp [h0]) ?_))
        cases b
        · exact (ExecLe.push 5 false _).cast (by simp only [σ']; ueq) le_rfl
        · exact (ExecLe.push 5 true _).cast (by simp only [σ']; ueq) le_rfl
      have ih := nav_exec_phaseN N w σ' Y (b :: U) F G (by simp [σ'])
        (by simp [σ']) (by simp [σ'])
        (by simp [σ', h4]) (by simp [σ', h9]) (by simp at hN ⊢; omega)
      exact nav_loopN hb (ih.cast (by simp [nav_runN]) le_rfl) (by simp; nlinarith)
  | pos :: w, σ, Y, U, F, G, h3, h0, h5, h4, h9, hN => by
    have h3' : σ 3 = true :: false :: w.flatMap ic := by simp [h3, ic]
    cases Y with
    | nil =>
      let σ' := update (update σ 3 (w.flatMap ic)) 9 [true]
      have hb : ExecLe nav_bodyN σ (.norm σ') (2 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_nil (by simp [h0])
            ((nav_exec_setG G _ (by simp [h9])).cast
              (by simp only [σ']; ueq) le_rfl)))
      have ih := nav_exec_phaseN N w σ' [] U F true (by simp [σ']) (by simp [σ', h0])
        (by simp [σ', h5]) (by simp [σ', h4]) (by simp [σ', CookLevin.fl]) (by simpa using hN)
      exact nav_loopN hb (ih.cast (by simp [nav_runN]) le_rfl) (by simp; nlinarith)
    | cons b Y =>
      cases b
      · let σ' := update (update (update (update σ 3 (w.flatMap ic)) 0 Y) 5 (false :: U)) 9
          [true]
        have hb : ExecLe nav_bodyN σ (.norm σ') (1 + 2 + 1 + 1 + 1) :=
          ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
            (by simp) (ExecLe.pop_cons (b := false) (s := Y) (by simp [h0])
              ((ExecLe.seq_norm (ExecLe.push 5 false _)
                (nav_exec_setG G _ (by simp [h9]))).cast
                  (by simp only [σ']; ueq) le_rfl)))
        have ih := nav_exec_phaseN N w σ' Y (false :: U) F true (by simp [σ'])
          (by simp [σ']) (by simp [σ'])
          (by simp [σ', h4]) (by simp [σ', CookLevin.fl]) (by simp at hN ⊢; omega)
        exact nav_loopN hb (ih.cast (by simp [nav_runN]) le_rfl) (by simp; nlinarith)
      · let σ' := update (update (update (update σ 3 (w.flatMap ic)) 0 Y) 5 (true :: U)) 4
          [true]
        have hb : ExecLe nav_bodyN σ (.norm σ') (1 + 2 + 1 + 1 + 1) :=
          ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := false) (s := w.flatMap ic)
            (by simp) (ExecLe.pop_cons (b := true) (s := Y) (by simp [h0])
              ((ExecLe.seq_norm (ExecLe.push 5 true _)
                (exec_setF F _ (by simp [h4]))).cast
                  (by simp only [σ']; ueq) le_rfl)))
        have ih := nav_exec_phaseN N w σ' Y (true :: U) true G (by simp [σ'])
          (by simp [σ']) (by simp [σ'])
          (by simp [σ', CookLevin.fl]) (by simp [σ', h9]) (by simp at hN ⊢; omega)
        exact nav_loopN hb (ih.cast (by simp [nav_runN]) le_rfl) (by simp; nlinarith)
  | neg :: w, σ, Y, U, F, G, h3, h0, h5, h4, h9, hN => by
    have h3' : σ 3 = true :: true :: w.flatMap ic := by simp [h3, ic]
    cases Y with
    | nil =>
      let σ' := update (update σ 3 (w.flatMap ic)) 4 [true]
      have hb : ExecLe nav_bodyN σ (.norm σ') (2 + 1 + 1 + 1) :=
        ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
          (by simp) (ExecLe.pop_nil (by simp [h0])
            ((exec_setF F _ (by simp [h4])).cast (by simp only [σ']; ueq) le_rfl)))
      have ih := nav_exec_phaseN N w σ' [] U true G (by simp [σ'])
        (by simp [σ', h0]) (by simp [σ', h5])
        (by simp [σ', CookLevin.fl]) (by simp [σ', h9]) (by simpa using hN)
      exact nav_loopN hb (ih.cast (by simp [nav_runN]) le_rfl) (by simp; nlinarith)
    | cons b Y =>
      cases b
      · let σ' := update (update (update (update σ 3 (w.flatMap ic)) 0 Y) 5 (false :: U)) 4
          [true]
        have hb : ExecLe nav_bodyN σ (.norm σ') (1 + 2 + 1 + 1 + 1) :=
          ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
            (by simp) (ExecLe.pop_cons (b := false) (s := Y) (by simp [h0])
              ((ExecLe.seq_norm (ExecLe.push 5 false _)
                (exec_setF F _ (by simp [h4]))).cast
                  (by simp only [σ']; ueq) le_rfl)))
        have ih := nav_exec_phaseN N w σ' Y (false :: U) true G (by simp [σ'])
          (by simp [σ']) (by simp [σ'])
          (by simp [σ', CookLevin.fl]) (by simp [σ', h9]) (by simp at hN ⊢; omega)
        exact nav_loopN hb (ih.cast (by simp [nav_runN]) le_rfl) (by simp; nlinarith)
      · let σ' := update (update (update (update σ 3 (w.flatMap ic)) 0 Y) 5 (true :: U)) 9
          [true]
        have hb : ExecLe nav_bodyN σ (.norm σ') (1 + 2 + 1 + 1 + 1) :=
          ExecLe.pop_cons (b := true) h3' (ExecLe.pop_cons (b := true) (s := w.flatMap ic)
            (by simp) (ExecLe.pop_cons (b := true) (s := Y) (by simp [h0])
              ((ExecLe.seq_norm (ExecLe.push 5 true _)
                (nav_exec_setG G _ (by simp [h9]))).cast
                  (by simp only [σ']; ueq) le_rfl)))
        have ih := nav_exec_phaseN N w σ' Y (true :: U) F true (by simp [σ'])
          (by simp [σ']) (by simp [σ'])
          (by simp [σ', h4]) (by simp [σ', CookLevin.fl]) (by simp at hN ⊢; omega)
        exact nav_loopN hb (ih.cast (by simp [nav_runN]) le_rfl) (by simp; nlinarith)

/-! ## The whole verifier -/

/-- The NAE-3SAT verifier program. -/
def nav_cmd : Cmd :=
  .seq phaseA (.seq (move 2 3) (.seq (copyVia 3 6 7) (.seq chkLoop nav_phaseN)))

theorem nav_exec_cmd (z : Str) :
    ExecLe nav_cmd (init [z]).stk
      (.halt (chk (dec z).1 0 && nav_runN (dec z).1 (dec z).2 [] false false))
      (Tsat3 z.length) := by
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
    have hC := nav_exec_phaseN Y.length w σ₄ Y [] false false
      (by simp [σ₄, σ₃, h23]) (by simp [σ₄, σ₃, σ₂, σ₁])
      (by simp [σ₄, σ₃, σ₂, σ₁, he 5 (by decide)])
      (by simp [σ₄, σ₃, σ₂, σ₁, he 4 (by decide), CookLevin.fl])
      (by simp [σ₄, σ₃, σ₂, σ₁, he 9 (by decide), CookLevin.fl]) (by simp)
    refine (ExecLe.seq_norm hA (ExecLe.seq_norm (ExecLe.of hM) (ExecLe.seq_norm (ExecLe.of hCp)
      (ExecLe.seq_norm hK' hC)))).cast (by simp) ?_
    have : Y.length ≤ z.length := by omega
    have : w.length * (2 * Y.length + 8) + 2 ≤ z.length * (2 * z.length + 8) + 2 := by
      nlinarith
    unfold Tsat3 Tsat; omega

/-! ## Transfer to the official class -/

/-- **NAE-3SAT ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem nae_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      NAE3Lang := by
  classical
  have hrun := fun z => ((nav_exec_cmd z).mono (Tsat3_le z.length)).runFor_toProg
  let S : Set Str := {z | runFor ∅ (toProg nav_cmd) (tb 4 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg nav_cmd, 4, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) nav_R := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq, Bool.and_eq_true]
    rw [nav_runN_eq, Bool.and_eq_true,
      run_eq y w y [] false 0 (by simp) (by simp) (by simp),
      run_eq y (w.map swp) y [] false 0 (by simp) (by simp) (by simp), ← is3_iff_chk]
    rfl
  refine ⟨Bool, inferInstance, nav_R, 1, hR, fun w => ?_⟩
  rw [nav_lang_iff]
  simp only [Millennium.fin_encoding_string_encode, pow_one]
  exact Iff.rfl

end Pnp.Karp.NAE
