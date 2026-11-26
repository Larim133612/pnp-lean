import Pnp.Oracle.FromNP
import Pnp.Oracle.OfficialP

/-!
# Official `NP` = our `NP ∅`

The verifier `V` (see `Pnp/Oracle/FromNP.lean`) is the concatenation of

* stage 1 `pre1 k` (move certificate and input, count the input),
* the nested counting loops `Comb.pad k` (a clock of `|x|^k` marks on stack `1`),
* stages 3–4 `P2` (decode the certificate, build the official input `x # y` on stack `0`),
* the compiled official machine `FromTM2.prog`.

`outcome`: on every input/certificate pair, `V` halts; if it accepts, the certificate encodes
some `y` with `|y| ≤ |x|^k` that the official machine accepts with `x`.  Conversely, the
honest certificate of such a `y` is accepted within polynomial time.
-/

namespace Pnp.Relativize.FromNP

open Turing Function Polynomial Pnp.Relativize.Comb Pnp.Relativize.FromTM2

/-- Running into a halting instruction. -/
theorem runFor_halt {p : Prog} {a pc t : ℕ} {σ σ' : ℕ → Str} {b : Bool}
    (h : Reach ∅ p a σ pc σ' t) (hp : p[pc]? = some (.halt b)) :
    runFor ∅ p (t + 1) (.run ⟨a, σ⟩) = .done b := by
  unfold Reach at h
  rw [runFor_add, h, runFor_succ_run]
  simp [step, hp]

theorem count_cs_big {k j : ℕ} (hj : 2 * k < j) : (cs k).count j = 0 := by
  rw [List.count_eq_zero]
  simp only [cs, List.mem_map, List.mem_range, not_exists, not_and]
  intro i hi h; unfold cnt at h; omega

/-- The official input `x # y` (as pair-alphabet symbols). -/
def inputOf {Γ₁ : Type} (x : Str) (ys : List Γ₁) : List (Bool ⊕ Option Γ₁) :=
  x.map .inl ++ .inr none :: ys.map (fun γ => .inr (some γ))

theorem inputOf_length {Γ₁ : Type} (x : Str) (ys : List Γ₁) :
    (inputOf x ys).length = x.length + 1 + ys.length := by
  simp [inputOf]; omega

section Main

variable (tm : FinTM2) {Γ₁ : Type} (e₀ : tm.Γ tm.k₀ ≃ (Bool ⊕ Option Γ₁))
  (e₁ : tm.Γ tm.k₁ ≃ Bool) (k : ℕ)

attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin FinTM2.kFin FinTM2.kDecidableEq

open scoped Classical

/-- Start address of stages 3–4. -/
def b2 (k : ℕ) : ℕ := 5 * k + 8

/-- Start address of the compiled official machine. -/
noncomputable def b3 : ℕ := b2 k + (P2 tm e₀ k).length

/-- The verifier. -/
noncomputable def V : Prog :=
  pre1 k ++ (pad k (7 + k) ++ ((P2 tm e₀ k).map (reloc (b2 k)) ++
    (prog tm (lay tm k) e₁).map (reloc (b3 tm e₀ k))))

theorem V_pre1 : CodeAt (V tm e₀ e₁ k) 0 (pre1 k) := (codeAt_self _).left

theorem V_pad : CodeAt (V tm e₀ e₁ k) (7 + k) (pad k (7 + k)) :=
  ((codeAt_self (V tm e₀ e₁ k)).right.left).rebase (by simp)

theorem V_P2 : CodeAt (V tm e₀ e₁ k) (b2 k) ((P2 tm e₀ k).map (reloc (b2 k))) :=
  ((codeAt_self (V tm e₀ e₁ k)).right.right.left).rebase (by simp [b2]; ring)

theorem V_P3 : CodeAt (V tm e₀ e₁ k) (b3 tm e₀ k) ((prog tm (lay tm k) e₁).map (reloc (b3 tm e₀ k))) :=
  ((codeAt_self (V tm e₀ e₁ k)).right.right.right).rebase (by simp [b3, b2]; ring)

theorem V_rej : (V tm e₀ e₁ k)[b2 k + i2 tm k .rej]? = some (.halt false) := by
  have hlt : i2 tm k .rej < (P2 tm e₀ k).length := by
    simp only [P2, List.length_map, i2]; exact List.idxOf_lt_length_iff.2 (rej_mem tm k)
  rw [V_P2 tm e₀ e₁ k _ (by simpa using hlt), List.getElem?_map,
    P2_idx tm e₀ k (rej_mem tm k)]
  rfl

theorem V_fin (b : Bool) :
    (V tm e₀ e₁ k)[b3 tm e₀ k + idx tm (lay tm k) (.fin b)]? = some (.halt b) := by
  have hm := fin_mem tm (lay tm k) b
  have hlt : idx tm (lay tm k) (.fin b) < (prog tm (lay tm k) e₁).length := by
    simp only [prog, List.length_map, idx]; exact List.idxOf_lt_length_iff.2 hm
  rw [V_P3 tm e₀ e₁ k _ (by simpa using hlt), List.getElem?_map, prog_idx tm (lay tm k) e₁ hm]
  rfl

theorem i2_rdW0 : i2 tm k (.rdW 0) = 0 := by
  simp [i2, S2, List.range_succ_eq_map]

variable {f : Str × List Γ₁ → Bool} {time : Polynomial ℕ}

/-- The bound on the running time. -/
noncomputable def bnd (time : Polynomial ℕ) (x : Str) (ys : List Γ₁) : ℕ :=
  2 * (ys.flatMap (cc tm e₀ k)).length + 1 + (x.length * (k + 3) + 1) + Tpad x.length k +
    (ys.length * (2 * n0 tm k + 2) + n0 tm k) + (ys.length * (2 * n0 tm k + 2) + n0 tm k) +
    (n0 tm k + 2) + (x.length * (n0 tm k + 3) + 1) +
    (time.eval (x.length + 1 + ys.length) * (Dm tm * B tm (lay tm k)) + 1 +
      N tm (lay tm k) tm.k₁) + 1

/-- **The verifier's behaviour.** -/
theorem outcome
    (hout : ∀ (x : Str) (ys : List Γ₁), TM2OutputsInTime tm ((inputOf x ys).map e₀.symm)
      (some [e₁.symm (f (x, ys))]) (time.eval (inputOf x ys).length))
    (x w : Str) :
    (∃ t, runFor ∅ (V tm e₀ e₁ k) t (.run (init [x, w])) = .done false ∧
      ¬ ∃ ys : List Γ₁, ys.length ≤ x.length ^ k ∧ w.reverse = ys.flatMap (cc tm e₀ k)) ∨
    (∃ (ys : List Γ₁) (t : ℕ), ys.length ≤ x.length ^ k ∧ w.reverse = ys.flatMap (cc tm e₀ k) ∧
      t ≤ bnd tm e₀ k time x ys ∧
      runFor ∅ (V tm e₀ e₁ k) t (.run (init [x, w])) = .done (f (x, ys))) := by
  set σ0 : ℕ → Str := fun j => [x, w].getD j [] with hσ0
  have e0 : init [x, w] = ⟨0, σ0⟩ := rfl
  rw [e0]
  have hbig0 : ∀ j, 2 ≤ j → σ0 j = [] := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    simp [hσ0]
  -- stage 1
  have hA := reach_mvW (V_pre1 tm e₀ e₁ k) w σ0 rfl
  set σa := update (update σ0 1 []) (sW k) (w.reverse ++ σ0 (sW k)) with hσa
  have hσa0 : σa 0 = x := by
    rw [hσa, update_of_ne (by unfold sW; omega), update_of_ne (by omega)]; rfl
  have hB := reach_mvX (V_pre1 tm e₀ e₁ k) x σa hσa0
  set σb := afterX k x σa with hσb
  have hfull : Full k x.length σb := by
    intro j hj
    have h1 : cnt j ≠ 0 := by unfold cnt; omega
    have h2 : cnt j ≠ sX k := by unfold cnt sX; omega
    have h3 : aux j ≠ 0 := by unfold aux; omega
    have h4 : aux j ≠ sX k := by unfold aux sX; omega
    have h5 : cnt j ≠ sW k := by unfold cnt sW; omega
    have h6 : aux j ≠ sW k := by unfold aux sW; omega
    have h7 : cnt j ≠ 1 := cnt_ne_one j
    have h8 : aux j ≠ 1 := aux_ne_one j
    simp only [hσb, afterX, h1, h2, h3, h4, if_false, count_cnt_cs hj, count_aux_cs, mul_one,
      mul_zero, List.replicate_zero, List.nil_append, hσa, update_of_ne h5, update_of_ne h6,
      update_of_ne h7, update_of_ne h8]
    exact ⟨by rw [hbig0 _ (by unfold cnt; omega), List.append_nil],
      hbig0 _ (by unfold aux; omega)⟩
  have hC := reach_pad (O := ∅) x.length k (7 + k) σb (V_pad tm e₀ e₁ k) hfull
  set σc := update σb 1 (List.replicate (x.length ^ k) true ++ σb 1) with hσc
  -- facts about `σc`
  have hσb1 : σb 1 = [] := by
    simp [hσb, afterX, count_cs_one, hσa, (sW_ne_one k).symm, sX]
  have hc1 : σc 1 = List.replicate (x.length ^ k) true := by simp [hσc, hσb1]
  have hcW : σc (sW k) = w.reverse := by
    have : sW k ≠ 0 := by unfold sW; omega
    have h2 : sW k ≠ sX k := by unfold sW sX; omega
    rw [hσc, update_of_ne (sW_ne_one k), hσb, afterX, if_neg this, if_neg h2,
      count_cs_big (by unfold sW; omega), hσa, update_self, hbig0 _ (by unfold sW; omega)]
    simp
  have hcbig : ∀ j, 2 * k + 4 ≤ j → σc j = [] := by
    intro j hj
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    have hX : j ≠ sX k := by unfold sX; omega
    have hW : j ≠ sW k := by unfold sW; omega
    rw [hσc, update_of_ne h1, hσb, afterX, if_neg h0, if_neg hX, count_cs_big (by omega), hσa,
      update_of_ne hW, update_of_ne h1, hbig0 j (by omega)]
    simp
  have hc0 : σc 0 = [] := by simp [hσc, hσb, afterX]
  have hcX : σc (sX k) = x.reverse := by
    have h1 : sX k ≠ 1 := by unfold sX; omega
    rw [hσc, update_of_ne h1, hσb, afterX, if_neg (sX_ne_zero k), if_pos rfl, hσa,
      update_of_ne (by unfold sX sW; omega), update_of_ne h1, hbig0 _ (by unfold sX; omega)]
    simp
  have hABC : Reach ∅ (V tm e₀ e₁ k) 0 σ0 (b2 k + i2 tm k (.rdW 0)) σc
      (2 * w.length + 1 + (x.length * (k + 3) + 1) + Tpad x.length k) :=
    ((hA.trans hB).trans hC).cast (by rw [i2_rdW0]; simp [b2]; ring) rfl rfl
  -- stage 3
  rcases decode tm e₀ k w.reverse (x.length ^ k) σc hcW hc1 with
    ⟨t, σ', h, hno⟩ | ⟨ys, t, σd, hyl, hys, ht, hD, hdZ, hdfr⟩
  · left
    exact ⟨_, runFor_halt (hABC.trans (Reach.embed (V_P2 tm e₀ e₁ k) h)) (V_rej tm e₀ e₁ k),
      hno⟩
  right
  have hcZ : σc (sZ k) = [] := hcbig _ (by unfold sZ; omega)
  -- stage 4a
  set zs := (ys.reverse).map (fun γ => cd tm e₀ k (.inr (some γ))) with hzs
  have hzlt : ∀ i ∈ zs, i < n0 tm k := by
    intro i hi; simp only [hzs, List.mem_map] at hi; obtain ⟨γ, -, rfl⟩ := hi; exact cd_lt _ _ _ _
  have hdZ' : σd (sZ k) = zs.flatMap (tu (n0 tm k)) := by
    rw [hdZ, hcZ, List.append_nil, hzs, List.flatMap_map]; rfl
  obtain ⟨t2, σe, hE2, ht2, he0, hefr⟩ := transfer tm e₀ k zs σd hzlt hdZ'
  -- the separator
  have hS := reach_oc tm e₀ k (cd_lt tm e₀ k (.inr none)) false σe
  simp only [Bool.false_eq_true, if_false] at hS
  set σf := update σe 0 (tu (n0 tm k) (cd tm e₀ k (.inr none)) ++ σe 0) with hσf
  -- stage 4b
  have hfX : σf (sX k) = x.reverse := by
    rw [hσf, update_of_ne (sX_ne_zero k), hefr _ (sX_ne_zero k) (by unfold sX sZ; omega),
      hdfr _ (by unfold sX sW; omega) (by unfold sX sZ; omega) (by unfold sX; omega), hcX]
  obtain ⟨t3, σg, hX3, ht3, hg0, hgfr⟩ := buildX tm e₀ k x.reverse σf hfX
  have hexit : b2 k + i2 tm k .exit = b3 tm e₀ k := by
    simp [b3, i2_exit, P2]
  have h34 := Reach.embed (V_P2 tm e₀ e₁ k) (((hD.trans hE2).trans hS).trans hX3)
  rw [hexit] at h34
  -- the compiled official machine
  have hEnc : Enc tm (lay tm k)
      (initList tm ((inputOf x ys).map e₀.symm) : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ).stk σg := by
    intro k'
    rw [Pnp.PPoly.initList_stk]
    by_cases hk : k' = tm.k₀
    · subst hk
      simp only [dite_true, sk_k₀]
      rw [hg0, hσf, update_self, he0, hdfr 0 (by unfold sW; omega) (by unfold sZ; omega)
        (by omega), hc0]
      simp only [FromTM2.enc, FromTM2.code, inputOf, List.map_append, List.map_cons, List.map_map,
        List.flatMap_append, List.flatMap_cons, List.flatMap_map, List.reverse_reverse,
        List.append_nil, hzs, List.map_reverse]
      rfl
    · simp only [hk, dite_false, FromTM2.enc, List.flatMap_nil]
      have hlt : 2 * k + 5 < sk tm (lay tm k) k' := o_lt_sk tm (lay tm k) hk
      set j := sk tm (lay tm k) k'
      rw [hgfr j (by omega) (by unfold sX; omega), hσf, update_of_ne (by omega),
        hefr j (by omega) (by unfold sZ; omega),
        hdfr j (by unfold sW; omega) (by unfold sZ; omega) (by omega), hcbig j (by omega)]
  obtain ⟨t4, σh, ht4, hR4⟩ := run_compiled tm (lay tm k) e₁ (hout x ys) σg hEnc
  have h5 := Reach.embed (V_P3 tm e₀ e₁ k) hR4
  rw [Nat.add_zero, Equiv.apply_symm_apply] at h5
  have hall := (hABC.trans h34).trans h5
  refine ⟨ys, _, hyl, hys, ?_, runFor_halt hall (V_fin tm e₀ e₁ k (f (x, ys)))⟩
  have hw : w.length = (ys.flatMap (cc tm e₀ k)).length := by rw [← hys, List.length_reverse]
  have hsep := cd_lt tm e₀ k (.inr none)
  simp only [hzs, List.length_map, List.length_reverse] at ht2
  simp only [List.length_reverse] at ht3
  rw [inputOf_length] at ht4
  simp only [bnd]
  omega

theorem cc_length_le (γ : Γ₁) : (cc tm e₀ k γ).length ≤ n0 tm k :=
  tu_length_le.trans (cd_lt tm e₀ k _)

theorem flatMap_cc_length_le (ys : List Γ₁) :
    (ys.flatMap (cc tm e₀ k)).length ≤ ys.length * n0 tm k := by
  induction ys with
  | nil => simp
  | cons γ ys ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := cc_length_le tm e₀ k γ
    rw [Nat.succ_mul]; omega

end Main

theorem Tpad_mono {m m' : ℕ} (h : m ≤ m') : ∀ d, Tpad m d ≤ Tpad m' d
  | 0 => le_rfl
  | d + 1 => by
    simp only [Tpad]
    have := Tpad_mono h d
    have := Nat.mul_le_mul h (Nat.add_le_add_right this 2)
    omega

end Pnp.Relativize.FromNP

namespace Pnp.Relativize.NPEquiv

theorem runFor_det {O : Oracle} {p : Prog} {s : State} {a a' : ℕ} {b b' : Bool}
    (h : runFor O p a s = .done b) (h' : runFor O p a' s = .done b') : b = b' := by
  rcases le_total a a' with hle | hle
  · rw [runFor_mono h hle] at h'; exact State.done.inj h'
  · rw [runFor_mono h' hle] at h; exact (State.done.inj h).symm

open Turing Function Polynomial Pnp.Relativize.Comb Pnp.Relativize.FromTM2 Pnp.Relativize.FromNP

/-- **Official `NP` ⊆ our `NP ∅`** (alphabet `Bool`). -/
theorem mem_NP_empty_of_inNP {L : Set Str}
    (h : Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Bool)
      (fun x => x ∈ L)) : L ∈ NP ∅ := by
  classical
  obtain ⟨Γ₁, hΓ, R, k, hR, hL⟩ := h
  obtain ⟨f, comp, hf⟩ := hR
  let tm := comp.tm
  let e₀ : tm.Γ tm.k₀ ≃ (Bool ⊕ Option Γ₁) := comp.inputAlphabet
  let e₁ : tm.Γ tm.k₁ ≃ Bool := comp.outputAlphabet
  have hout : ∀ (x : Str) (ys : List Γ₁), TM2OutputsInTime tm ((inputOf x ys).map e₀.symm)
      (some [e₁.symm (f (x, ys))]) (comp.time.eval (inputOf x ys).length) :=
    fun x ys => comp.outputsFun (x, ys)
  obtain ⟨c, d, hcd⟩ := OfficialP.eval_le comp.time
  -- constants
  set n := n0 tm k with hn
  set DB := Dm tm * B tm (lay tm k) with hDB
  set N₁ := N tm (lay tm k) tm.k₁ with hN₁
  let E := 3 * k + 1 + (k + 1) * d
  let M := 2 * n + (k + 3) + 1 + 2 * (2 * n + 2) + 3 * n + 2 + (n + 3) + 1 +
    c * 3 ^ d * DB + 1 + N₁ + 1 + 1 + 1
  let K := M + 0 + E
  refine ⟨V tm e₀ e₁ k, K, fun x => ?_⟩
  set X := x.length + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hP : ∀ a, a ≤ E → X ^ a ≤ X ^ E := fun a ha => Nat.pow_le_pow_right (by omega) ha
  have hP1 : 1 ≤ X ^ E := Nat.one_le_pow _ _ (by omega)
  have hxk : x.length ^ k ≤ X ^ E :=
    (Nat.pow_le_pow_left (by omega) k).trans (hP k (by omega))
  have hxX : x.length ≤ X ^ E := by
    have := hP 1 (by omega); rw [pow_one] at this; omega
  have hKb : M * X ^ E ≤ tb K x.length := by
    have := OfficialP.absorb M 0 E x.length
    simpa [tb, K] using this
  -- bound of a run on an honest certificate
  have hbnd : ∀ ys : List Γ₁, ys.length ≤ x.length ^ k →
      bnd tm e₀ k comp.time x ys ≤ M * X ^ E := by
    intro ys hy
    have hy' : ys.length ≤ X ^ E := hy.trans hxk
    have h1 := flatMap_cc_length_le tm e₀ k ys
    have h2 : Tpad x.length k ≤ X ^ E :=
      (Tpad_mono (by omega) k).trans ((Tpad_le hX2 k).trans (hP _ (by omega)))
    have h3 : comp.time.eval (x.length + 1 + ys.length) ≤ c * 3 ^ d * X ^ E := by
      refine (hcd _).trans ?_
      have hk1 : X ≤ X ^ (k + 1) := by
        calc X = X ^ 1 := (pow_one X).symm
          _ ≤ X ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hk2 : 1 ≤ X ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
      have hk3 : ys.length ≤ X ^ (k + 1) :=
        hy.trans ((Nat.pow_le_pow_left (by omega) k).trans
          (Nat.pow_le_pow_right (by omega) (by omega)))
      have hb : x.length + 1 + ys.length + 2 ≤ 3 * X ^ (k + 1) := by omega
      calc c * (x.length + 1 + ys.length + 2) ^ d ≤ c * (3 * X ^ (k + 1)) ^ d :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb d)
        _ = c * 3 ^ d * X ^ ((k + 1) * d) := by rw [mul_pow, ← pow_mul]; ring
        _ ≤ c * 3 ^ d * X ^ E := Nat.mul_le_mul_left _ (hP _ (by omega))
    have h4 := Nat.mul_le_mul_right DB h3
    have h5 : ys.length * n ≤ X ^ E * n := Nat.mul_le_mul_right _ hy'
    have h6 : ys.length * (2 * n + 2) ≤ X ^ E * (2 * n + 2) := Nat.mul_le_mul_right _ hy'
    have h7 : x.length * (k + 3) ≤ X ^ E * (k + 3) := Nat.mul_le_mul_right _ hxX
    have h8 : x.length * (n + 3) ≤ X ^ E * (n + 3) := Nat.mul_le_mul_right _ hxX
    have hnP : n ≤ n * X ^ E := Nat.le_mul_of_pos_right _ hP1
    have hNP : N₁ ≤ N₁ * X ^ E := Nat.le_mul_of_pos_right _ hP1
    have hFL : (ys.flatMap (cc tm e₀ k)).length ≤ X ^ E * n := h1.trans h5
    simp only [bnd]
    simp only [M]
    rw [← hn, ← hDB, ← hN₁]
    generalize X ^ E = P at *
    nlinarith [h1, h2, h4, h5, h6, h7, h8, hnP, hNP, hFL, hP1]
  constructor
  · -- completeness
    intro hx
    obtain ⟨ys, hyl, hRy⟩ := (hL x).1 hx
    have hfy : f (x, ys) = true := (hf (x, ys)).1 hRy
    refine ⟨(ys.flatMap (cc tm e₀ k)).reverse, ?_, ?_⟩
    · rw [List.length_reverse]
      have := flatMap_cc_length_le tm e₀ k ys
      have h5 : ys.length * n ≤ X ^ E * n := Nat.mul_le_mul_right _ (hyl.trans hxk)
      have h6 : X ^ E * n ≤ M * X ^ E := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by simp only [M]; omega)
      rw [← hn] at this
      exact le_trans (by omega) hKb
    · rcases outcome tm e₀ e₁ k hout x (ys.flatMap (cc tm e₀ k)).reverse with
        ⟨t, -, hno⟩ | ⟨ys', t, hyl', hys', htb, ht⟩
      · exact absurd ⟨ys, hyl, by rw [List.reverse_reverse]⟩ hno
      · rw [List.reverse_reverse] at hys'
        have := flatMap_cc_injective tm e₀ k hys'
        subst this
        rw [hfy] at ht
        exact runFor_mono ht ((htb.trans (hbnd ys hyl)).trans hKb)
  · -- soundness
    rintro ⟨w, -, hw⟩
    rcases outcome tm e₀ e₁ k hout x w with ⟨t, ht, -⟩ | ⟨ys, t, hyl, -, -, ht⟩
    · have := runFor_det hw ht
      exact absurd this (by simp)
    · have := runFor_det hw ht
      exact (hL x).2 ⟨ys, hyl, (hf (x, ys)).2 this.symm⟩

/-- Our `NP ∅` is exactly the official class `NP` over the alphabet `Bool`. -/
theorem mem_NP_empty_iff {L : Set Str} :
    L ∈ NP ∅ ↔
      Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Bool)
        (fun x => x ∈ L) :=
  ⟨OfficialNP.inNP_of_mem_NP_empty, mem_NP_empty_of_inNP⟩

/-- The official `P = NP` question over the alphabet `Bool` is exactly our `P ∅ = NP ∅`. -/
theorem official_P_eq_NP_bool_iff :
    (∀ p : List Bool → Prop,
      Millennium.InPolynomialTime (Millennium.fin_encoding_string Bool) p ↔
        Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string Bool) p) ↔
      (∀ L : Set Str, L ∈ P ∅ ↔ L ∈ NP ∅) := by
  constructor
  · intro h L
    rw [OfficialP.mem_P_empty_iff, mem_NP_empty_iff]
    exact h _
  · intro h p
    have := h {x | p x}
    rw [OfficialP.mem_P_empty_iff, mem_NP_empty_iff] at this
    exact this

end Pnp.Relativize.NPEquiv
