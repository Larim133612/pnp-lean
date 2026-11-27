import Pnp.KarpLipton.KarpLipton
import Pnp.KarpLipton.EvalCmd

/-!
# Karp–Lipton witnesses as dense circuit codes (M32d)

The mathematical half of the official `Π₂ᴾ ⊆ Σ₂ᴾ` collapse.  For the inner polynomial-time
predicate `L''` of a `Π₂ᴾ` language and every pair of lengths `(n, m)` we produce, under the
Karp–Lipton hypothesis `SmallExistentials T`, one **dense circuit code** `G` (the format of
`Pnp.Relativize.Struct.evalD`) of polynomial length such that for every `w` of length `n` and `b`
of length `m`: if `(w, b)` has a certificate of length `≤ N = q(|w#b|)`, then some prefix of
`decL N (evalD G (bits of oneHot (w#b)) [] false false).reverse` is one.

`decL N k bits` cuts the bit list into `N` blocks of `k = |γ|` bits and decodes each block by its
**first** `true` bit (`decSym`); this is the decoding a stack program can carry out.  The search
circuits of `Pnp.KarpLipton.search_circuit` only guarantee a certificate under the one-hot
decoding `decOH` (which uses choice on non-one-hot blocks), so the verifier is composed with the
local normalization `normZ` (first `true` bit ↦ exact one-hot block) before the search.

* `decL_ofFn`: `decL` on the bits of `z` is `decB N z`;
* `decB_oneHot`, `decWord_normZ`: honest blocks are unchanged, normalized blocks decode as `decB`;
* `hasMCircuitOfSize_normApp`: normalization is a local map;
* `dense_search`: the dense witness codes.
-/

namespace Pnp.KarpLipton

open Pnp.Circuits Pnp.PPoly Pnp.CookLevin Pnp.Relativize.Struct Classical

noncomputable section

/-! ## First-true decoding -/

/-- Position of the first `true` bit. -/
def firstIdx : List Bool → Option ℕ
  | [] => none
  | true :: _ => some 0
  | false :: l => (firstIdx l).map (· + 1)

theorem firstIdx_replicate (i : ℕ) (l : List Bool) :
    firstIdx (List.replicate i false ++ true :: l) = some i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, firstIdx, ih]

section Decode

variable {γ : Type} [Fintype γ] [Nonempty γ] [DecidableEq γ]

/-- Decode a block by its first `true` bit (a fixed default if there is none). -/
def decSym (bl : List Bool) : γ :=
  match firstIdx bl with
  | some j => if h : j < Fintype.card γ then (Fintype.equivFin γ).symm ⟨j, h⟩ else Classical.arbitrary γ
  | none => Classical.arbitrary γ

/-- Decode `N` blocks of `k` bits each from a bit list (missing bits read `false`). -/
def decL (N k : ℕ) (bits : List Bool) : List γ :=
  (List.range N).map fun t => decSym ((List.range k).map fun j => bits.getD (t * k + j) false)

/-- Decode the blocks of a certificate bit vector. -/
def decB (N : ℕ) (z : Fin (N * Fintype.card γ) → Bool) : List γ :=
  List.ofFn fun t : Fin N =>
    decSym (List.ofFn fun j : Fin (Fintype.card γ) => z (finProdFinEquiv (t, j)))

omit [DecidableEq γ] in
theorem length_decB (N : ℕ) (z : Fin (N * Fintype.card γ) → Bool) : (decB N z).length = N := by
  simp [decB]

theorem finProdFinEquiv_val {N k : ℕ} (t : Fin N) (j : Fin k) :
    (finProdFinEquiv (t, j)).val = t.val * k + j.val := by
  simp [finProdFinEquiv]; ring

omit [DecidableEq γ] in
theorem decL_ofFn (N : ℕ) (z : Fin (N * Fintype.card γ) → Bool) (rest : List Bool) :
    decL (γ := γ) N (Fintype.card γ) (List.ofFn z ++ rest) = decB N z := by
  rw [decL, decB]
  refine List.ext_getElem (by simp) fun t h₁ h₂ => ?_
  simp only [List.length_map, List.length_range] at h₁
  rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  congr 1
  refine List.ext_getElem (by simp) fun j g₁ g₂ => ?_
  simp only [List.length_map, List.length_range] at g₁
  rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  have hlt : t * Fintype.card γ + j < N * Fintype.card γ := by
    have : t * Fintype.card γ + j < (t + 1) * Fintype.card γ := by nlinarith
    exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ (by omega))
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hlt),
    List.getElem?_ofFn, dif_pos hlt, Option.getD_some]
  congr 1
  ext; simp; ring

omit [Nonempty γ] in
/-- The one-hot block of `g`. -/
theorem ofFn_oneHot_block (g : γ) :
    (List.ofFn fun j : Fin (Fintype.card γ) => decide (g = (Fintype.equivFin γ).symm j)) =
      List.replicate (Fintype.equivFin γ g) false ++
        true :: List.replicate (Fintype.card γ - 1 - Fintype.equivFin γ g) false := by
  have hg := (Fintype.equivFin γ g).isLt
  set e := Fintype.equivFin γ
  refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
  simp only [List.length_ofFn] at h₁
  rw [List.getElem_ofFn]
  have key : (g = e.symm ⟨j, h₁⟩) ↔ j = (e g).val := by
    rw [Equiv.eq_symm_apply]
    constructor
    · intro h; rw [h]
    · intro h; ext; exact h.symm
  by_cases hj : j < (e g).val
  · rw [List.getElem_append_left (by simpa using hj)]
    simp only [List.getElem_replicate, decide_eq_false_iff_not, key]
    omega
  · rw [List.getElem_append_right (by simpa using hj)]
    simp only [List.length_replicate]
    by_cases hj' : j = (e g).val
    · subst hj'
      simp
    · rw [List.getElem_cons, dif_neg (by omega)]
      simp only [List.getElem_replicate, decide_eq_false_iff_not, key]
      exact hj'

theorem decSym_block (g : γ) :
    decSym (List.ofFn fun j : Fin (Fintype.card γ) => decide (g = (Fintype.equivFin γ).symm j)) = g := by
  rw [ofFn_oneHot_block, decSym, firstIdx_replicate]
  simp

theorem decB_oneHot (N : ℕ) (y : List γ) (hy : y.length = N) : decB N (oneHot N y) = y := by
  subst hy
  refine List.ext_getElem (by simp [decB]) fun t h₁ h₂ => ?_
  simp only [decB, List.getElem_ofFn]
  have : (fun j : Fin (Fintype.card γ) => oneHot y.length y (finProdFinEquiv (⟨t, h₂⟩, j))) =
      fun j => decide (y[t] = (Fintype.equivFin γ).symm j) := by
    funext j
    simp [oneHot, List.getElem?_eq_getElem h₂]
  rw [this, decSym_block]

/-- Normalization of the certificate blocks: first `true` bit ↦ exact one-hot block. -/
def normZ (N : ℕ) (z : Fin (N * Fintype.card γ) → Bool) : Fin (N * Fintype.card γ) → Bool :=
  oneHot N (decB N z)

theorem decWord_normZ (N : ℕ) (z : Fin (N * Fintype.card γ) → Bool) :
    decWord N (normZ N z) = decB N z :=
  decWord_oneHot _ (length_decB N z)

theorem normZ_oneHot (N : ℕ) (y : List γ) (hy : y.length = N) :
    normZ N (oneHot N y) = oneHot N y := by
  rw [normZ, decB_oneHot N y hy]

theorem cert_normZ (N m : ℕ) (z : Fin (N * Fintype.card γ) → Bool) :
    cert γ N m (normZ N z) = (decB N z).take m := by
  unfold cert
  rw [dif_pos (inferInstance : Nonempty γ), decWord_normZ]

theorem normZ_congr (N : ℕ) (z z' : Fin (N * Fintype.card γ) → Bool) (o : Fin (N * Fintype.card γ))
    (h : ∀ d, z (finProdFinEquiv ((finProdFinEquiv.symm o).1, d)) =
      z' (finProdFinEquiv ((finProdFinEquiv.symm o).1, d))) :
    normZ N z o = normZ N z' o := by
  have hb : (decB N z)[(finProdFinEquiv.symm o).1.val]? =
      (decB N z')[(finProdFinEquiv.symm o).1.val]? := by
    simp only [decB, List.getElem?_ofFn, (finProdFinEquiv.symm o).1.isLt, dif_pos]
    simp only [Option.some.injEq]
    congr 1
    exact List.ofFn_inj.2 (funext h)
  simp only [normZ, oneHot, hb]

/-- Normalizing the certificate part of `x ++ z` is a local map. -/
theorem hasMCircuitOfSize_normApp (a N : ℕ) (hN : 0 < a + N * Fintype.card γ) :
    HasMCircuitOfSize (fun u : Fin (a + N * Fintype.card γ) → Bool =>
        Fin.append (fun i => u (Fin.castAdd _ i)) (normZ N fun j => u (Fin.natAdd a j)))
      ((a + N * Fintype.card γ) * juntaSize (Fintype.card (Fin (Fintype.card γ)))) := by
  let d0 : Fin (a + N * Fintype.card γ) := ⟨0, hN⟩
  let ι : Fin (a + N * Fintype.card γ) → Fin (Fintype.card γ) → Fin (a + N * Fintype.card γ) :=
    fun o d => if h : o.val < a then o else
      Fin.natAdd a (finProdFinEquiv ((finProdFinEquiv.symm
        (⟨o.val - a, by omega⟩ : Fin (N * Fintype.card γ))).1, d))
  refine hasMCircuitOfSize_dep hN _ ι fun o x y hxy => ?_
  by_cases h : o.val < a
  · have e : o = Fin.castAdd _ ⟨o.val, h⟩ := rfl
    rw [e, Fin.append_left, Fin.append_left]
    have := hxy ⟨0, Fintype.card_pos⟩
    simp only [ι, dif_pos h] at this
    exact this
  · have e : o = Fin.natAdd a (⟨o.val - a, by omega⟩ : Fin (N * Fintype.card γ)) := by
      ext; simp; omega
    rw [e, Fin.append_right, Fin.append_right]
    refine normZ_congr N _ _ _ fun d => ?_
    have := hxy d
    simp only [ι, dif_neg h] at this
    exact this

end Decode

/-- Reversing the outputs of a reversed circuit gives the natural order. -/
theorem reverse_map_range_rev (M : ℕ) (z : Fin M → Bool) :
    ((List.range M).map fun t => if h : t < M then z (Fin.rev ⟨t, h⟩) else false).reverse =
      List.ofFn z := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.length_ofFn] at h₂
  rw [List.getElem_reverse, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  simp only [List.length_map, List.length_range]
  rw [dif_pos (by omega)]
  congr 1
  ext; simp; omega

/-- **Dense Karp–Lipton witnesses.**  Under `SmallExistentials T`, for every pair of lengths
`(n, m)` there is one dense circuit code `G` of polynomial length such that, whenever `(w, b)`
has a certificate of length `≤ q(|w#b|)`, a prefix of the first-true decoding of the reversed
output of `evalD G` on the bits of `oneHot (w#b)` is one. -/
theorem dense_search {T : Polynomial ℕ} (hT : SmallExistentials T)
    {α β γ : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ] [Primcodable α] [Primcodable β] [Primcodable γ]
    (L'' : Millennium.Language ((List α × List β) × List γ))
    (hL'' : Millennium.InPolynomialTime
      (Millennium.pair_encoding (Millennium.pair_encoding (Millennium.fin_encoding_string α)
        (Millennium.fin_encoding_string β)) (Millennium.fin_encoding_string γ))
      (Millennium.complement L''))
    (q : Polynomial ℕ) :
    ∃ r : Polynomial ℕ, ∀ n m : ℕ, ∃ G : List Bool, G.length ≤ r.eval (n + m) ∧
      ∀ (w : List α) (b : List β), w.length = n → b.length = m →
        (∃ c : List γ, c.length ≤ q.eval (n + 1 + m) ∧ L'' ((w, b), c)) →
        ∃ m' ≤ q.eval (n + 1 + m), L'' ((w, b),
          (decL (γ := γ) (q.eval (n + 1 + m)) (Fintype.card γ)
            (evalD G (List.ofFn (oneHot (n + 1 + m) (pe2 w b))) [] false false).reverse).take m') := by
  have hR := nested_circuits L'' hL''
  obtain ⟨P, hP⟩ := verifier_circuits_on (fun x : List (α ⊕ Option β) => ∃ w b, x = pe2 w b)
    (fun x y => ∀ w b, x = pe2 w b → L'' ((w, b), y)) q hR
  have hd : 0 < Fintype.card (α ⊕ Option β) := Fintype.card_pos
  let cδ := Fintype.card (α ⊕ Option β)
  let k := Fintype.card γ
  let J := juntaSize (Fintype.card (Fin (Fintype.card γ)))
  let NP : Polynomial ℕ := Polynomial.X + 1
  let DP : Polynomial ℕ := NP * Polynomial.C cδ
  let ZP : Polynomial ℕ := q.comp NP * Polynomial.C k
  let VP : Polynomial ℕ := (DP + ZP) * Polynomial.C J + P.comp NP
  let FP : Polynomial ℕ := ZP * ((DP + ZP) * T.comp (DP + ZP + ZP + (VP + 1)))
  let r : Polynomial ℕ := (FP + ZP) * (3 * (DP + FP + ZP) + 5)
  refine ⟨r, fun n m => ?_⟩
  set n' := n + 1 + m with hn'
  have hn'0 : 0 < n' := by omega
  have hNq : nCert γ q n' = q.eval n' := by unfold nCert; rw [if_pos (inferInstance : Nonempty γ)]
  set N := nCert γ q n' with hN
  obtain ⟨f, hf, hfR⟩ := hP n' hn'0
  have hnorm := hasMCircuitOfSize_normApp (γ := γ) (n' * cδ) N
    (Nat.add_pos_left (Nat.mul_pos hn'0 hd) _)
  have hV := hnorm.comp_single hf
  obtain ⟨F, hF, hFs⟩ := search_circuit hT (Nat.mul_pos hn'0 hd) hV
  have hF' := hF.comp (hasMCircuitOfSize_rewire (n := N * k) (m := N * k) Fin.rev)
  obtain ⟨t, ht, C, hC⟩ := hF'
  refine ⟨mcDense C, ?_, fun w b hw hb hc => ?_⟩
  · -- the length bound
    have hlen := length_mcDense_le C
    have e1 : n' = n + m + 1 := by omega
    have hZ : N * k = ZP.eval (n + m) := by
      simp only [ZP, NP, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      rw [hNq, e1]
    have hD : n' * cδ = DP.eval (n + m) := by
      simp only [DP, NP, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_one]
      rw [e1]
    have hPn : P.eval n' = (P.comp NP).eval (n + m) := by
      simp only [NP, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one]
      rw [e1]
    have htF : t ≤ FP.eval (n + m) := by
      refine ht.trans (le_of_eq ?_)
      simp only [FP, VP, ZP, DP, NP, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_X]
      rw [← e1, ← hNq]
      simp only [Nat.add_zero, cδ, k, J]
    simp only [r, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat]
    refine hlen.trans ?_
    rw [hZ, hD]
    gcongr
  · -- correctness
    have hlx : (pe2 w b).length = n' := by rw [length_pe2, hw, hb]
    have hSx : ∃ w' b', pe2 w b = pe2 w' b' := ⟨w, b, rfl⟩
    set xo := oneHot n' (pe2 w b) with hxo
    -- an honest certificate
    obtain ⟨c, hcl, hcL⟩ := hc
    rw [← hNq] at hcl
    let d : γ := Classical.arbitrary γ
    let y' : List γ := c ++ List.replicate (N - c.length) d
    have hy' : y'.length = N := by simp [y']; omega
    have hzV : (f ∘ fun u : Fin (n' * cδ + N * k) → Bool =>
        Fin.append (fun i => u (Fin.castAdd _ i)) (normZ N fun j => u (Fin.natAdd (n' * cδ) j)))
        (Fin.append xo (oneHot N y')) = true := by
      simp only [Function.comp, Fin.append_left, Fin.append_right]
      rw [normZ_oneHot N y' hy']
      refine (hfR (pe2 w b) hSx hlx _).2 ⟨c.length, hcl, fun w' b' e => ?_⟩
      obtain ⟨rfl, rfl⟩ := pe2_injective e
      unfold cert
      rw [dif_pos (inferInstance : Nonempty γ), decWord_oneHot y' hy']
      simpa [y'] using hcL
    have hout := hFs xo ⟨_, hzV⟩
    simp only [Function.comp, Fin.append_left] at hout
    obtain ⟨m', hm', hR'⟩ := (hfR (pe2 w b) hSx hlx _).1 hout
    refine ⟨m', hNq ▸ hm', ?_⟩
    have hev := evalD_mcDense C (Nat.mul_pos hn'0 hd) xo
    rw [hev, List.reverse_append]
    have hCe : ∀ (j : ℕ) (h : j < N * k), C.eval xo ⟨j, h⟩ = F xo (Fin.rev ⟨j, h⟩) := by
      intro j h; rw [hC]; rfl
    simp only [hCe]
    rw [reverse_map_range_rev, ← hNq, decL_ofFn, ← cert_normZ]
    have er : (fun j => Fin.append xo (F xo) (Fin.natAdd (n' * cδ) j)) = F xo :=
      funext fun j => Fin.append_right _ _ _
    have := hR' w b rfl
    rw [er] at this
    exact this

end

end Pnp.KarpLipton
