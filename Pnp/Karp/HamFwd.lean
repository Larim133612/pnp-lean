import Pnp.Karp.Ham

/-!
# SAT ≤ HAMILTONIAN CYCLE: the forward direction

From a satisfying assignment of `w` we build a directed Hamiltonian cycle of `DA w` (rows are
traversed left to right for true variables, right to left for false ones, and each clause
vertex is visited in a detour from the row of a chosen true literal), and then split it into a
Hamiltonian cycle of `H w`.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Generic lemmas -/

/-- A list covering `[0, n)` with length at most `n` is a permutation of `[0, n)`. -/
theorem hf_perm_range {l : List ℕ} {n : ℕ} (hmem : ∀ x < n, x ∈ l) (hlen : l.length ≤ n) :
    l.Perm (List.range n) :=
  (((List.nodup_range).subperm (fun x hx => hmem x (List.mem_range.1 hx))).perm_of_length_le
    (by simpa using hlen)).symm

/-- A Hamiltonian cycle from a permutation whose cyclic closure is a chain. -/
theorem hf_ham_of_chain {n : ℕ} {adj : ℕ → ℕ → Prop} {σ : List ℕ} (hp : σ.Perm (List.range n))
    (hc : (σ ++ σ.take 1).IsChain adj) : IsHamCycle n adj σ := by
  refine ⟨hp, fun i hi => ?_⟩
  have hlen : (σ ++ σ.take 1).length = σ.length + 1 := by
    simp; omega
  have h := List.isChain_iff_getElem.1 hc i (by omega)
  rw [List.getElem_append_left hi] at h
  rcases Nat.lt_or_ge (i + 1) σ.length with h1 | h1
  · rw [List.getElem_append_left h1] at h
    rw [Nat.mod_eq_of_lt h1]
    simpa [List.getD_eq_getElem?_getD, hi, h1] using h
  · have he : i + 1 = σ.length := by omega
    rw [he, Nat.mod_self]
    have h0 : 0 < σ.length := by omega
    rw [List.getElem_append_right (by omega)] at h
    simpa [List.getD_eq_getElem?_getD, hi, h0, he] using h

/-- Chains through consecutive blocks `g j :: rest j`, closed by `ys`. -/
theorem hf_chain_blocks {R : ℕ → ℕ → Prop} (g : ℕ → ℕ) (rest : ℕ → List ℕ) (ys : List ℕ) :
    ∀ n a, (∀ j, a ≤ j → j < a + n → (g j :: rest j ++ [g (j + 1)]).IsChain R) →
      (g (a + n) :: ys).IsChain R →
      (g a :: ((List.range' a n).flatMap (fun j => rest j ++ [g (j + 1)])) ++ ys).IsChain R
  | 0, a, _, hy => by simpa using hy
  | n + 1, a, hb, hy => by
    have ih := hf_chain_blocks g rest ys n (a + 1)
      (fun j h1 h2 => hb j (by omega) (by omega)) (by rw [show a + 1 + n = a + (n + 1) by omega]; exact hy)
    have e : g a :: ((List.range' a (n + 1)).flatMap (fun j => rest j ++ [g (j + 1)])) ++ ys =
        (g a :: rest a) ++ [g (a + 1)] ++
          (((List.range' (a + 1) n).flatMap (fun j => rest j ++ [g (j + 1)])) ++ ys) := by
      simp [List.range'_succ]
    rw [e]
    exact List.IsChain.append_overlap (by simpa using hb a le_rfl (by omega))
      (by simpa using ih) (by simp)

/-! ## Splitting -/

/-- The three split vertices of `x`. -/
def hf_trip (x : ℕ) : List ℕ := [3 * x, 3 * x + 1, 3 * x + 2]

theorem hf_chain_split_aux {V : ℕ} {A : ℕ → ℕ → Prop} : ∀ (l : List ℕ) (x : ℕ), x < V →
    (∀ z ∈ l, z < V) → (x :: l).IsChain A → ((x :: l).flatMap hf_trip).IsChain (SplitAdj V A)
  | [], x, hx, _, _ => by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hf_trip]
    exact .cons_cons (Or.inl ⟨x, hx, Or.inl ⟨rfl, rfl⟩⟩)
      (.cons_cons (Or.inl ⟨x, hx, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩) (.singleton _))
  | y :: l, x, hx, hl, hc => by
    rw [List.isChain_cons_cons] at hc
    have ih := hf_chain_split_aux l y (hl y (by simp)) (fun z hz => hl z (by simp [hz])) hc.2
    simp only [List.flatMap_cons, hf_trip, List.cons_append, List.nil_append] at ih ⊢
    exact .cons_cons (Or.inl ⟨x, hx, Or.inl ⟨rfl, rfl⟩⟩)
      (.cons_cons (Or.inl ⟨x, hx, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)
        (.cons_cons (Or.inr ⟨x, y, hc.1, Or.inl ⟨rfl, rfl⟩⟩) ih))

/-- **Splitting a directed Hamiltonian cycle** gives an undirected one of the split. -/
theorem hf_split {V : ℕ} {A : ℕ → ℕ → Prop} {τ : List ℕ} (hp : τ.Perm (List.range V))
    (hc : (τ ++ τ.take 1).IsChain A) :
    IsHamCycle (3 * V) (SplitAdj V A) (τ.flatMap hf_trip) := by
  have hlt : ∀ z ∈ τ, z < V := fun z hz => List.mem_range.1 (hp.subset hz)
  refine hf_ham_of_chain (hf_perm_range (fun x hx => ?_) ?_) ?_
  · have : x / 3 ∈ τ := hp.symm.subset (List.mem_range.2 (by omega))
    exact List.mem_flatMap.2 ⟨x / 3, this, by simp [hf_trip]; omega⟩
  · simp [List.length_flatMap, hf_trip, hp.length_eq]; omega
  · cases τ with
    | nil => simp
    | cons x τ' =>
      have h := hf_chain_split_aux (τ' ++ [x]) x (hlt x (by simp))
        (fun z hz => by
          rcases List.mem_append.1 hz with hz | hz
          · exact hlt z (by simp [hz])
          · exact hlt z (by simp at hz; simp [hz]))
        (by simpa using hc)
      refine h.prefix ⟨[3 * x + 1, 3 * x + 2], ?_⟩
      simp [hf_trip]

/-! ## The directed cycle -/

/-- The row vertex `(j, t)`. -/
def hf_v (w : List SatSym) (j t : ℕ) : ℕ := mC w + j * RW (mC w) + t

theorem hf_RW (m : ℕ) : RW m = 3 * m + 4 := rfl

theorem hf_arc_d1 (w : List SatSym) {j t : ℕ} (hj : j < NV w) (ht : t < RW (mC w)) :
    DA w (hf_v w j t) (hf_v w j (d1 t)) := Or.inl ⟨j, hj, t, ht, rfl, Or.inl rfl⟩

theorem hf_arc_d2 (w : List SatSym) {j t : ℕ} (hj : j < NV w) (ht : t < RW (mC w)) :
    DA w (hf_v w j t) (hf_v w j (d2 (RW (mC w)) t)) := Or.inl ⟨j, hj, t, ht, rfl, Or.inr rfl⟩

theorem hf_arc_up (w : List SatSym) {j t : ℕ} (hj : j < NV w) (h2 : 2 ≤ t)
    (ht : t + 1 < RW (mC w)) : DA w (hf_v w j t) (hf_v w j (t + 1)) := by
  have e : d2 (RW (mC w)) t = t + 1 := by unfold d2; split_ifs <;> omega
  simpa [e] using hf_arc_d2 w hj (t := t) (by omega)

theorem hf_arc_down (w : List SatSym) {j t : ℕ} (hj : j < NV w) (h1 : 1 ≤ t)
    (ht : t + 1 < RW (mC w)) : DA w (hf_v w j (t + 1)) (hf_v w j t) := by
  have e : d1 (t + 1) = t := by unfold d1; rw [if_neg (by omega), if_neg (by omega)]; omega
  simpa [e] using hf_arc_d1 w hj (t := t + 1) ht

theorem hf_arc_hubL (w : List SatSym) {j : ℕ} (hj : j < NV w) :
    DA w (hf_v w j 0) (hf_v w j 1) := by
  simpa [d1] using hf_arc_d1 w hj (t := 0) (by rw [hf_RW]; omega)

theorem hf_arc_hubR (w : List SatSym) {j : ℕ} (hj : j < NV w) :
    DA w (hf_v w j 0) (hf_v w j (RW (mC w) - 1)) := by
  simpa [d2] using hf_arc_d2 w hj (t := 0) (by rw [hf_RW]; omega)

theorem hf_v_next (w : List SatSym) (j : ℕ) :
    hf_v w j (RW (mC w)) = hf_v w (j + 1) 0 := by
  unfold hf_v; ring

theorem hf_arc_endL (w : List SatSym) {j : ℕ} (hj : j < NV w) :
    DA w (hf_v w j 1) (hf_v w (j + 1) 0) := by
  have e : d2 (RW (mC w)) 1 = RW (mC w) := by unfold d2; simp
  rw [← hf_v_next, ← e]
  exact hf_arc_d2 w hj (by rw [hf_RW]; omega)

theorem hf_arc_endR (w : List SatSym) {j : ℕ} (hj : j < NV w) :
    DA w (hf_v w j (RW (mC w) - 1)) (hf_v w (j + 1) 0) := by
  have e : d2 (RW (mC w)) (RW (mC w) - 1) = RW (mC w) := by
    unfold d2; rw [hf_RW]; split_ifs <;> omega
  have h := hf_arc_d2 w hj (t := RW (mC w) - 1) (by rw [hf_RW]; omega)
  rwa [e, hf_v_next] at h

theorem hf_arc_Z (w : List SatSym) : DA w (hf_v w (NV w) 0) (hf_v w 0 0) :=
  Or.inr (Or.inl ⟨by simp [hf_v], by simp [hf_v]⟩)

theorem hf_arc_pos (w : List SatSym) {j k : ℕ} (hj : j < NV w) (hk : k < mC w)
    (h : sy w k j = pos) :
    DA w (hf_v w j (3 + 3 * k)) k ∧ DA w k (hf_v w j (4 + 3 * k)) :=
  ⟨Or.inr (Or.inr (Or.inl ⟨k, hk, j, hj, h, Or.inl ⟨by simp only [hf_v]; omega, rfl⟩⟩)),
    Or.inr (Or.inr (Or.inl ⟨k, hk, j, hj, h, Or.inr ⟨rfl, by simp only [hf_v]; omega⟩⟩))⟩

theorem hf_arc_neg (w : List SatSym) {j k : ℕ} (hj : j < NV w) (hk : k < mC w)
    (h : sy w k j = neg) :
    DA w (hf_v w j (4 + 3 * k)) k ∧ DA w k (hf_v w j (3 + 3 * k)) :=
  ⟨Or.inr (Or.inr (Or.inr ⟨k, hk, j, hj, h, Or.inl ⟨by simp only [hf_v]; omega, rfl⟩⟩)),
    Or.inr (Or.inr (Or.inr ⟨k, hk, j, hj, h, Or.inr ⟨rfl, by simp only [hf_v]; omega⟩⟩))⟩

/-! ### The cycle -/

/-- The detour to clause `k` from row `j` (if `j` is the witness of `k`). -/
def hf_det (wit : ℕ → ℕ) (j k : ℕ) : List ℕ := if wit k = j then [k] else []

/-- The pair of clause `k` in a left-to-right row. -/
def hf_blkT (w : List SatSym) (wit : ℕ → ℕ) (j k : ℕ) : List ℕ :=
  hf_v w j (3 + 3 * k) :: hf_det wit j k ++ [hf_v w j (4 + 3 * k)]

/-- The pair of clause `m - 1 - i` in a right-to-left row. -/
def hf_blkF (w : List SatSym) (wit : ℕ → ℕ) (j i : ℕ) : List ℕ :=
  hf_v w j (4 + 3 * (mC w - 1 - i)) :: hf_det wit j (mC w - 1 - i) ++
    [hf_v w j (3 + 3 * (mC w - 1 - i))]

/-- Separators, left to right. -/
def hf_sT (w : List SatSym) (j k : ℕ) : ℕ := hf_v w j (2 + 3 * k)

/-- Separators, right to left. -/
def hf_sF (w : List SatSym) (j i : ℕ) : ℕ := hf_v w j (2 + 3 * (mC w - i))

/-- The row `j` after its hub. -/
def hf_rest (w : List SatSym) (a : ℕ → Bool) (wit : ℕ → ℕ) (j : ℕ) : List ℕ :=
  if a j then
    hf_v w j 1 :: (hf_sT w j 0 ::
      (List.range (mC w)).flatMap (fun k => hf_blkT w wit j k ++ [hf_sT w j (k + 1)])) ++
      [hf_v w j (RW (mC w) - 1)]
  else
    hf_v w j (RW (mC w) - 1) :: (hf_sF w j 0 ::
      (List.range (mC w)).flatMap (fun i => hf_blkF w wit j i ++ [hf_sF w j (i + 1)])) ++
      [hf_v w j 1]

/-- The directed Hamiltonian cycle. -/
def hf_tau (w : List SatSym) (a : ℕ → Bool) (wit : ℕ → ℕ) : List ℕ :=
  hf_v w 0 0 :: (List.range (NV w)).flatMap (fun j => hf_rest w a wit j ++ [hf_v w (j + 1) 0])

section Cycle

variable (w : List SatSym) (a : ℕ → Bool) (wit : ℕ → ℕ)
  (hwit : ∀ k < mC w, wit k < NV w ∧ litTrue a (wit k) (sy w k (wit k)))

include hwit in
theorem hf_wit_pos {k : ℕ} (hk : k < mC w) (ha : a (wit k) = true) : sy w k (wit k) = pos := by
  have h := (hwit k hk).2
  revert h; cases sy w k (wit k) <;> simp [litTrue, ha]

include hwit in
theorem hf_wit_neg {k : ℕ} (hk : k < mC w) (ha : a (wit k) = false) :
    sy w k (wit k) = neg := by
  have h := (hwit k hk).2
  revert h; cases sy w k (wit k) <;> simp [litTrue, ha]

include hwit in
theorem hf_chain_blkT {j k : ℕ} (hj : j < NV w) (hk : k < mC w) (ha : a j = true) :
    (hf_sT w j k :: hf_blkT w wit j k ++ [hf_sT w j (k + 1)]).IsChain (DA w) := by
  have hR := hf_RW (mC w)
  have e1 : hf_sT w j (k + 1) = hf_v w j ((4 + 3 * k) + 1) := by
    unfold hf_sT; congr 1; omega
  have hs : (hf_sT w j k) = hf_v w j (2 + 3 * k) := rfl
  have up1 := hf_arc_up w hj (t := 2 + 3 * k) (by omega) (by omega)
  have up2 := hf_arc_up w hj (t := 3 + 3 * k) (by omega) (by omega)
  have up3 := hf_arc_up w hj (t := 4 + 3 * k) (by omega) (by omega)
  rw [show 2 + 3 * k + 1 = 3 + 3 * k by omega] at up1
  rw [show 3 + 3 * k + 1 = 4 + 3 * k by omega] at up2
  rw [hs, e1]
  unfold hf_blkT hf_det
  split_ifs with hw
  · subst hw
    have hp := hf_arc_pos w hj hk (hf_wit_pos w a wit hwit hk ha)
    simp only [List.cons_append, List.nil_append]
    exact .cons_cons up1 (.cons_cons hp.1 (.cons_cons hp.2 (.cons_cons up3 (.singleton _))))
  · simp only [List.cons_append, List.nil_append]
    exact .cons_cons up1 (.cons_cons up2 (.cons_cons up3 (.singleton _)))

include hwit in
theorem hf_chain_blkF {j i : ℕ} (hj : j < NV w) (hi : i < mC w) (ha : a j = false) :
    (hf_sF w j i :: hf_blkF w wit j i ++ [hf_sF w j (i + 1)]).IsChain (DA w) := by
  have hR := hf_RW (mC w)
  set k := mC w - 1 - i with hk'
  have hk : k < mC w := by omega
  have e0 : hf_sF w j i = hf_v w j ((4 + 3 * k) + 1) := by
    unfold hf_sF; congr 1; omega
  have e1 : hf_sF w j (i + 1) = hf_v w j (2 + 3 * k) := by
    unfold hf_sF; congr 1; omega
  have d1 := hf_arc_down w hj (t := 4 + 3 * k) (by omega) (by omega)
  have d2 := hf_arc_down w hj (t := 3 + 3 * k) (by omega) (by omega)
  have d3 := hf_arc_down w hj (t := 2 + 3 * k) (by omega) (by omega)
  rw [show 3 + 3 * k + 1 = 4 + 3 * k by omega] at d2
  rw [show 2 + 3 * k + 1 = 3 + 3 * k by omega] at d3
  rw [e0, e1]
  unfold hf_blkF hf_det
  rw [← hk']
  split_ifs with hw
  · subst hw
    have hp := hf_arc_neg w hj hk (hf_wit_neg w a wit hwit hk ha)
    simp only [List.cons_append, List.nil_append]
    exact .cons_cons d1 (.cons_cons hp.1 (.cons_cons hp.2 (.cons_cons d3 (.singleton _))))
  · simp only [List.cons_append, List.nil_append]
    exact .cons_cons d1 (.cons_cons d2 (.cons_cons d3 (.singleton _)))

include hwit in
theorem hf_chain_row {j : ℕ} (hj : j < NV w) :
    (hf_v w j 0 :: hf_rest w a wit j ++ [hf_v w (j + 1) 0]).IsChain (DA w) := by
  have hR := hf_RW (mC w)
  unfold hf_rest
  split_ifs with ha
  · have hin := hf_chain_blocks (R := DA w) (hf_sT w j) (hf_blkT w wit j)
      [hf_v w j (RW (mC w) - 1), hf_v w (j + 1) 0] (mC w) 0
      (fun k _ hk => hf_chain_blkT w a wit hwit hj (by omega) ha)
      (by
        have e : hf_sT w j (0 + mC w) = hf_v w j (RW (mC w) - 2) := by
          unfold hf_sT; congr 1; omega
        have u := hf_arc_up w hj (t := RW (mC w) - 2) (by omega) (by omega)
        rw [show RW (mC w) - 2 + 1 = RW (mC w) - 1 by omega] at u
        rw [e]
        exact .cons_cons u (.cons_cons (hf_arc_endR w hj) (.singleton _)))
    rw [← List.range_eq_range'] at hin
    have e2 : hf_sT w j 0 = hf_v w j (1 + 1) := rfl
    simp only [List.cons_append, List.append_assoc] at hin ⊢
    refine .cons_cons (hf_arc_hubL w hj) (.cons_cons ?_ hin)
    have e : d1 1 = 1 + 1 := rfl
    rw [e2, ← e]; exact hf_arc_d1 w hj (by omega)
  · have ha' : a j = false := by simpa using ha
    have hin := hf_chain_blocks (R := DA w) (hf_sF w j) (hf_blkF w wit j)
      [hf_v w j 1, hf_v w (j + 1) 0] (mC w) 0
      (fun k _ hk => hf_chain_blkF w a wit hwit hj (by omega) ha')
      (by
        have e : hf_sF w j (0 + mC w) = hf_v w j (1 + 1) := by
          unfold hf_sF; congr 1; omega
        rw [e]
        exact .cons_cons (hf_arc_down w hj (t := 1) le_rfl (by omega))
          (.cons_cons (hf_arc_endL w hj) (.singleton _)))
    rw [← List.range_eq_range'] at hin
    have e2 : hf_sF w j 0 = hf_v w j ((RW (mC w) - 2)) := by
      unfold hf_sF; congr 1; omega
    have dn := hf_arc_down w hj (t := RW (mC w) - 2) (by omega) (by omega)
    rw [show RW (mC w) - 2 + 1 = RW (mC w) - 1 by omega] at dn
    simp only [List.cons_append, List.append_assoc] at hin ⊢
    refine .cons_cons (hf_arc_hubR w hj) (.cons_cons ?_ hin)
    rw [e2]; exact dn

include hwit in
theorem hf_chain_tau :
    (hf_tau w a wit ++ (hf_tau w a wit).take 1).IsChain (DA w) := by
  have h := hf_chain_blocks (R := DA w) (fun j => hf_v w j 0) (hf_rest w a wit)
    [hf_v w 0 0] (NV w) 0 (fun j _ hj => hf_chain_row w a wit hwit (by omega))
    (by simpa using List.IsChain.cons_cons (hf_arc_Z w) (.singleton _))
  rw [← List.range_eq_range'] at h
  simpa [hf_tau] using h

/-! ### Counting -/

theorem hf_len_flatMap_range (f : ℕ → List ℕ) (n : ℕ) :
    ((List.range n).flatMap f).length = ∑ i ∈ Finset.range n, (f i).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, Finset.sum_range_succ]
    simp

theorem hf_len_det (j k : ℕ) : (hf_det wit j k).length = if wit k = j then 1 else 0 := by
  unfold hf_det; split_ifs <;> rfl

theorem hf_len_rest (j : ℕ) : (hf_rest w a wit j).length =
    3 + 3 * mC w + ∑ k ∈ Finset.range (mC w), (if wit k = j then 1 else 0) := by
  unfold hf_rest
  split_ifs
  · simp only [List.length_cons, List.length_append, hf_len_flatMap_range, hf_blkT,
      hf_len_det, List.length_nil, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
    ring
  · simp only [List.length_cons, List.length_append, hf_len_flatMap_range, hf_blkF,
      hf_len_det, List.length_nil, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, smul_eq_mul]
    rw [Finset.sum_range_reflect (fun k => if wit k = j then 1 else 0) (mC w)]
    ring

include hwit in
theorem hf_len_tau : (hf_tau w a wit).length = VV w := by
  have hs : ∑ j ∈ Finset.range (NV w), ∑ k ∈ Finset.range (mC w),
      (if wit k = j then 1 else 0) = mC w := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (g := fun _ => 1) (fun k hk => by
      rw [Finset.sum_ite_eq]
      simp [(hwit k (Finset.mem_range.1 hk)).1])]
    simp
  simp only [hf_tau, List.length_cons, hf_len_flatMap_range, List.length_append, hf_len_rest,
    List.length_nil, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, hs, VV, hf_RW]
  ring

/-! ### Covering -/

theorem hf_mem_tau_rest {j x : ℕ} (hj : j < NV w) (hx : x ∈ hf_rest w a wit j) :
    x ∈ hf_tau w a wit :=
  List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_append_left _ hx⟩)

theorem hf_mem_tau_hub {j : ℕ} (hj : j ≤ NV w) : hf_v w j 0 ∈ hf_tau w a wit := by
  rcases j with _ | j
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 (by omega),
      List.mem_append_right _ (List.mem_singleton_self _)⟩)

theorem hf_mem_rest {j t : ℕ} (h1 : 1 ≤ t) (ht : t < RW (mC w)) :
    hf_v w j t ∈ hf_rest w a wit j := by
  have hR := hf_RW (mC w)
  unfold hf_rest
  rcases (by omega : t = 1 ∨ t = RW (mC w) - 1 ∨ 2 ≤ t ∧ t ≤ RW (mC w) - 2) with
    rfl | rfl | ⟨h2, h3⟩
  · split_ifs <;> simp
  · split_ifs <;> simp
  obtain ⟨q, hq⟩ : ∃ q, (t = 2 + 3 * q ∧ q ≤ mC w) ∨ (t = 3 + 3 * q ∧ q < mC w) ∨
      (t = 4 + 3 * q ∧ q < mC w) := ⟨(t - 2) / 3, by omega⟩
  split_ifs
  · refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
    rcases hq with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩
    · rcases q with _ | q
      · simp [hf_sT]
      · refine List.mem_cons_of_mem _
          (List.mem_flatMap.2 ⟨q, List.mem_range.2 (by omega), ?_⟩)
        simp [hf_sT]
    · refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨q, List.mem_range.2 hq, ?_⟩)
      simp [hf_blkT]
    · refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨q, List.mem_range.2 hq, ?_⟩)
      simp [hf_blkT]
  · refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
    rcases hq with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩
    · by_cases hqm : q = mC w
      · have e : hf_v w j (2 + 3 * q) = hf_sF w j 0 := by unfold hf_sF; congr 1; omega
        rw [e]; exact List.mem_cons_self ..
      · have e : hf_v w j (2 + 3 * q) = hf_sF w j (mC w - q - 1 + 1) := by
          unfold hf_sF; congr 1; omega
        rw [e]
        refine List.mem_cons_of_mem _
          (List.mem_flatMap.2 ⟨mC w - q - 1, List.mem_range.2 (by omega), ?_⟩)
        simp
    · have e : hf_v w j (3 + 3 * q) = hf_v w j (3 + 3 * (mC w - 1 - (mC w - 1 - q))) := by
        congr 2; omega
      rw [e]
      refine List.mem_cons_of_mem _
        (List.mem_flatMap.2 ⟨mC w - 1 - q, List.mem_range.2 (by omega), ?_⟩)
      simp [hf_blkF]
    · have e : hf_v w j (4 + 3 * q) = hf_v w j (4 + 3 * (mC w - 1 - (mC w - 1 - q))) := by
        congr 2; omega
      rw [e]
      refine List.mem_cons_of_mem _
        (List.mem_flatMap.2 ⟨mC w - 1 - q, List.mem_range.2 (by omega), ?_⟩)
      simp [hf_blkF]

theorem hf_mem_rest_clause {k : ℕ} (hk : k < mC w) : k ∈ hf_rest w a wit (wit k) := by
  unfold hf_rest
  split_ifs
  · refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩)))
    simp [hf_blkT, hf_det]
  · refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_flatMap.2 ⟨mC w - 1 - k, List.mem_range.2 (by omega), ?_⟩)))
    have e : mC w - 1 - (mC w - 1 - k) = k := by omega
    simp [hf_blkF, hf_det, e]

include hwit in
theorem hf_mem_tau {x : ℕ} (hx : x < VV w) : x ∈ hf_tau w a wit := by
  have hR := hf_RW (mC w)
  unfold VV at hx
  by_cases h1 : x < mC w
  · exact hf_mem_tau_rest w a wit (hwit x h1).1 (hf_mem_rest_clause w a wit h1)
  by_cases h2 : x = mC w + NV w * RW (mC w)
  · have := hf_mem_tau_hub w a wit (j := NV w) le_rfl
    simpa [hf_v, h2] using this
  have hj : (x - mC w) / RW (mC w) < NV w := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  have hd := Nat.div_add_mod (x - mC w) (RW (mC w))
  have hlt := Nat.mod_lt (x - mC w) (show RW (mC w) > 0 by omega)
  have e : x = hf_v w ((x - mC w) / RW (mC w)) ((x - mC w) % RW (mC w)) := by
    unfold hf_v; rw [Nat.mul_comm ((x - mC w) / RW (mC w))]; omega
  rw [e]
  by_cases ht : (x - mC w) % RW (mC w) = 0
  · rw [ht]; exact hf_mem_tau_hub w a wit hj.le
  · exact hf_mem_tau_rest w a wit hj (hf_mem_rest w a wit (by omega) hlt)

include hwit in
theorem hf_perm_tau : (hf_tau w a wit).Perm (List.range (VV w)) :=
  hf_perm_range (fun _ hx => hf_mem_tau w a wit hwit hx) (hf_len_tau w a wit hwit).le

end Cycle

/-! ## The forward direction -/

theorem hf_len_clause_lt (w : List SatSym) {c : List SatSym} (hc : c ∈ clauses w) :
    c.length < NV w := by
  have h : List.Sublist (c ++ [sep]) (trunc w) := by
    unfold trunc
    rw [List.flatMap_def]
    exact List.sublist_flatten_of_mem (List.mem_map.2 ⟨c, hc, rfl⟩)
  have := h.length_le
  simp at this
  unfold NV; omega

/-- **SAT ≤ HAMILTONIAN CYCLE, forward direction.** -/
theorem ham_of_sat (w : List SatSym) (h : SATLang w) : UHamLang (H w) := by
  obtain ⟨a, ha⟩ := (clauses_sat_iff w).1 h
  have hex : ∀ k, ∃ j, k < mC w → j < NV w ∧ litTrue a j (sy w k j) := by
    intro k
    by_cases hk : k < mC w
    · have hc : (clauses w).getD k [] ∈ clauses w := by
        rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
      obtain ⟨j, hj, hl⟩ := ha _ hc
      exact ⟨j, fun _ => ⟨lt_trans hj (hf_len_clause_lt w hc), hl⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose wit hwit using hex
  have hwit' : ∀ k < mC w, wit k < NV w ∧ litTrue a (wit k) (sy w k (wit k)) :=
    fun k hk => hwit k hk
  have hadj : adjU (H w) = SplitAdj (VV w) (DA w) :=
    funext fun u => funext fun v => propext (adj_H_iff w u v)
  refine ⟨?_, (hf_tau w a wit).flatMap hf_trip, ?_⟩
  · rw [clauses_H, length_hRows]; unfold VV; omega
  · rw [clauses_H, length_hRows, hadj]
    exact hf_split (hf_perm_tau w a wit hwit') (hf_chain_tau w a wit hwit')

end Pnp.Karp.Ham
