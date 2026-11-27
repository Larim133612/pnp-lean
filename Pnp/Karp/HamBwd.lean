import Pnp.Karp.Ham

/-!
# HAMILTONIAN CYCLE: the backward direction of the reduction

`sat_of_ham`: if `H w` has a Hamiltonian cycle, then the formula `w` is satisfiable.

* **A.** Generic facts about a Hamiltonian cycle `σ`: every vertex has exactly two distinct
  cycle-neighbours (`hb_two`), and a nonempty set of vertices closed under cycle-neighbours
  contains every vertex (`hb_closed`).
* **B.** For the split of a directed graph, a Hamiltonian cycle induces a cover by directed
  cycles of length `≥ 3`: a successor `D` and a predecessor `P` (`hb_cover_of_ham`).
* **C.** For `DA w`, such a cover runs through every row in one direction, and every clause
  vertex is entered from a row whose direction makes a literal of the clause true.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## A. Hamiltonian cycles -/

/-- `u` and `v` are consecutive (in some order) along the cycle `σ`. -/
def hb_CN (σ : List ℕ) (u v : ℕ) : Prop :=
  ∃ i < σ.length, (σ.getD i 0 = u ∧ σ.getD ((i + 1) % σ.length) 0 = v) ∨
    (σ.getD i 0 = v ∧ σ.getD ((i + 1) % σ.length) 0 = u)

theorem hb_CN_symm {σ : List ℕ} {u v : ℕ} (h : hb_CN σ u v) : hb_CN σ v u := by
  obtain ⟨i, hi, h | h⟩ := h
  exacts [⟨i, hi, Or.inr h⟩, ⟨i, hi, Or.inl h⟩]

section Cycle

variable {n : ℕ} {adj : ℕ → ℕ → Prop} {σ : List ℕ}

theorem hb_len (hσ : IsHamCycle n adj σ) : σ.length = n := by
  simpa using hσ.1.length_eq

theorem hb_nodup (hσ : IsHamCycle n adj σ) : σ.Nodup := hσ.1.nodup_iff.2 List.nodup_range

theorem hb_getD_lt (hσ : IsHamCycle n adj σ) {i : ℕ} (hi : i < σ.length) : σ.getD i 0 < n := by
  have : σ.getD i 0 ∈ σ := by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  simpa using hσ.1.mem_iff.1 this

theorem hb_getD_inj (hσ : IsHamCycle n adj σ) {i j : ℕ} (hi : i < σ.length) (hj : j < σ.length)
    (h : σ.getD i 0 = σ.getD j 0) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact (hb_nodup hσ).getElem_inj_iff.1 h

theorem hb_exists_idx (hσ : IsHamCycle n adj σ) {u : ℕ} (hu : u < n) :
    ∃ i < σ.length, σ.getD i 0 = u := by
  have : u ∈ σ := hσ.1.mem_iff.2 (List.mem_range.2 hu)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem this
  exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩

theorem hb_mod_succ {i L : ℕ} (h : i < L) : (i + 1) % L = if i + 1 = L then 0 else i + 1 := by
  split_ifs with h'
  · rw [h', Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem hb_CN_lt (hσ : IsHamCycle n adj σ) {u v : ℕ} (h : hb_CN σ u v) : u < n ∧ v < n := by
  obtain ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h <;>
    exact ⟨hb_getD_lt hσ (by first | exact hi | exact Nat.mod_lt _ (by omega)),
      hb_getD_lt hσ (by first | exact hi | exact Nat.mod_lt _ (by omega))⟩

theorem hb_CN_adj (hσ : IsHamCycle n adj σ) (hs : ∀ u v, adj u v → adj v u) {u v : ℕ}
    (h : hb_CN σ u v) : adj u v := by
  obtain ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact hσ.2 i hi
  · exact hs _ _ (hσ.2 i hi)

/-- Every vertex has exactly two distinct cycle-neighbours. -/
theorem hb_two (hσ : IsHamCycle n adj σ) (hn : 3 ≤ n) {u : ℕ} (hu : u < n) :
    ∃ p q, p ≠ q ∧ ∀ v, hb_CN σ u v ↔ v = p ∨ v = q := by
  have hL := hb_len hσ
  obtain ⟨i, hi, rfl⟩ := hb_exists_idx hσ hu
  have e1 := hb_mod_succ hi
  have hq : (if i = 0 then σ.length - 1 else i - 1) < σ.length := by split_ifs <;> omega
  have hq1 : ((if i = 0 then σ.length - 1 else i - 1) + 1) % σ.length = i := by
    rw [hb_mod_succ hq]; split_ifs <;> omega
  have hp : (i + 1) % σ.length < σ.length := Nat.mod_lt _ (by omega)
  refine ⟨σ.getD ((i + 1) % σ.length) 0, σ.getD (if i = 0 then σ.length - 1 else i - 1) 0,
    ?_, ?_⟩
  · intro h
    have := hb_getD_inj hσ hp hq h
    rw [e1] at this; split_ifs at this <;> omega
  · intro v
    constructor
    · rintro ⟨i', hi', ⟨h1, rfl⟩ | ⟨rfl, h2⟩⟩
      · left; rw [hb_getD_inj hσ hi' hi h1]
      · right
        have hm : (i' + 1) % σ.length < σ.length := Nat.mod_lt _ (by omega)
        have := hb_getD_inj hσ hm hi h2
        rw [hb_mod_succ hi'] at this
        congr 1; split_ifs at this ⊢ <;> omega
    · rintro (rfl | rfl)
      · exact ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, hq, Or.inr ⟨rfl, by rw [hq1]⟩⟩

/-- A nonempty set of vertices closed under cycle-neighbours contains all vertices. -/
theorem hb_closed (hσ : IsHamCycle n adj σ) (S : ℕ → Prop) {u0 : ℕ} (hu0 : u0 < n) (h0 : S u0)
    (hcl : ∀ u v, S u → hb_CN σ u v → S v) : ∀ v < n, S v := by
  have hL := hb_len hσ
  obtain ⟨i0, hi0, rfl⟩ := hb_exists_idx hσ hu0
  have key : ∀ k, S (σ.getD ((i0 + k) % σ.length) 0) := by
    intro k
    induction k with
    | zero => simpa [Nat.mod_eq_of_lt hi0] using h0
    | succ k ih =>
      refine hcl _ _ ih ⟨(i0 + k) % σ.length, Nat.mod_lt _ (by omega), Or.inl ⟨rfl, ?_⟩⟩
      rw [Nat.mod_add_mod, Nat.add_assoc]
  intro v hv
  obtain ⟨i, hi, rfl⟩ := hb_exists_idx hσ hv
  have := key (i + σ.length - i0)
  rwa [show i0 + (i + σ.length - i0) = i + σ.length by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hi] at this

end Cycle

/-! ## B. Hamiltonian cycles of a split graph -/

section Split

variable {V : ℕ} {A : ℕ → ℕ → Prop} {σ : List ℕ}

theorem hb_split_symm {u v : ℕ} (h : SplitAdj V A u v) : SplitAdj V A v u := by
  rcases h with ⟨x, hx, h⟩ | ⟨x, y, hxy, h⟩
  · exact Or.inl ⟨x, hx, by omega⟩
  · exact Or.inr ⟨x, y, hxy, by omega⟩

theorem hb_nb_mid {x v : ℕ} (h : SplitAdj V A (3 * x + 1) v) : v = 3 * x ∨ v = 3 * x + 2 := by
  rcases h with ⟨x', -, h⟩ | ⟨x', y', -, h⟩ <;> omega

theorem hb_nb_out {x v : ℕ} (h : SplitAdj V A (3 * x + 2) v) :
    v = 3 * x + 1 ∨ ∃ y, A x y ∧ v = 3 * y := by
  rcases h with ⟨x', -, h⟩ | ⟨x', y', hA, h | h⟩
  · left; omega
  · obtain rfl : x' = x := by omega
    exact Or.inr ⟨y', hA, h.2⟩
  · omega

theorem hb_nb_in {x v : ℕ} (h : SplitAdj V A (3 * x) v) :
    v = 3 * x + 1 ∨ ∃ z, A z x ∧ v = 3 * z + 2 := by
  rcases h with ⟨x', -, h⟩ | ⟨x', y', hA, h | h⟩
  · left; omega
  · omega
  · obtain rfl : y' = x := by omega
    exact Or.inr ⟨x', hA, h.2⟩

variable (hσ : IsHamCycle (3 * V) (SplitAdj V A) σ) (hV : 3 ≤ V)
include hσ hV

omit hV in
theorem hb_adj {u v : ℕ} (h : hb_CN σ u v) : SplitAdj V A u v :=
  hb_CN_adj hσ (fun _ _ => hb_split_symm) h

theorem hb_two_cases {u a b v : ℕ} (hu : u < 3 * V) (ha : hb_CN σ u a) (hb : hb_CN σ u b)
    (hab : a ≠ b) (hv : hb_CN σ u v) : v = a ∨ v = b := by
  obtain ⟨p, q, hpq, h⟩ := hb_two hσ (by omega) hu
  rw [h] at ha hb hv
  omega

theorem hb_mid {x : ℕ} (hx : x < V) :
    hb_CN σ (3 * x + 1) (3 * x) ∧ hb_CN σ (3 * x + 1) (3 * x + 2) := by
  obtain ⟨p, q, hpq, h⟩ := hb_two hσ (by omega) (u := 3 * x + 1) (by omega)
  have hp := hb_nb_mid (hb_adj hσ ((h p).2 (Or.inl rfl)))
  have hq := hb_nb_mid (hb_adj hσ ((h q).2 (Or.inr rfl)))
  rw [h, h]; omega

theorem hb_out_ex {x : ℕ} (hx : x < V) : ∃ y, hb_CN σ (3 * x + 2) (3 * y) := by
  obtain ⟨p, q, hpq, h⟩ := hb_two hσ (by omega) (u := 3 * x + 2) (by omega)
  by_cases hp : p = 3 * x + 1
  · rcases hb_nb_out (hb_adj hσ ((h q).2 (Or.inr rfl))) with h' | ⟨y, -, rfl⟩
    · omega
    · exact ⟨y, (h _).2 (Or.inr rfl)⟩
  · rcases hb_nb_out (hb_adj hσ ((h p).2 (Or.inl rfl))) with h' | ⟨y, -, rfl⟩
    · omega
    · exact ⟨y, (h _).2 (Or.inl rfl)⟩

theorem hb_in_ex {x : ℕ} (hx : x < V) : ∃ z, hb_CN σ (3 * x) (3 * z + 2) := by
  obtain ⟨p, q, hpq, h⟩ := hb_two hσ (by omega) (u := 3 * x) (by omega)
  by_cases hp : p = 3 * x + 1
  · rcases hb_nb_in (hb_adj hσ ((h q).2 (Or.inr rfl))) with h' | ⟨z, -, rfl⟩
    · omega
    · exact ⟨z, (h _).2 (Or.inr rfl)⟩
  · rcases hb_nb_in (hb_adj hσ ((h p).2 (Or.inl rfl))) with h' | ⟨z, -, rfl⟩
    · omega
    · exact ⟨z, (h _).2 (Or.inl rfl)⟩

theorem hb_out_uniq {x y y' : ℕ} (hx : x < V) (h1 : hb_CN σ (3 * x + 2) (3 * y))
    (h2 : hb_CN σ (3 * x + 2) (3 * y')) : y = y' := by
  have hm := hb_CN_symm (hb_mid hσ hV hx).2
  have := hb_two_cases hσ hV (by omega) hm h1 (by omega) h2
  omega

theorem hb_in_uniq {x z z' : ℕ} (hx : x < V) (h1 : hb_CN σ (3 * x) (3 * z + 2))
    (h2 : hb_CN σ (3 * x) (3 * z' + 2)) : z = z' := by
  have hm := hb_CN_symm (hb_mid hσ hV hx).1
  have := hb_two_cases hσ hV (by omega) hm h1 (by omega) h2
  omega

omit hσ hV in
open Classical in
/-- The successor of `x`: the other cycle-neighbour of the out-vertex `3x + 2` is `3 (D x)`. -/
noncomputable def hb_D (σ : List ℕ) (x : ℕ) : ℕ :=
  if h : ∃ y, hb_CN σ (3 * x + 2) (3 * y) then h.choose else 0

omit hσ hV in
open Classical in
/-- The predecessor of `x`: the other cycle-neighbour of the in-vertex `3x` is `3 (P x) + 2`. -/
noncomputable def hb_P (σ : List ℕ) (x : ℕ) : ℕ :=
  if h : ∃ z, hb_CN σ (3 * x) (3 * z + 2) then h.choose else 0

theorem hb_D_spec {x : ℕ} (hx : x < V) : hb_CN σ (3 * x + 2) (3 * hb_D σ x) := by
  have h := hb_out_ex hσ hV hx
  rw [hb_D, dif_pos h]; exact h.choose_spec

theorem hb_P_spec {x : ℕ} (hx : x < V) : hb_CN σ (3 * x) (3 * hb_P σ x + 2) := by
  have h := hb_in_ex hσ hV hx
  rw [hb_P, dif_pos h]; exact h.choose_spec

end Split

/-- A cover of the vertices `[0, V)` of `A` by directed cycles of length `≥ 3`, given by the
successor `D` and the predecessor `P`. -/
def hb_Cover (V : ℕ) (A : ℕ → ℕ → Prop) (D P : ℕ → ℕ) : Prop :=
  ∀ x < V, D x < V ∧ P x < V ∧ A x (D x) ∧ A (P x) x ∧ D (P x) = x ∧ P (D x) = x ∧ P x ≠ D x

/-- **A Hamiltonian cycle of the split graph gives a cycle cover without 1- and 2-cycles.** -/
theorem hb_cover_of_ham {V : ℕ} {A : ℕ → ℕ → Prop} {σ : List ℕ} (hV : 3 ≤ V)
    (hσ : IsHamCycle (3 * V) (SplitAdj V A) σ) : ∃ D P, hb_Cover V A D P := by
  have Dlt : ∀ x < V, hb_D σ x < V := fun x hx => by
    have := (hb_CN_lt hσ (hb_D_spec hσ hV hx)).2; omega
  have Plt : ∀ x < V, hb_P σ x < V := fun x hx => by
    have := (hb_CN_lt hσ (hb_P_spec hσ hV hx)).2; omega
  have PD : ∀ x < V, hb_P σ (hb_D σ x) = x := fun x hx =>
    hb_in_uniq hσ hV (Dlt x hx) (hb_P_spec hσ hV (Dlt x hx)) (hb_CN_symm (hb_D_spec hσ hV hx))
  have DP : ∀ x < V, hb_D σ (hb_P σ x) = x := fun x hx =>
    hb_out_uniq hσ hV (Plt x hx) (hb_D_spec hσ hV (Plt x hx)) (hb_CN_symm (hb_P_spec hσ hV hx))
  refine ⟨hb_D σ, hb_P σ, fun x hx => ⟨Dlt x hx, Plt x hx, ?_, ?_, DP x hx, PD x hx, ?_⟩⟩
  · rcases hb_nb_out (hb_adj hσ (hb_D_spec hσ hV hx)) with h | ⟨y, hy, e⟩
    · omega
    · rwa [show hb_D σ x = y by omega]
  · rcases hb_nb_in (hb_adj hσ (hb_P_spec hσ hV hx)) with h | ⟨z, hz, e⟩
    · omega
    · rwa [show hb_P σ x = z by omega]
  · intro he
    have hy := Dlt x hx
    have hPy := PD x hx
    have hDy : hb_D σ (hb_D σ x) = x := by rw [← he]; exact DP x hx
    generalize hy' : hb_D σ x = y at hy hPy hDy he
    let S : ℕ → Prop := fun v => (3 * x ≤ v ∧ v < 3 * x + 3) ∨ (3 * y ≤ v ∧ v < 3 * y + 3)
    have hcl : ∀ u v, S u → hb_CN σ u v → S v := by
      intro u v hu huv
      have hmx := hb_mid hσ hV hx
      have hmy := hb_mid hσ hV hy
      have : u = 3 * x ∨ u = 3 * x + 1 ∨ u = 3 * x + 2 ∨ u = 3 * y ∨ u = 3 * y + 1 ∨
          u = 3 * y + 2 := by simp only [S] at hu; omega
      simp only [S]
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl
      · have := hb_two_cases hσ hV (by omega) (hb_CN_symm hmx.1) (hb_P_spec hσ hV hx)
          (by omega) huv
        omega
      · have := hb_two_cases hσ hV (by omega) hmx.1 hmx.2 (by omega) huv
        omega
      · have := hb_two_cases hσ hV (by omega) (hb_CN_symm hmx.2) (hb_D_spec hσ hV hx)
          (by omega) huv
        omega
      · have := hb_two_cases hσ hV (by omega) (hb_CN_symm hmy.1) (hb_P_spec hσ hV hy)
          (by omega) huv
        omega
      · have := hb_two_cases hσ hV (by omega) hmy.1 hmy.2 (by omega) huv
        omega
      · have := hb_two_cases hσ hV (by omega) (hb_CN_symm hmy.2) (hb_D_spec hσ hV hy)
          (by omega) huv
        omega
    have hall := hb_closed hσ S (u0 := 3 * x) (by omega) (by simp only [S]; omega) hcl
    have h0 := hall 0 (by omega)
    have h3 := hall 3 (by omega)
    have h6 := hall 6 (by omega)
    simp only [S] at h0 h3 h6
    omega

theorem hb_cov_iff {V : ℕ} {A : ℕ → ℕ → Prop} {D P : ℕ → ℕ} (hc : hb_Cover V A D P) {x y : ℕ}
    (hx : x < V) (hy : y < V) : D x = y ↔ P y = x := by
  constructor
  · rintro rfl; exact (hc x hx).2.2.2.2.2.1
  · rintro rfl; exact (hc y hy).2.2.2.2.1

theorem hb_injD {V : ℕ} {A : ℕ → ℕ → Prop} {D P : ℕ → ℕ} (hc : hb_Cover V A D P) {x x' : ℕ}
    (hx : x < V) (hx' : x' < V) (h : D x = D x') : x = x' := by
  have h1 := (hc x hx).2.2.2.2.2.1
  have h2 := (hc x' hx').2.2.2.2.2.1
  rw [h] at h1; omega

theorem hb_injP {V : ℕ} {A : ℕ → ℕ → Prop} {D P : ℕ → ℕ} (hc : hb_Cover V A D P) {x x' : ℕ}
    (hx : x < V) (hx' : x' < V) (h : P x = P x') : x = x' := by
  have h1 := (hc x hx).2.2.2.2.1
  have h2 := (hc x' hx').2.2.2.2.1
  rw [h] at h1; omega

/-! ## C. Cycle covers of `DA w` -/

theorem hb_row_eq {R j j' d t : ℕ} (h : j * R + d = j' * R + t) (hd : d ≤ R) (ht : t < R) :
    (j = j' ∧ d = t) ∨ (j' = j + 1 ∧ d = R ∧ t = 0) := by
  rcases lt_trichotomy j j' with h1 | rfl | h1
  · obtain ⟨c, rfl⟩ : ∃ c, j' = j + 1 + c := ⟨j' - j - 1, by omega⟩
    have e : (j + 1 + c) * R = j * R + R + c * R := by ring
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · right; omega
    · have : R ≤ c * R := Nat.le_mul_of_pos_left R hc
      omega
  · left; omega
  · obtain ⟨c, rfl⟩ : ∃ c, j = j' + 1 + c := ⟨j - j' - 1, by omega⟩
    have e : (j' + 1 + c) * R = j' * R + R + c * R := by ring
    omega

theorem hb_rv_lt' {w : List SatSym} {j t : ℕ} (hj : j < NV w) (ht : t < RW (mC w)) :
    mC w + j * RW (mC w) + t < mC w + NV w * RW (mC w) := by
  have h1 : (j + 1) * RW (mC w) ≤ NV w * RW (mC w) := Nat.mul_le_mul_right _ hj
  have h2 : (j + 1) * RW (mC w) = j * RW (mC w) + RW (mC w) := by ring
  omega

theorem hb_rv_lt {w : List SatSym} {j t : ℕ} (hj : j < NV w) (ht : t < RW (mC w)) :
    mC w + j * RW (mC w) + t < VV w := by
  have h1 : (j + 1) * RW (mC w) ≤ NV w * RW (mC w) := Nat.mul_le_mul_right _ hj
  have h2 : (j + 1) * RW (mC w) = j * RW (mC w) + RW (mC w) := by ring
  unfold VV; omega

theorem hb_d1_cases (t : ℕ) :
    (t = 0 ∧ d1 t = 1) ∨ (t = 1 ∧ d1 t = 2) ∨ (2 ≤ t ∧ d1 t = t - 1) := by
  unfold d1; split_ifs <;> omega

theorem hb_d2_cases (R t : ℕ) :
    (t = 0 ∧ d2 R t = R - 1) ∨ ((t = 1 ∨ t = R - 1) ∧ d2 R t = R) ∨
      (t ≠ 0 ∧ t ≠ 1 ∧ t ≠ R - 1 ∧ d2 R t = t + 1) := by
  unfold d2; split_ifs <;> omega

/-- Out-neighbours of an inner row vertex. -/
theorem hb_out_row {w : List SatSym} {j t x y : ℕ} (hj : j < NV w) (ht2 : 2 ≤ t)
    (ht : t + 2 ≤ RW (mC w)) (hx : x = mC w + j * RW (mC w) + t) (h : DA w x y) :
    y + 1 = x ∨ y = x + 1 ∨ (y < mC w ∧ (t = 3 + 3 * y ∨ t = 4 + 3 * y)) := by
  have hR : RW (mC w) = 3 * mC w + 4 := rfl
  subst hx
  rcases h with ⟨j', hj', t', ht', hx, hy⟩ | ⟨hx, -⟩ |
      ⟨k, hk, j', hj', -, ⟨hx, rfl⟩ | ⟨hx, -⟩⟩ | ⟨k, hk, j', hj', -, ⟨hx, rfl⟩ | ⟨hx, -⟩⟩
  · have := hb_row_eq (R := RW (mC w)) (j := j') (j' := j) (d := t') (t := t) (by omega)
      (by omega) (by omega)
    have h1 := hb_d1_cases t'
    have h2 := hb_d2_cases (RW (mC w)) t'
    omega
  · have := hb_rv_lt' hj (t := t) (by omega); omega
  · have := hb_row_eq (R := RW (mC w)) (j := j') (j' := j) (d := 3 + 3 * y) (t := t) (by omega)
      (by omega) (by omega)
    omega
  · omega
  · have := hb_row_eq (R := RW (mC w)) (j := j') (j' := j) (d := 4 + 3 * y) (t := t) (by omega)
      (by omega) (by omega)
    omega
  · omega

/-- In-neighbours of an inner row vertex. -/
theorem hb_in_row {w : List SatSym} {j t x y : ℕ} (_hj : j < NV w) (ht2 : 2 ≤ t)
    (ht : t + 2 ≤ RW (mC w)) (hy : y = mC w + j * RW (mC w) + t) (h : DA w x y) :
    x + 1 = y ∨ x = y + 1 ∨ (x < mC w ∧ (t = 3 + 3 * x ∨ t = 4 + 3 * x)) := by
  have hR : RW (mC w) = 3 * mC w + 4 := rfl
  subst hy
  rcases h with ⟨j', hj', t', ht', rfl, hy⟩ | ⟨-, hy⟩ |
      ⟨k, hk, j', hj', -, ⟨-, hy⟩ | ⟨rfl, hy⟩⟩ | ⟨k, hk, j', hj', -, ⟨-, hy⟩ | ⟨rfl, hy⟩⟩
  · rcases hy with hy | hy
    · have h1 := hb_d1_cases t'
      have := hb_row_eq (R := RW (mC w)) (j := j') (j' := j) (d := d1 t') (t := t) (by omega)
        (by omega) (by omega)
      omega
    · have h2 := hb_d2_cases (RW (mC w)) t'
      have := hb_row_eq (R := RW (mC w)) (j := j') (j' := j) (d := d2 (RW (mC w)) t') (t := t)
        (by omega) (by omega) (by omega)
      omega
  · omega
  · omega
  · have := hb_row_eq (R := RW (mC w)) (j := j') (j' := j) (d := 4 + 3 * x) (t := t) (by omega)
      (by omega) (by omega)
    omega
  · omega
  · have := hb_row_eq (R := RW (mC w)) (j := j') (j' := j) (d := 3 + 3 * x) (t := t) (by omega)
      (by omega) (by omega)
    omega

/-- In-neighbours of a clause vertex. -/
theorem hb_in_clause {w : List SatSym} {k x : ℕ} (hk : k < mC w) (h : DA w x k) :
    ∃ j < NV w, (x = mC w + j * RW (mC w) + (3 + 3 * k) ∧ sy w k j = pos) ∨
      (x = mC w + j * RW (mC w) + (4 + 3 * k) ∧ sy w k j = neg) := by
  rcases h with ⟨j', hj', t', ht', -, hy⟩ | ⟨-, hy⟩ |
      ⟨k', hk', j, hj, hs, ⟨hx, rfl⟩ | ⟨-, hy⟩⟩ | ⟨k', hk', j, hj, hs, ⟨hx, rfl⟩ | ⟨-, hy⟩⟩
  · rcases hy with hy | hy <;> omega
  · omega
  · exact ⟨j, hj, Or.inl ⟨by omega, hs⟩⟩
  · omega
  · exact ⟨j, hj, Or.inr ⟨by omega, hs⟩⟩
  · omega

section Sat

variable {w : List SatSym} {D P : ℕ → ℕ}

/-- The separator `2 + 3k` of row `j` goes right. -/
def hb_Rt (w : List SatSym) (D : ℕ → ℕ) (j k : ℕ) : Prop :=
  D (mC w + j * RW (mC w) + (2 + 3 * k)) = mC w + j * RW (mC w) + (2 + 3 * k) + 1

/-- A separator goes right or left. -/
theorem hb_dich (hc : hb_Cover (VV w) (DA w) D P) {j k x : ℕ} (hj : j < NV w) (hk : k ≤ mC w)
    (hx : x = mC w + j * RW (mC w) + (2 + 3 * k)) :
    (D x = x + 1 ∧ P x + 1 = x) ∨ (D x + 1 = x ∧ P x = x + 1) := by
  have hR : RW (mC w) = 3 * mC w + 4 := rfl
  obtain ⟨-, -, h1, h2, -, -, hne⟩ := hc x (by rw [hx]; exact hb_rv_lt hj (by omega))
  have o := hb_out_row hj (t := 2 + 3 * k) (by omega) (by omega) hx h1
  have i := hb_in_row hj (t := 2 + 3 * k) (by omega) (by omega) hx h2
  omega

/-- Propagation of the direction along a row. -/
theorem hb_prop (hc : hb_Cover (VV w) (DA w) D P) {j k : ℕ} (hj : j < NV w) (hk : k < mC w) :
    hb_Rt w D j k ↔ hb_Rt w D j (k + 1) := by
  unfold hb_Rt
  have hR : RW (mC w) = 3 * mC w + 4 := rfl
  rw [show mC w + j * RW (mC w) + (2 + 3 * (k + 1)) = mC w + j * RW (mC w) + (2 + 3 * k) + 3 by
    ring]
  have hlt := hb_rv_lt hj (t := 5 + 3 * k) (by omega)
  generalize hs : mC w + j * RW (mC w) + (2 + 3 * k) = s
  have d0 := hb_dich hc hj (k := k) (by omega) hs.symm
  have d1 := hb_dich hc hj (k := k + 1) (x := s + 3) (by omega) (by omega)
  obtain ⟨-, -, haD, haP, -, -, hane⟩ := hc (s + 1) (by omega)
  obtain ⟨-, -, hbD, hbP, -, -, hbne⟩ := hc (s + 2) (by omega)
  have cv : ∀ x y, x < VV w → y < VV w → (D x = y → P y = x) ∧ (P y = x → D x = y) :=
    fun x y hx hy => ⟨(hb_cov_iff hc hx hy).1, (hb_cov_iff hc hx hy).2⟩
  constructor
  · intro hr
    rcases d1 with h | h
    · exact h.1
    exfalso
    have pa : P (s + 1) = s := (cv s (s + 1) (by omega) (by omega)).1 hr
    have pb : P (s + 2) = s + 3 := (cv (s + 3) (s + 2) (by omega) (by omega)).1 (by omega)
    have da : D (s + 1) = k := by
      have oa := hb_out_row hj (t := 3 + 3 * k) (x := s + 1) (by omega) (by omega) (by omega) haD
      rcases oa with h' | h' | h'
      · omega
      · have := (cv (s + 1) (s + 2) (by omega) (by omega)).1 h'; omega
      · omega
    have db : D (s + 2) = k := by
      have ob := hb_out_row hj (t := 4 + 3 * k) (x := s + 2) (by omega) (by omega) (by omega) hbD
      rcases ob with h' | h' | h'
      · have := (cv (s + 2) (s + 1) (by omega) (by omega)).1 (by omega); omega
      · omega
      · omega
    have := hb_injD hc (x := s + 1) (x' := s + 2) (by omega) (by omega) (by omega); omega
  · intro hr
    rcases d0 with h | h
    · exact h.1
    exfalso
    have da : D (s + 1) = s := (cv (s + 1) s (by omega) (by omega)).2 (by omega)
    have hp3 : P (s + 3) = s + 2 := by omega
    have db : D (s + 2) = s + 3 := (cv (s + 2) (s + 3) (by omega) (by omega)).2 hp3
    have pa : P (s + 1) = k := by
      have ia := hb_in_row hj (t := 3 + 3 * k) (y := s + 1) (by omega) (by omega) (by omega) haP
      rcases ia with h' | h' | h'
      · omega
      · have := (cv (s + 2) (s + 1) (by omega) (by omega)).2 h'; omega
      · omega
    have pb : P (s + 2) = k := by
      have ib := hb_in_row hj (t := 4 + 3 * k) (y := s + 2) (by omega) (by omega) (by omega) hbP
      rcases ib with h' | h' | h'
      · have := (cv (s + 1) (s + 2) (by omega) (by omega)).2 (by omega); omega
      · omega
      · omega
    have := hb_injP hc (x := s + 1) (x' := s + 2) (by omega) (by omega) (by omega); omega

theorem hb_rt0 (hc : hb_Cover (VV w) (DA w) D P) {j : ℕ} (hj : j < NV w) {k : ℕ}
    (hk : k ≤ mC w) : hb_Rt w D j k ↔ hb_Rt w D j 0 := by
  induction k with
  | zero => exact Iff.rfl
  | succ k ih => exact (hb_prop hc hj (by omega)).symm.trans (ih (by omega))

/-- Every clause vertex is entered from a row whose direction makes the literal true. -/
theorem hb_clause (hc : hb_Cover (VV w) (DA w) D P) {k : ℕ} (hk : k < mC w) :
    ∃ j, (sy w k j = pos ∧ hb_Rt w D j 0) ∨ (sy w k j = neg ∧ ¬ hb_Rt w D j 0) := by
  have hR : RW (mC w) = 3 * mC w + 4 := rfl
  obtain ⟨-, -, -, hA, -, -, -⟩ := hc k (by unfold VV; omega)
  obtain ⟨j, hj, ⟨hx, hs⟩ | ⟨hx, hs⟩⟩ := hb_in_clause hk hA
  · refine ⟨j, Or.inl ⟨hs, (hb_rt0 hc hj (k := k) (by omega)).1 ?_⟩⟩
    unfold hb_Rt
    have hlt := hb_rv_lt hj (t := 5 + 3 * k) (by omega)
    generalize hsx : mC w + j * RW (mC w) + (2 + 3 * k) = s
    have d := hb_dich hc hj (k := k) (by omega) hsx.symm
    have i1 := hb_cov_iff hc (x := s + 1) (y := s) (by omega) (by omega)
    have i2 := hb_cov_iff hc (x := s + 1) (y := k) (by omega) (by unfold VV; omega)
    omega
  · refine ⟨j, Or.inr ⟨hs, fun hR0 => ?_⟩⟩
    have h1 := (hb_rt0 hc hj (k := k + 1) (by omega)).2 hR0
    unfold hb_Rt at h1
    rw [show mC w + j * RW (mC w) + (2 + 3 * (k + 1)) = mC w + j * RW (mC w) + (5 + 3 * k) by
      ring] at h1
    have hlt := hb_rv_lt hj (t := 5 + 3 * k) (by omega)
    generalize hsx : mC w + j * RW (mC w) + (5 + 3 * k) = s at h1
    have d := hb_dich hc hj (k := k + 1) (x := s) (by omega) (by omega)
    have i1 := hb_cov_iff hc (x := s - 1) (y := s) (by omega) (by omega)
    have i2 := hb_cov_iff hc (x := s - 1) (y := k) (by omega) (by unfold VV; omega)
    omega

/-- **A cycle cover of `DA w` without 1- and 2-cycles gives a satisfying assignment.** -/
theorem hb_sat_of_cover (hc : hb_Cover (VV w) (DA w) D P) :
    ∃ a : ℕ → Bool, ∀ c ∈ clauses w, ClauseSat a c := by
  classical
  refine ⟨fun j => decide (hb_Rt w D j 0), ?_⟩
  intro c hcm
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hcm
  have hsy : ∀ j, sy w k j = (clauses w)[k].getD j zero := fun j => by
    simp only [sy, List.getD_eq_getElem _ _ hk]
  obtain ⟨j, h⟩ := hb_clause hc hk
  have hlen : j < (clauses w)[k].length := by
    by_contra hh
    have := List.getD_eq_default (clauses w)[k] zero (not_lt.1 hh)
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hsy, this] at h <;> cases h
  refine ⟨j, hlen, ?_⟩
  rw [← hsy]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, litTrue, h2]

end Sat

/-- **Backward direction of SAT ≤ HAMILTONIAN CYCLE.** -/
theorem sat_of_ham (w : List SatSym) (h : UHamLang (H w)) : SATLang w := by
  obtain ⟨-, σ, hσ⟩ := h
  rw [clauses_H, length_hRows] at hσ
  have hσ' : IsHamCycle (3 * VV w) (SplitAdj (VV w) (DA w)) σ :=
    ⟨hσ.1, fun i hi => (adj_H_iff w _ _).1 (hσ.2 i hi)⟩
  have hV : 3 ≤ VV w := by
    have : 1 * RW (mC w) ≤ NV w * RW (mC w) := Nat.mul_le_mul_right _ (by unfold NV; omega)
    have hR : RW (mC w) = 3 * mC w + 4 := rfl
    unfold VV; omega
  obtain ⟨D, P, hc⟩ := hb_cover_of_ham hV hσ'
  exact (clauses_sat_iff w).2 (hb_sat_of_cover hc)

end Pnp.Karp.Ham
