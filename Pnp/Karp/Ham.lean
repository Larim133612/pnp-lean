import Pnp.Karp.CliqueRed

/-!
# HAMILTONIAN CYCLE: the language and the reduction graph

## Encoding of (undirected) HAMILTONIAN CYCLE instances

An instance is a word `w` over `SatSym`, read as its rows `clauses w` (the maximal
`sep`-terminated blocks; symbols after the last `sep` are ignored).  The number of vertices is
the number of rows `n = |clauses w|`, and the entry `(i, j)` is
`((clauses w).getD i []).getD j zero` (missing entries count as `zero`).  There is an
(undirected) edge between `u` and `v` iff the entry `(u, v)` or the entry `(v, u)` is `pos`.

`UHamLang w` holds iff `n ≥ 3` and some ordering `σ` of the vertices (a permutation of
`[0, n)`) visits them along a cycle: `σᵢ` and `σᵢ₊₁` are adjacent for every `i`, cyclically.

## The reduction (from a dense CNF formula `w`)

Let `C = clauses w`, `m = |C|`, `N = |trunc w| + 1` (more than enough variables: every literal
of a clause sits at a position `< N`), `R = 3m + 4`, and `sy w k j` the symbol at position `j`
of clause `k`.  First a **directed** graph `DA w` on `V = m + N R + 1` vertices:

* the clause vertices `k < m`;
* for every variable `j < N` a row of `R` vertices `m + jR + t` (`t < R`): the hub `t = 0`, the
  ends `t = 1` and `t = R - 1`, the separators `t = 2 + 3k` (`k ≤ m`) and the pair `a = 3 + 3k`,
  `b = 4 + 3k` for clause `k < m`.  Arcs: hub → both ends, ends → the next hub
  `m + (j + 1)R`, the end `t = 1` → `t = 2`, the end `t = R - 1` → `t = R - 2`, and both
  directions between neighbours `t, t ± 1` for `2 ≤ t ≤ R - 2`;
* the final hub `Z = m + NR` with the arc `Z → m` (the first hub);
* if `x_j` occurs positively in clause `k`: `a → k → b`; negatively: `b → k → a`.

A Hamiltonian cycle runs through the rows in order, each row from left to right ("`x_j` true")
or from right to left ("false"), and visits every clause vertex in a detour from a pair of a row
whose direction makes the literal true.

The undirected graph `H w` is the *split* of `DA w`: every vertex `x` becomes `3x` (in),
`3x + 1` (middle), `3x + 2` (out), with edges `3x — 3x+1 — 3x+2`, and every arc `x → y` becomes
the edge `3x + 2 — 3y` (`SplitAdj`).  The rows of `H w` (`hRows`) are laid out so that they
are easy to print: the arcs into/out of clause vertices are stored in the rows of the clause
vertex, all other arcs in the out-row `3x + 2`.

`adj_H_iff` (proved below) characterizes the adjacency of `H w` by `SplitAdj (VV w) (DA w)`.
-/

namespace Pnp.Karp.Ham

open Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## The language -/

/-- The entry `(u, v)` of the adjacency matrix of `w`. -/
def ent (w : List SatSym) (u v : ℕ) : SatSym := ((clauses w).getD u []).getD v zero

/-- Undirected adjacency: the entry `(u, v)` or `(v, u)` is `pos`. -/
def adjU (w : List SatSym) (u v : ℕ) : Prop := ent w u v = pos ∨ ent w v u = pos

/-- `σ` is a Hamiltonian cycle for the adjacency relation `adj` on `n` vertices. -/
def IsHamCycle (n : ℕ) (adj : ℕ → ℕ → Prop) (σ : List ℕ) : Prop :=
  σ.Perm (List.range n) ∧ ∀ i < σ.length, adj (σ.getD i 0) (σ.getD ((i + 1) % σ.length) 0)

/-- **(Undirected) HAMILTONIAN CYCLE** over `SatSym` (see the module docstring). -/
def UHamLang : Millennium.Language (List SatSym) := fun w =>
  3 ≤ (clauses w).length ∧ ∃ σ : List ℕ, IsHamCycle (clauses w).length (adjU w) σ

/-! ## Parameters of the reduction -/

/-- The number of clauses. -/
def mC (w : List SatSym) : ℕ := (clauses w).length

/-- The number of variable rows. -/
def NV (w : List SatSym) : ℕ := (trunc w).length + 1

/-- The width of a row. -/
def RW (m : ℕ) : ℕ := 3 * m + 4

/-- The number of vertices of the directed graph. -/
def VV (w : List SatSym) : ℕ := mC w + NV w * RW (mC w) + 1

/-- The symbol at position `j` of clause `k`. -/
def sy (w : List SatSym) (k j : ℕ) : SatSym := ((clauses w).getD k []).getD j zero

/-- Offset (inside the row, relative to the hub) of the first out-neighbour of `t`. -/
def d1 (t : ℕ) : ℕ := if t = 0 then 1 else if t = 1 then 2 else t - 1

/-- Offset of the second out-neighbour of `t` (`R` is the next hub). -/
def d2 (R t : ℕ) : ℕ := if t = 0 then R - 1 else if t = 1 ∨ t = R - 1 then R else t + 1

/-! ## The directed graph -/

/-- The arcs of the directed graph (see the module docstring). -/
def DA (w : List SatSym) (x y : ℕ) : Prop :=
  (∃ j < NV w, ∃ t < RW (mC w), x = mC w + j * RW (mC w) + t ∧
      (y = mC w + j * RW (mC w) + d1 t ∨ y = mC w + j * RW (mC w) + d2 (RW (mC w)) t)) ∨
  (x = mC w + NV w * RW (mC w) ∧ y = mC w) ∨
  (∃ k < mC w, ∃ j < NV w, sy w k j = pos ∧
      ((x = mC w + j * RW (mC w) + 3 + 3 * k ∧ y = k) ∨
        (x = k ∧ y = mC w + j * RW (mC w) + 4 + 3 * k))) ∨
  (∃ k < mC w, ∃ j < NV w, sy w k j = neg ∧
      ((x = mC w + j * RW (mC w) + 4 + 3 * k ∧ y = k) ∨
        (x = k ∧ y = mC w + j * RW (mC w) + 3 + 3 * k)))

/-- Adjacency of the split of a directed graph `A` on `V` vertices. -/
def SplitAdj (V : ℕ) (A : ℕ → ℕ → Prop) (u v : ℕ) : Prop :=
  (∃ x < V, (u = 3 * x ∧ v = 3 * x + 1) ∨ (u = 3 * x + 1 ∧ v = 3 * x) ∨
      (u = 3 * x + 1 ∧ v = 3 * x + 2) ∨ (u = 3 * x + 2 ∧ v = 3 * x + 1)) ∨
  (∃ x y, A x y ∧ ((u = 3 * x + 2 ∧ v = 3 * y) ∨ (u = 3 * y ∧ v = 3 * x + 2)))

/-! ## The rows of the undirected graph `H w` -/

/-- A run of `zero`s. -/
abbrev zs (n : ℕ) : List SatSym := List.replicate n zero

/-- A row with one `pos`, at column `a`. -/
def one (a : ℕ) : List SatSym := zs a ++ [pos]

/-- A row with two `pos`, at columns `a` and `a + b + 1`. -/
def two (a b : ℕ) : List SatSym := zs a ++ pos :: zs b ++ [pos]

/-- The out-row of the row vertex `m + jR + t`: edges to the in-vertices of its two
out-neighbours (no clause arcs). -/
def outV (m j t : ℕ) : List SatSym :=
  two (3 * (m + j * RW m + d1 t)) (3 * (d2 (RW m) t - d1 t) - 1)

/-- Block `j` of the in-row of clause `k`: the edge to the out-vertex of `a` (`pos`) or `b`
(`neg`) of row `j`. -/
def blkIn (m k : ℕ) : SatSym → List SatSym
  | pos => one (11 + 9 * k) ++ zs (3 * RW m - 12 - 9 * k)
  | neg => one (14 + 9 * k) ++ zs (3 * RW m - 15 - 9 * k)
  | _ => zs (3 * RW m)

/-- Block `j` of the out-row of clause `k`: the edge to the in-vertex of `b` (`pos`) or `a`
(`neg`) of row `j`. -/
def blkOut (m k : ℕ) : SatSym → List SatSym
  | pos => one (12 + 9 * k) ++ zs (3 * RW m - 13 - 9 * k)
  | neg => one (9 + 9 * k) ++ zs (3 * RW m - 10 - 9 * k)
  | _ => zs (3 * RW m)

/-- The in-row of clause vertex `k` (in-vertex `3k`): the middle vertex and the out-vertices of
the in-neighbours of `k`. -/
def inC (w : List SatSym) (k : ℕ) : List SatSym :=
  one (3 * k + 1) ++ zs (3 * mC w - 3 * k - 2) ++
    (List.range (NV w)).flatMap fun j => blkIn (mC w) k (sy w k j)

/-- The out-row of clause vertex `k` (out-vertex `3k + 2`): the in-vertices of the
out-neighbours of `k`. -/
def outC (w : List SatSym) (k : ℕ) : List SatSym :=
  zs (3 * mC w) ++ (List.range (NV w)).flatMap fun j => blkOut (mC w) k (sy w k j)

/-- The three rows of clause vertex `k`. -/
def rowsC (w : List SatSym) (k : ℕ) : List (List SatSym) :=
  [inC w k, one (3 * k + 2), outC w k]

/-- The three rows of the row vertex `x = m + jR + t`. -/
def rowsV (m j t : ℕ) : List (List SatSym) :=
  [one (3 * (m + j * RW m + t) + 1), one (3 * (m + j * RW m + t) + 2), outV m j t]

/-- The three rows of the final hub `Z = m + NR` (arc `Z → m`). -/
def rowsZ (m N : ℕ) : List (List SatSym) :=
  [one (3 * (m + N * RW m) + 1), one (3 * (m + N * RW m) + 2), one (3 * m)]

/-- The rows of `H w`, three per vertex of `DA w`. -/
def hRows (w : List SatSym) : List (List SatSym) :=
  (List.range (mC w)).flatMap (rowsC w) ++
    (List.range (NV w)).flatMap (fun j => (List.range (RW (mC w))).flatMap (rowsV (mC w) j)) ++
    rowsZ (mC w) (NV w)

/-- The HAMILTONIAN CYCLE instance of the formula `w`. -/
def H (w : List SatSym) : List SatSym := (hRows w).flatMap (· ++ [sep])

/-! ## Rows of `H w` -/

theorem sep_not_mem_one (a : ℕ) : sep ∉ one a := by simp [one, List.mem_replicate]

theorem sep_not_mem_two (a b : ℕ) : sep ∉ two a b := by simp [two, List.mem_replicate]

theorem sep_not_mem_blkIn (m k : ℕ) (s : SatSym) : sep ∉ blkIn m k s := by
  cases s <;> simp [blkIn, one, List.mem_replicate]

theorem sep_not_mem_blkOut (m k : ℕ) (s : SatSym) : sep ∉ blkOut m k s := by
  cases s <;> simp [blkOut, one, List.mem_replicate]

theorem sep_not_mem_hRows (w : List SatSym) : ∀ c ∈ hRows w, sep ∉ c := by
  intro c hc
  simp only [hRows, rowsC, rowsV, rowsZ, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (⟨k, _, rfl | rfl | rfl⟩ | ⟨j, _, t, _, rfl | rfl | rfl⟩) | rfl | rfl | rfl
  · simp only [inC, List.mem_append, List.mem_flatMap, not_or, not_exists, not_and]
    exact ⟨⟨sep_not_mem_one _, by simp [List.mem_replicate]⟩,
      fun j _ => sep_not_mem_blkIn _ _ _⟩
  · exact sep_not_mem_one _
  · simp only [outC, List.mem_append, List.mem_flatMap, not_or, not_exists, not_and]
    exact ⟨by simp [List.mem_replicate], fun j _ => sep_not_mem_blkOut _ _ _⟩
  · exact sep_not_mem_one _
  · exact sep_not_mem_one _
  · exact sep_not_mem_two _ _
  · exact sep_not_mem_one _
  · exact sep_not_mem_one _
  · exact sep_not_mem_one _

theorem clauses_H (w : List SatSym) : clauses (H w) = hRows w :=
  clauses_flatMap _ (sep_not_mem_hRows w)

theorem length_hRows (w : List SatSym) : (hRows w).length = 3 * VV w := by
  simp [hRows, rowsC, rowsV, rowsZ, List.length_flatMap, VV]
  ring

/-! ## Entries of lists built from blocks -/

section Blocks
variable {α : Type} (d : α) (Q : α → Prop)

theorem ham_Q_getD_append (hQ : ¬ Q d) (l₁ l₂ : List α) (u : ℕ) :
    Q ((l₁ ++ l₂).getD u d) ↔ Q (l₁.getD u d) ∨ ∃ u', u = l₁.length + u' ∧ Q (l₂.getD u' d) := by
  rcases Nat.lt_or_ge u l₁.length with h | h
  · rw [List.getD_append _ _ _ _ h]
    constructor
    · exact Or.inl
    · rintro (h' | ⟨u', rfl, _⟩)
      · exact h'
      · omega
  · rw [List.getD_append_right _ _ _ _ h, List.getD_eq_default _ _ h]
    constructor
    · intro h'; exact Or.inr ⟨u - l₁.length, by omega, h'⟩
    · rintro (h' | ⟨u', rfl, h'⟩)
      · exact absurd h' hQ
      · simpa using h'

theorem ham_Q_getD_flatMap (hQ : ¬ Q d) (B : ℕ) (f : ℕ → List α) (hf : ∀ j, (f j).length = B) :
    ∀ (n u : ℕ), Q (((List.range n).flatMap f).getD u d) ↔
      ∃ j < n, ∃ o, u = j * B + o ∧ Q ((f j).getD o d)
  | 0, u => by simp [hQ]
  | n + 1, u => by
    have hl : ((List.range n).flatMap f).length = n * B := by
      simp [List.length_flatMap, hf]
    rw [List.range_succ, List.flatMap_append, ham_Q_getD_append d Q hQ,
      ham_Q_getD_flatMap hQ B f hf n u, hl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    constructor
    · rintro (⟨j, hj, o, rfl, h⟩ | ⟨u', rfl, h⟩)
      · exact ⟨j, by omega, o, rfl, h⟩
      · exact ⟨n, by omega, u', rfl, h⟩
    · rintro ⟨j, hj, o, rfl, h⟩
      rcases Nat.lt_or_ge j n with h' | h'
      · exact Or.inl ⟨j, h', o, rfl, h⟩
      · obtain rfl : j = n := by omega
        exact Or.inr ⟨o, rfl, h⟩

theorem ham_Q_getD_three (a b c : α) (r : ℕ) (hQ : ¬ Q d) :
    Q ([a, b, c].getD r d) ↔ (r = 0 ∧ Q a) ∨ (r = 1 ∧ Q b) ∨ (r = 2 ∧ Q c) := by
  rcases r with _ | _ | _ | r <;> simp [hQ]

end Blocks

theorem ham_pos_ne_zero : ¬ (zero = pos) := by decide

theorem ham_getD_zs (n v : ℕ) : ¬ (zs n).getD v zero = pos := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : (zs n)[v]? with _ | s
  · simp
  · have := List.mem_of_getElem? h
    simp [List.mem_replicate] at this
    simp [this.2]

theorem ham_getD_one (a v : ℕ) : (one a).getD v zero = pos ↔ v = a := by
  unfold one
  rw [ham_Q_getD_append zero (· = pos) ham_pos_ne_zero]
  simp only [ham_getD_zs, false_or, List.length_replicate]
  constructor
  · rintro ⟨u', rfl, h⟩
    rcases u' with _ | u'
    · rfl
    · simp at h
  · rintro rfl; exact ⟨0, by simp, rfl⟩

theorem ham_getD_two (a b v : ℕ) : (two a b).getD v zero = pos ↔ v = a ∨ v = a + b + 1 := by
  unfold two
  rw [List.append_assoc, ham_Q_getD_append zero (· = pos) ham_pos_ne_zero]
  simp only [ham_getD_zs, false_or, List.length_replicate, List.cons_append]
  constructor
  · rintro ⟨u', rfl, h⟩
    rcases u' with _ | u'
    · left; rfl
    · simp only [List.getD_cons_succ] at h
      rw [ham_Q_getD_append zero (· = pos) ham_pos_ne_zero] at h
      simp only [ham_getD_zs, false_or, List.length_replicate] at h
      obtain ⟨u'', rfl, h⟩ := h
      rcases u'' with _ | u''
      · right; omega
      · simp at h
  · rintro (rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · refine ⟨b + 1, by omega, ?_⟩
      simp only [List.getD_cons_succ]
      rw [ham_Q_getD_append zero (· = pos) ham_pos_ne_zero]
      exact Or.inr ⟨0, by simp, rfl⟩

theorem ham_getD_one_zs (a n v : ℕ) : (one a ++ zs n).getD v zero = pos ↔ v = a := by
  rw [ham_Q_getD_append zero (· = pos) ham_pos_ne_zero, ham_getD_one]
  simp

theorem ham_length_blkIn (m k : ℕ) (hk : k < m) (s : SatSym) :
    (blkIn m k s).length = 3 * RW m := by
  cases s <;> simp [blkIn, one, RW] <;> omega

theorem ham_length_blkOut (m k : ℕ) (hk : k < m) (s : SatSym) :
    (blkOut m k s).length = 3 * RW m := by
  cases s <;> simp [blkOut, one, RW] <;> omega

theorem ham_getD_blkIn (m k : ℕ) (s : SatSym) (o : ℕ) :
    (blkIn m k s).getD o zero = pos ↔
      (s = pos ∧ o = 11 + 9 * k) ∨ (s = neg ∧ o = 14 + 9 * k) := by
  cases s <;> simp only [blkIn, ham_getD_one_zs, ham_getD_zs] <;> simp

theorem ham_getD_blkOut (m k : ℕ) (s : SatSym) (o : ℕ) :
    (blkOut m k s).getD o zero = pos ↔
      (s = pos ∧ o = 12 + 9 * k) ∨ (s = neg ∧ o = 9 + 9 * k) := by
  cases s <;> simp only [blkOut, ham_getD_one_zs, ham_getD_zs] <;> simp

/-! ## Entries of `H w` -/

theorem ham_length_rowsC (w : List SatSym) (k : ℕ) : (rowsC w k).length = 3 := rfl
theorem ham_length_rowsV (m j t : ℕ) : (rowsV m j t).length = 3 := rfl

theorem ham_getD_inC (w : List SatSym) (k : ℕ) (hk : k < mC w) (v : ℕ) :
    (inC w k).getD v zero = pos ↔ v = 3 * k + 1 ∨ ∃ j < NV w,
      (sy w k j = pos ∧ v = 3 * mC w + j * (3 * RW (mC w)) + 11 + 9 * k) ∨
      (sy w k j = neg ∧ v = 3 * mC w + j * (3 * RW (mC w)) + 14 + 9 * k) := by
  unfold inC
  rw [ham_Q_getD_append zero (· = pos) ham_pos_ne_zero, ham_getD_one_zs]
  simp only [ham_Q_getD_flatMap zero (· = pos) ham_pos_ne_zero (3 * RW (mC w))
      (fun j => blkIn (mC w) k (sy w k j)) (fun j => ham_length_blkIn _ _ hk _)]
  simp only [ham_getD_blkIn, List.length_append, List.length_replicate, one,
    List.length_singleton]
  constructor
  · rintro (h | ⟨u', rfl, j, hj, o, rfl, (⟨hs, rfl⟩ | ⟨hs, rfl⟩)⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, Or.inl ⟨hs, by omega⟩⟩
    · exact Or.inr ⟨j, hj, Or.inr ⟨hs, by omega⟩⟩
  · rintro (h | ⟨j, hj, (⟨hs, rfl⟩ | ⟨hs, rfl⟩)⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j * (3 * RW (mC w)) + (11 + 9 * k), by omega,
        j, hj, _, rfl, Or.inl ⟨hs, rfl⟩⟩
    · exact Or.inr ⟨j * (3 * RW (mC w)) + (14 + 9 * k), by omega,
        j, hj, _, rfl, Or.inr ⟨hs, rfl⟩⟩

theorem ham_getD_outC (w : List SatSym) (k : ℕ) (hk : k < mC w) (v : ℕ) :
    (outC w k).getD v zero = pos ↔ ∃ j < NV w,
      (sy w k j = pos ∧ v = 3 * mC w + j * (3 * RW (mC w)) + 12 + 9 * k) ∨
      (sy w k j = neg ∧ v = 3 * mC w + j * (3 * RW (mC w)) + 9 + 9 * k) := by
  unfold outC
  rw [ham_Q_getD_append zero (· = pos) ham_pos_ne_zero]
  simp only [ham_Q_getD_flatMap zero (· = pos) ham_pos_ne_zero (3 * RW (mC w))
      (fun j => blkOut (mC w) k (sy w k j)) (fun j => ham_length_blkOut _ _ hk _)]
  simp only [ham_getD_blkOut, ham_getD_zs, false_or, List.length_replicate]
  constructor
  · rintro ⟨u', rfl, j, hj, o, rfl, (⟨hs, rfl⟩ | ⟨hs, rfl⟩)⟩
    · exact ⟨j, hj, Or.inl ⟨hs, by omega⟩⟩
    · exact ⟨j, hj, Or.inr ⟨hs, by omega⟩⟩
  · rintro ⟨j, hj, (⟨hs, rfl⟩ | ⟨hs, rfl⟩)⟩
    · exact ⟨j * (3 * RW (mC w)) + (12 + 9 * k), by omega, j, hj, _, rfl, Or.inl ⟨hs, rfl⟩⟩
    · exact ⟨j * (3 * RW (mC w)) + (9 + 9 * k), by omega, j, hj, _, rfl, Or.inr ⟨hs, rfl⟩⟩

/-- The `pos` entries of `H w`, by rows. -/
theorem ham_ent_H (w : List SatSym) (u v : ℕ) :
    ent (H w) u v = pos ↔
      (∃ k < mC w, ∃ r, u = k * 3 + r ∧
        ((r = 0 ∧ (inC w k).getD v zero = pos) ∨ (r = 1 ∧ v = 3 * k + 2) ∨
          (r = 2 ∧ (outC w k).getD v zero = pos))) ∨
      (∃ j < NV w, ∃ t < RW (mC w), ∃ r,
        u = 3 * mC w + j * (RW (mC w) * 3) + t * 3 + r ∧
        ((r = 0 ∧ v = 3 * (mC w + j * RW (mC w) + t) + 1) ∨
          (r = 1 ∧ v = 3 * (mC w + j * RW (mC w) + t) + 2) ∨
          (r = 2 ∧ (outV (mC w) j t).getD v zero = pos))) ∨
      (∃ r, u = 3 * mC w + NV w * (RW (mC w) * 3) + r ∧
        ((r = 0 ∧ v = 3 * (mC w + NV w * RW (mC w)) + 1) ∨
          (r = 1 ∧ v = 3 * (mC w + NV w * RW (mC w)) + 2) ∨ (r = 2 ∧ v = 3 * mC w))) := by
  set Q : List SatSym → Prop := fun row => row.getD v zero = pos with hQdef
  have hQ : ¬ Q [] := by simp [Q]
  have hlen1 : ((List.range (mC w)).flatMap (rowsC w)).length = 3 * mC w := by
    simp [List.length_flatMap, rowsC]; ring
  have hlen2 : ((List.range (NV w)).flatMap
      (fun j => (List.range (RW (mC w))).flatMap (rowsV (mC w) j))).length =
        NV w * (RW (mC w) * 3) := by
    simp [List.length_flatMap, rowsV]
  have hB : ∀ j, ((List.range (RW (mC w))).flatMap (rowsV (mC w) j)).length = RW (mC w) * 3 := by
    intro j; simp [List.length_flatMap, rowsV]
  unfold ent
  show Q _ ↔ _
  rw [clauses_H, hRows, ham_Q_getD_append [] Q hQ, ham_Q_getD_append [] Q hQ,
    ham_Q_getD_flatMap [] Q hQ 3 (rowsC w) (ham_length_rowsC w), hlen1]
  simp only [ham_Q_getD_flatMap [] Q hQ _ _ hB, List.length_append, hlen1, hlen2,
    ham_Q_getD_flatMap [] Q hQ 3 (rowsV (mC w) _) (ham_length_rowsV (mC w) _)]
  simp only [rowsC, rowsV, rowsZ, ham_Q_getD_three [] Q _ _ _ _ hQ, Q, ham_getD_one]
  constructor
  · rintro ((h | ⟨u', rfl, j, hj, o, rfl, t, ht, r, rfl, h⟩) | ⟨r, rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨j, hj, t, ht, r, by ring, h⟩)
    · exact Or.inr (Or.inr ⟨r, rfl, h⟩)
  · rintro (h | ⟨j, hj, t, ht, r, rfl, h⟩ | ⟨r, rfl, h⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨j * (RW (mC w) * 3) + (t * 3 + r), by ring, j, hj, _, rfl, t, ht, r,
        rfl, h⟩)
    · exact Or.inr ⟨r, rfl, h⟩

theorem ham_d1_lt (R t : ℕ) (hR : 4 ≤ R) (ht : t < R) : d1 t < d2 R t := by
  unfold d1 d2; split_ifs <;> omega

theorem ham_d2_le (R t : ℕ) (hR : 4 ≤ R) (ht : t < R) : d2 R t ≤ R := by
  unfold d2; split_ifs <;> omega

theorem ham_RW_ge (m : ℕ) : 4 ≤ RW m := by unfold RW; omega

theorem ham_jR_lt {j N R : ℕ} (hj : j < N) : j * R + R ≤ N * R := by
  have := Nat.mul_le_mul_right R (show j + 1 ≤ N by omega)
  rw [Nat.add_mul, Nat.one_mul] at this; exact this

theorem ham_getD_outV (m j t v : ℕ) (ht : t < RW m) :
    (outV m j t).getD v zero = pos ↔
      v = 3 * (m + j * RW m + d1 t) ∨ v = 3 * (m + j * RW m + d2 (RW m) t) := by
  have h1 := ham_d1_lt (RW m) t (ham_RW_ge m) ht
  rw [outV, ham_getD_two]
  omega

/-- The arcs of `DA w` stay below `VV w`. -/
theorem DA_lt (w : List SatSym) {x y : ℕ} (h : DA w x y) : x < VV w ∧ y < VV w := by
  have hR := ham_RW_ge (mC w)
  unfold VV
  unfold DA at h
  rcases h with ⟨j, hj, t, ht, rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨k, hk, j, hj, -, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨k, hk, j, hj, -, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
  · have := ham_jR_lt (R := RW (mC w)) hj
    have := ham_d1_lt _ t hR ht
    have := ham_d2_le _ t hR ht
    omega
  · have := ham_jR_lt (R := RW (mC w)) hj
    have := ham_d2_le _ t hR ht
    omega
  · omega
  · have := ham_jR_lt (R := RW (mC w)) hj
    unfold RW at *; omega
  · have := ham_jR_lt (R := RW (mC w)) hj
    unfold RW at *; omega
  · have := ham_jR_lt (R := RW (mC w)) hj
    unfold RW at *; omega
  · have := ham_jR_lt (R := RW (mC w)) hj
    unfold RW at *; omega

/-- The stored `pos` entries of `H w`: the edges inside the triples, the out-rows of the non-clause
vertices and of the clause vertices (arcs `x → y` with `y ≥ m`, stored at `(3x + 2, 3y)`), and the
in-rows of the clause vertices (arcs `x → k`, stored at `(3k, 3x + 2)`). -/
def EntP (w : List SatSym) (u v : ℕ) : Prop :=
  (∃ x < VV w, u = 3 * x ∧ v = 3 * x + 1) ∨ (∃ x < VV w, u = 3 * x + 1 ∧ v = 3 * x + 2) ∨
  (∃ x y, DA w x y ∧ mC w ≤ y ∧ u = 3 * x + 2 ∧ v = 3 * y) ∨
  (∃ x y, DA w x y ∧ y < mC w ∧ u = 3 * y ∧ v = 3 * x + 2)

theorem ham_ent_iff (w : List SatSym) (u v : ℕ) : ent (H w) u v = pos ↔ EntP w u v := by
  have hR := ham_RW_ge (mC w)
  have e3 : ∀ j, j * (3 * RW (mC w)) = 3 * (j * RW (mC w)) := fun j => by ring
  have e3' : ∀ j, j * (RW (mC w) * 3) = 3 * (j * RW (mC w)) := fun j => by ring
  rw [ham_ent_H]
  unfold EntP
  constructor
  · rintro (⟨k, hk, r, rfl, h⟩ | ⟨j, hj, t, ht, r, rfl, h⟩ | ⟨r, rfl, h⟩)
    · rcases h with ⟨rfl, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h⟩
      · rw [ham_getD_inC w k hk] at h
        rcases h with rfl | ⟨j, hj, (⟨hs, rfl⟩ | ⟨hs, rfl⟩)⟩
        · exact Or.inl ⟨k, by unfold VV; omega, by ring, rfl⟩
        · refine Or.inr (Or.inr (Or.inr ⟨mC w + j * RW (mC w) + 3 + 3 * k, k, ?_, hk, by ring,
            by rw [e3]; ring⟩))
          exact Or.inr (Or.inr (Or.inl ⟨k, hk, j, hj, hs, Or.inl ⟨rfl, rfl⟩⟩))
        · refine Or.inr (Or.inr (Or.inr ⟨mC w + j * RW (mC w) + 4 + 3 * k, k, ?_, hk, by ring,
            by rw [e3]; ring⟩))
          exact Or.inr (Or.inr (Or.inr ⟨k, hk, j, hj, hs, Or.inl ⟨rfl, rfl⟩⟩))
      · exact Or.inr (Or.inl ⟨k, by unfold VV; omega, by ring, rfl⟩)
      · rw [ham_getD_outC w k hk] at h
        rcases h with ⟨j, hj, (⟨hs, rfl⟩ | ⟨hs, rfl⟩)⟩
        · refine Or.inr (Or.inr (Or.inl ⟨k, mC w + j * RW (mC w) + 4 + 3 * k, ?_, by omega,
            by ring, by rw [e3]; ring⟩))
          exact Or.inr (Or.inr (Or.inl ⟨k, hk, j, hj, hs, Or.inr ⟨rfl, rfl⟩⟩))
        · refine Or.inr (Or.inr (Or.inl ⟨k, mC w + j * RW (mC w) + 3 + 3 * k, ?_, by omega,
            by ring, by rw [e3]; ring⟩))
          exact Or.inr (Or.inr (Or.inr ⟨k, hk, j, hj, hs, Or.inr ⟨rfl, rfl⟩⟩))
    · have hb := ham_jR_lt (R := RW (mC w)) hj
      have hx : mC w + j * RW (mC w) + t < VV w := by unfold VV; omega
      rw [e3']
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h⟩
      · exact Or.inl ⟨_, hx, by ring, rfl⟩
      · exact Or.inr (Or.inl ⟨_, hx, by ring, rfl⟩)
      · rw [ham_getD_outV _ _ _ _ ht] at h
        rcases h with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl ⟨_, _, Or.inl ⟨j, hj, t, ht, rfl, Or.inl rfl⟩,
            by omega, by ring, rfl⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨_, _, Or.inl ⟨j, hj, t, ht, rfl, Or.inr rfl⟩,
            by omega, by ring, rfl⟩))
    · have hx : mC w + NV w * RW (mC w) < VV w := by unfold VV; omega
      rw [e3']
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨_, hx, by ring, rfl⟩
      · exact Or.inr (Or.inl ⟨_, hx, by ring, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl⟩), le_rfl, by ring, rfl⟩))
  · -- decomposition of a vertex below `VV w`
    have dec : ∀ x < VV w, x < mC w ∨
        (∃ j < NV w, ∃ t < RW (mC w), x = mC w + j * RW (mC w) + t) ∨
        x = mC w + NV w * RW (mC w) := by
      intro x hx
      unfold VV at hx
      rcases Nat.lt_or_ge x (mC w) with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge (x - mC w) (NV w * RW (mC w)) with h' | h'
        · refine Or.inr (Or.inl ⟨(x - mC w) / RW (mC w), ?_, (x - mC w) % RW (mC w),
            Nat.mod_lt _ (by omega), ?_⟩)
          · exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h')
          · have := Nat.div_add_mod (x - mC w) (RW (mC w))
            rw [Nat.mul_comm] at this; omega
        · exact Or.inr (Or.inr (by omega))
    rintro (⟨x, hx, rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩ | ⟨x, y, hxy, hy, rfl, rfl⟩ |
      ⟨x, y, hxy, hy, rfl, rfl⟩)
    · rcases dec x hx with h | ⟨j, hj, t, ht, rfl⟩ | rfl
      · exact Or.inl ⟨x, h, 0, by ring, Or.inl ⟨rfl, (ham_getD_inC w x h _).2 (Or.inl rfl)⟩⟩
      · exact Or.inr (Or.inl ⟨j, hj, t, ht, 0, by rw [e3']; ring, Or.inl ⟨rfl, rfl⟩⟩)
      · exact Or.inr (Or.inr ⟨0, by rw [e3']; ring, Or.inl ⟨rfl, rfl⟩⟩)
    · rcases dec x hx with h | ⟨j, hj, t, ht, rfl⟩ | rfl
      · exact Or.inl ⟨x, h, 1, by ring, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
      · exact Or.inr (Or.inl ⟨j, hj, t, ht, 1, by rw [e3']; ring, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
      · exact Or.inr (Or.inr ⟨1, by rw [e3']; ring, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
    · rcases hxy with ⟨j, hj, t, ht, rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨k, hk, j, hj, hs, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨k, hk, j, hj, hs, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact Or.inr (Or.inl ⟨j, hj, t, ht, 2, by rw [e3']; ring,
          Or.inr (Or.inr ⟨rfl, (ham_getD_outV _ _ _ _ ht).2 (Or.inl rfl)⟩)⟩)
      · exact Or.inr (Or.inl ⟨j, hj, t, ht, 2, by rw [e3']; ring,
          Or.inr (Or.inr ⟨rfl, (ham_getD_outV _ _ _ _ ht).2 (Or.inr rfl)⟩)⟩)
      · exact Or.inr (Or.inr ⟨2, by rw [e3']; ring, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)
      · omega
      · exact Or.inl ⟨x, hk, 2, by ring, Or.inr (Or.inr ⟨rfl,
          (ham_getD_outC w x hk _).2 ⟨j, hj, Or.inl ⟨hs, by rw [e3]; ring⟩⟩⟩)⟩
      · omega
      · exact Or.inl ⟨x, hk, 2, by ring, Or.inr (Or.inr ⟨rfl,
          (ham_getD_outC w x hk _).2 ⟨j, hj, Or.inr ⟨hs, by rw [e3]; ring⟩⟩⟩)⟩
    · rcases hxy with ⟨j, hj, t, ht, rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨k, hk, j, hj, hs, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨k, hk, j, hj, hs, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · omega
      · omega
      · omega
      · exact Or.inl ⟨y, hk, 0, by ring, Or.inl ⟨rfl,
          (ham_getD_inC w y hk _).2 (Or.inr ⟨j, hj, Or.inl ⟨hs, by rw [e3]; ring⟩⟩)⟩⟩
      · omega
      · exact Or.inl ⟨y, hk, 0, by ring, Or.inl ⟨rfl,
          (ham_getD_inC w y hk _).2 (Or.inr ⟨j, hj, Or.inr ⟨hs, by rw [e3]; ring⟩⟩)⟩⟩
      · omega

/-- **The adjacency of `H w` is the split of `DA w`.** -/
theorem adj_H_iff (w : List SatSym) (u v : ℕ) :
    adjU (H w) u v ↔ SplitAdj (VV w) (DA w) u v := by
  unfold adjU SplitAdj
  rw [ham_ent_iff, ham_ent_iff]
  unfold EntP
  constructor
  · rintro ((⟨x, hx, rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩ | ⟨x, y, h, -, rfl, rfl⟩ |
        ⟨x, y, h, -, rfl, rfl⟩) | (⟨x, hx, rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩ | ⟨x, y, h, -, rfl, rfl⟩ |
        ⟨x, y, h, -, rfl, rfl⟩))
    · exact Or.inl ⟨x, hx, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨x, hx, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact Or.inr ⟨x, y, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨x, y, h, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨x, hx, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact Or.inl ⟨x, hx, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · exact Or.inr ⟨x, y, h, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨x, y, h, Or.inl ⟨rfl, rfl⟩⟩
  · rintro (⟨x, hx, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ |
      ⟨x, y, h, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩)
    · exact Or.inl (Or.inl ⟨x, hx, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨x, hx, rfl, rfl⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨x, hx, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨x, hx, rfl, rfl⟩))
    · rcases Nat.lt_or_ge y (mC w) with hy | hy
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨x, y, h, hy, rfl, rfl⟩)))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨x, y, h, hy, rfl, rfl⟩)))
    · rcases Nat.lt_or_ge y (mC w) with hy | hy
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨x, y, h, hy, rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, h, hy, rfl, rfl⟩)))

end Pnp.Karp.Ham
