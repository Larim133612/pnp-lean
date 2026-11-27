import Pnp.Karp.ThreeDM
import Pnp.Karp.SubProg

/-!
# The 3DM / X3C reduction program, part 1: primitives, one-hot rows, the printing form

A stack program printing `DMI w` / `X3I w` (`Pnp/Karp/ThreeDM.lean`), on the layout `st2` of
`Pnp/Karp/CliqueGen.lean` with the printing primitives of `Pnp/Karp/SubGen.lean`.

* `mg_zsL l` prints `∑_{r ∈ l} v r` zeros; `mg_ohC s` prints a one-hot block
  `zero^a ++ pos :: zero^b` (`mg_ohOut a b`), the counts `a`, `b` being sums of registers plus
  small constants; `mg_rowC` prints three blocks and `sep` (the row of a triple, `mg_tOut`).
* `mg_loop`: a generic counter loop.
* `mg_out_eq`: the instance as a concatenation of the printed sections.
-/

namespace Pnp.Karp.ThreeDM

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum

/-! ## Runs of zeros given by registers -/

/-- Print `v r` zeros for each `r ∈ l`. -/
def mg_zsL : List ℕ → Cmd
  | [] => .skip
  | r :: l => .seq (sg_zsC r) (mg_zsL l)

/-- The sum of the registers `l`. -/
def mg_sum (v : ℕ → ℕ) (l : List ℕ) : ℕ := (l.map v).sum

@[simp] theorem mg_sum_nil (v : ℕ → ℕ) : mg_sum v [] = 0 := rfl
@[simp] theorem mg_sum_cons (v : ℕ → ℕ) (r : ℕ) (l : List ℕ) :
    mg_sum v (r :: l) = v r + mg_sum v l := by simp [mg_sum]

theorem mg_em_zsL (U : ℕ) {v : ℕ → ℕ} (h7 : v 7 = 0) (h11 : v 11 = 0) : ∀ l : List ℕ,
    (∀ r ∈ l, 5 ≤ r ∧ r ≠ 7 ∧ r ≠ 11 ∧ v r ≤ U) →
    sg_Em (mg_zsL l) v (List.replicate (mg_sum v l) zero) (l.length * (9 * U + 6) + 1)
  | [], _ => fun _ _ _ _ => (ExecLe.skip _).cast (by simp) (by simp)
  | r :: l, h => by
    obtain ⟨a, b, c, d⟩ := h r (by simp)
    have := (sg_em_zsC a b c h7 h11).seq
      (mg_em_zsL U h7 h11 l (fun r' hr => h r' (by simp [hr])))
    refine this.cast ?_ ?_
    · simp
    · rw [List.length_cons, Nat.add_mul, Nat.one_mul]; omega

/-! ## One-hot blocks and rows -/

/-- A one-hot block `zero^a ++ pos :: zero^b`. -/
def mg_ohOut (a b : ℕ) : List SatSym := List.replicate a zero ++ pos :: List.replicate b zero

theorem mg_oh_eq {q a : ℕ} (h : a < q) : oh q a = mg_ohOut a (q - 1 - a) := by
  apply List.ext_getElem
  · simp [oh, mg_ohOut]; omega
  · intro n h1 h2
    simp only [oh, mg_ohOut, List.getElem_map, List.getElem_range, List.getElem_append,
      List.length_replicate, List.getElem_replicate, List.getElem_cons]
    by_cases h3 : n < a
    · simp [h3, show n ≠ a by omega]
    · by_cases h4 : n = a
      · subst h4; simp
      · simp [h3, h4, show n - a ≠ 0 by omega]

/-- The specification of a printed block: registers before, constant zeros before / after the
`pos`, registers after. -/
structure mg_S where
  pre : List ℕ
  e1 : ℕ
  e2 : ℕ
  post : List ℕ

/-- Print a one-hot block. -/
def mg_ohC (s : mg_S) : Cmd :=
  .seq (mg_zsL s.pre) (.seq (emL (List.replicate s.e1 zero ++ pos :: List.replicate s.e2 zero))
    (mg_zsL s.post))

/-- Admissible block specifications. -/
def mg_V (U : ℕ) (v : ℕ → ℕ) (s : mg_S) : Prop :=
  (∀ r ∈ s.pre ++ s.post, 5 ≤ r ∧ r ≠ 7 ∧ r ≠ 11 ∧ v r ≤ U) ∧ s.pre.length ≤ 3 ∧
    s.post.length ≤ 3 ∧ s.e1 + s.e2 ≤ 1

def mg_ohT (U : ℕ) : ℕ := 6 * (9 * U + 6) + 7

theorem mg_em_oh (U : ℕ) {v : ℕ → ℕ} (h7 : v 7 = 0) (h11 : v 11 = 0) (s : mg_S)
    (hs : mg_V U v s) :
    sg_Em (mg_ohC s) v (mg_ohOut (mg_sum v s.pre + s.e1) (s.e2 + mg_sum v s.post)) (mg_ohT U) := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have a := mg_em_zsL U h7 h11 s.pre (fun r hr => h1 r (by simp [hr]))
  have b := mg_em_zsL U h7 h11 s.post (fun r hr => h1 r (by simp [hr]))
  have c := sg_em_emL (List.replicate s.e1 zero ++ pos :: List.replicate s.e2 zero) v
  refine (a.seq (c.seq b)).cast ?_ ?_
  · simp only [mg_ohOut, List.append_assoc, List.cons_append, ← List.replicate_append_replicate]
  · have k1 : s.pre.length * (9 * U + 6) ≤ 3 * (9 * U + 6) := Nat.mul_le_mul_right _ h2
    have k2 : s.post.length * (9 * U + 6) ≤ 3 * (9 * U + 6) := Nat.mul_le_mul_right _ h3
    simp only [List.length_append, List.length_replicate, List.length_cons]
    unfold mg_ohT; omega

/-- The printed row of a triple (with its `sep`). -/
def mg_tOut (q : ℕ) (t : ℕ × ℕ × ℕ) : List SatSym :=
  mg_ohOut t.1 (q - 1 - t.1) ++ (mg_ohOut t.2.1 (q - 1 - t.2.1) ++
    (mg_ohOut t.2.2 (q - 1 - t.2.2) ++ [sep]))

theorem mg_triRow_eq {q : ℕ} {t : ℕ × ℕ × ℕ} (h1 : t.1 < q) (h2 : t.2.1 < q) (h3 : t.2.2 < q) :
    triRow q t ++ [sep] = mg_tOut q t := by
  simp [triRow, mg_tOut, mg_oh_eq h1, mg_oh_eq h2, mg_oh_eq h3]

/-- Print a row. -/
def mg_rowC (s1 s2 s3 : mg_S) : Cmd :=
  .seq (mg_ohC s1) (.seq (mg_ohC s2) (.seq (mg_ohC s3) (emL [sep])))

def mg_rowT (U : ℕ) : ℕ := 3 * mg_ohT U + 3

theorem mg_em_row (U q a b c : ℕ) {v : ℕ → ℕ} (h7 : v 7 = 0) (h11 : v 11 = 0) (s1 s2 s3 : mg_S)
    (V1 : mg_V U v s1) (V2 : mg_V U v s2) (V3 : mg_V U v s3)
    (ha : mg_sum v s1.pre + s1.e1 = a) (ha' : s1.e2 + mg_sum v s1.post = q - 1 - a)
    (hb : mg_sum v s2.pre + s2.e1 = b) (hb' : s2.e2 + mg_sum v s2.post = q - 1 - b)
    (hc : mg_sum v s3.pre + s3.e1 = c) (hc' : s3.e2 + mg_sum v s3.post = q - 1 - c) :
    sg_Em (mg_rowC s1 s2 s3) v (mg_tOut q (a, b, c)) (mg_rowT U) := by
  have x := mg_em_oh U h7 h11 s1 V1
  have y := mg_em_oh U h7 h11 s2 V2
  have z := mg_em_oh U h7 h11 s3 V3
  rw [ha, ha'] at x
  rw [hb, hb'] at y
  rw [hc, hc'] at z
  exact (x.seq (y.seq (z.seq (sg_em_emL [sep] v)))).cast rfl (by unfold mg_rowT; simp; omega)

/-! ## A generic counter loop -/

theorem mg_loop {c : ℕ} (hc : 5 ≤ c) {B : Cmd} (W Q : Str) (Os : ℕ → Str)
    (P : ℕ → (ℕ → ℕ) → Prop) (out : ℕ → List SatSym) (T jend : ℕ)
    (hP : ∀ j u x, P j u → P j (update u c x))
    (hB : ∀ j u E, j < jend → P j u → ∃ u', P (j + 1) u' ∧ u' c = u c ∧
      ExecLe B (st2 W (Os j) Q (rv E) u) (.norm (st2 W (Os (j + 1)) Q (rv (E ++ out j)) u')) T) :
    ∀ (n j : ℕ) (E : List SatSym) (v : ℕ → ℕ), j + n ≤ jend → P j v → v c = n →
    ∃ v', P (j + n) v' ∧ v' c = 0 ∧
      ExecLe (.loop (.pop c .brk B B)) (st2 W (Os j) Q (rv E) v)
        (.norm (st2 W (Os (j + n)) Q (rv (E ++ (List.range' j n).flatMap out)) v'))
        (n * (T + 1) + 2)
  | 0, j, E, v, _, hv, hn => ⟨v, hv, hn,
      (Ham.hg_cend (by rw [st2_reg hc, hn]; rfl)).cast (by simp) (by simp)⟩
  | n + 1, j, E, v, hj, hv, hn => by
    obtain ⟨u1, p1, c1, e1⟩ := hB j (update v c n) E (by omega) (hP j v n hv)
    obtain ⟨v', p2, c2, e2⟩ := mg_loop hc W Q Os P out T jend hP hB n (j + 1) (E ++ out j) u1
      (by omega) p1 (by rw [c1]; simp)
    refine ⟨v', by rwa [show j + (n + 1) = j + 1 + n by omega], c2,
      (Ham.hg_cstep (n := n) (by rw [st2_reg hc, hn]) (by rw [upd2_reg hc]; exact e1) e2).cast ?_
        ?_⟩
    · rw [show j + (n + 1) = j + 1 + n by omega, List.range'_succ, List.flatMap_cons,
        List.append_assoc]
    · rw [Nat.succ_mul]; omega

/-! ## The printed sections -/

/-- The two ring rows of variable `i` at a clause index `k < m - 1`. -/
def mg_regO (q m i k : ℕ) : List SatSym :=
  mg_tOut q (2 * (m * i + k) + 1, m * i + k, m * i + k) ++
    mg_tOut q (2 * (m * i + k), m * i + k + 1, m * i + k)

/-- The two ring rows of variable `i` at the clause index `m - 1`. -/
def mg_spcO (q m i : ℕ) : List SatSym :=
  mg_tOut q (2 * (m * i + (m - 1)) + 1, m * i + (m - 1), m * i + (m - 1)) ++
    mg_tOut q (2 * (m * i + (m - 1)), m * i, m * i + (m - 1))

/-- The ring rows of variable `i`. -/
def mg_ringO (q m i : ℕ) : List SatSym :=
  (List.range' 0 (m - 1)).flatMap (mg_regO q m i) ++ mg_spcO q m i

/-- All ring rows. -/
def mg_ringP (q N m : ℕ) : List SatSym :=
  (List.range' 0 (if m = 0 then 0 else N)).flatMap (mg_ringO q m)

/-- The clause row of symbol `s` at position `j` of clause `k` (`M = N m`). -/
def mg_symO (q M m k j : ℕ) : SatSym → List SatSym
  | pos => mg_tOut q (2 * (m * j + k), M + k, M + k)
  | neg => mg_tOut q (2 * (m * j + k) + 1, M + k, M + k)
  | _ => []

/-- The clause rows of the symbols `c` of clause `k`, from position `j` on. -/
def mg_scanO (q M m k : ℕ) : ℕ → List SatSym → List SatSym
  | _, [] => []
  | j, s :: c => mg_symO q M m k j s ++ mg_scanO q M m k (j + 1) c

/-- All clause rows. -/
def mg_clP (q M m : ℕ) (cs : List (List SatSym)) : List SatSym :=
  (List.range' 0 m).flatMap (fun k => mg_scanO q M m k 0 (cs.getD k []))

/-- All garbage rows. -/
def mg_garP (q M m : ℕ) : List SatSym :=
  (List.range' 0 q).flatMap
    (fun x => (List.range' 0 (M - m)).flatMap (fun t => mg_tOut q (x, M + m + t, M + m + t)))

/-- The instance with header `zero^(hd q)` (`hd = 1`: `DMI`, `hd = 3`: `X3I`). -/
def mg_out (hd : ℕ) (w : List SatSym) : List SatSym :=
  (List.replicate (hd * qB w) zero :: triRows w).flatMap (· ++ [sep])

theorem mg_DMI (w : List SatSym) : DMI w = mg_out 1 w := by simp [DMI, mg_out]

theorem mg_X3I (w : List SatSym) : X3I w = mg_out 3 w := rfl

theorem mg_scanO_eq (q M m k : ℕ) : ∀ (c : List SatSym) (j : ℕ), mg_scanO q M m k j c =
    (List.range c.length).flatMap (fun i => mg_symO q M m k (j + i) (c.getD i zero))
  | [], _ => rfl
  | a :: c, j => by
    rw [mg_scanO, mg_scanO_eq q M m k c (j + 1), List.length_cons, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine List.flatMap_congr fun i _ => ?_
    rw [show j + 1 + i = j + (i + 1) by omega]

theorem mg_ring_eq (q N m : ℕ) (hq : q = 2 * (N * m)) :
    ((List.range N).flatMap (fun i => (List.range m).flatMap fun k => ringT m i k)).flatMap
      (fun t => triRow q t ++ [sep]) = mg_ringP q N m := by
  unfold mg_ringP
  rw [List.flatMap_assoc]
  by_cases hm : m = 0
  · subst hm; simp
  rw [if_neg hm, ← List.range_eq_range']
  refine List.flatMap_congr fun i hi => ?_
  have hi := List.mem_range.1 hi
  have hb : m * i + m ≤ N * m := by
    have := Nat.mul_le_mul_left m (show i + 1 ≤ N by omega)
    rw [Nat.mul_succ, Nat.mul_comm m N] at this; exact this
  rw [List.flatMap_assoc, show List.range m = List.range (m - 1) ++ [m - 1] by
    rw [← List.range_succ]; congr; omega, List.flatMap_append, mg_ringO, ← List.range_eq_range']
  congr 1
  · refine List.flatMap_congr fun k hk => ?_
    have hk := List.mem_range.1 hk
    rw [ringT, Nat.mod_eq_of_lt (show k + 1 < m by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, tipI, Bool.false_eq_true,
      if_false, if_true, Nat.add_zero]
    rw [mg_triRow_eq (by simp; omega) (by simp; omega) (by simp; omega),
      mg_triRow_eq (by simp; omega) (by simp; omega) (by simp; omega)]
    rfl
  · rw [List.flatMap_singleton, ringT, Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.mod_self]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, tipI, Bool.false_eq_true,
      if_false, if_true, Nat.add_zero]
    rw [mg_triRow_eq (by simp; omega) (by simp; omega) (by simp; omega),
      mg_triRow_eq (by simp; omega) (by simp; omega) (by simp; omega)]
    rfl

theorem mg_cl_eq (w : List SatSym) :
    ((List.range (mC w)).flatMap (fun k => (List.range ((clauses w).getD k []).length).flatMap
      fun j => clT (NV w) (mC w) k j (sy w k j))).flatMap (fun t => triRow (qB w) t ++ [sep]) =
      mg_clP (qB w) (NV w * mC w) (mC w) (clauses w) := by
  unfold mg_clP
  rw [List.flatMap_assoc, ← List.range_eq_range']
  refine List.flatMap_congr fun k hk => ?_
  have hk : k < mC w := List.mem_range.1 hk
  obtain ⟨-, hl⟩ := Ham.hg_clause_facts w k hk
  have hNV : Ham.NV w = NV w := rfl
  rw [hNV] at hl
  rw [List.flatMap_assoc, mg_scanO_eq]
  refine List.flatMap_congr fun j hj => ?_
  have hj : j < ((clauses w).getD k []).length := List.mem_range.1 hj
  have hb : mC w * j + mC w ≤ NV w * mC w := by
    have := Nat.mul_le_mul_left (mC w) (show j + 1 ≤ NV w by omega)
    rw [Nat.mul_succ, Nat.mul_comm (mC w) (NV w)] at this; exact this
  have hq : qB w = 2 * (NV w * mC w) := by unfold qB; ring
  rw [Nat.zero_add]
  show _ = mg_symO (qB w) (NV w * mC w) (mC w) k j (sy w k j)
  cases sy w k j with
  | pos =>
    simp only [clT, tipI, List.flatMap_cons, List.flatMap_nil, List.append_nil, if_true,
      Nat.add_zero]
    rw [mg_triRow_eq (by simp; omega) (by simp; omega) (by simp; omega)]; rfl
  | neg =>
    simp only [clT, tipI, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Bool.false_eq_true, if_false]
    rw [mg_triRow_eq (by simp; omega) (by simp; omega) (by simp; omega)]; rfl
  | zero => rfl
  | sep => rfl

theorem mg_gar_eq (q N m : ℕ) (hq : q = 2 * (N * m)) :
    ((List.range q).flatMap (fun x => garT N m x)).flatMap (fun t => triRow q t ++ [sep]) =
      mg_garP q (N * m) m := by
  unfold mg_garP
  rw [List.flatMap_assoc]
  simp only [← List.range_eq_range']
  refine List.flatMap_congr fun x hx => ?_
  have hx := List.mem_range.1 hx
  rw [garT, List.flatMap_map, show m * (N - 1) = N * m - m by
    rw [Nat.mul_sub_one, Nat.mul_comm]]
  refine List.flatMap_congr fun t ht => ?_
  have ht := List.mem_range.1 ht
  rw [mg_triRow_eq (by simp; omega) (by simp; omega) (by simp; omega)]

/-- **The instance as printed by the program.** -/
theorem mg_out_eq (hd : ℕ) (w : List SatSym) : mg_out hd w =
    List.replicate (hd * qB w) zero ++ [sep] ++ mg_ringP (qB w) (NV w) (mC w) ++
      mg_clP (qB w) (NV w * mC w) (mC w) (clauses w) ++ mg_garP (qB w) (NV w * mC w) (mC w) := by
  have hq : qB w = 2 * (NV w * mC w) := by unfold qB; ring
  unfold mg_out triRows tris
  rw [List.flatMap_cons, List.flatMap_map, List.flatMap_append, List.flatMap_append,
    mg_ring_eq _ _ _ hq, mg_cl_eq, mg_gar_eq _ _ _ hq]
  simp only [List.append_assoc]

end Pnp.Karp.ThreeDM
