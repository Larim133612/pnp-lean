import Pnp.Karp.SubGen
import Pnp.Karp.HamGen

/-!
# The SUBSET SUM reduction program, part 2: the loops, the whole program, SAT ≤ₚ SUBSET SUM

`sg_redCmd` (rows and primitives: `Pnp/Karp/SubGen.lean`), on the bit string `x` on stack `0`:

1. `parseLoop`, `trimC 4`, `move 4 2` (as for CLIQUE): stack `2` holds the code `W` of
   `trunc w`, `w = dec2 x`; `sg_cntLoop`: `N = |trunc w| + 1` (register `5`), `m` (`9`);
2. the target row `sg_tgtC`;
3. `sg_jLoop`: the rows `tP j`, `fP j` for `j < N`;
4. `sg_clLoop` (scanning `trunc w` on stack `3`): the rows `wP k j (sy w k j)`;
5. `sg_fkLoop`: the filler rows.

`sg_SS_eq` shows that this prints `SS w`; `sg_exec_redCmd` bounds the run by a polynomial, and
`sat_le_ss_of` follows from `FunBridge.computable_of_cmd_code`.
-/

namespace Pnp.Karp.SubsetSum

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique

/-! ## Register steps -/

section Reg
variable {W O Q : Str}

theorem sg_ex_dec {r : ℕ} (hr : 5 ≤ r) (o : Str) (v : ℕ → ℕ) :
    ExecLe (Ham.hg_dec r) (st2 W O Q o v) (.norm (st2 W O Q o (update v r (v r - 1)))) 2 := by
  rcases h : v r with _ | n
  · refine (ExecLe.pop_nil (by rw [st2_reg hr, h]; rfl) (ExecLe.skip _)).cast ?_ le_rfl
    rw [Nat.zero_sub, ← h, update_eq_self]
  · refine ExecLe.pop_cons (b := true) (s := List.replicate n true)
      (by rw [st2_reg hr, h, List.replicate_succ]) ?_
    rw [if_pos rfl, upd2_reg hr, Nat.add_sub_cancel]
    exact ExecLe.skip _

/-- Reset `j = 0`, `j' = N - 1`. -/
def sg_resetJ : Cmd :=
  .seq (drain 13) (.seq (drain 14) (.seq (copyVia 5 14 11) (Ham.hg_dec 14)))

theorem sg_ex_resetJ (o : Str) (v : ℕ → ℕ) (h11 : v 11 = 0) :
    ExecLe sg_resetJ (st2 W O Q o v) (.norm (st2 W O Q o (update (update v 13 0) 14 (v 5 - 1))))
      (2 * v 13 + 2 * v 14 + 5 * v 5 + 10) := by
  have p1 := ex_drain_reg (W := W) (O := O) (Q := Q) (r := 13) (by norm_num) o v
  have p2 := ex_drain_reg (W := W) (O := O) (Q := Q) (r := 14) (by norm_num) o (update v 13 0)
  have p3 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 5) (b := 14) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) o (update (update v 13 0) 14 0)
    (by simp [h11])
  have p4 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 14) (by norm_num) o
    (update (update (update v 13 0) 14 0) 14
      (update (update v 13 0) 14 0 14 + update (update v 13 0) 14 0 5))
  refine (p1.seq_norm (p2.seq_norm (p3.seq_norm p4))).cast ?_ ?_
  · congr 2; funext r; simp only [update_apply]; split_ifs <;> simp_all
  · simp; omega

/-- Reset `k = 0`, `d = m - 1`. -/
def sg_resetK : Cmd :=
  .seq (drain 6) (.seq (drain 8) (.seq (copyVia 9 8 11) (Ham.hg_dec 8)))

theorem sg_ex_resetK (o : Str) (v : ℕ → ℕ) (h11 : v 11 = 0) :
    ExecLe sg_resetK (st2 W O Q o v) (.norm (st2 W O Q o (update (update v 6 0) 8 (v 9 - 1))))
      (2 * v 6 + 2 * v 8 + 5 * v 9 + 10) := by
  have p1 := ex_drain_reg (W := W) (O := O) (Q := Q) (r := 6) (by norm_num) o v
  have p2 := ex_drain_reg (W := W) (O := O) (Q := Q) (r := 8) (by norm_num) o (update v 6 0)
  have p3 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 9) (b := 8) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) o (update (update v 6 0) 8 0)
    (by simp [h11])
  have p4 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 8) (by norm_num) o
    (update (update (update v 6 0) 8 0) 8
      (update (update v 6 0) 8 0 8 + update (update v 6 0) 8 0 9))
  refine (p1.seq_norm (p2.seq_norm (p3.seq_norm p4))).cast ?_ ?_
  · congr 2; funext r; simp only [update_apply]; split_ifs <;> simp_all
  · simp; omega

end Reg

/-! ## Counter loops over `j` printing two rows -/

theorem sg_ex_jgen {c : ℕ} (hc : 5 ≤ c) (hc13 : c ≠ 13) (hc14 : c ≠ 14) (A B : Cmd)
    (oA oB : ℕ → List SatSym) (T N : ℕ) (P : (ℕ → ℕ) → Prop)
    (hP : ∀ u r n, (r = 13 ∨ r = 14 ∨ r = c) → P u → P (update u r n))
    (hA : ∀ u j, P u → u 13 = j → u 14 = N - 1 - j → j < N → sg_Em A u (oA j) T)
    (hB : ∀ u j, P u → u 13 = j → u 14 = N - 1 - j → j < N → sg_Em B u (oB j) T)
    (W O Q : Str) : ∀ (n j : ℕ) (E : List SatSym) (v : ℕ → ℕ), P v → v c = n → v 13 = j →
    v 14 = N - 1 - j → j + n ≤ N →
    ∃ v', (∀ r, r ≠ 13 → r ≠ 14 → r ≠ c → v' r = v r) ∧ v' c = 0 ∧ v' 13 = j + n ∧
      v' 14 = N - 1 - j - n ∧
      ExecLe (.loop (.pop c .brk (.seq A (.seq B (.seq (.push 13 true) (Ham.hg_dec 14))))
        (.seq A (.seq B (.seq (.push 13 true) (Ham.hg_dec 14))))))
        (st2 W O Q (rv E) v)
        (.norm (st2 W O Q (rv (E ++ (List.range' j n).flatMap (fun j => oA j ++ oB j))) v'))
        (n * (2 * T + 4) + 2)
  | 0, j, E, v, _, hn, h13, h14, _ => ⟨v, fun _ _ _ _ => rfl, hn, by simp [h13], by simp [h14],
      (Ham.hg_cend (by rw [st2_reg hc, hn]; rfl)).cast (by simp) (by simp)⟩
  | n + 1, j, E, v, hv, hn, h13, h14, hjn => by
    set u := update v c n
    have hu : P u := hP v c n (Or.inr (Or.inr rfl)) hv
    have u13 : u 13 = j := by simp [u, Ne.symm hc13, h13]
    have u14 : u 14 = N - 1 - j := by simp [u, Ne.symm hc14, h14]
    have q1 := hA u j hu u13 u14 (by omega) W O Q E
    have q2 := hB u j hu u13 u14 (by omega) W O Q (E ++ oA j)
    have q3 := ex_push_reg (W := W) (O := O) (Q := Q) (r := 13) (by norm_num)
      (rv (E ++ oA j ++ oB j)) u
    set u1 := update u 13 (u 13 + 1)
    have q4 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 14) (by norm_num)
      (rv (E ++ oA j ++ oB j)) u1
    set u2 := update u1 14 (u1 14 - 1)
    have hu2 : P u2 := hP _ _ _ (Or.inr (Or.inl rfl)) (hP _ _ _ (Or.inl rfl) hu)
    obtain ⟨v', f1, f2, f3, f4, ih⟩ := sg_ex_jgen hc hc13 hc14 A B oA oB T N P hP hA hB W O Q n
      (j + 1) (E ++ oA j ++ oB j) u2 hu2 (by simp [u2, u1, u, hc14, hc13])
      (by simp [u2, u1, u13]) (by simp [u2, u1, u14]; omega) (by omega)
    refine ⟨v', fun r a b d => ?_, f2, by rw [f3]; omega, by rw [f4]; omega, ?_⟩
    · rw [f1 r a b d]; simp [u2, u1, u, a, b, d]
    · refine (Ham.hg_cstep (n := n) (by rw [st2_reg hc, hn])
        (by rw [upd2_reg hc]; exact q1.seq_norm (q2.seq_norm (q3.seq_norm q4))) ih).cast
        ?_ ?_
      · simp [List.range'_succ, List.append_assoc]
      · simp only [Nat.add_mul, Nat.one_mul]; omega

/-! ## The variable rows -/

def sg_jB : Cmd := .seq (sg_vRowC true) (.seq (sg_vRowC false) (.seq (.push 13 true) (Ham.hg_dec 14)))

def sg_jLoop : Cmd := .loop (.pop 15 .brk sg_jB sg_jB)

/-- The two printed rows of variable `j`. -/
def sg_jOut (N m j : ℕ) : List SatSym :=
  sg_pr N (sg_vDg m j (N - 1 - j) true) ++ [sep] ++ (sg_pr N (sg_vDg m j (N - 1 - j) false) ++ [sep])

theorem sg_ex_jLoop (N m V : ℕ) (hN : N ≤ V) (hm : m ≤ V) (W O Q : Str) (E : List SatSym)
    (v : ℕ → ℕ) (h5 : v 5 = N) (h9 : v 9 = m) (hz : sg_Z v) (h12 : v 12 = 0) (h15 : v 15 = N)
    (h13 : v 13 = 0) (h14 : v 14 = N - 1) :
    ∃ v', (∀ r, r ≠ 13 → r ≠ 14 → r ≠ 15 → v' r = v r) ∧ v' 15 = 0 ∧ v' 13 = N ∧ v' 14 = 0 ∧
      ExecLe sg_jLoop (st2 W O Q (rv E) v)
        (.norm (st2 W O Q (rv (E ++ (List.range' 0 N).flatMap (sg_jOut N m))) v'))
        (N * (2 * sg_rowT V + 4) + 2) := by
  obtain ⟨v', f1, f2, f3, f4, h⟩ := sg_ex_jgen (c := 15) (by norm_num) (by norm_num) (by norm_num)
    (sg_vRowC true) (sg_vRowC false) (fun j => sg_pr N (sg_vDg m j (N - 1 - j) true) ++ [sep])
    (fun j => sg_pr N (sg_vDg m j (N - 1 - j) false) ++ [sep]) (sg_rowT V) N
    (fun u => u 5 = N ∧ u 9 = m ∧ sg_Z u ∧ u 12 = 0)
    (fun u r n hr ⟨a, b, c, d⟩ => by
      rcases hr with rfl | rfl | rfl <;>
        exact ⟨by simp [a], by simp [b], sg_Z_upd c (by norm_num) (by norm_num) (by norm_num) n,
          by simp [d]⟩)
    (fun u j ⟨a, b, c, d⟩ h13 h14 hj => sg_em_vRow true a b h13 h14 hN hm (by omega) (by omega) c d)
    (fun u j ⟨a, b, c, d⟩ h13 h14 hj => sg_em_vRow false a b h13 h14 hN hm (by omega) (by omega) c d)
    W O Q N 0 E v ⟨h5, h9, hz, h12⟩ h15 h13 (by simpa using h14) (by omega)
  exact ⟨v', f1, f2, by simpa using f3, by rw [f4]; omega, h⟩

/-! ## The witness rows: one clause -/

def sg_wRowC : SatSym → Cmd
  | pos => sg_cRowC true false
  | neg => sg_cRowC true true
  | _ => sg_zRowC

/-- The printed witness row of symbol `a` at position `j` of clause `k` (`d` clauses after). -/
def sg_wOut (N m k d j j' : ℕ) : SatSym → List SatSym
  | pos => sg_pr N (sg_cDg N k d j j' true false) ++ [sep]
  | neg => sg_pr N (sg_cDg N k d j j' true true) ++ [sep]
  | _ => sg_pr N (sg_F (DD N m)) ++ [sep]

theorem sg_em_wRow (a : SatSym) {v : ℕ → ℕ} {N m V k d j j' : ℕ} (h5 : v 5 = N) (h9 : v 9 = m)
    (h6 : v 6 = k) (h8 : v 8 = d) (h13 : v 13 = j) (h14 : v 14 = j') (hN : N ≤ V) (hm : m ≤ V)
    (hk : k ≤ V) (hd : d ≤ V) (hj : j ≤ V) (hj' : j' ≤ V) (hz : sg_Z v) (h12 : v 12 = 0) :
    sg_Em (sg_wRowC a) v (sg_wOut N m k d j j' a) (sg_rowT V) := by
  cases a with
  | pos => exact sg_em_cRow true false h5 h6 h8 h13 h14 hN hk hd hj hj' hz h12
  | neg => exact sg_em_cRow true true h5 h6 h8 h13 h14 hN hk hd hj hj' hz h12
  | zero => exact sg_em_zRow h5 h9 hN hm hz h12
  | sep => exact sg_em_zRow h5 h9 hN hm hz h12

def sg_cBr : SatSym → Cmd
  | sep => .brk
  | a => .seq (sg_wRowC a) (.seq (.push 13 true) (Ham.hg_dec 14))

def sg_inner : Cmd := .loop (disp 3 sg_cBr)

/-- The printed witness rows of a clause `c`, from position `j` on. -/
def sg_symOut (N m k d : ℕ) : ℕ → List SatSym → List SatSym
  | _, [] => []
  | j, a :: c => sg_wOut N m k d j (N - 1 - j) a ++ sg_symOut N m k d (j + 1) c

theorem sg_ex_inner (N m V k d : ℕ) (hN : N ≤ V) (hm : m ≤ V) (hk : k ≤ V) (hd : d ≤ V)
    (W Q : Str) : ∀ (c : List SatSym), sep ∉ c → ∀ (rest E : List SatSym) (j : ℕ) (v : ℕ → ℕ),
    v 5 = N → v 9 = m → v 6 = k → v 8 = d → sg_Z v → v 12 = 0 → v 13 = j → v 14 = N - 1 - j →
    j + c.length ≤ N →
    ∃ v', (∀ r, r ≠ 13 → r ≠ 14 → v' r = v r) ∧ v' 13 = j + c.length ∧
      v' 14 = N - 1 - j - c.length ∧
      ExecLe sg_inner (st2 W ((c ++ sep :: rest).flatMap ic) Q (rv E) v)
        (.norm (st2 W (rest.flatMap ic) Q (rv (E ++ sg_symOut N m k d j c)) v'))
        (c.length * (sg_rowT V + 6) + 4)
  | [], _, rest, E, j, v, _, _, _, _, _, _, h13, h14, _ => by
    refine ⟨v, fun _ _ _ => rfl, by simp [h13], by simp [h14], ?_⟩
    have hb := ex_disp (k := 3) (f := sg_cBr) (s := sep) (Q' := rest.flatMap ic)
      (σ := st2 W (([] ++ sep :: rest).flatMap ic) Q (rv E) v) (by simp) (ExecLe.brk _)
    refine (ExecLe.loop_brk hb).cast ?_ (by simp)
    rw [upd2_3]; simp [sg_symOut]
  | a :: c, hc, rest, E, j, v, h5, h9, h6, h8, hz, h12, h13, h14, hl => by
    have ha : a ≠ sep := fun e => hc (e ▸ List.mem_cons_self ..)
    have hc' : sep ∉ c := fun e => hc (List.mem_cons_of_mem _ e)
    simp only [List.length_cons] at hl
    have q1 := sg_em_wRow a h5 h9 h6 h8 h13 h14 hN hm hk hd (by omega) (by omega) hz h12 W
      ((c ++ sep :: rest).flatMap ic) Q E
    set o := sg_wOut N m k d j (N - 1 - j) a
    have q2 := ex_push_reg (W := W) (O := (c ++ sep :: rest).flatMap ic) (Q := Q) (r := 13)
      (by norm_num) (rv (E ++ o)) v
    set u1 := update v 13 (v 13 + 1)
    have q3 := sg_ex_dec (W := W) (O := (c ++ sep :: rest).flatMap ic) (Q := Q) (r := 14)
      (by norm_num) (rv (E ++ o)) u1
    set u2 := update u1 14 (u1 14 - 1)
    have hbr : ExecLe (sg_cBr a) (st2 W ((c ++ sep :: rest).flatMap ic) Q (rv E) v)
        (.norm (st2 W ((c ++ sep :: rest).flatMap ic) Q (rv (E ++ o)) u2)) (sg_rowT V + 3) := by
      have h := q1.seq_norm (q2.seq_norm q3)
      cases a with
      | sep => exact absurd rfl ha
      | zero => exact h
      | pos => exact h
      | neg => exact h
    have hb := ex_disp (k := 3) (f := sg_cBr) (s := a) (Q' := (c ++ sep :: rest).flatMap ic)
      (σ := st2 W ((a :: c ++ sep :: rest).flatMap ic) Q (rv E) v) (by simp)
      (by rw [upd2_3]; exact hbr)
    obtain ⟨v', f1, f2, f3, ih⟩ := sg_ex_inner N m V k d hN hm hk hd W Q c hc' rest (E ++ o)
      (j + 1) u2 (by simp [u2, u1, h5]) (by simp [u2, u1, h9]) (by simp [u2, u1, h6])
      (by simp [u2, u1, h8]) (sg_Z_upd (sg_Z_upd hz (by norm_num) (by norm_num) (by norm_num) _)
        (by norm_num) (by norm_num) (by norm_num) _) (by simp [u2, u1, h12])
      (by simp [u2, u1, h13]) (by simp [u2, u1, h14]; omega) (by omega)
    refine ⟨v', fun r a b => by rw [f1 r a b]; simp [u2, u1, a, b], by rw [f2]; simp; omega,
      by rw [f3]; simp; omega, (ExecLe.loop_norm hb ih).cast ?_ ?_⟩
    · simp [sg_symOut, o, List.append_assoc]
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega

/-! ## The witness rows: all clauses -/

def sg_clB : Cmd := .seq sg_inner (.seq sg_resetJ (.seq (.push 6 true) (Ham.hg_dec 8)))

def sg_clLoop : Cmd := .loop (.pop 15 .brk sg_clB sg_clB)

/-- The printed witness rows of the clauses `cs`, from clause `k` on. -/
def sg_clOut (N m : ℕ) : ℕ → List (List SatSym) → List SatSym
  | _, [] => []
  | k, c :: cs => sg_symOut N m k cs.length 0 c ++ sg_clOut N m (k + 1) cs

/-- Cost bound of one clause. -/
def sg_tC (V : ℕ) : ℕ := V * (sg_rowT V + 6) + 9 * V + 20

theorem sg_ex_clLoop (N m V : ℕ) (hN : N ≤ V) (hm : m ≤ V) (W Q : Str) :
    ∀ (cs : List (List SatSym)) (k : ℕ) (E : List SatSym) (v : ℕ → ℕ),
    (∀ c ∈ cs, sep ∉ c ∧ c.length ≤ N) → k + cs.length ≤ m → v 5 = N → v 9 = m → sg_Z v →
    v 12 = 0 → v 15 = cs.length → v 6 = k → v 8 = cs.length - 1 → v 13 = 0 → v 14 = N - 1 →
    ∃ v', (∀ r, r ≠ 6 → r ≠ 8 → r ≠ 13 → r ≠ 14 → r ≠ 15 → v' r = v r) ∧ v' 15 = 0 ∧
      v' 6 = k + cs.length ∧ v' 8 = 0 ∧ v' 13 = 0 ∧ v' 14 = N - 1 ∧
      ExecLe sg_clLoop (st2 W ((cs.flatMap (· ++ [sep])).flatMap ic) Q (rv E) v)
        (.norm (st2 W [] Q (rv (E ++ sg_clOut N m k cs)) v')) (cs.length * sg_tC V + 2)
  | [], k, E, v, _, _, _, _, _, _, h15, h6, h8, h13, h14 =>
    ⟨v, fun _ _ _ _ _ _ => rfl, h15, by simp [h6], by simpa using h8, h13, h14,
      (Ham.hg_cend (by rw [st2_reg (by norm_num), h15]; rfl)).cast (by simp [sg_clOut]) (by simp)⟩
  | c :: cs, k, E, v, hcs, hkm, h5, h9, hz, h12, h15, h6, h8, h13, h14 => by
    obtain ⟨hc, hcN⟩ := hcs c (by simp)
    have hcs' : ∀ c ∈ cs, sep ∉ c ∧ c.length ≤ N := fun c' h => hcs c' (by simp [h])
    simp only [List.length_cons] at hkm h15 h8 ⊢
    set rest := cs.flatMap (· ++ [sep])
    have eW : ((c :: cs).flatMap (· ++ [sep])).flatMap ic = (c ++ sep :: rest).flatMap ic := by
      simp [rest]
    rw [eW]
    set u := update v 15 cs.length
    obtain ⟨u1, g1, g2, g3, q1⟩ := sg_ex_inner N m V k cs.length hN hm (by omega) (by omega) W Q c
      hc rest E 0 u (by simp [u, h5]) (by simp [u, h9]) (by simp [u, h6]) (by simp [u, h8])
      (sg_Z_upd hz (by norm_num) (by norm_num) (by norm_num) _) (by simp [u, h12])
      (by simp [u, h13]) (by simp [u, h14]) (by omega)
    have e1 : ∀ r, r ≠ 13 → r ≠ 14 → r ≠ 15 → u1 r = v r := fun r a b d => by
      rw [g1 r a b]; simp [u, d]
    set E1 := E ++ sg_symOut N m k cs.length 0 c
    have q2 := sg_ex_resetJ (W := W) (O := rest.flatMap ic) (Q := Q) (rv E1) u1
      (by rw [e1 11 (by norm_num) (by norm_num) (by norm_num)]; exact hz.2.2)
    set u2 := update (update u1 13 0) 14 (u1 5 - 1)
    have q3 := ex_push_reg (W := W) (O := rest.flatMap ic) (Q := Q) (r := 6) (by norm_num) (rv E1) u2
    set u3 := update u2 6 (u2 6 + 1)
    have q4 := sg_ex_dec (W := W) (O := rest.flatMap ic) (Q := Q) (r := 8) (by norm_num) (rv E1) u3
    set u4 := update u3 8 (u3 8 - 1)
    have hu15 : u1 15 = cs.length := by
      rw [g1 15 (by norm_num) (by norm_num)]; simp [u]
    obtain ⟨v', f1, f2, f3, f4, f5, f6, ih⟩ := sg_ex_clLoop N m V hN hm W Q cs (k + 1) E1 u4 hcs'
      (by omega) (by simp [u4, u3, u2, e1, h5]) (by simp [u4, u3, u2, e1, h9])
      ⟨by simp [u4, u3, u2, e1, hz.1], by simp [u4, u3, u2, e1, hz.2.1],
        by simp [u4, u3, u2, e1, hz.2.2]⟩ (by simp [u4, u3, u2, e1, h12])
      (by simp [u4, u3, u2, hu15]) (by simp [u4, u3, u2, e1, h6])
      (by simp [u4, u3, u2, e1, h8]) (by simp [u4, u3, u2]) (by simp [u4, u3, u2, e1, h5])
    have hpop : st2 W ((c ++ sep :: rest).flatMap ic) Q (rv E) v 15 =
        List.replicate (cs.length + 1) true := by rw [st2_reg (by norm_num), h15]
    have hstep := q1.seq_norm (q2.seq_norm (q3.seq_norm q4))
    rw [← upd2_reg (by norm_num)] at hstep
    refine ⟨v', fun r a b c d e => ?_, f2, by rw [f3]; omega, f4, f5, f6,
      (Ham.hg_cstep hpop hstep ih).cast ?_ ?_⟩
    · rw [f1 r a b c d e]; simp [u4, u3, u2, a, b, c, d, e1 r c d e]
    · simp [sg_clOut, E1, List.append_assoc]
    · have hc1 : c.length * (sg_rowT V + 6) ≤ V * (sg_rowT V + 6) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [g2, g3, e1 5 (by norm_num) (by norm_num) (by norm_num), h5]
      simp only [sg_tC, Nat.add_mul, Nat.one_mul] at *
      omega

/-! ## The filler rows -/

def sg_fjB : Cmd :=
  .seq (sg_cRowC false false) (.seq (sg_cRowC false true) (.seq (.push 13 true) (Ham.hg_dec 14)))

def sg_fjLoop : Cmd := .loop (.pop 16 .brk sg_fjB sg_fjB)

/-- The two printed filler rows of pair `j` of clause `k`. -/
def sg_fOut (N k d j : ℕ) : List SatSym :=
  sg_pr N (sg_cDg N k d j (N - 1 - j) false false) ++ [sep] ++
    (sg_pr N (sg_cDg N k d j (N - 1 - j) false true) ++ [sep])

def sg_fkB : Cmd :=
  .seq (copyVia 5 16 11) (.seq sg_fjLoop (.seq sg_resetJ (.seq (.push 6 true) (Ham.hg_dec 8))))

def sg_fkLoop : Cmd := .loop (.pop 15 .brk sg_fkB sg_fkB)

/-- Cost bound of the filler rows of one clause. -/
def sg_tE (V : ℕ) : ℕ := V * (2 * sg_rowT V + 4) + 14 * V + 30

theorem sg_ex_fkLoop (N m V : ℕ) (hN : N ≤ V) (hm : m ≤ V) (W O Q : Str) :
    ∀ (n k : ℕ) (E : List SatSym) (v : ℕ → ℕ), k + n = m → v 5 = N → v 9 = m → sg_Z v →
    v 12 = 0 → v 15 = n → v 16 = 0 → v 6 = k → v 8 = n - 1 → v 13 = 0 → v 14 = N - 1 →
    ∃ v', ExecLe sg_fkLoop (st2 W O Q (rv E) v)
      (.norm (st2 W O Q (rv (E ++ (List.range' k n).flatMap
        (fun k => (List.range' 0 N).flatMap (sg_fOut N k (m - 1 - k))))) v'))
      (n * sg_tE V + 2)
  | 0, k, E, v, _, _, _, _, _, h15, _, _, _, _, _ =>
    ⟨v, (Ham.hg_cend (by rw [st2_reg (by norm_num), h15]; rfl)).cast (by simp) (by simp)⟩
  | n + 1, k, E, v, hkm, h5, h9, hz, h12, h15, h16, h6, h8, h13, h14 => by
    set u := update v 15 n
    have q1 := ex_copy_reg (W := W) (O := O) (Q := Q) (a := 5) (b := 16) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E) u (by simp [u, hz.2.2])
    set u1 := update u 16 (u 16 + u 5)
    obtain ⟨u2, g1, g2, g3, g4, q2⟩ := sg_ex_jgen (c := 16) (by norm_num) (by norm_num)
      (by norm_num) (sg_cRowC false false) (sg_cRowC false true)
      (fun j => sg_pr N (sg_cDg N k (m - 1 - k) j (N - 1 - j) false false) ++ [sep])
      (fun j => sg_pr N (sg_cDg N k (m - 1 - k) j (N - 1 - j) false true) ++ [sep]) (sg_rowT V) N
      (fun u => u 5 = N ∧ u 6 = k ∧ u 8 = m - 1 - k ∧ sg_Z u ∧ u 12 = 0)
      (fun u r n hr ⟨a, b, c, d, e⟩ => by
        rcases hr with rfl | rfl | rfl <;>
          exact ⟨by simp [a], by simp [b], by simp [c],
            sg_Z_upd d (by norm_num) (by norm_num) (by norm_num) n, by simp [e]⟩)
      (fun u j ⟨a, b, c, d, e⟩ h13 h14 hj =>
        sg_em_cRow false false a b c h13 h14 hN (by omega) (by omega) (by omega) (by omega) d e)
      (fun u j ⟨a, b, c, d, e⟩ h13 h14 hj =>
        sg_em_cRow false true a b c h13 h14 hN (by omega) (by omega) (by omega) (by omega) d e)
      W O Q N 0 E u1 ⟨by simp [u1, u, h5], by simp [u1, u, h6], by simp [u1, u, h8]; omega,
        sg_Z_upd (sg_Z_upd hz (by norm_num) (by norm_num) (by norm_num) _) (by norm_num)
          (by norm_num) (by norm_num) _, by simp [u1, u, h12]⟩
      (by simp [u1, u, h16, h5]) (by simp [u1, u, h13]) (by simp [u1, u, h14]) (by omega)
    have e1 : ∀ r, r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → u2 r = v r := fun r a b c d => by
      rw [g1 r a b d]; simp [u1, u, c, d]
    set E1 := E ++ (List.range' 0 N).flatMap (fun j =>
      sg_pr N (sg_cDg N k (m - 1 - k) j (N - 1 - j) false false) ++ [sep] ++
        (sg_pr N (sg_cDg N k (m - 1 - k) j (N - 1 - j) false true) ++ [sep]))
    have q3 := sg_ex_resetJ (W := W) (O := O) (Q := Q) (rv E1) u2
      (by rw [e1 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact hz.2.2)
    set u3 := update (update u2 13 0) 14 (u2 5 - 1)
    have q4 := ex_push_reg (W := W) (O := O) (Q := Q) (r := 6) (by norm_num) (rv E1) u3
    set u4 := update u3 6 (u3 6 + 1)
    have q5 := sg_ex_dec (W := W) (O := O) (Q := Q) (r := 8) (by norm_num) (rv E1) u4
    set u5 := update u4 8 (u4 8 - 1)
    have hu15 : u2 15 = n := by
      rw [g1 15 (by norm_num) (by norm_num) (by norm_num)]; simp [u1, u]
    obtain ⟨v', ih⟩ := sg_ex_fkLoop N m V hN hm W O Q n (k + 1) E1 u5 (by omega)
      (by simp [u5, u4, u3, e1, h5]) (by simp [u5, u4, u3, e1, h9])
      ⟨by simp [u5, u4, u3, e1, hz.1], by simp [u5, u4, u3, e1, hz.2.1],
        by simp [u5, u4, u3, e1, hz.2.2]⟩ (by simp [u5, u4, u3, e1, h12])
      (by simp [u5, u4, u3, hu15]) (by simp [u5, u4, u3, g2]) (by simp [u5, u4, u3, e1, h6])
      (by simp [u5, u4, u3, e1, h8]) (by simp [u5, u4, u3]) (by simp [u5, u4, u3, e1, h5])
    have hpop : st2 W O Q (rv E) v 15 = List.replicate (n + 1) true := by
      rw [st2_reg (by norm_num), h15]
    have hstep := q1.seq_norm (q2.seq_norm (q3.seq_norm (q4.seq_norm q5)))
    rw [← upd2_reg (by norm_num)] at hstep
    refine ⟨v', (Ham.hg_cstep hpop hstep ih).cast ?_ ?_⟩
    · rw [List.range'_succ, List.flatMap_cons, ← List.append_assoc]; rfl
    · have hu5 : u 5 = N := by simp [u, h5]
      rw [g3, g4, e1 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num), h5, hu5]
      have hN2 : N * (2 * sg_rowT V + 4) ≤ V * (2 * sg_rowT V + 4) := Nat.mul_le_mul_right _ hN
      simp only [sg_tE, Nat.add_mul, Nat.one_mul] at *
      omega

/-! ## Counting -/

def sg_cB : SatSym → Cmd
  | sep => .seq (.push 5 true) (.push 9 true)
  | _ => .push 5 true

def sg_cntLoop : Cmd := .loop (disp 4 sg_cB)

theorem sg_ex_cnt (W O : Str) : ∀ (l E : List SatSym) (v : ℕ → ℕ),
    ∃ v', (∀ r, r ≠ 5 → r ≠ 9 → v' r = v r) ∧ v' 5 = v 5 + l.length ∧
      v' 9 = v 9 + (l.flatMap Clique.hg).length ∧
      ExecLe sg_cntLoop (st2 W O (l.flatMap ic) (rv E) v) (.norm (st2 W O [] (rv E) v'))
        (4 * l.length + 2)
  | [], E, v => ⟨v, fun _ _ _ => rfl, by simp, by simp, (ex_disp_nil rfl).cast rfl (by simp)⟩
  | a :: l, E, v => by
    have hb : ∃ u, (∀ r, r ≠ 5 → r ≠ 9 → u r = v r) ∧ u 5 = v 5 + 1 ∧
        u 9 = v 9 + (Clique.hg a).length ∧
        ExecLe (sg_cB a) (st2 W O (l.flatMap ic) (rv E) v) (.norm (st2 W O (l.flatMap ic) (rv E) u))
          2 := by
      have p5 := ex_push_reg (W := W) (O := O) (Q := l.flatMap ic) (r := 5) (by norm_num) (rv E) v
      cases a with
      | sep =>
        have p9 := ex_push_reg (W := W) (O := O) (Q := l.flatMap ic) (r := 9) (by norm_num) (rv E)
          (update v 5 (v 5 + 1))
        exact ⟨_, fun r a b => by simp [a, b], by simp, by simp [Clique.hg],
          (p5.seq_norm p9).cast rfl le_rfl⟩
      | zero => exact ⟨_, fun r a b => by simp [a], by simp, by simp [Clique.hg], p5.cast rfl
          (by omega)⟩
      | pos => exact ⟨_, fun r a b => by simp [a], by simp, by simp [Clique.hg], p5.cast rfl
          (by omega)⟩
      | neg => exact ⟨_, fun r a b => by simp [a], by simp, by simp [Clique.hg], p5.cast rfl
          (by omega)⟩
    obtain ⟨u, g1, g2, g3, hb⟩ := hb
    have hd := ex_disp (k := 4) (f := sg_cB) (s := a) (Q' := l.flatMap ic)
      (σ := st2 W O ((a :: l).flatMap ic) (rv E) v) (by simp) (by rw [upd2_4]; exact hb)
    obtain ⟨v', f1, f2, f3, ih⟩ := sg_ex_cnt W O l E u
    refine ⟨v', fun r a b => by rw [f1 r a b, g1 r a b], by simp [f2, g2]; omega,
      by simp [f3, g3]; omega, (ExecLe.loop_norm hd ih).cast rfl (by simp; omega)⟩

/-! ## The printing form of `SS w` -/

theorem sg_symOut_eq (N m k d : ℕ) : ∀ (c : List SatSym) (j : ℕ), sg_symOut N m k d j c =
    (List.range c.length).flatMap
      (fun i => sg_wOut N m k d (j + i) (N - 1 - (j + i)) (c.getD i zero))
  | [], _ => rfl
  | a :: c, j => by
    rw [sg_symOut, sg_symOut_eq N m k d c (j + 1), List.length_cons, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    simp only [Nat.add_zero, List.getD_cons_zero, Nat.succ_eq_add_one, List.getD_cons_succ]
    congr 1
    refine List.flatMap_congr fun i _ => ?_
    rw [show j + 1 + i = j + (i + 1) by omega]

theorem sg_clOut_eq (N m : ℕ) : ∀ (cs : List (List SatSym)) (k : ℕ), sg_clOut N m k cs =
    (List.range cs.length).flatMap
      (fun i => sg_symOut N m (k + i) (cs.length - i - 1) 0 (cs.getD i []))
  | [], _ => rfl
  | c :: cs, k => by
    rw [sg_clOut, sg_clOut_eq N m cs (k + 1), List.length_cons, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    simp only [Nat.add_zero, List.getD_cons_zero, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.succ_eq_add_one, List.getD_cons_succ]
    congr 1
    refine List.flatMap_congr fun i _ => ?_
    rw [show k + 1 + i = k + (i + 1) by omega,
      show cs.length + 1 - (i + 1) - 1 = cs.length - i - 1 by omega]

/-- **`SS w` as printed by the program.** -/
theorem sg_SS_eq (w : List SatSym) : SS w =
    sg_pr (NV w) (List.replicate (DD (NV w) (mC w)) true) ++ [sep] ++
      (List.range' 0 (NV w)).flatMap (sg_jOut (NV w) (mC w)) ++
      sg_clOut (NV w) (mC w) 0 (clauses w) ++
      (List.range' 0 (mC w)).flatMap
        (fun k => (List.range' 0 (NV w)).flatMap (sg_fOut (NV w) k (mC w - 1 - k))) := by
  unfold SS itemRows itemsP
  rw [List.flatMap_cons, List.flatMap_map, List.flatMap_append, List.flatMap_append]
  set N := NV w
  set m := mC w
  have hb : BW w = N + 1 := rfl
  have h0 : target w = sg_pr N (List.replicate (DD N m) true) := by
    rw [target, hb, sg_digRow, List.map_const', List.length_range]
  have hA : ((List.range N).flatMap (fun j => [tP N m j, fP N m j])).flatMap
      (fun S => digRow (BW w) (DD N m) S ++ [sep]) = (List.range' 0 N).flatMap (sg_jOut N m) := by
    rw [List.flatMap_assoc]
    simp only [← List.range_eq_range']
    refine List.flatMap_congr fun j hj => ?_
    have hj := List.mem_range.1 hj
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hb, sg_digRow,
      sg_tP_dig N m j hj, sg_fP_dig N m j hj, sg_jOut]
  have hB : ((List.range m).flatMap (fun k =>
      (List.range ((clauses w).getD k []).length).map fun j => wP N k j (sy w k j))).flatMap
      (fun S => digRow (BW w) (DD N m) S ++ [sep]) = sg_clOut N m 0 (clauses w) := by
    rw [sg_clOut_eq, List.flatMap_assoc]
    refine List.flatMap_congr fun k hk => ?_
    have hk : k < m := List.mem_range.1 hk
    obtain ⟨-, hl⟩ := Ham.hg_clause_facts w k hk
    have hNV : Ham.NV w = N := rfl
    rw [hNV] at hl
    rw [List.flatMap_map, sg_symOut_eq]
    refine List.flatMap_congr fun j hj => ?_
    have hj : j < ((clauses w).getD k []).length := List.mem_range.1 hj
    have hjN : j < N := by omega
    have hm : (clauses w).length = m := rfl
    rw [hm, Nat.zero_add, Nat.zero_add, hb, sg_digRow]
    show _ = sg_wOut N m k (m - k - 1) j (N - 1 - j) (sy w k j)
    cases sy w k j with
    | pos => rw [sg_wPpos_dig N m k (m - k - 1) j hjN (by omega)]; rfl
    | neg => rw [sg_wPneg_dig N m k (m - k - 1) j hjN (by omega)]; rfl
    | zero => simp only [wP, List.map_const', List.length_range]; rfl
    | sep => simp only [wP, List.map_const', List.length_range]; rfl
  have hC : ((List.range m).flatMap (fun k => (List.range N).flatMap fun j =>
      [oneP (pD N k j), oneP (qD N k j)])).flatMap
      (fun S => digRow (BW w) (DD N m) S ++ [sep]) =
      (List.range' 0 m).flatMap (fun k => (List.range' 0 N).flatMap (sg_fOut N k (m - 1 - k))) := by
    rw [List.flatMap_assoc]
    simp only [← List.range_eq_range']
    refine List.flatMap_congr fun k hk => ?_
    have hk : k < m := List.mem_range.1 hk
    rw [List.flatMap_assoc]
    refine List.flatMap_congr fun j hj => ?_
    have hj := List.mem_range.1 hj
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hb, sg_digRow,
      sg_oneP_dig N m k (m - 1 - k) j hj (by omega), sg_oneQ_dig N m k (m - 1 - k) j hj (by omega),
      sg_fOut]
  rw [h0, hA, hB, hC]
  simp only [List.append_assoc]

/-! ## The whole program -/

theorem sg_ex_cpW3 {W Q : Str} (o : Str) (v : ℕ → ℕ) (hv : v 11 = 0) :
    ExecLe (copyVia 2 3 11) (st2 W [] Q o v) (.norm (st2 W W Q o v)) (5 * W.length + 4) := by
  refine (ExecLe.of (exec_copyVia (a := 2) (b := 3) (t := 11) (by decide) (by decide)
    (by decide) _ (by rw [st2_reg (by norm_num), hv]; rfl))).cast ?_ (by simp)
  rw [st2_2, st2_3, List.append_nil, upd2_3]

/-- The reduction program. -/
def sg_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 2) (.seq (copyVia 2 4 11) (.seq (.push 5 true)
  (.seq sg_cntLoop (.seq sg_tgtC (.seq sg_resetJ (.seq (copyVia 5 15 11) (.seq sg_jLoop
  (.seq sg_resetJ (.seq sg_resetK (.seq (copyVia 2 3 11) (.seq (copyVia 9 15 11) (.seq sg_clLoop
  (.seq sg_resetK (.seq (copyVia 9 15 11) sg_fkLoop))))))))))))))))

/-- Time bound of the program. -/
def sg_Tred (n : ℕ) : ℕ :=
  100 * (n + 1) + 100 + sg_rowT (n + 1) + (n + 1) * (2 * sg_rowT (n + 1) + 4) +
    (n + 1) * sg_tC (n + 1) + (n + 1) * sg_tE (n + 1)

set_option maxHeartbeats 1600000 in
theorem sg_exec_redCmd (x : Str) : ∃ σ', ExecLe sg_redCmd (init [x]).stk (.norm σ')
    (sg_Tred x.length) ∧ σ' 1 = ((SS (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  set L := trunc w
  set W := L.flatMap ic
  set m := mC w
  set N := NV w
  set V := x.length + 1 with hVd
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have hLw : L.length ≤ w.length := length_trunc_le w
  have hmw : m ≤ w.length := length_clauses_le w
  have hW : W.length = 2 * L.length := length_flatMap_ic L
  have hN : N = L.length + 1 := rfl
  have hNV : N ≤ V := by omega
  have hmV : m ≤ V := by omega
  have hcnt : (L.flatMap Clique.hg).length = m := by
    simp only [L, hg_trunc, List.length_replicate]; rfl
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ1 := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := exec_trimC_word 4 w σ1 (by simp [σ1, he 4 (by decide)])
  set σ2 := update σ1 4 ((L.flatMap ic).reverse)
  have p3 := exec_move (a := 4) (b := 2) (by decide) _ σ2 rfl
  have e3 : update (update σ2 4 []) 2 ((σ2 4).reverse ++ σ2 2) =
      Clique.st2 W [] [] (rv []) fun _ => 0 := by
    funext j
    simp only [σ2, σ1, Clique.st2, update_apply, rv_nil, W, L]
    split_ifs <;> simp_all
  rw [e3] at p3
  -- counting
  have q1 := ex_copyW (W := W) (O := []) (rv []) (fun _ : ℕ => (0 : ℕ)) rfl
  have q2 := ex_push_reg (W := W) (O := []) (Q := W) (r := 5) (by norm_num) (rv [])
    (fun _ : ℕ => (0 : ℕ))
  obtain ⟨v1, c1, c2, c3, q3⟩ := sg_ex_cnt W [] L []
    (update (fun _ : ℕ => (0 : ℕ)) 5 ((fun _ : ℕ => (0 : ℕ)) 5 + 1))
  have v1_5 : v1 5 = N := by rw [c2]; simp [hN]; omega
  have v1_9 : v1 9 = m := by rw [c3, hcnt]; simp
  have v1_o : ∀ r, r ≠ 5 → r ≠ 9 → v1 r = 0 := fun r a b => by rw [c1 r a b]; simp [a]
  have z1 : sg_Z v1 := ⟨v1_o 7 (by norm_num) (by norm_num), v1_o 10 (by norm_num) (by norm_num),
    v1_o 11 (by norm_num) (by norm_num)⟩
  -- the target
  have q4 := sg_em_tgt (V := V) v1_5 v1_9 hNV hmV z1 (v1_o 12 (by norm_num) (by norm_num))
    W [] [] []
  set E1 := [] ++ (sg_pr N (List.replicate (DD N m) true) ++ [sep])
  -- the variable rows
  have q5 := sg_ex_resetJ (W := W) (O := []) (Q := []) (rv E1) v1 z1.2.2
  set v2 := update (update v1 13 0) 14 (v1 5 - 1)
  have q6 := ex_copy_reg (W := W) (O := []) (Q := []) (a := 5) (b := 15) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E1) v2 (by simp [v2, z1.2.2])
  set v3 := update v2 15 (v2 15 + v2 5)
  obtain ⟨v4, f1, f2, f3, f4, q7⟩ := sg_ex_jLoop N m V hNV hmV W [] [] E1 v3
    (by simp [v3, v2, v1_5]) (by simp [v3, v2, v1_9])
    ⟨by simp [v3, v2, z1.1], by simp [v3, v2, z1.2.1], by simp [v3, v2, z1.2.2]⟩
    (by simp [v3, v2, v1_o]) (by simp [v3, v2, v1_o, v1_5]) (by simp [v3, v2])
    (by simp [v3, v2, v1_5])
  set E2 := E1 ++ (List.range' 0 N).flatMap (sg_jOut N m)
  -- the witness rows
  have q8 := sg_ex_resetJ (W := W) (O := []) (Q := []) (rv E2) v4
    (by rw [f1 11 (by norm_num) (by norm_num) (by norm_num)]; simp [v3, v2, z1.2.2])
  set v5 := update (update v4 13 0) 14 (v4 5 - 1)
  have q9 := sg_ex_resetK (W := W) (O := []) (Q := []) (rv E2) v5
    (by simp [v5, f1, v3, v2, z1.2.2])
  set v6 := update (update v5 6 0) 8 (v5 9 - 1)
  have q10 := sg_ex_cpW3 (W := W) (Q := []) (rv E2) v6 (by simp [v6, v5, f1, v3, v2, z1.2.2])
  have q11 := ex_copy_reg (W := W) (O := W) (Q := []) (a := 9) (b := 15) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E2) v6
    (by simp [v6, v5, f1, v3, v2, z1.2.2])
  set v7 := update v6 15 (v6 15 + v6 9)
  have hv7 : ∀ r, r ≠ 6 → r ≠ 8 → r ≠ 13 → r ≠ 14 → r ≠ 15 → v7 r = v1 r := fun r a b c d e => by
    simp [v7, v6, v5, a, b, c, d, e, f1 r c d e, v3, v2]
  obtain ⟨v8, g1, g2, g3, g4, g5, g6, q12⟩ := sg_ex_clLoop N m V hNV hmV W [] (clauses w) 0 E2 v7
    (fun c hc => by
      refine ⟨sep_not_mem_clauses w c hc, ?_⟩
      have := Ham.hg_len_le_flatMap hc
      simp only [N, NV, trunc] at this ⊢; omega)
    (by simp; rfl) (by rw [hv7 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), v1_5]) (by rw [hv7 9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), v1_9])
    ⟨by rw [hv7 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact z1.1,
      by rw [hv7 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
         exact z1.2.1,
      by rw [hv7 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
         exact z1.2.2⟩
    (by rw [hv7 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        exact v1_o 12 (by norm_num) (by norm_num))
    (by simp [v7, v6, v5, f2, v1_9, f1, v3, v2]; rfl) (by simp [v7, v6, v5])
    (by simp [v7, v6, v5, f1, v3, v2, v1_9]; rfl) (by simp [v7, v6, v5]) (by simp [v7, v6, v5, f1, v3, v2, v1_5])
  set E3 := E2 ++ sg_clOut N m 0 (clauses w)
  -- the filler rows
  have hv8 : ∀ r, r ≠ 6 → r ≠ 8 → r ≠ 13 → r ≠ 14 → r ≠ 15 → v8 r = v1 r := fun r a b c d e => by
    rw [g1 r a b c d e, hv7 r a b c d e]
  have q13 := sg_ex_resetK (W := W) (O := []) (Q := []) (rv E3) v8
    (by rw [hv8 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        exact z1.2.2)
  set v9 := update (update v8 6 0) 8 (v8 9 - 1)
  have q14 := ex_copy_reg (W := W) (O := []) (Q := []) (a := 9) (b := 15) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (rv E3) v9 (by simp [v9, hv8, z1.2.2])
  set v10 := update v9 15 (v9 15 + v9 9)
  obtain ⟨v11, q15⟩ := sg_ex_fkLoop N m V hNV hmV W [] [] m 0 E3 v10 (by omega)
    (by simp [v10, v9, hv8, v1_5]) (by simp [v10, v9, hv8, v1_9])
    ⟨by simp [v10, v9, hv8, z1.1], by simp [v10, v9, hv8, z1.2.1], by simp [v10, v9, hv8, z1.2.2]⟩
    (by simp [v10, v9, hv8, v1_o]) (by simp [v10, v9, g2, hv8, v1_9])
    (by simp [v10, v9, hv8, v1_o]) (by simp [v10, v9]) (by simp [v10, v9, hv8, v1_9])
    (by simp [v10, v9, g5]) (by simp [v10, v9, g6])
  refine ⟨_, (p1.seq_norm (p2.seq_norm ((ExecLe.of p3).seq_norm (q1.seq_norm (q2.seq_norm
    (q3.seq_norm (q4.seq_norm (q5.seq_norm (q6.seq_norm (q7.seq_norm (q8.seq_norm (q9.seq_norm
    (q10.seq_norm (q11.seq_norm (q12.seq_norm (q13.seq_norm (q14.seq_norm
    q15))))))))))))))))).cast rfl ?_, ?_⟩
  · have t1 : v1 13 = 0 := v1_o 13 (by norm_num) (by norm_num)
    have t2 : v1 14 = 0 := v1_o 14 (by norm_num) (by norm_num)
    have t3 : v2 5 = N := by simp [v2, v1_5]
    have t5 : v4 5 = N := by
      rw [f1 5 (by norm_num) (by norm_num) (by norm_num)]; simp [v3, v2, v1_5]
    have t6 : v5 6 = 0 := by simp [v5, f1, v3, v2, v1_o]
    have t7 : v5 8 = 0 := by simp [v5, f1, v3, v2, v1_o]
    have t8 : v5 9 = m := by simp [v5, f1, v3, v2, v1_9]
    have t9 : v6 9 = m := by simp [v6, t8]
    have t10 : v8 9 = m := by
      rw [hv8 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), v1_9]
    have t11 : v9 9 = m := by simp [v9, t10]
    have tσ : (σ2 4).length = W.length := by simp [σ2, W]
    rw [t1, t2, v1_5, t3, f3, f4, t5, t6, t7, t8, t9, g3, g4, t10, t11, tσ, hW]
    have b1 : N * (2 * sg_rowT V + 4) ≤ V * (2 * sg_rowT V + 4) := Nat.mul_le_mul_right _ hNV
    have b2 : m * sg_tC V ≤ V * sg_tC V := Nat.mul_le_mul_right _ hmV
    have b3 : m * sg_tE V ≤ V * sg_tE V := Nat.mul_le_mul_right _ hmV
    have hcl : (clauses w).length = m := rfl
    rw [hcl]
    unfold sg_Tred
    rw [← hVd]
    omega
  · simp only [st2_1, rv, E3, E2, E1]
    rw [sg_SS_eq w]
    simp only [List.append_assoc, List.nil_append]
    rfl

theorem sg_Tred_le (n : ℕ) : sg_Tred n ≤ tb 18 n := by
  unfold sg_Tred tb
  set V := n + 1
  set P := n + 2
  have e : 100 * V + 100 + sg_rowT V + V * (2 * sg_rowT V + 4) + V * sg_tC V + V * sg_tE V =
      216 * V ^ 5 + 882 * V ^ 4 + 1392 * V ^ 3 + 1146 * V ^ 2 + 640 * V + 205 := by
    unfold sg_tC sg_tE sg_rowT sg_tB sg_tP sg_tZ sg_tD; ring
  rw [e]
  have hVP : V ≤ P := by omega
  have h1 : 1 ≤ P := by omega
  have k5 : V ^ 5 ≤ P ^ 5 := Nat.pow_le_pow_left hVP 5
  have k4 : V ^ 4 ≤ P ^ 5 := le_trans (Nat.pow_le_pow_left hVP 4) (Nat.pow_le_pow_right h1 (by norm_num))
  have k3 : V ^ 3 ≤ P ^ 5 := le_trans (Nat.pow_le_pow_left hVP 3) (Nat.pow_le_pow_right h1 (by norm_num))
  have k2 : V ^ 2 ≤ P ^ 5 := le_trans (Nat.pow_le_pow_left hVP 2) (Nat.pow_le_pow_right h1 (by norm_num))
  have k1 : V ≤ P ^ 5 := le_trans hVP (by
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ 5 := Nat.pow_le_pow_right h1 (by norm_num))
  have k0 : 1 ≤ P ^ 5 := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 ^ 13 ≤ P ^ 13 := Nat.pow_le_pow_left (by omega) 13
  have h3 : 2 ^ 13 * P ^ 5 ≤ P ^ 13 * P ^ 5 := Nat.mul_le_mul h2 le_rfl
  have e2 : P ^ 18 = P ^ 13 * P ^ 5 := by ring
  rw [e2]
  norm_num at h3
  generalize P ^ 13 * P ^ 5 = A at *
  generalize P ^ 5 = B at *
  generalize V ^ 5 = a5 at *
  generalize V ^ 4 = a4 at *
  generalize V ^ 3 = a3 at *
  generalize V ^ 2 = a2 at *
  clear_value V P
  omega

/-! ## The reduction -/

/-- **SAT ≤ₚ SUBSET SUM** (official polynomial-time many-one reducibility), given the
correctness of the reduction instance `SS`. -/
theorem sat_le_ss_of (h : ∀ w, SATLang w ↔ SSLang (SS w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang SSLang := by
  obtain ⟨hc⟩ := FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    sg_redCmd 1 18 (fun x => SS (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := sg_exec_redCmd x
      exact ⟨σ', h1.mono (sg_Tred_le _), h2⟩)
    SS (fun t => (congrArg SS (FunBridge.dec2_flatMap_ic t)).symm)
  exact ⟨SS, hc, h⟩

end Pnp.Karp.SubsetSum
