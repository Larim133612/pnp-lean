import Pnp.Karp.ThreePartU
import Pnp.Karp.ThreePartProg
import Pnp.Karp.ThreeDMRed

/-!
# Unary 3-PARTITION reduction program, part A: printing unary items

Generic commands on stacks `σ : ℕ → Str` (output on stack `0` as `rv E`):

* `tpup_rep c p d`: append stack `p` onto stack `d`, once per element of stack `c`
  (temporaries `7`, `3`);
* `tpup_dgC p cs`: one digit (for each count stack `c ∈ cs`, `|c|` copies of `p`);
* `tpup_itC i ds`: an item with the digits `ds` (digit `j` prints copies of stack `26 + i + j`,
  which holds `R ^ (i + j)` printed `pos`), then `sep`;
* `tpup_psL k p`: split a block `false^e true rest` into `false^e` (onto `p`) and `rest`.

The item specifications `tpup_sp ip x` (lists of count stacks for the nine digits of an item)
and their values (`tpup_sp_val`).
-/

set_option linter.unusedSimpArgs false

namespace Pnp.Karp.ThreePartU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.BinPacking Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

/-! ## Repeated appending -/

def tpup_repL (p d : ℕ) : Cmd := .loop (.pop 7 .brk (copyVia p d 3) (copyVia p d 3))

theorem tpup_ex_repL {p d : ℕ} (hpd : p ≠ d) (hp3 : p ≠ 3) (hd3 : d ≠ 3) (hp7 : p ≠ 7)
    (hd7 : d ≠ 7) : ∀ (l : Str) (σ : ℕ → Str), σ 7 = l → σ 3 = [] →
    ExecLe (tpup_repL p d) σ (.norm (update (update σ 7 []) d
      ((List.replicate l.length (σ p)).flatten ++ σ d))) (l.length * (5 * (σ p).length + 5) + 2)
  | [], σ, h7, _ => (ExecLe.loop_brk (ExecLe.pop_nil h7 (ExecLe.brk _))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all) (by simp)
  | b :: l, σ, h7, h3 => by
    have h1 : ExecLe (.pop 7 .brk (copyVia p d 3) (copyVia p d 3)) σ
        (.norm (update (update σ 7 l) d (σ p ++ σ d))) (5 * (σ p).length + 5) := by
      refine ExecLe.pop_same h7 ?_
      have := ExecLe.of (exec_copyVia hpd hp3 hd3 (update σ 7 l)
        (by rw [update_of_ne (by norm_num), h3]))
      refine this.cast ?_ ?_
      · rw [update_of_ne hp7, update_of_ne hd7]
      · rw [update_of_ne hp7]
    have ih := tpup_ex_repL hpd hp3 hd3 hp7 hd7 l (update (update σ 7 l) d (σ p ++ σ d))
      (by rw [update_of_ne (Ne.symm hd7), update_self])
      (by rw [update_of_ne (Ne.symm hd3), update_of_ne (by norm_num), h3])
    have e1 : update (update σ 7 l) d (σ p ++ σ d) p = σ p := by
      rw [update_of_ne hpd, update_of_ne hp7]
    rw [e1] at ih
    refine (ExecLe.loop_norm h1 ih).cast ?_ (by simp only [List.length_cons]; ring_nf; omega)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all [List.replicate_succ']

/-- Append stack `p` onto `d`, once per element of stack `c`. -/
def tpup_rep (c p d : ℕ) : Cmd := .seq (copyVia c 7 3) (tpup_repL p d)

theorem tpup_ex_rep {c p d : ℕ} (hc7 : c ≠ 7) (hc3 : c ≠ 3) (hpd : p ≠ d) (hp3 : p ≠ 3)
    (hd3 : d ≠ 3) (hp7 : p ≠ 7) (hd7 : d ≠ 7) (σ : ℕ → Str) (h7 : σ 7 = []) (h3 : σ 3 = []) :
    ExecLe (tpup_rep c p d) σ (.norm (update σ d ((List.replicate (σ c).length (σ p)).flatten ++
      σ d))) (5 * (σ c).length + 4 + ((σ c).length * (5 * (σ p).length + 5) + 2)) := by
  have p1 := ExecLe.of (exec_copyVia hc7 hc3 (by norm_num) σ h3)
  rw [h7, List.append_nil] at p1
  have p2 := tpup_ex_repL hpd hp3 hd3 hp7 hd7 (σ c) (update σ 7 (σ c)) (by simp)
    (by rw [update_of_ne (by norm_num), h3])
  rw [update_of_ne hp7, update_of_ne hd7] at p2
  refine (p1.seq_norm p2).cast ?_ le_rfl
  congr 1; funext j; simp only [update_apply]
  split_ifs <;> simp_all

theorem tpup_rv_rep (E : List SatSym) (m : ℕ) : ∀ n : ℕ,
    (List.replicate n (rv (List.replicate m pos))).flatten ++ rv E =
      rv (E ++ List.replicate (n * m) pos)
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc, tpup_rv_rep E m n,
      ← rv_append, Nat.succ_mul, List.replicate_add, List.append_assoc]

/-! ## Digits, items, blocks of items -/

/-- Admissible count stack. -/
def tpup_ok (j : ℕ) : Prop := j ≠ 0 ∧ j ≠ 3 ∧ j ≠ 7

def tpup_dgC (p : ℕ) : List ℕ → Cmd
  | [] => .skip
  | c :: cs => .seq (tpup_rep c p 0) (tpup_dgC p cs)

theorem tpup_ex_dgC {p : ℕ} (hp : tpup_ok p) (m W : ℕ) (cnt : ℕ → ℕ) :
    ∀ (cs : List ℕ) (σ : ℕ → Str) (E : List SatSym), σ 0 = rv E → σ 3 = [] → σ 7 = [] →
    σ p = rv (List.replicate m pos) → (σ p).length ≤ W →
    (∀ c ∈ cs, tpup_ok c ∧ (σ c).length = cnt c ∧ cnt c ≤ W) →
    ExecLe (tpup_dgC p cs) σ
      (.norm (update σ 0 (rv (E ++ List.replicate ((cs.map cnt).sum * m) pos))))
      (cs.length * (6 * (W + 1) ^ 2) + 1)
  | [], σ, E, h0, _, _, _, _, _ => (ExecLe.skip σ).cast
      (by congr 1; simp [← h0]) (by simp)
  | c :: cs, σ, E, h0, h3, h7, hpm, hpW, hc => by
    obtain ⟨⟨c0, c3, c7⟩, hcl, hcW⟩ := hc c List.mem_cons_self
    have p1 := tpup_ex_rep c7 c3 hp.1 hp.2.1 (by norm_num) hp.2.2 (by norm_num) σ h7 h3
    rw [h0, hpm, tpup_rv_rep, hcl] at p1
    have ih := tpup_ex_dgC hp m W cnt cs (update σ 0 (rv (E ++ List.replicate (cnt c * m) pos)))
      (E ++ List.replicate (cnt c * m) pos) (by simp) (by simp [h3]) (by simp [h7])
      (by rw [update_of_ne hp.1, hpm]) (by rw [update_of_ne hp.1]; exact hpW)
      (fun c' hc' => by
        obtain ⟨hok, h1, h2⟩ := hc c' (List.mem_cons_of_mem _ hc')
        exact ⟨hok, by rw [update_of_ne hok.1]; exact h1, h2⟩)
    refine (p1.seq_norm ih).cast ?_ ?_
    · congr 1; rw [update_idem]; congr 2
      simp only [List.map_cons, List.sum_cons, Nat.add_mul, List.replicate_add, List.append_assoc]
    · have hcW' : (σ c).length ≤ W := hcl ▸ hcW
      have e1 : 5 * (σ c).length + 4 + ((σ c).length * (5 * (rv (List.replicate m pos)).length + 5)
          + 2) ≤ 6 * (W + 1) ^ 2 := by
        rw [← hpm]; nlinarith
      simp only [List.length_cons]; nlinarith

/-- The value of an item with digit count lists `ds` (digit `j` has weight `R ^ (i + j)`). -/
def tpup_iv (cnt : ℕ → ℕ) (R : ℕ) : ℕ → List (List ℕ) → ℕ
  | _, [] => 0
  | i, d :: ds => (d.map cnt).sum * R ^ i + tpup_iv cnt R (i + 1) ds

/-- The printed row of an item. -/
def tpup_itO (cnt : ℕ → ℕ) (R : ℕ) (ds : List (List ℕ)) : List SatSym :=
  uRow (tpup_iv cnt R 0 ds) ++ [sep]

def tpup_itC : ℕ → List (List ℕ) → Cmd
  | _, [] => tpp_em [sep]
  | i, d :: ds => .seq (tpup_dgC (26 + i) d) (tpup_itC (i + 1) ds)

/-- The hypotheses on the power stacks `26 + j`. -/
def tpup_QH (σ : ℕ → Str) (R W : ℕ) : Prop :=
  ∀ j < 9, σ (26 + j) = rv (List.replicate (R ^ j) pos) ∧ 2 * R ^ j ≤ W

/-- The hypotheses on the count stacks of a digit list. -/
def tpup_CH (σ : ℕ → Str) (cnt : ℕ → ℕ) (W : ℕ) (ds : List (List ℕ)) : Prop :=
  ∀ d ∈ ds, d.length ≤ 3 ∧ ∀ c ∈ d, tpup_ok c ∧ (σ c).length = cnt c ∧ cnt c ≤ W

theorem tpup_QH_upd {σ : ℕ → Str} {R W : ℕ} (h : tpup_QH σ R W) (v : Str) :
    tpup_QH (update σ 0 v) R W := fun j hj => by
  rw [update_of_ne (by omega)]; exact h j hj

theorem tpup_CH_upd {σ : ℕ → Str} {cnt : ℕ → ℕ} {W : ℕ} {ds : List (List ℕ)}
    (h : tpup_CH σ cnt W ds) (v : Str) : tpup_CH (update σ 0 v) cnt W ds := fun d hd => by
  refine ⟨(h d hd).1, fun c hc => ?_⟩
  obtain ⟨hok, h1, h2⟩ := (h d hd).2 c hc
  exact ⟨hok, by rw [update_of_ne hok.1]; exact h1, h2⟩

theorem tpup_ex_itC (cnt : ℕ → ℕ) (R W : ℕ) : ∀ (ds : List (List ℕ)) (i : ℕ) (σ : ℕ → Str)
    (E : List SatSym), i + ds.length ≤ 9 → σ 0 = rv E → σ 3 = [] → σ 7 = [] →
    tpup_QH σ R W → tpup_CH σ cnt W ds →
    ExecLe (tpup_itC i ds) σ
      (.norm (update σ 0 (rv (E ++ (uRow (tpup_iv cnt R i ds) ++ [sep])))))
      (ds.length * (18 * (W + 1) ^ 2 + 1) + 3)
  | [], i, σ, E, _, h0, _, _, _, _ =>
    (tpp_ex_em [sep] E σ h0).cast (by simp [tpup_iv, uRow]) (by simp)
  | d :: ds, i, σ, E, hi, h0, h3, h7, hQ, hC => by
    simp only [List.length_cons] at hi
    obtain ⟨hQ1, hQ2⟩ := hQ i (by omega)
    have p1 := tpup_ex_dgC (p := 26 + i) ⟨by omega, by omega, by omega⟩ (R ^ i) W cnt d σ E h0
      h3 h7 hQ1 (by rw [hQ1]; simp [rv, ic]; omega)
      (hC d List.mem_cons_self).2
    have ih := tpup_ex_itC cnt R W ds (i + 1)
      (update σ 0 (rv (E ++ List.replicate ((d.map cnt).sum * R ^ i) pos)))
      (E ++ List.replicate ((d.map cnt).sum * R ^ i) pos) (by omega) (by simp) (by simp [h3])
      (by simp [h7]) (tpup_QH_upd hQ _)
      (tpup_CH_upd (fun d' hd' => hC d' (List.mem_cons_of_mem _ hd')) _)
    refine (p1.seq_norm ih).cast ?_ ?_
    · congr 1; rw [update_idem]; congr 2
      simp only [tpup_iv, uRow, List.replicate_add, List.append_assoc]
    · have hd := (hC d List.mem_cons_self).1
      have : d.length * (6 * (W + 1) ^ 2) ≤ 18 * (W + 1) ^ 2 := by nlinarith
      simp only [List.length_cons]; nlinarith

def tpup_blkC : List (List (List ℕ)) → Cmd
  | [] => .skip
  | ds :: its => .seq (tpup_itC 0 ds) (tpup_blkC its)

def tpup_blkO (cnt : ℕ → ℕ) (R : ℕ) (its : List (List (List ℕ))) : List SatSym :=
  its.flatMap (tpup_itO cnt R)

theorem tpup_ex_blkC (cnt : ℕ → ℕ) (R W : ℕ) : ∀ (its : List (List (List ℕ))) (σ : ℕ → Str)
    (E : List SatSym), σ 0 = rv E → σ 3 = [] → σ 7 = [] → tpup_QH σ R W →
    (∀ ds ∈ its, ds.length ≤ 9 ∧ tpup_CH σ cnt W ds) →
    ExecLe (tpup_blkC its) σ (.norm (update σ 0 (rv (E ++ tpup_blkO cnt R its))))
      (its.length * (200 * (W + 1) ^ 2) + 1)
  | [], σ, E, h0, _, _, _, _ => (ExecLe.skip σ).cast
      (by congr 1; simp [tpup_blkO, ← h0]) (by simp)
  | ds :: its, σ, E, h0, h3, h7, hQ, hI => by
    obtain ⟨hl, hC⟩ := hI ds List.mem_cons_self
    have p1 := tpup_ex_itC cnt R W ds 0 σ E (by omega) h0 h3 h7 hQ hC
    have ih := tpup_ex_blkC cnt R W its (update σ 0 (rv (E ++ tpup_itO cnt R ds)))
      (E ++ tpup_itO cnt R ds) (by simp) (by simp [h3]) (by simp [h7]) (tpup_QH_upd hQ _)
      (fun ds' hds' => ⟨(hI ds' (List.mem_cons_of_mem _ hds')).1,
        tpup_CH_upd (hI ds' (List.mem_cons_of_mem _ hds')).2 _⟩)
    refine (p1.seq_norm ih).cast ?_ ?_
    · congr 1; rw [update_idem]; congr 2
      simp only [tpup_blkO, tpup_itO, List.flatMap_cons, List.append_assoc]
    · have hX : 1 ≤ (W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      have h1 := Nat.mul_le_mul_right (18 * (W + 1) ^ 2 + 1) hl
      rw [List.length_cons]
      generalize (W + 1) ^ 2 = X at hX h1 ⊢
      have h2 : (its.length + 1) * (200 * X) = its.length * (200 * X) + 200 * X := by ring
      omega

/-! ## Splitting a one-hot block -/

def tpup_psL (k p : ℕ) : Cmd := .loop (.pop k .brk (.push p false) .brk)

/-- The number of leading `false`s. -/
def tpup_pf : List Bool → ℕ
  | [] => 0
  | false :: l => tpup_pf l + 1
  | true :: _ => 0

/-- The rest after the first `true`. -/
def tpup_sf : List Bool → List Bool
  | [] => []
  | false :: l => tpup_sf l
  | true :: l => l

theorem tpup_ex_psL {k p : ℕ} (hkp : k ≠ p) : ∀ (l : Str) (σ : ℕ → Str), σ k = l →
    ExecLe (tpup_psL k p) σ (.norm (update (update σ k (tpup_sf l)) p
      (List.replicate (tpup_pf l) false ++ σ p))) (2 * l.length + 2)
  | [], σ, hk => (ExecLe.loop_brk (ExecLe.pop_nil hk (ExecLe.brk _))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [tpup_sf, tpup_pf])
      (by simp)
  | true :: l, σ, hk => (ExecLe.loop_brk (ExecLe.pop_cons hk (ExecLe.brk _))).cast
      (by congr 1; funext j; simp only [update_apply]; split_ifs <;> simp_all [tpup_sf, tpup_pf])
      (by simp)
  | false :: l, σ, hk => by
    have h1 : ExecLe (.pop k .brk (.push p false) .brk) σ
        (.norm (update (update σ k l) p (false :: σ p))) 2 :=
      ExecLe.pop_cons hk ((ExecLe.push p false _).cast (by rw [update_of_ne (Ne.symm hkp)])
        le_rfl)
    have ih := tpup_ex_psL hkp l (update (update σ k l) p (false :: σ p))
      (by rw [update_of_ne hkp, update_self])
    refine (ExecLe.loop_norm h1 ih).cast ?_ (by simp; omega)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all [tpup_sf, tpup_pf, List.replicate_succ']

theorem tpup_pf_tag (e : ℕ) (r : List Bool) :
    tpup_pf (List.replicate e false ++ true :: r) = e := by
  induction e with
  | zero => rfl
  | succ e ih => rw [List.replicate_succ, List.cons_append, tpup_pf, ih]

theorem tpup_sf_tag (e : ℕ) (r : List Bool) :
    tpup_sf (List.replicate e false ++ true :: r) = r := by
  induction e with
  | zero => rfl
  | succ e ih => rw [List.replicate_succ, List.cons_append, tpup_sf, ih]

theorem tpup_pf_le : ∀ l : List Bool, tpup_pf l ≤ l.length
  | [] => le_rfl
  | false :: l => by have := tpup_pf_le l; simp [tpup_pf]; omega
  | true :: _ => by simp [tpup_pf]

theorem tpup_sf_le : ∀ l : List Bool, (tpup_sf l).length ≤ l.length
  | [] => le_rfl
  | false :: l => by have := tpup_sf_le l; simp [tpup_sf]; omega
  | true :: _ => by simp [tpup_sf]

/-! ## Item specifications -/

/-- Count stacks of a block digit: `L + 1` (`18`) and the prefix `pu.1` for a one-hot block;
`2 L - n` (`cn`) and the suffix `pu.2` for a complement; `3 L` (`21`) for all ones. -/
def tpup_cs (cn : ℕ) (pu : ℕ × ℕ) : Sh → List ℕ
  | .z => []
  | .o _ => [18, pu.1]
  | .c _ => [cn, pu.2]
  | .a => [21]

/-- The digit count lists of an item (`ip c'` the prefix/suffix stacks of index block `c'`;
`5`, `6` those of the tag; `22` holds a single bit). -/
def tpup_sp (ip : ℕ → ℕ × ℕ) (x : El) : List (List ℕ) :=
  [tpup_cs 19 (ip 0) (shI x 0), tpup_cs 19 (ip 1) (shI x 1), tpup_cs 19 (ip 2) (shI x 2),
    tpup_cs 20 (5, 6) (shL x 0), tpup_cs 20 (5, 6) (shL x 1), tpup_cs 20 (5, 6) (shL x 2),
    if st1 x then [22] else [], if st2 x then [22] else [], [22]]

/-- The count condition of a block shape. -/
def tpup_okS (cnt : ℕ → ℕ) (n : ℕ) (pu : ℕ × ℕ) : Sh → Prop
  | .o e => cnt pu.1 = e
  | .c e => cnt pu.2 = n - 1 - e
  | _ => True

/-- The fixed count stacks for `q`, `M`. -/
def tpup_FH (cnt : ℕ → ℕ) (q M : ℕ) : Prop :=
  cnt 18 = uL M + 1 ∧ cnt 19 = 2 * uL M - q ∧ cnt 20 = 2 * uL M - M ∧ cnt 21 = 3 * uL M ∧
    cnt 22 = 1

theorem tpup_cs_sum {cnt : ℕ → ℕ} {L n cn : ℕ} {pu : ℕ × ℕ} (h18 : cnt 18 = L + 1)
    (hcn : cnt cn = 2 * L - n) (h21 : cnt 21 = 3 * L) :
    ∀ s : Sh, tpup_okS cnt n pu s → ((tpup_cs cn pu s).map cnt).sum = dv L n s
  | .z, _ => rfl
  | .o e, h => by simp only [tpup_cs, tpup_okS, dv] at h ⊢; simp [h18, h]
  | .c e, h => by simp only [tpup_cs, tpup_okS, dv] at h ⊢; simp [hcn, h]
  | .a, _ => by simp [tpup_cs, dv, h21]

theorem tpup_iv_eq (cnt : ℕ → ℕ) (R : ℕ) : ∀ (ds : List (List ℕ)) (i : ℕ),
    tpup_iv cnt R i ds = R ^ i * nv R (ds.map fun d => (d.map cnt).sum)
  | [], _ => by simp [tpup_iv, nv]
  | d :: ds, i => by
    rw [tpup_iv, tpup_iv_eq cnt R ds (i + 1)]
    simp only [List.map_cons, nv, pow_succ]; ring

/-- **An item prints its unary row.** -/
theorem tpup_sp_val {cnt : ℕ → ℕ} {q M : ℕ} (ip : ℕ → ℕ × ℕ) (x : El) (hF : tpup_FH cnt q M)
    (hI : ∀ c' < 3, tpup_okS cnt q (ip c') (shI x c'))
    (hL : ∀ c' < 3, tpup_okS cnt M (5, 6) (shL x c')) :
    tpup_itO cnt (uR M) (tpup_sp ip x) = uRow (uval q (M) x) ++ [sep] := by
  obtain ⟨h18, h19, h20, h21, h22⟩ := hF
  unfold tpup_itO uval
  rw [tpup_iv_eq, pow_zero, one_mul]
  congr 3
  simp only [tpup_sp, udg, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [tpup_cs_sum h18 h19 h21 _ (hI 0 (by norm_num)), tpup_cs_sum h18 h19 h21 _ (hI 1 (by norm_num)),
    tpup_cs_sum h18 h19 h21 _ (hI 2 (by norm_num)), tpup_cs_sum h18 h20 h21 _ (hL 0 (by norm_num)),
    tpup_cs_sum h18 h20 h21 _ (hL 1 (by norm_num)), tpup_cs_sum h18 h20 h21 _ (hL 2 (by norm_num))]
  cases st1 x <;> cases st2 x <;> simp [h22]

end Pnp.Karp.ThreePartU
