import Pnp.Karp.BinPackU
import Pnp.Karp.BinPackingProg
import Pnp.Karp.ThreePartUProg

/-!
# The unary BIN PACKING reduction program, SAT ≤ₚ unary BIN PACKING

`bpup_redCmd`, on the bit string `x` on stack `0`, prints `bpuT u` (`u = dec2 x`) on stack `0`:

1. `parseLoop`, `trimC 4`, `move 4 3`: stack `3` holds the code of `trunc u`
   (the rows of `u`, each followed by `sep`);
2. `bpup_loop`: print every symbol, and push one `false` onto stack `5` per `sep`
   (stack `5` then holds `false ^ |clauses u|`);
3. `bpup_div`: pop the counter three at a time, printing one `pos` per full triple;
4. print `sep`.

`bpuT_computable` follows from `FunBridge.computable_of_cmd_code` (time bound `tb 6`), and
`sat_le_bpu_of` composes the 3DM printer, the unary 3-PARTITION transformer and `bpuT`.
-/

namespace Pnp.Karp.BinPackU

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Partition Pnp.Karp.ThreePartU Pnp.Karp.ThreeDM

/-! ## Copying the rows and counting them -/

/-- Per-symbol action: print the symbol; at `sep`, count it on stack `5`. -/
def bpup_act : SatSym → Cmd
  | sep => .seq (pp_emL [sep]) (.push 5 false)
  | zero => pp_emL [zero]
  | pos => pp_emL [pos]
  | neg => pp_emL [neg]

def bpup_B : Cmd :=
  .pop 3 .brk (.pop 3 .brk (bpup_act sep) (bpup_act zero))
    (.pop 3 .brk (bpup_act pos) (bpup_act neg))

def bpup_loop : Cmd := .loop bpup_B

/-- The counter update of a symbol. -/
def bpup_c (s : SatSym) : ℕ := if s = sep then 1 else 0

theorem bpup_ex_act (s : SatSym) (σ : ℕ → Str) (E : List SatSym) (n : ℕ)
    (h0 : σ 0 = rv E) (h5 : σ 5 = List.replicate n false) :
    ExecLe (bpup_act s) σ
      (.norm (update (update σ 0 (rv (E ++ [s]))) 5 (List.replicate (n + bpup_c s) false))) 4 := by
  by_cases hs : s = sep
  · subst hs
    simp only [bpup_act]
    have h1 := pp_ex_emL' [sep] E σ h0
    have h2 := ExecLe.push 5 false (update σ 0 (rv (E ++ [sep])))
    have h3 := h1.seq_norm h2
    refine ExecLe.cast h3 ?_ (by simp)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all [bpup_c, List.replicate_succ]
  · have e : bpup_act s = pp_emL [s] := by cases s <;> simp_all [bpup_act]
    rw [e]
    have h3 := pp_ex_emL' [s] E σ h0
    refine ExecLe.cast h3 ?_ (by simp)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all [bpup_c]

theorem bpup_ex_B (s : SatSym) (rest : Str) (σ : ℕ → Str) (E : List SatSym) (n : ℕ)
    (h3 : σ 3 = ic s ++ rest) (h0 : σ 0 = rv E) (h5 : σ 5 = List.replicate n false) :
    ExecLe bpup_B σ (.norm (update (update (update σ 3 rest) 0 (rv (E ++ [s]))) 5
      (List.replicate (n + bpup_c s) false))) 6 := by
  have g0 : ∀ v, update (update σ 3 v) 3 rest = update σ 3 rest := fun v => by simp
  cases s
  all_goals
    simp only [ic, List.cons_append, List.nil_append] at h3
    refine ExecLe.pop_cons h3 ?_
    refine ExecLe.pop_cons (by rw [update_self]) ?_
    rw [update_idem]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine bpup_ex_act _ _ E n ?_ ?_ <;> simp [h0, h5]

theorem bpup_ex_loop : ∀ (L : List SatSym) (σ : ℕ → Str) (E : List SatSym) (n : ℕ),
    σ 3 = L.flatMap ic → σ 0 = rv E → σ 5 = List.replicate n false →
    ExecLe bpup_loop σ (.norm (update (update (update σ 3 []) 0 (rv (E ++ L))) 5
      (List.replicate (n + L.count sep) false))) (6 * L.length + 2)
  | [], σ, E, n, h3, h0, h5 => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil (by simpa using h3) (ExecLe.brk _))).cast ?_
      (by simp)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all
  | s :: L, σ, E, n, h3, h0, h5 => by
    have hb := bpup_ex_B s (L.flatMap ic) σ E n (by simpa using h3) h0 h5
    have ih := bpup_ex_loop L (update (update (update σ 3 (L.flatMap ic)) 0 (rv (E ++ [s]))) 5
      (List.replicate (n + bpup_c s) false)) (E ++ [s]) (n + bpup_c s) (by simp) (by simp)
      (by simp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by simp; omega)
    have e : n + bpup_c s + L.count sep = n + (s :: L).count sep := by
      rw [List.count_cons]; cases s <;> simp [bpup_c]; omega
    rw [e]
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all

/-! ## Dividing the counter by three -/

def bpup_D2 : Cmd := .pop 5 .brk (pp_emL [pos]) (pp_emL [pos])
def bpup_D1 : Cmd := .pop 5 .brk bpup_D2 bpup_D2
def bpup_dB : Cmd := .pop 5 .brk bpup_D1 bpup_D1
def bpup_div : Cmd := .loop bpup_dB

theorem bpup_ex_div : ∀ (n : ℕ) (σ : ℕ → Str) (E : List SatSym),
    σ 5 = List.replicate n false → σ 0 = rv E →
    ExecLe bpup_div σ (.norm (update (update σ 5 []) 0 (rv (E ++ List.replicate (n / 3) pos))))
      (2 * n + 4)
  | 0, σ, E, h5, h0 => by
    refine (ExecLe.loop_brk (ExecLe.pop_nil (by simpa using h5) (ExecLe.brk _))).cast ?_
      (by simp)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all
  | 1, σ, E, h5, h0 => by
    refine (ExecLe.loop_brk (ExecLe.pop_same (by simpa using h5)
      (ExecLe.pop_nil (by rw [update_self]) (ExecLe.brk _)))).cast ?_ (by simp)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all
  | 2, σ, E, h5, h0 => by
    refine (ExecLe.loop_brk (ExecLe.pop_same (by simpa using h5)
      (ExecLe.pop_same (by rw [update_self]) (ExecLe.pop_nil (by rw [update_self]) (ExecLe.brk _))))).cast ?_ (by simp)
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all
  | n + 3, σ, E, h5, h0 => by
    have h5' : σ 5 = false :: false :: false :: List.replicate n false := by
      simp [h5, List.replicate_succ]
    have hb : ExecLe bpup_dB σ (.norm (update (update σ 5 (List.replicate n false)) 0
        (rv (E ++ [pos])))) 6 := by
      refine ExecLe.pop_same h5' (ExecLe.pop_same (by rw [update_self])
        (ExecLe.pop_same (by rw [update_self]) ?_))
      simp only [update_idem]
      exact pp_ex_emL' [pos] E _ (by simp [h0])
    have ih := bpup_ex_div n (update (update σ 5 (List.replicate n false)) 0
        (rv (E ++ [pos]))) (E ++ [pos]) (by simp) (by simp)
    refine (ExecLe.loop_norm hb ih).cast ?_ (by omega)
    have e : (n + 3) / 3 = n / 3 + 1 := by omega
    rw [e, List.replicate_succ', List.append_assoc, List.singleton_append,
      ← List.replicate_succ, List.replicate_succ']
    congr 1; funext j; simp only [update_apply]
    split_ifs <;> simp_all

/-! ## The program -/

def bpup_redCmd : Cmd :=
  .seq parseLoop (.seq (trimC 4) (.seq (move 4 3) (.seq bpup_loop (.seq bpup_div
    (pp_emL [sep])))))

theorem bpup_count_sep : ∀ L : List (List SatSym), (∀ r ∈ L, sep ∉ r) →
    (L.flatMap (· ++ [sep])).count sep = L.length
  | [], _ => rfl
  | r :: L, h => by
    have h1 := bpup_count_sep L (fun r' hr => h r' (List.mem_cons_of_mem _ hr))
    have h2 : r.count sep = 0 := List.count_eq_zero_of_not_mem (h r List.mem_cons_self)
    simp [List.flatMap_cons, List.count_append, h1, h2]

theorem bpup_exec_redCmd (x : Str) : ∃ σ', ExecLe bpup_redCmd (init [x]).stk (.norm σ')
    (16 * (x.length + 2) ^ 2) ∧ σ' 0 = ((bpuT (FunBridge.dec2 x)).flatMap ic).reverse := by
  set w := FunBridge.dec2 x
  have hwx : w.length ≤ x.length := FunBridge.length_dec2_le x
  have hLw : (trunc w).length ≤ w.length := length_trunc_le w
  have h0 : (init [x]).stk 0 = x := rfl
  have he : ∀ j, j ≠ 0 → (init [x]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have p1 := ex_parseLoop x _ h0
  set σ1 := update (update (init [x]).stk 0 []) 4 ((w.flatMap ic).reverse ++ (init [x]).stk 4)
  have p2 := exec_trimC_word 4 w σ1 (by simp [σ1, he 4 (by decide)])
  set σ2 := update σ1 4 (((trunc w).flatMap ic).reverse)
  have hW : (σ2 4).length = 2 * (trunc w).length := by
    simp only [σ2, update_self, List.length_reverse, length_flatMap_ic]
  have m1 := exec_move (a := 4) (b := 3) (by decide) _ σ2 rfl
  set σ3 := update (update σ2 4 []) 3 ((σ2 4).reverse ++ σ2 3)
  have m2 := bpup_ex_loop (trunc w) σ3 [] 0
    (by simp [σ3, σ2, σ1, he 3 (by decide)]) (by simp [σ3, σ2, σ1, rv])
    (by simp [σ3, σ2, σ1, he 5 (by decide)])
  set σ4 := update (update (update σ3 3 []) 0 (rv ([] ++ trunc w))) 5
    (List.replicate (0 + (trunc w).count sep) false)
  have m3 := bpup_ex_div (0 + (trunc w).count sep) σ4 (trunc w) (by simp [σ4]) (by simp [σ4])
  set σ5 := update (update σ4 5 []) 0
    (rv (trunc w ++ List.replicate ((0 + (trunc w).count sep) / 3) pos))
  have m4 := pp_ex_emL' [sep]
    (trunc w ++ List.replicate ((0 + (trunc w).count sep) / 3) pos) σ5 (by simp [σ5])
  have hall := p1.seq_norm (p2.seq_norm ((ExecLe.of m1).seq_norm (m2.seq_norm
    (m3.seq_norm m4))))
  have hc : (trunc w).count sep ≤ (trunc w).length := List.count_le_length
  refine ⟨_, hall.mono ?_, ?_⟩
  · simp only [hW, List.length_nil, List.length_cons]
    nlinarith
  · simp only [update_self]
    have hcs : (trunc w).count sep = (clauses w).length :=
      bpup_count_sep _ (sep_not_mem_clauses w)
    rw [hcs, Nat.zero_add]
    simp [bpuT, trunc, uRow, List.flatMap_append, rv]

/-- **`bpuT` is polynomial-time computable.** -/
theorem bpuT_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode
    bpuT) :=
  FunBridge.computable_of_cmd_code (Millennium.fin_encoding_string SatSym) ic
    bpup_redCmd 0 6 (fun x => bpuT (FunBridge.dec2 x))
    (fun x => by
      obtain ⟨σ', h1, h2⟩ := bpup_exec_redCmd x
      exact ⟨σ', h1.mono (pp_T_le _), h2⟩)
    bpuT (fun t => (congrArg bpuT (FunBridge.dec2_flatMap_ic t)).symm)

/-- **SAT ≤ₚ unary BIN PACKING**, given the correctness of the reduction instance `BPUI`. -/
theorem sat_le_bpu_of (h : ∀ w, SATLang w ↔ UBPLang (BPUI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang UBPLang := by
  obtain ⟨hd⟩ := mg_computable 1 (by norm_num) DMI mg_DMI
  obtain ⟨ht⟩ := tpup_F_computable
  obtain ⟨hb⟩ := bpuT_computable
  refine ⟨bpuT ∘ tpup_F ∘ DMI, Pnp.TM2Comp.comp (Pnp.TM2Comp.comp hd ht) hb, fun w => ?_⟩
  simp only [Function.comp_apply, tpup_F_DMI]
  exact h w

end Pnp.Karp.BinPackU
