import Pnp.Karp.Tsp
import Pnp.Karp.HamVer
import Pnp.Karp.KnapVer

/-!
# TRAVELING SALESMAN ∈ NP: the verifier program

The verifier decides the bit code `w.flatMap ec ++ false :: false :: y` of an instance `w`
(rows `Bd :: M`, `Pnp/Karp/Tsp.lean`) and a certificate `y : List Bool`.  Let `n = |M|`; as for
HAMILTONIAN CYCLE (`Pnp/Karp/HamVer.lean`) the certificate is read as `n` blocks of `n` bits,
`B_i = hv_tk n (y.drop (i n))`, and `B_i[u]` should say `σᵢ = u`.

It reuses the stack layout `hv_HS` and most commands of the HAMILTONIAN CYCLE verifier
(block reading `hv_takeN`, permutation check `hv_permC`, initialization, main loop shape), and
the ripple-carry adder `sv_addLoop` of SUBSET SUM (renamed by `kv_ren`, framed by `kv_mix`, as
in `Pnp/Karp/KnapVer.lean`) and the comparison loop `kv_cmpLoop`.  Stack use beyond `hv_ver`:
`2` (`P`) the accumulator (bits, least significant on top), `14` (`H`) the budget, `12` (`XC`)
the code of the extracted weight chunk; the adder runs on `11` (input), `2`, `13`, `10`.

Program (`tv_ver`):
1. parse (`phaseA`, `trimC 2`, `move 2 1`); read the first row (the budget) into `H`
   (`tv_frL`, halt `false` if there is no row, `move 10 14`); `hv_pre` on the matrix rows;
2. `n - 1` times `tv_body`: read the next block `Y`; check the block `X` (`hv_permC`); scan
   the matrix row-major by `neg`-separated chunks (`tv_scan`) and extract the chunks at rows
   flagged in `X` and columns flagged in `Y` (`tv_goE`); add their value to the accumulator
   (`tv_add`); `X := Y`;
3. replace the certificate by the copy `Z` of `B_0`, run `tv_body` once more (the wrap-around
   step) and compare accumulator `≤` budget (`tv_cmp`).

`tv_exec_ver`: the program halts with `tv_vres (dec z).1 (dec z).2` within `tv_Tver |z|` steps.
-/

namespace Pnp.Karp.Tsp

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.Ham Pnp.Karp.SubsetSum Pnp.Karp.Knapsack

/-! ## Extracting chunks: semantics -/

/-- The symbols of the row `r` in chunks whose column bit (in `C`) is set, if the row flag `g`
is set. -/
def tv_rowE : List SatSym → Str → Bool → List SatSym
  | [], _, _ => []
  | x :: r, C, g =>
    if x = neg then tv_rowE r C.tail g else (if g && C.headD false then [x] else []) ++ tv_rowE r C g

/-- The extracted symbols of all rows (row flags `RF`, column bits `C`). -/
def tv_goE (C : Str) : List (List SatSym) → Str → List SatSym
  | [], _ => []
  | r :: rows, RF => tv_rowE r C (RF.headD false) ++ tv_goE C rows RF.tail

theorem tv_goE_cons_headD (C : Str) (rows : List (List SatSym)) (L : Str) :
    tv_goE C rows (L.headD false :: L.tail) = tv_goE C rows L := by
  cases rows <;> simp [tv_goE]

theorem tv_rowE_sep : ∀ (r : List SatSym) (C : Str) (g : Bool), sep ∉ r → sep ∉ tv_rowE r C g
  | [], _, _, _ => by simp [tv_rowE]
  | x :: r, C, g, h => by
    have hx : x ≠ sep := fun e => h (e ▸ List.mem_cons_self ..)
    have hr : sep ∉ r := fun e => h (List.mem_cons_of_mem _ e)
    unfold tv_rowE
    split_ifs
    · exact tv_rowE_sep r _ g hr
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨Ne.symm hx, tv_rowE_sep r _ g hr⟩
    · simpa using tv_rowE_sep r _ g hr

theorem tv_goE_sep (C : Str) : ∀ (rows : List (List SatSym)) (RF : Str), (∀ r ∈ rows, sep ∉ r) →
    sep ∉ tv_goE C rows RF
  | [], _, _ => by simp [tv_goE]
  | r :: rows, RF, h => by
    simp only [tv_goE, List.mem_append, not_or]
    exact ⟨tv_rowE_sep r C _ (h r (by simp)),
      tv_goE_sep C rows RF.tail (fun r' hr => h r' (by simp [hr]))⟩

theorem tv_length_rowE : ∀ (r : List SatSym) (C : Str) (g : Bool), (tv_rowE r C g).length ≤ r.length
  | [], _, _ => by simp [tv_rowE]
  | x :: r, C, g => by
    unfold tv_rowE
    have h1 := tv_length_rowE r C.tail g
    have h2 := tv_length_rowE r C g
    split_ifs <;> simp <;> omega

theorem tv_length_goE (C : Str) : ∀ (rows : List (List SatSym)) (RF : Str),
    (tv_goE C rows RF).length ≤ (rows.map List.length).sum
  | [], _ => by simp [tv_goE]
  | r :: rows, RF => by
    have h1 := tv_length_rowE r C (RF.headD false)
    have h2 := tv_length_goE C rows RF.tail
    simp only [tv_goE, List.length_append, List.map_cons, List.sum_cons]; omega

/-! ## The chunk scan -/

/-- Push the (reversed) code of the symbol `x` (`zero` or `pos`) onto stack `12`. -/
def tv_put : SatSym → Cmd
  | pos => .seq (.push 12 true) (.push 12 false)
  | _ => .seq (.push 12 false) (.push 12 true)

/-- Push the code of `x` if the current column bit is set (without popping it). -/
def tv_chk (x : SatSym) : Cmd := .pop 17 .skip (.push 17 false) (.seq (.push 17 true) (tv_put x))

/-- Push the code of `x` if the row flag and the column bit are set. -/
def tv_hit (x : SatSym) : Cmd := .pop 18 .skip .skip (.seq (.push 18 true) (tv_chk x))

def tv_scB : Cmd :=
  .pop 3 (.seq hv_endS .brk) (.pop 3 (.halt false) (.seq hv_endS hv_srS) (tv_hit zero))
    (.pop 3 (.halt false) (tv_hit pos) (.pop 17 .skip .skip .skip))

def tv_scL : Cmd := .loop tv_scB

/-- One scan: row flags `RF`, column template `CT`; pushes the extracted codes onto `XC`. -/
def tv_scanCore : Cmd :=
  .seq (copyVia 1 3 10) (.seq hv_srS (.seq tv_scL (.seq (drain 15) (drain 16))))

/-- The scan with row flags `X` and column template `Y`. -/
def tv_scan : Cmd := .seq (copyVia 6 15 10) (.seq (copyVia 7 16 10) tv_scanCore)

theorem tv_ex_put (x : SatSym) (hx : x = zero ∨ x = pos) (s : hv_HS) :
    ExecLe (tv_put x) s.st (.norm {s with XC := (ic x).reverse ++ s.XC}.st) 2 := by
  rcases hx with rfl | rfl
  · exact ((ExecLe.push 12 _ _).seq_norm (ExecLe.push 12 _ _)).cast (by simp [ic]) le_rfl
  · exact ((ExecLe.push 12 _ _).seq_norm (ExecLe.push 12 _ _)).cast (by simp [ic]) le_rfl

theorem tv_ex_chk (x : SatSym) (hx : x = zero ∨ x = pos) (s : hv_HS) :
    ExecLe (tv_chk x) s.st
      (.norm {s with XC := (if s.CC.headD false then (ic x).reverse else []) ++ s.XC}.st) 4 := by
  rcases hC : s.CC with _ | ⟨_ | _, C'⟩
  · exact (ExecLe.pop_nil (by simp [hC]) (ExecLe.skip _)).cast
      (by congr 1; cases s; simp_all) (by omega)
  · refine (ExecLe.pop_cons (b := false) (s := C') (by simp [hC])
      (ExecLe.push 17 false _)).cast ?_ (by omega)
    simp only [hv_u17, hv_st17]; congr 1
  · have hp := tv_ex_put x hx {s with CC := true :: C'}
    refine (ExecLe.pop_cons (b := true) (s := C') (by simp [hC])
      (((ExecLe.push 17 true _).cast (by simp) le_rfl).seq_norm hp)).cast ?_ (by omega)
    simp only [List.headD_cons, if_true]

theorem tv_ex_hit (x : SatSym) (hx : x = zero ∨ x = pos) (s : hv_HS) (g : Bool)
    (hG : s.G = CookLevin.fl g) :
    ExecLe (tv_hit x) s.st
      (.norm {s with XC := (if g && s.CC.headD false then (ic x).reverse else []) ++ s.XC}.st)
      6 := by
  cases g
  · exact (ExecLe.pop_nil (by simp [hG, CookLevin.fl]) (ExecLe.skip _)).cast
      (by congr 1) (by omega)
  · have hc := tv_ex_chk x hx {s with G := [true]}
    refine (ExecLe.pop_cons (b := true) (s := []) (by simp [hG, CookLevin.fl])
      (((ExecLe.push 18 true _).cast (by simp) le_rfl).seq_norm hc)).cast ?_ (by omega)
    simp only [Bool.true_and]; congr 1; cases s; simp_all [CookLevin.fl]

theorem tv_ex_row (C : Str) (Nb : ℕ) (hC : C.length ≤ Nb) (Q' : Str) :
    ∀ (r : List SatSym) (s : hv_HS) (g : Bool), sep ∉ r →
    s.Q = r.flatMap ic ++ false :: false :: Q' → s.CT = C → s.G = CookLevin.fl g →
    s.T = [] → s.CC.length ≤ Nb → ∀ (E : Str),
    E = ((tv_rowE r s.CC g).flatMap ic).reverse ++ s.XC →
    ∀ (res : Res) (T' : ℕ), ExecLe tv_scL
      {s with Q := Q', CC := C, G := CookLevin.fl (s.RF.headD false), RF := s.RF.tail, XC := E}.st res T' →
    ExecLe tv_scL s.st res (T' + (10 * r.length + 7 * Nb + 20))
  | [], s, g, _, hQ, hCT, hG, hT, hCC, E, hE, res, T', hk => by
    have he := hv_ex_endS {s with Q := Q'}
    have hs := hv_ex_srS {s with Q := Q', CC := [], G := []} hT rfl rfl
    have hGl : s.G.length ≤ 1 := by rw [hG]; cases g <;> simp [CookLevin.fl]
    have hb : ExecLe tv_scB s.st
        (.norm {s with Q := Q', CC := C, G := CookLevin.fl (s.RF.headD false), RF := s.RF.tail, XC := E}.st) (7 * Nb + 16) := by
      refine ExecLe.pop_cons (b := false) (s := false :: Q') (by simp [hQ]) ?_
      refine ExecLe.pop_cons (b := false) (s := Q') (by simp) ?_
      simp only [hv_u3, Bool.false_eq_true, if_false]
      refine (he.seq_norm hs).cast ?_ (by simp [hCT]; omega)
      simp only [tv_rowE, List.flatMap_nil, List.reverse_nil, List.nil_append] at hE
      congr 1; cases s; simp_all
    exact (ExecLe.loop_norm hb hk).cast rfl (by simp; omega)
  | x :: r, s, g, hr, hQ, hCT, hG, hT, hCC, E, hE, res, T', hk => by
    have hx : x ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ r := fun e => hr (List.mem_cons_of_mem _ e)
    set Q1 := r.flatMap ic ++ false :: false :: Q'
    by_cases hn : x = neg
    · subst hn
      have hb : ExecLe tv_scB s.st (.norm {s with Q := Q1, CC := s.CC.tail}.st) 4 := by
        refine ExecLe.pop_cons (σ := s.st) (k := 3) (b := true) (s := true :: Q1)
          (by simp [hQ, ic, Q1]) (ExecLe.pop_cons (b := true) (s := Q1) (by simp) ?_)
        simp only [hv_u3, if_true]
        exact (hv_pop3 (ExecLe.skip _)).cast (by simp) le_rfl
      have ih := tv_ex_row C Nb hC Q' r {s with Q := Q1, CC := s.CC.tail} g hr' rfl hCT hG hT
        (by simp; omega) E (by rw [hE]; simp [tv_rowE]) res T' hk
      exact (ExecLe.loop_norm hb ih).cast rfl (by simp; omega)
    · have hx' : x = zero ∨ x = pos := by cases x <;> simp_all
      have hc := tv_ex_hit x hx' {s with Q := Q1} g hG
      simp only at hc
      have hb : ExecLe tv_scB s.st (.norm {s with Q := Q1, XC := (if g && s.CC.headD false then (ic x).reverse else []) ++ s.XC}.st) 8 := by
        rcases hx' with rfl | rfl
        · exact ExecLe.pop_cons (σ := s.st) (k := 3) (b := false) (s := true :: Q1)
            (by simp [hQ, ic, Q1]) (ExecLe.pop_cons (b := true) (s := Q1) (by simp)
              (by simpa using hc))
        · exact ExecLe.pop_cons (σ := s.st) (k := 3) (b := true) (s := false :: Q1)
            (by simp [hQ, ic, Q1]) (ExecLe.pop_cons (b := false) (s := Q1) (by simp)
              (by simpa using hc))
      have ih := tv_ex_row C Nb hC Q' r {s with Q := Q1, XC := (if g && s.CC.headD false then (ic x).reverse else []) ++ s.XC} g hr' rfl hCT hG
        hT hCC E (by rw [hE]; simp only [tv_rowE, if_neg hn]; split_ifs <;> simp) res T' hk
      exact (ExecLe.loop_norm hb ih).cast rfl (by simp; omega)

theorem tv_ex_rows (C : Str) (Nb : ℕ) (hC : C.length ≤ Nb) :
    ∀ (rows : List (List SatSym)) (s : hv_HS) (g : Bool), (∀ r ∈ rows, sep ∉ r) →
    s.Q = enc rows → s.CT = C → s.CC = C → s.G = CookLevin.fl g → s.T = [] →
    ExecLe tv_scL s.st
      (.norm {s with Q := [], CC := [], G := [], RF := s.RF.drop rows.length, XC := ((tv_goE C rows (g :: s.RF)).flatMap ic).reverse ++ s.XC}.st)
      (hv_Tsc Nb rows)
  | [], s, g, _, hQ, hCT, hCC, hG, hT => by
    have he := hv_ex_endS s
    have hGl : s.G.length ≤ 1 := by rw [hG]; cases g <;> simp [CookLevin.fl]
    refine (ExecLe.loop_brk (ExecLe.pop_nil (by simpa [enc] using hQ)
      (he.seq_norm (ExecLe.brk _)))).cast ?_ (by simp [hv_Tsc, hCC]; omega)
    simp only [tv_goE, List.flatMap_nil, List.reverse_nil, List.nil_append]
    congr 1; cases s; simp_all [enc]
  | r :: rows, s, g, hrows, hQ, hCT, hCC, hG, hT => by
    have hr : sep ∉ r := hrows r (by simp)
    have hrs : ∀ r ∈ rows, sep ∉ r := fun r' h => hrows r' (by simp [h])
    rw [enc_cons] at hQ
    have ih := (tv_ex_rows C Nb hC rows
        {s with Q := enc rows, CC := C, G := CookLevin.fl (s.RF.headD false), RF := s.RF.tail, XC := ((tv_rowE r C g).flatMap ic).reverse ++ s.XC}
        (s.RF.headD false) hrs rfl hCT rfl rfl hT).cast
      (r' := .norm {s with Q := [], CC := [], G := [], RF := s.RF.drop (r :: rows).length, XC := ((tv_goE C (r :: rows) (g :: s.RF)).flatMap ic).reverse ++ s.XC}.st)
      (by simp only [tv_goE_cons_headD]; simp [tv_goE, List.drop_tail]) le_rfl
    exact (tv_ex_row C Nb hC (enc rows) r s g hr hQ hCT hG hT (by rw [hCC]; exact hC)
      _ (by rw [hCC]) _ _ ih).cast rfl (by simp [hv_Tsc]; omega)

theorem tv_ex_scanCore (rows : List (List SatSym)) (Nb : ℕ) (s : hv_HS)
    (hsep : ∀ r ∈ rows, sep ∉ r) (hM : s.M = enc rows) (hQ : s.Q = []) (hCC : s.CC = [])
    (hG : s.G = []) (hT : s.T = []) (hCT : s.CT.length ≤ Nb) :
    ExecLe tv_scanCore s.st
      (.norm {s with RF := [], CT := [], XC := ((tv_goE s.CT rows s.RF).flatMap ic).reverse ++ s.XC}.st)
      (5 * s.M.length + 9 * Nb + 2 * s.RF.length + hv_Tsc Nb rows + 16) := by
  have h1 := hv_ex_copy (a := 1) (b := 3) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st1, hv_st3, hv_u3, hQ, List.append_nil] at h1
  have h2 := hv_ex_srS {s with Q := s.M} hT hCC hG
  simp only at h2
  have h3 := tv_ex_rows s.CT Nb hCT rows
    {s with Q := s.M, CC := s.CT, G := CookLevin.fl (s.RF.headD false), RF := s.RF.tail}
    (s.RF.headD false) hsep hM rfl rfl rfl hT
  simp only [tv_goE_cons_headD] at h3
  refine (h1.seq_norm (h2.seq_norm (h3.seq_norm ((hv_ex_drain 15 _).seq_norm
    (hv_ex_drain 16 _))))).cast ?_ ?_
  · congr 1; cases s; simp_all
  · simp; omega

theorem tv_ex_scan (rows : List (List SatSym)) (Nb : ℕ) (s : hv_HS)
    (hsep : ∀ r ∈ rows, sep ∉ r) (hM : s.M = enc rows) (hQ : s.Q = []) (hCC : s.CC = [])
    (hG : s.G = []) (hT : s.T = []) (hRF : s.RF = [])
    (hCT : s.CT = []) (hX : s.X.length ≤ Nb) (hY : s.Y.length ≤ Nb) :
    ExecLe tv_scan s.st
      (.norm {s with XC := ((tv_goE s.Y rows s.X).flatMap ic).reverse ++ s.XC}.st)
      (5 * s.M.length + 26 * Nb + hv_Tsc Nb rows + 24) := by
  have h1 := hv_ex_copy (a := 6) (b := 15) (by decide) (by decide) (by decide) s.st (by simpa)
  simp only [hv_st6, hv_st15, hv_u15, hRF, List.append_nil] at h1
  have h2 := hv_ex_copy (a := 7) (b := 16) (by decide) (by decide) (by decide)
    {s with RF := s.X}.st (by simpa)
  simp only [hv_st7, hv_st16, hv_u16] at h2
  have h3 := tv_ex_scanCore rows Nb {s with RF := s.X, CT := s.Y ++ s.CT} hsep hM hQ hCC hG hT
    (by simp [hCT]; omega)
  simp only at h3
  refine (h1.seq_norm (h2.seq_norm h3)).cast ?_ (by omega)
  congr 1; cases s; simp_all

/-! ## Adding the extracted chunk to the accumulator -/

/-- The stacks untouched by the adder `sv_addLoop` (all but `3`–`7`). -/
def tv_Fa : ℕ → Bool := fun j => !(decide (3 ≤ j) && decide (j ≤ 7))

/-- The renaming of the adder: input `3 ↦ 11`, accumulator `5 ↦ 2`, sum bits `6 ↦ 13`,
carry `7 ↦ 10`. -/
def tv_π : Equiv.Perm ℕ := Equiv.swap 3 11 * Equiv.swap 5 2 * Equiv.swap 6 13 * Equiv.swap 7 10

theorem tv_av_add : kv_av tv_Fa sv_addLoop = true := by decide

theorem tv_π_big (j : ℕ) (h : 19 ≤ j) : tv_π j = j ∧ tv_π.symm j = j := by
  have e : ∀ a b : ℕ, a < 19 → b < 19 → Equiv.swap a b j = j := fun a b ha hb =>
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · simp only [tv_π, Equiv.Perm.mul_apply]
    rw [e 7 10 (by omega) (by omega), e 6 13 (by omega) (by omega), e 5 2 (by omega) (by omega),
      e 3 11 (by omega) (by omega)]
  · rw [← Equiv.Perm.inv_def]
    simp only [tv_π, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]
    rw [e 3 11 (by omega) (by omega), e 5 2 (by omega) (by omega), e 6 13 (by omega) (by omega),
      e 7 10 (by omega) (by omega)]

theorem tv_mixst (s : hv_HS) (R Q Tv A S : Str) (c : Bool) :
    kv_mix tv_Fa (sv_st R Q Tv A S c) (s.st ∘ tv_π) ∘ tv_π.symm =
      {s with K := Q, N := Tv, P := A, F := S, T := CookLevin.fl c}.st := by
  funext j
  by_cases hj : j < 19
  · interval_cases j <;> rfl
  · obtain ⟨h1, h2⟩ := tv_π_big j (by omega)
    have hF : tv_Fa j = true := by simp [tv_Fa]; omega
    simp only [comp_apply, h2, kv_mix, hF, if_true, h1]
    rw [hv_st_big _ _ (by omega), hv_st_big _ _ (by omega)]

/-- The accumulator after adding the value of the symbols `e`. -/
def tv_acc (A : Str) (e : List SatSym) : Str := sv_addL false A (sv_bits e)

def tv_addR : Cmd := kv_ren tv_π sv_addLoop

/-- Turn the extracted codes into a row (`sep`-terminated) on `11` and add it to `P`. -/
def tv_add : Cmd := .seq (.push 11 false) (.seq (.push 11 false) (.seq (move 12 11) tv_addR))

theorem tv_ex_add (s : hv_HS) (Nacc : ℕ) (e : List SatSym) (hsep : sep ∉ e)
    (hXC : s.XC = (e.flatMap ic).reverse) (hK : s.K = []) (hF : s.F = []) (hT : s.T = [])
    (hN : s.P.length + e.length ≤ Nacc) :
    ExecLe tv_add s.st (.norm {s with XC := [], P := tv_acc s.P e}.st)
      (11 * e.length + 8 * Nacc + 26) := by
  have h1 := ExecLe.push 11 false s.st
  have h2 := ExecLe.push 11 false (update s.st 11 (false :: s.st 11))
  simp only [hv_u11, hv_st11] at h1 h2
  set s2 : hv_HS := {s with K := false :: false :: s.K}
  have h3 := exec_move (a := 12) (b := 11) (by decide) _ s2.st rfl
  simp only [hv_u12, hv_st12, hv_u11, hv_st11, s2] at h3
  set s3 : hv_HS := {s with XC := [], K := e.flatMap ic ++ false :: false :: []}
  have h := sv_ex_addRow (R := s.R) (T := s.N) Nacc [] e s.P [] false hsep (by simp; omega)
  have h' := kv_ren_le tv_π (kv_mix_le (s3.st ∘ tv_π) h tv_av_add) kv_nc_add
  simp only [kv_rmap] at h'
  rw [tv_mixst, tv_mixst] at h'
  have e3 : {s3 with K := e.flatMap ic ++ false :: false :: [], N := s.N, P := s.P, F := [], T := CookLevin.fl false} = s3 := by
    simp only [s3]; cases s; simp_all [CookLevin.fl]
  rw [e3] at h'
  have hl : (s.XC).length = 2 * e.length := by rw [hXC, List.length_reverse, length_flatMap_ic]
  refine (h1.seq_norm (h2.seq_norm ((ExecLe.of h3).cast (r' := .norm s3.st) ?_ le_rfl |>.seq_norm
    h'))).cast ?_ ?_
  · simp only [s3]; congr 1; cases s; simp_all
  · simp only [tv_acc, s3]; congr 1; cases s; simp_all [CookLevin.fl]
  · simp only [hl]; omega

/-! ## The final comparison -/

/-- Halt with "accumulator `≤` budget" (flag on `13`). -/
def tv_cmp : Cmd :=
  .seq (.push 13 true) (.seq (kv_cmpLoop 2 14 13) (.pop 13 (.halt false) (.halt false) (.halt true)))

theorem tv_ex_cmp (s : hv_HS) (hF : s.F = []) :
    ExecLe tv_cmp s.st (.halt (kv_leF true s.P s.H)) (5 * (s.P.length + s.H.length) + 6) := by
  have hp := ExecLe.push 13 true s.st
  obtain ⟨σ', h1, h1f, -⟩ := kv_ex_cmp (a := 2) (b := 14) (f := 13) (by decide) (by decide)
    (by decide) s.P s.H true (update s.st 13 (true :: s.st 13)) (by simp) (by simp)
    (by simp [hF, CookLevin.fl])
  refine (hp.seq_norm (h1.seq_norm (T₂ := 2) ?_)).cast rfl (by omega)
  cases hr : kv_leF true s.P s.H
  · rw [hr] at h1f
    exact (ExecLe.pop_nil h1f (ExecLe.halt false _)).cast (by simp) (by omega)
  · rw [hr] at h1f
    exact (ExecLe.pop_cons (b := true) (s := []) h1f (ExecLe.halt true _)).cast (by simp)
      (by omega)

/-! ## One step of the main loop -/

/-- Read the next block, check the current block, add the weight of the step, shift. -/
def tv_body : Cmd :=
  .seq hv_takeN (.seq hv_permC (.seq tv_scan (.seq tv_add (.seq (drain 6) (hv_mvo 7 6)))))

/-- The invariant of the main loop (apart from `R`, `I`, `X`, `Z`, `S`, `P`, `H`). -/
structure tv_Inv (rows : List (List SatSym)) (n : ℕ) (s : hv_HS) : Prop where
  hN : s.N = List.replicate n true
  hM : s.M = enc rows
  hK : s.K = []
  hT : s.T = []
  hY : s.Y = []
  hXC : s.XC = []
  hF : s.F = []
  hQ : s.Q = []
  hCC : s.CC = []
  hG : s.G = []
  hRF : s.RF = []
  hCT : s.CT = []
  hX : s.X.length = n
  hS : s.S.length = n

/-- Cost of the loop body. -/
def tv_Tb (n Lm Ts Nacc : ℕ) : ℕ := 60 * n + 20 * Lm + Ts + 8 * Nacc + 80

theorem tv_length_goE_enc (C : Str) (rows : List (List SatSym)) (RF : Str) :
    (tv_goE C rows RF).length ≤ (enc rows).length := by
  have h := tv_length_goE C rows RF
  have hlen : (enc rows).length = 2 * ((rows.map List.length).sum + rows.length) := by
    simp only [enc, length_flatMap_ic]; rw [sum_length_le]
  omega

theorem tv_ex_body (rows : List (List SatSym)) (n Nacc : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r)
    (s : hv_HS) (hi : tv_Inv rows n s) (hA : s.P.length + s.M.length ≤ Nacc) :
    ExecLe tv_body s.st
      (if hv_permOk s.X s.S then
        .norm {s with R := s.R.drop n, X := hv_tk n s.R, S := hv_orV s.X s.S, P := tv_acc s.P (tv_goE (hv_tk n s.R) rows s.X)}.st
      else .halt false) (tv_Tb n s.M.length (hv_Tsc n rows) Nacc) := by
  have h1 := hv_ex_takeN n s hi.hN hi.hK hi.hT hi.hY
  have h2 := hv_ex_permC {s with R := s.R.drop n, Y := hv_tk n s.R} hi.hXC hi.hF hi.hT
    (by simp [hi.hX, hi.hS])
  simp only at h2
  have h3 := tv_ex_scan rows n
    {s with R := s.R.drop n, Y := hv_tk n s.R, S := hv_orV s.X s.S} hsep hi.hM hi.hQ hi.hCC
    hi.hG hi.hT hi.hRF hi.hCT (by simp [hi.hX]) (by simp [hv_length_tk])
  simp only at h3
  set e := tv_goE (hv_tk n s.R) rows s.X
  have hel : e.length ≤ s.M.length := by rw [hi.hM]; exact tv_length_goE_enc _ _ _
  have h4 := tv_ex_add {s with R := s.R.drop n, Y := hv_tk n s.R, S := hv_orV s.X s.S, XC := (e.flatMap ic).reverse ++ s.XC} Nacc e (tv_goE_sep _ rows _ hsep) (by simp [hi.hXC]) hi.hK hi.hF hi.hT
    (by simp; omega)
  simp only at h4
  have h5 := hv_ex_drain 6 {s with R := s.R.drop n, Y := hv_tk n s.R, S := hv_orV s.X s.S, XC := [], P := tv_acc s.P e}.st
  simp only [hv_u6, hv_st6] at h5
  have h6 := hv_ex_mvo (a := 7) (b := 6) (by decide) (by decide) (by decide)
    {s with R := s.R.drop n, Y := hv_tk n s.R, S := hv_orV s.X s.S, XC := [], P := tv_acc s.P e, X := []}.st (by simpa using hi.hT)
  simp only [hv_u6, hv_st6, hv_u7, hv_st7, List.append_nil] at h6
  have hTb : 10 * n + 8 + (12 * s.X.length + 10 + (5 * s.M.length + 26 * n + hv_Tsc n rows + 24 +
      (11 * e.length + 8 * Nacc + 26 + (2 * s.X.length + 2 + (4 * (hv_tk n s.R).length + 4))))) ≤
      tv_Tb n s.M.length (hv_Tsc n rows) Nacc := by
    simp only [tv_Tb, hv_length_tk, hi.hX]; omega
  by_cases hp : hv_permOk s.X s.S = true
  · rw [if_pos hp] at h2
    rw [if_pos hp]
    refine (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm h6))))).cast ?_ hTb
    have hY := hi.hY
    have hXC := hi.hXC
    congr 1; cases s; simp_all
  · rw [if_neg hp] at h2
    rw [if_neg hp]
    exact (h1.seq_norm (ExecLe.seq_halt h2)).cast rfl (by omega)

/-! ## The main loop -/

/-- The last iteration: the step back to `B_0` (the copy `Z`), then the comparison. -/
def tv_finB : Cmd := .seq (drain 0) (.seq (hv_mvo 8 0) (.seq tv_body tv_cmp))

def tv_mainL : Cmd := .loop (.pop 5 tv_finB tv_body tv_body)

/-- What the main loop computes (`k`: the remaining ordinary iterations, `B`: the budget,
`A`: the accumulator). -/
def tv_mainF (rows : List (List SatSym)) (n : ℕ) (Z B : Str) : ℕ → Str → Str → Str → Str → Bool
  | 0, _, X, S, A => hv_permOk X S && kv_leF true (tv_acc A (tv_goE (hv_tk n Z) rows X)) B
  | k + 1, R, X, S, A => hv_permOk X S &&
      tv_mainF rows n Z B k (R.drop n) (hv_tk n R) (hv_orV X S) (tv_acc A (tv_goE (hv_tk n R) rows X))

theorem tv_length_acc (A : Str) (e : List SatSym) : (tv_acc A e).length ≤ A.length + e.length + 1 := by
  have := sv_addL_length false A (sv_bits e)
  simpa [tv_acc, sv_bits] using this

theorem tv_ex_mainL (rows : List (List SatSym)) (n Lr Nacc : ℕ) (hsep : ∀ r ∈ rows, sep ∉ r) :
    ∀ (k : ℕ) (s : hv_HS), tv_Inv rows n s → s.I = List.replicate k true → s.R.length ≤ Lr →
    s.Z.length = n → s.P.length + (k + 1) * (s.M.length + 1) ≤ Nacc →
    ExecLe tv_mainL s.st (.halt (tv_mainF rows n s.Z s.H k s.R s.X s.S s.P))
      ((k + 1) * (tv_Tb n s.M.length (hv_Tsc n rows) Nacc + 1) + 2 * Lr + 4 * n +
        5 * (Nacc + s.H.length) + 20)
  | 0, s, hi, hI, hR, hZ, hA => by
    have h1 := hv_ex_drain 0 s.st
    simp only [hv_u0, hv_st0] at h1
    have h2 := hv_ex_mvo (a := 8) (b := 0) (by decide) (by decide) (by decide)
      {s with R := []}.st (by simpa using hi.hT)
    simp only [hv_u0, hv_st0, hv_u8, hv_st8, List.append_nil] at h2
    have hi' : tv_Inv rows n {s with R := s.Z, Z := []} := by
      obtain ⟨⟩ := hi; constructor <;> assumption
    have h3 := tv_ex_body rows n Nacc hsep _ hi' (by simp; omega)
    simp only at h3
    set e := tv_goE (hv_tk n s.Z) rows s.X
    have hel : e.length ≤ s.M.length := by rw [hi.hM]; exact tv_length_goE_enc _ _ _
    have hal := tv_length_acc s.P e
    have h4 := tv_ex_cmp {s with R := (s.Z).drop n, Z := [], X := hv_tk n s.Z, S := hv_orV s.X s.S, P := tv_acc s.P e} hi.hF
    simp only at h4
    have hfin : ExecLe tv_finB s.st (.halt (tv_mainF rows n s.Z s.H 0 s.R s.X s.S s.P))
        (2 * s.R.length + 2 + (4 * s.Z.length + 4 + (tv_Tb n s.M.length (hv_Tsc n rows) Nacc +
          (5 * (Nacc + s.H.length) + 6)))) := by
      simp only [tv_mainF, tv_finB]
      by_cases hc : hv_permOk s.X s.S = true
      · rw [if_pos hc] at h3
        refine (h1.seq_norm (h2.seq_norm (h3.seq_norm h4))).cast (by simp [hc, e]) ?_
        simp only [Nat.add_le_add_iff_left]; omega
      · rw [if_neg hc] at h3
        exact (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3))).cast
          (by simp only [Bool.not_eq_true] at hc; rw [hc]; rfl) (by omega)
    refine (ExecLe.loop_halt (ExecLe.pop_nil (by simpa using hI) hfin)).cast rfl ?_
    simp only [hZ]; omega
  | k + 1, s, hi, hI, hR, hZ, hA => by
    have hb := tv_ex_body rows n Nacc hsep {s with I := List.replicate k true}
      (by obtain ⟨⟩ := hi; constructor <;> assumption) (by simp; nlinarith)
    simp only at hb
    simp only [tv_mainF]
    set e := tv_goE (hv_tk n s.R) rows s.X
    have hel : e.length ≤ s.M.length := by rw [hi.hM]; exact tv_length_goE_enc _ _ _
    have hal := tv_length_acc s.P e
    by_cases hc : hv_permOk s.X s.S = true
    · rw [if_pos hc] at hb
      have hi' : tv_Inv rows n
          {s with I := List.replicate k true, R := s.R.drop n, X := hv_tk n s.R, S := hv_orV s.X s.S, P := tv_acc s.P e} := by
        obtain ⟨⟩ := hi; constructor <;> simp_all [hv_length_tk, hv_length_orV]
      have ih := tv_ex_mainL rows n Lr Nacc hsep k _ hi' rfl (by simp; omega) hZ
        (by simp only; nlinarith)
      simp only at ih
      rw [hc, Bool.true_and]
      refine (ExecLe.loop_norm (ExecLe.pop_cons (b := true) (s := List.replicate k true)
        (by simp [hI, List.replicate_succ]) (by simpa using hb)) ih).cast rfl ?_
      simp only [Nat.succ_mul]; omega
    · rw [if_neg hc] at hb
      rw [Bool.eq_false_iff.mpr hc, Bool.false_and]
      refine (ExecLe.loop_halt (ExecLe.pop_cons (b := true) (s := List.replicate k true)
        (by simp [hI, List.replicate_succ]) (by simpa using hb))).cast rfl ?_
      simp only [Nat.succ_mul]; omega

/-! ## Reading the budget -/

def tv_frB : Cmd :=
  .pop 1 (.halt false) (.pop 1 (.halt false) .brk (.push 10 false))
    (.pop 1 (.halt false) (.push 10 true) (.push 10 false))

/-- Read the first row (the budget) onto stack `10` (bits reversed). -/
def tv_frL : Cmd := .loop tv_frB

theorem tv_ex_fr (Q' : Str) : ∀ (t : List SatSym) (s : hv_HS), sep ∉ t →
    s.M = t.flatMap ic ++ false :: false :: Q' →
    ExecLe tv_frL s.st (.norm {s with M := Q', T := (sv_bits t).reverse ++ s.T}.st)
      (3 * t.length + 3)
  | [], s, _, hM => (ExecLe.loop_brk (ExecLe.pop_cons (b := false) (s := false :: Q')
      (by simp [hM]) (ExecLe.pop_cons (b := false) (s := Q') (by simp) (ExecLe.brk _)))).cast
      (by simp [sv_bits]) (by simp)
  | x :: t, s, hr, hM => by
    have hx : x ≠ sep := fun e => hr (e ▸ List.mem_cons_self ..)
    have hr' : sep ∉ t := fun e => hr (List.mem_cons_of_mem _ e)
    set Q := t.flatMap ic ++ false :: false :: Q'
    have ih := tv_ex_fr Q' t {s with M := Q, T := isPos x :: s.T} hr' rfl
    have hb : ExecLe tv_frB s.st (.norm {s with M := Q, T := isPos x :: s.T}.st) 3 := by
      have hp : ∀ b : Bool, b = isPos x →
          ExecLe (.push 10 b) (update s.st 1 Q) (.norm {s with M := Q, T := isPos x :: s.T}.st) 1 := by
        rintro b rfl; exact (ExecLe.push 10 _ _).cast (by simp) le_rfl
      cases x with
      | sep => exact absurd rfl hx
      | zero =>
        refine ExecLe.pop_cons (σ := s.st) (k := 1) (b := false) (s := true :: Q) ?_ ?_
        · simp [hM, ic, Q]
        · exact ExecLe.pop_cons (b := true) (s := Q) (by simp) (by simpa using hp false rfl)
      | pos =>
        refine ExecLe.pop_cons (σ := s.st) (k := 1) (b := true) (s := false :: Q) ?_ ?_
        · simp [hM, ic, Q]
        · exact ExecLe.pop_cons (b := false) (s := Q) (by simp) (by simpa using hp true rfl)
      | neg =>
        refine ExecLe.pop_cons (σ := s.st) (k := 1) (b := true) (s := true :: Q) ?_ ?_
        · simp [hM, ic, Q]
        · exact ExecLe.pop_cons (b := true) (s := Q) (by simp) (by simpa using hp false rfl)
    exact (ExecLe.loop_norm hb ih).cast (by simp [sv_bits]) (by simp; omega)

/-! ## The whole verifier -/

def tv_ver : Cmd :=
  .seq phaseA (.seq (trimC 2) (.seq (move 2 1) (.seq tv_frL (.seq (move 10 14)
    (.seq hv_pre tv_mainL)))))

/-- The answer of the verifier on `(w, y)`. -/
def tv_vres (w : List SatSym) (y : Str) : Bool :=
  match clauses w with
  | [] => false
  | Bd :: M => decide (3 ≤ M.length) &&
      tv_mainF M M.length (hv_tk M.length y) (sv_bits Bd) (M.length - 1) (y.drop M.length)
        (hv_tk M.length y) (List.replicate M.length false) []

theorem tv_ex_run (rows : List (List SatSym)) (Bd : Str) (y : Str) (Lr : ℕ) (hy : y.length ≤ Lr)
    (hsep : ∀ r ∈ rows, sep ∉ r) :
    ExecLe (.seq hv_pre tv_mainL) {hv_s0 y (enc rows) with H := Bd}.st
      (.halt (decide (3 ≤ rows.length) && tv_mainF rows rows.length (hv_tk rows.length y) Bd
        (rows.length - 1) (y.drop rows.length) (hv_tk rows.length y)
        (List.replicate rows.length false) []))
      (10 * (enc rows).length + 60 * rows.length + 3 * Lr + 70 +
        rows.length * (tv_Tb rows.length (enc rows).length (hv_Tsc rows.length rows)
          (rows.length * ((enc rows).length + 1)) + 1) +
        5 * (rows.length * ((enc rows).length + 1) + Bd.length) + 20) := by
  set n := rows.length
  set s0 : hv_HS := {hv_s0 y (enc rows) with H := Bd}
  have h1 := hv_ex_copy (a := 1) (b := 3) (by decide) (by decide) (by decide) s0.st rfl
  simp only [hv_st1, hv_st3, hv_u3, List.append_nil, s0] at h1
  have h2 := hv_ex_cntL (rows.flatMap (· ++ [sep])) {s0 with Q := enc rows} (by simp [enc])
  rw [hv_count_sep rows hsep] at h2
  simp only [List.append_nil, s0] at h2
  set s2 : hv_HS := {s0 with Q := [], N := List.replicate n true}
  have h3 := hv_ex_chk3 n s2 rfl rfl rfl
  have hlen : (enc rows).length = 2 * ((rows.map List.length).sum + rows.length) := by
    simp only [enc, length_flatMap_ic]; rw [sum_length_le]
  by_cases hn : 3 ≤ n
  · rw [if_pos hn] at h3
    have h4 := hv_ex_initI n s2 rfl rfl rfl
    have h5 := hv_ex_initS n {s2 with I := List.replicate (n - 1) true} rfl rfl rfl
    simp only at h5
    have h6 := hv_ex_takeN n
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ []} rfl rfl rfl rfl
    simp only at h6
    have h7 := hv_ex_copy (a := 7) (b := 8) (by decide) (by decide) (by decide)
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := hv_tk n y}.st rfl
    simp only [hv_st7, hv_st8, hv_u8] at h7
    have h8 := hv_ex_mvo (a := 7) (b := 6) (by decide) (by decide) (by decide)
      {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := hv_tk n y, Z := hv_tk n y ++ []}.st rfl
    simp only [hv_st7, hv_st6, hv_u7, hv_u6] at h8
    set s9 : hv_HS := {s2 with I := List.replicate (n - 1) true, S := List.replicate n false ++ [], R := y.drop n, Y := [], Z := hv_tk n y ++ [], X := hv_tk n y ++ []}
    have hi : tv_Inv rows n s9 := by
      constructor <;> simp [s9, s2, s0, hv_length_tk]
    have h9 := tv_ex_mainL rows n Lr (n * ((enc rows).length + 1)) hsep (n - 1) s9 hi rfl
      (by simp [s9]; omega) (by simp [s9, hv_length_tk])
      (by show 0 + (n - 1 + 1) * ((enc rows).length + 1) ≤ _; rw [Nat.sub_add_cancel (by omega)]; simp)
    simp only [s9, s2, s0, List.append_nil] at h3 h4 h5 h6 h7 h8 h9
    rw [show (n - 1 + 1) = n by omega] at h9
    refine (ExecLe.seq_norm (h1.seq_norm (h2.seq_norm (h3.seq_norm (h4.seq_norm (h5.seq_norm
      (h6.seq_norm (h7.seq_norm h8))))))) h9).cast (by simp [hn]) ?_
    simp [hv_length_tk]
    omega
  · rw [if_neg hn] at h3
    refine (ExecLe.seq_halt (h1.seq_norm (h2.seq_norm (ExecLe.seq_halt h3)))).cast
      (by simp [hn]) ?_
    simp
    omega

/-- Time bound of the verifier. -/
def tv_Tver (L : ℕ) : ℕ := 300 * (L + 2) ^ 3

theorem tv_bound (L W t n S b : ℕ) (h1 : b + S + (n + 1) = t) (h2 : t ≤ W) (h3 : 2 * W ≤ L) :
    3 * L + 4 + (4 * W + 6 + (2 * (2 * t) + 2 + (3 * b + 3 + (2 * b + 2 +
      (10 * (2 * (S + n)) + 60 * n + 3 * L + 70 +
        n * (60 * n + 20 * (2 * (S + n)) + (10 * S + n * (7 * n + 20) + 2 * n + 8) +
          8 * (n * (2 * (S + n) + 1)) + 80 + 1) +
        5 * (n * (2 * (S + n) + 1) + b) + 20))))) ≤ tv_Tver L := by
  have hn : n ≤ L := by omega
  have hD : S + n ≤ L := by omega
  have hnn : n * n ≤ L * L := Nat.mul_le_mul hn hn
  have hnD : n * (S + n) ≤ L * L := Nat.mul_le_mul hn hD
  have hX : 60 * n + 20 * (2 * (S + n)) + (10 * S + n * (7 * n + 20) + 2 * n + 8) +
      8 * (n * (2 * (S + n) + 1)) + 80 + 1 ≤ 23 * (L * L) + 140 * L + 89 := by nlinarith
  have hY := Nat.mul_le_mul hn hX
  unfold tv_Tver
  nlinarith

theorem tv_exec_ver (z : Str) :
    ExecLe tv_ver (init [z]).stk (.halt (tv_vres (dec z).1 (dec z).2)) (tv_Tver z.length) := by
  have hl := dec_length z
  set w := (dec z).1
  set y := (dec z).2
  have h0 : (init [z]).stk 0 = z := rfl
  have he : ∀ j, j ≠ 0 → (init [z]).stk j = [] := by
    intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [init]
  have hA := exec_phaseA z (init [z]).stk h0
  set σ₁ := update (update (init [z]).stk 0 y) 2 ((w.flatMap ic).reverse ++ (init [z]).stk 2)
  have hT := exec_trimC_word 2 w σ₁ (by simp [σ₁, he 2 (by decide)])
  set σ₂ := update σ₁ 2 (((trunc w).flatMap ic).reverse)
  have hM := exec_move (a := 2) (b := 1) (by decide) _ σ₂ rfl
  have hσ : update (update σ₂ 2 []) 1 ((σ₂ 2).reverse ++ σ₂ 1) =
      (hv_s0 y (enc (clauses w))).st := by
    funext j
    by_cases hj : j < 19
    · interval_cases j <;> simp [σ₂, σ₁, he, enc, trunc, hv_HS.st]
    · rw [hv_st_big _ _ (by omega)]
      simp [σ₂, σ₁, he j (by omega), show j ≠ 0 by omega, show j ≠ 1 by omega,
        show j ≠ 2 by omega]
  rw [hσ] at hM
  have hw : (trunc w).length ≤ w.length := length_trunc_le w
  have hcl := length_clauses_le w
  have hsum : ((clauses w).map List.length).sum + (clauses w).length = (trunc w).length :=
    sum_length_le _
  have htl : (σ₂ 2).length = 2 * (trunc w).length := by
    simp only [σ₂, update_self]; rw [List.length_reverse, length_flatMap_ic]
  have hpre : ∀ (c : Cmd) (r : Res) (T : ℕ), ExecLe c (hv_s0 y (enc (clauses w))).st r T →
      ExecLe (.seq phaseA (.seq (trimC 2) (.seq (move 2 1) c))) (init [z]).stk r
        (3 * z.length + 4 + (4 * w.length + 6 + (2 * (σ₂ 2).length + 2 + T))) :=
    fun c r T h => hA.seq_norm (hT.seq_norm ((ExecLe.of hM).seq_norm h))
  have hsep := sep_not_mem_clauses w
  unfold tv_vres tv_ver
  rcases hcw : clauses w with _ | ⟨Bd, M⟩
  · rw [hcw] at hpre
    have hf : ExecLe (.seq tv_frL (.seq (move 10 14) (.seq hv_pre tv_mainL)))
        (hv_s0 y (enc [])).st (.halt false) 2 :=
      ExecLe.seq_halt (ExecLe.loop_halt ((ExecLe.pop_nil (by simp [enc]) (ExecLe.halt false _)).cast
        rfl le_rfl))
    refine (hpre _ _ _ hf).cast rfl ?_
    have : z.length + 2 ≤ (z.length + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
    simp only [htl, tv_Tver]; omega
  · rw [hcw] at hsum hsep hpre hcl
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum hcl
    have hF := tv_ex_fr (enc M) Bd (hv_s0 y (enc (Bd :: M))) (hsep Bd (by simp))
      (by simp [enc_cons])
    simp only [List.append_nil] at hF
    have hM2 := exec_move (a := 10) (b := 14) (by decide) _
      {hv_s0 y (enc (Bd :: M)) with M := enc M, T := (sv_bits Bd).reverse}.st rfl
    simp only [hv_u10, hv_u14, hv_st10, hv_st14, List.reverse_reverse, List.append_nil] at hM2
    have hR := tv_ex_run M (sv_bits Bd) y z.length (by omega)
      (fun r hr => hsep r (by simp [hr]))
    refine (hpre _ _ _ (hF.seq_norm ((ExecLe.of hM2).seq_norm hR))).cast rfl ?_
    have hen : (enc M).length = 2 * ((M.map List.length).sum + M.length) := by
      simp only [enc, length_flatMap_ic]; rw [sum_length_le]
    rw [hv_Tsc_eq]
    simp only [tv_Tb, htl, hen, sv_bits, List.length_map, List.length_reverse]
    have hb := tv_bound z.length w.length (trunc w).length M.length (M.map List.length).sum
      Bd.length (by omega) hw (by omega)
    exact hb

theorem tv_Tver_le (n : ℕ) : tv_Tver n ≤ tb 12 n := by
  unfold tv_Tver tb
  have h9 : 2 ^ 9 ≤ (n + 2) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have e : (n + 2) ^ 12 = (n + 2) ^ 9 * (n + 2) ^ 3 := by ring
  rw [e]
  have : 300 ≤ (n + 2) ^ 9 := le_trans (by norm_num) h9
  exact Nat.mul_le_mul_right _ this

end Pnp.Karp.Tsp




