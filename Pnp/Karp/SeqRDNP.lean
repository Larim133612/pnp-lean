import Pnp.Karp.SeqRDVer

/-!
# Unary SEQUENCING WITH RELEASE TIMES AND DEADLINES ∈ NP (official definition)

The checking relation is `srv_vres w y = true` (`Pnp/Karp/SeqRDVer.lean`):

* `srv_go_sound`: an accepted certificate gives start times with the release times, deadlines
  and pairwise non-overlap of `SRDLang` (and disjointness from the intervals `P`);
* `srv_go_cert`: the unary code `srv_cert s k` of a schedule `s` is accepted;
* `srv_lang_iff`: `SRDLang w ↔ ∃ y, |y| ≤ |w|² ∧ srv_vres w y`;
* `srd_in_np`: `SRDLang ∈ NP`, via `srv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.SeqRD

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.SubsetSum Pnp.Karp.Knapsack Pnp.Karp.BinPacking Pnp.Karp.ThreePart
  Pnp.Karp.ThreePartU

/-! ## Shifting the tasks -/

section Shift
variable (l r d : List SatSym) (rs : List (List SatSym)) (i : ℕ)

theorem srv_tLen0 : tLen (l :: r :: d :: rs) 0 = l.length := rfl
theorem srv_tRel0 : tRel (l :: r :: d :: rs) 0 = r.length := rfl
theorem srv_tDl0 : tDl (l :: r :: d :: rs) 0 = d.length := rfl

theorem srv_tLenS : tLen (l :: r :: d :: rs) (i + 1) = tLen rs i := by
  simp [tLen, show 3 * (i + 1) = 3 * i + 1 + 1 + 1 by ring]
theorem srv_tRelS : tRel (l :: r :: d :: rs) (i + 1) = tRel rs i := by
  simp [tRel, show 3 * (i + 1) + 1 = 3 * i + 1 + 1 + 1 + 1 by ring]
theorem srv_tDlS : tDl (l :: r :: d :: rs) (i + 1) = tDl rs i := by
  simp [tDl, show 3 * (i + 1) + 2 = 3 * i + 2 + 1 + 1 + 1 by ring]

end Shift

theorem srv_ok_iff (s e : ℕ) : ∀ P : List (ℕ × ℕ),
    srv_ok s e P = true ↔ ∀ p ∈ P, p.2 ≤ s ∨ e ≤ p.1
  | [] => by simp [srv_ok]
  | p :: P => by
    simp only [srv_ok, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, srv_ok_iff s e P,
      List.mem_cons, forall_eq_or_imp]

/-- The schedule conditions for the rows `rs` and the earlier intervals `P`. -/
def srv_Sch (P : List (ℕ × ℕ)) (rs : List (List SatSym)) (s : ℕ → ℕ) : Prop :=
  (∀ i < rs.length / 3, tRel rs i ≤ s i ∧ s i + tLen rs i ≤ tDl rs i) ∧
    (∀ i < rs.length / 3, ∀ j < rs.length / 3, i ≠ j →
      s i + tLen rs i ≤ s j ∨ s j + tLen rs j ≤ s i) ∧
    ∀ i < rs.length / 3, ∀ p ∈ P, p.2 ≤ s i ∨ s i + tLen rs i ≤ p.1

/-! ## Certificate → schedule -/

theorem srv_go_sound : ∀ (P : List (ℕ × ℕ)) (rs : List (List SatSym)) (Y : Str),
    srv_go P rs Y = true → rs.length % 3 = 0 ∧ ∃ s, srv_Sch P rs s
  | P, [], _, _ => ⟨rfl, fun _ => 0, by simp [srv_Sch]⟩
  | _, [_], _, h => by simp [srv_go] at h
  | _, [_, _], _, h => by simp [srv_go] at h
  | P, l :: r :: d :: rs, Y, h => by
    rw [show srv_go P (l :: r :: d :: rs) Y = (srv_chk P l r d Y && srv_go
      (((srv_rdU Y).1, (srv_rdU Y).1 + l.length) :: P) rs (srv_rdU Y).2) from rfl,
      Bool.and_eq_true] at h
    obtain ⟨hc, hg⟩ := h
    simp only [srv_chk, Bool.and_eq_true, decide_eq_true_eq, srv_ok_iff] at hc
    obtain ⟨⟨hr, hd⟩, hok⟩ := hc
    obtain ⟨hm, s', h1, h2, h3⟩ := srv_go_sound _ rs _ hg
    set s0 := (srv_rdU Y).1
    have hk : (l :: r :: d :: rs).length / 3 = rs.length / 3 + 1 := by simp; omega
    refine ⟨by simp; omega, fun i => match i with | 0 => s0 | i + 1 => s' i, ?_, ?_, ?_⟩
    · intro i hi
      rw [hk] at hi
      rcases i with _ | i
      · exact ⟨hr, hd⟩
      · rw [srv_tRelS, srv_tLenS, srv_tDlS]; exact h1 i (by omega)
    · intro i hi j hj hij
      rw [hk] at hi hj
      rcases i with _ | i <;> rcases j with _ | j
      · exact absurd rfl hij
      · have := h3 j (by omega) _ (List.mem_cons_self ..)
        simp only [srv_tLen0, srv_tLenS]
        omega
      · have := h3 i (by omega) _ (List.mem_cons_self ..)
        simp only [srv_tLen0, srv_tLenS]
        omega
      · simp only [srv_tLenS]
        exact h2 i (by omega) j (by omega) (by omega)
    · intro i hi p hp
      rw [hk] at hi
      rcases i with _ | i
      · exact hok p hp
      · rw [srv_tLenS]; exact h3 i (by omega) p (List.mem_cons_of_mem _ hp)

/-! ## Schedule → certificate -/

/-- The unary code of the start times `s 0, …, s (k - 1)`. -/
def srv_cert (s : ℕ → ℕ) : ℕ → Str
  | 0 => []
  | k + 1 => tpuv_u (s 0) ++ false :: srv_cert (fun i => s (i + 1)) k

theorem srv_cert_length (M : ℕ) : ∀ (k : ℕ) (s : ℕ → ℕ), (∀ i < k, s i ≤ M) →
    (srv_cert s k).length ≤ k * (M + 1)
  | 0, _, _ => by simp [srv_cert]
  | k + 1, s, h => by
    have ih := srv_cert_length M k (fun i => s (i + 1)) (fun i hi => h (i + 1) (by omega))
    have := h 0 (by omega)
    simp only [srv_cert, List.length_append, List.length_cons, tpuv_u_length]
    rw [Nat.succ_mul]; omega

theorem srv_go_cert : ∀ (P : List (ℕ × ℕ)) (rs : List (List SatSym)) (s : ℕ → ℕ),
    rs.length % 3 = 0 → srv_Sch P rs s → srv_go P rs (srv_cert s (rs.length / 3)) = true
  | P, [], _, _, _ => rfl
  | _, [_], _, h, _ => by simp at h
  | _, [_, _], _, h, _ => by simp at h
  | P, l :: r :: d :: rs, s, hm, ⟨h1, h2, h3⟩ => by
    have hk : (l :: r :: d :: rs).length / 3 = rs.length / 3 + 1 := by simp; omega
    rw [hk, srv_cert]
    rw [show srv_go P (l :: r :: d :: rs) (tpuv_u (s 0) ++ false ::
        srv_cert (fun i => s (i + 1)) (rs.length / 3)) =
      (srv_chk P l r d (tpuv_u (s 0) ++ false :: srv_cert (fun i => s (i + 1)) (rs.length / 3))
        && srv_go (((srv_rdU (tpuv_u (s 0) ++ false :: srv_cert (fun i => s (i + 1))
          (rs.length / 3))).1, (srv_rdU (tpuv_u (s 0) ++ false :: srv_cert (fun i => s (i + 1))
          (rs.length / 3))).1 + l.length) :: P) rs (srv_rdU (tpuv_u (s 0) ++ false ::
          srv_cert (fun i => s (i + 1)) (rs.length / 3))).2) from rfl]
    simp only [srv_rdU_u, Bool.and_eq_true]
    have h0 := h1 0 (by omega)
    rw [srv_tRel0, srv_tLen0, srv_tDl0] at h0
    refine ⟨?_, srv_go_cert _ rs _ (by simp at hm; omega) ⟨?_, ?_, ?_⟩⟩
    · simp only [srv_chk, srv_rdU_u, Bool.and_eq_true, decide_eq_true_eq, srv_ok_iff]
      refine ⟨h0, fun p hp => ?_⟩
      have := h3 0 (by omega) p hp
      rwa [srv_tLen0] at this
    · intro i hi
      have := h1 (i + 1) (by omega)
      rwa [srv_tRelS, srv_tLenS, srv_tDlS] at this
    · intro i hi j hj hij
      have := h2 (i + 1) (by omega) (j + 1) (by omega) (by omega)
      rwa [srv_tLenS, srv_tLenS] at this
    · intro i hi p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · have := h2 0 (by omega) (i + 1) (by omega) (by omega)
        rw [srv_tLen0, srv_tLenS] at this
        simp only
        omega
      · have := h3 (i + 1) (by omega) p hp
        rwa [srv_tLenS] at this

/-! ## The language -/

theorem srv_getD_le (w : List SatSym) (n : ℕ) : ((clauses w).getD n []).length ≤ w.length := by
  by_cases hn : n < (clauses w).length
  · rw [List.getD_eq_getElem _ _ hn]
    exact srv_row_le w _ (List.getElem_mem hn)
  · rw [List.getD_eq_default _ _ (by omega)]; simp

theorem srv_lang_iff (w : List SatSym) :
    SRDLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ srv_vres w y = true := by
  constructor
  · rintro ⟨hm, s, h1, h2⟩
    have hS : srv_Sch [] (clauses w) s := ⟨h1, h2, by simp⟩
    refine ⟨srv_cert s ((clauses w).length / 3), ?_, srv_go_cert [] _ s hm hS⟩
    have hb : ∀ i < (clauses w).length / 3, s i ≤ w.length := by
      intro i hi
      have := (h1 i hi).2
      have := srv_getD_le w (3 * i + 2)
      unfold tDl at *
      omega
    have hc := srv_cert_length w.length _ s hb
    have hcl := length_clauses_le w
    set k := (clauses w).length / 3
    have h3 : 3 * k ≤ w.length := by omega
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · simp [h0, srv_cert]
    · rw [pow_two]; nlinarith
  · rintro ⟨y, -, hy⟩
    obtain ⟨hm, s, h1, h2, -⟩ := srv_go_sound [] (clauses w) y hy
    exact ⟨hm, s, h1, h2⟩

/-! ## Transfer to the official class -/

/-- **Unary SEQUENCING WITH RELEASE TIMES AND DEADLINES ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem srd_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      SRDLang := by
  classical
  have hrun := fun z => ((srv_exec_ver z).mono (srv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg srv_ver) (tb 9 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg srv_ver, 9, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => srv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => srv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [srv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.SeqRD
