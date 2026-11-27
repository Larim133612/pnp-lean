import Pnp.Karp.SteinerVer
import Pnp.Karp.HamNP

/-!
# STEINER TREE ∈ NP (official definition)

The checking relation is `stv_vres w y = true` (`Pnp/Karp/SteinerVer.lean`).  For an instance
with rows `kr :: tr :: rows` (`n = |rows|`), the certificate is `[false]` if there is no terminal,
and otherwise `true :: B(v₀) ++ (true :: B(v₁)) ++ … ++ (true :: B(v_m))` where `B(v)` is the
one-hot block of `n` bits of the vertex `v` (`stv_blk`, `stv_enc`): `v₀` is a terminal and every
`v_i` is joined by an edge of the graph to an earlier vertex.

* `stv_sound`: if the main loop accepts, the attaching edges (one per listed vertex) form a set
  `F` of at most `|kr|` edges joining the first vertex to every terminal;
* `stv_main_ok`, `stv_card`, `stv_exists`: completeness.  From a connecting edge set `F`, list
  the vertices reachable from a terminal `t₀` along `F` in an order where each vertex is
  `F`-adjacent to an earlier one (grow the list while some `F`-edge leaves it); the attaching
  `F`-edges are pairwise distinct, so `m ≤ |F| ≤ |kr|`;
* `stv_lang_iff`: `STLang w ↔ ∃ y, |y| ≤ |w|² ∧ stv_vres w y`;
* `st_in_np`: `STLang ∈ NP`, via `stv_exec_ver` and `Pnp.TM2Hom.inPolynomialTime_of_code`.
-/

namespace Pnp.Karp.Steiner

open Function Pnp.Relativize Pnp.Relativize.Struct Pnp.CookLevin SatSym Pnp.Karp.Clique
  Pnp.Karp.Ham

/-! ## Bits -/

theorem stv_lt_of_getD {S : Str} {u : ℕ} (h : S.getD u false = true) : u < S.length := by
  by_contra hc
  rw [List.getD_eq_default _ _ (by omega)] at h
  exact absurd h (by decide)

theorem stv_tc_iff : ∀ (P S : Str), stv_tc P S = true ↔
    ∀ t < S.length, P.getD t false = true → S.getD t false = true
  | P, [] => by simp [stv_tc]
  | P, b :: S => by
    rw [stv_tc, Bool.and_eq_true, stv_tc_iff P.tail S]
    constructor
    · rintro ⟨h1, h2⟩ t ht hP
      rcases t with _ | t
      · cases b
        · cases P <;> simp_all
        · rfl
      · simp only [List.getD_cons_succ]
        exact h2 t (by simpa using ht) (by rwa [hv_getD_tail])
    · intro h
      refine ⟨?_, fun t ht hP => ?_⟩
      · have := h 0 (by simp)
        revert this
        rcases P with _ | ⟨_ | _, P⟩ <;> cases b <;> simp
      · have := h (t + 1) (by simp; omega) (by rwa [hv_getD_tail] at hP)
        simpa using this

theorem stv_getD_isPos : ∀ (tr : List SatSym) (t : ℕ),
    (tr.map isPos).getD t false = true ↔ tr.getD t zero = pos
  | [], t => by simp
  | x :: tr, 0 => by cases x <;> simp [isPos]
  | x :: tr, t + 1 => by simpa using stv_getD_isPos tr t

theorem stv_getD_rep (n w : ℕ) : (List.replicate n false).getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem stv_rtg_symm {F : Finset (ℕ × ℕ)} {a b : ℕ}
    (h : Relation.ReflTransGen (adjF F) a b) : Relation.ReflTransGen (adjF F) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (Or.symm hbc) ih

/-! ## Soundness -/

theorem stv_sound (rows : List (List SatSym)) (P : Str) : ∀ (c : ℕ) (R S : Str)
    (F : Finset (ℕ × ℕ)) (r : ℕ), S.length = rows.length → (∀ e ∈ F, IsEdge rows e) →
    (∀ v, S.getD v false = true → Relation.ReflTransGen (adjF F) r v) →
    stv_mainF rows rows.length P c R S = true →
    ∃ F' : Finset (ℕ × ℕ), F'.card ≤ F.card + c ∧ (∀ e ∈ F', IsEdge rows e) ∧
      ∀ t < rows.length, P.getD t false = true → Relation.ReflTransGen (adjF F') r t := by
  intro c
  induction c with
  | zero =>
    intro R S F r hS hF hr h
    rcases R with _ | ⟨_ | _, R⟩
    · simp only [stv_mainF, stv_tc_iff] at h
      exact ⟨F, by omega, hF, fun t ht hP => hr t (h t (by omega) hP)⟩
    · simp only [stv_mainF, stv_tc_iff] at h
      exact ⟨F, by omega, hF, fun t ht hP => hr t (h t (by omega) hP)⟩
    · simp [stv_mainF] at h
  | succ c ih =>
    intro R S F r hS hF hr h
    rcases R with _ | ⟨_ | _, R⟩
    · simp only [stv_mainF, stv_tc_iff] at h
      exact ⟨F, by omega, hF, fun t ht hP => hr t (h t (by omega) hP)⟩
    · simp only [stv_mainF, stv_tc_iff] at h
      exact ⟨F, by omega, hF, fun t ht hP => hr t (h t (by omega) hP)⟩
    · simp only [stv_mainF, Bool.and_eq_true] at h
      obtain ⟨⟨he, hp⟩, hm⟩ := h
      set n := rows.length
      set Y := hv_tk n R
      obtain ⟨x, hx1, hx2⟩ := (hv_permOk_iff _ _).1 hp
      have hYl : Y.length = n := hv_length_tk _ _
      have hxn : x < n := by
        have := stv_lt_of_getD (show Y.getD x false = true by rw [hx1]; simp)
        omega
      have hY : ∀ v, Y.getD v false = true → v = x := fun v hv => by
        rw [hx1] at hv; simpa using hv
      obtain ⟨u, v, hent, hcase⟩ := (hv_edgeB_iff _ _ _).1 he
      -- the attaching edge `e` joins `x` to a vertex `z` of `S`
      obtain ⟨e, z, heF, hzS, hadj⟩ : ∃ e : ℕ × ℕ, ∃ z, IsEdge rows e ∧ S.getD z false = true ∧
          ∀ G : Finset (ℕ × ℕ), e ∈ G → adjF G z x := by
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hv := hY v h2
          subst hv
          refine ⟨(u, v), u, ⟨by have := stv_lt_of_getD h1; omega, hxn, fun h => ?_, hent⟩, h1,
            fun G hG => Or.inl hG⟩
          simp only at h; rw [h, hx2] at h1; exact absurd h1 (by decide)
        · have hu := hY u h1
          subst hu
          refine ⟨(u, v), v, ⟨hxn, by have := stv_lt_of_getD h2; omega, fun h => ?_, hent⟩, h2,
            fun G hG => Or.inr hG⟩
          simp only at h; rw [← h, hx2] at h2; exact absurd h2 (by decide)
      have hmono : ∀ a b, Relation.ReflTransGen (adjF F) a b →
          Relation.ReflTransGen (adjF (insert e F)) a b := fun a b h =>
        h.mono fun a b h => h.imp (Finset.mem_insert_of_mem) (Finset.mem_insert_of_mem)
      obtain ⟨F', h1, h2, h3⟩ := ih (R.drop n) (hv_orV Y S) (insert e F) r
        (by rw [hv_length_orV, hYl])
        (by
          intro e' he'
          rcases Finset.mem_insert.1 he' with rfl | h
          · exact heF
          · exact hF e' h)
        (by
          intro w hw
          rw [hv_getD_orV, Bool.and_eq_true, Bool.or_eq_true] at hw
          rcases hw.2 with h | h
          · rw [hY w h]
            exact (hmono _ _ (hr z hzS)).tail (hadj _ (Finset.mem_insert_self _ _))
          · exact hmono _ _ (hr w h))
        hm
      refine ⟨F', ?_, h2, h3⟩
      have := Finset.card_insert_le e F
      omega

/-! ## Completeness -/

/-- The one-hot block of the vertex `v`. -/
def stv_blk (n v : ℕ) : Str := (List.range n).map fun u => decide (u = v)

/-- The indicator vector of the vertex list `A`. -/
def stv_Sv (n : ℕ) (A : List ℕ) : Str := (List.range n).map fun u => decide (u ∈ A)

/-- The certificate part listing the vertices `Ls`. -/
def stv_enc (n : ℕ) (Ls : List ℕ) : Str := Ls.flatMap fun v => true :: stv_blk n v

/-- Every vertex of `Ls` is `F`-adjacent to an earlier vertex (the list `A` is listed first). -/
def stv_Good (F : Finset (ℕ × ℕ)) : List ℕ → List ℕ → Prop
  | [], _ => True
  | v :: Ls, A => (∃ u ∈ A, adjF F v u) ∧ stv_Good F Ls (v :: A)

theorem stv_getD_range (n : ℕ) (f : ℕ → Bool) (u : ℕ) :
    ((List.range n).map f).getD u false = (decide (u < n) && f u) := by
  by_cases h : u < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [h]

theorem stv_length_blk (n v : ℕ) : (stv_blk n v).length = n := by simp [stv_blk]

theorem stv_length_Sv (n : ℕ) (A : List ℕ) : (stv_Sv n A).length = n := by simp [stv_Sv]

theorem stv_length_enc (n : ℕ) : ∀ Ls : List ℕ, (stv_enc n Ls).length = Ls.length * (n + 1)
  | [] => by simp [stv_enc]
  | v :: Ls => by
    have := stv_length_enc n Ls
    simp only [stv_enc, List.flatMap_cons, List.length_append, List.length_cons,
      stv_length_blk] at this ⊢
    rw [this]; ring

theorem stv_tk_append : ∀ (L rest : Str), hv_tk L.length (L ++ rest) = L
  | [], _ => rfl
  | b :: L, rest => by simp [hv_tk, stv_tk_append L rest]

theorem stv_ext {l₁ l₂ : Str} (hl : l₁.length = l₂.length)
    (h : ∀ i, l₁.getD i false = l₂.getD i false) : l₁ = l₂ := by
  refine List.ext_getElem hl fun i h1 h2 => ?_
  have := h i
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem stv_orV_blk (n v : ℕ) (A : List ℕ) :
    hv_orV (stv_blk n v) (stv_Sv n A) = stv_Sv n (v :: A) := by
  refine stv_ext (by rw [hv_length_orV, stv_length_blk, stv_length_Sv]) fun i => ?_
  rw [hv_getD_orV, stv_length_blk, stv_blk, stv_Sv, stv_Sv, stv_getD_range, stv_getD_range,
    stv_getD_range]
  by_cases hi : i < n <;> simp [hi]

theorem stv_Sv_nil (n : ℕ) : stv_Sv n [] = List.replicate n false := by
  refine stv_ext (by simp [stv_length_Sv]) fun i => ?_
  rw [stv_Sv, stv_getD_range, stv_getD_rep]; simp

theorem stv_permOk_blk (n v : ℕ) (A : List ℕ) (hv : v < n) (hA : v ∉ A) :
    hv_permOk (stv_blk n v) (stv_Sv n A) = true := by
  rw [hv_permOk_iff]
  refine ⟨v, fun w => ?_, ?_⟩
  · rw [stv_blk, stv_getD_range]
    by_cases hw : w = v
    · subst hw; simp [hv]
    · simp [hw]
  · rw [stv_Sv, stv_getD_range]; simp [hA]

theorem stv_main_ok (rows : List (List SatSym)) (F : Finset (ℕ × ℕ))
    (hF : ∀ e ∈ F, IsEdge rows e) (P : Str) : ∀ (Ls A : List ℕ) (c : ℕ),
    stv_Good F Ls A → (Ls ++ A).Nodup → (∀ x ∈ Ls ++ A, x < rows.length) → Ls.length ≤ c →
    (∀ t < rows.length, P.getD t false = true → t ∈ Ls ++ A) →
    stv_mainF rows rows.length P c (stv_enc rows.length Ls) (stv_Sv rows.length A) = true
  | [], A, c, _, _, hlt, _, hT => by
    rw [stv_enc, List.flatMap_nil]
    have e : stv_mainF rows rows.length P c [] (stv_Sv rows.length A) =
        stv_tc P (stv_Sv rows.length A) := by cases c <;> rfl
    rw [e, stv_tc_iff]
    intro t ht hP
    rw [stv_length_Sv] at ht
    rw [stv_Sv, stv_getD_range]
    simpa [ht] using hT t ht hP
  | v :: Ls, A, c, hG, hnd, hlt, hc, hT => by
    obtain ⟨⟨u, huA, hadj⟩, hG'⟩ := hG
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by simp at hc; omega⟩
    set n := rows.length
    have he : stv_enc n (v :: Ls) = true :: (stv_blk n v ++ stv_enc n Ls) := by
      simp [stv_enc]
    have htk : hv_tk n (stv_blk n v ++ stv_enc n Ls) = stv_blk n v := by
      have := stv_tk_append (stv_blk n v) (stv_enc n Ls)
      rwa [stv_length_blk] at this
    have hdr : (stv_blk n v ++ stv_enc n Ls).drop n = stv_enc n Ls := by
      have := List.drop_left (l₁ := stv_blk n v) (l₂ := stv_enc n Ls)
      rwa [stv_length_blk] at this
    have hvn : v < n := hlt v (by simp)
    have hun : u < n := hlt u (by simp [huA])
    have hvA : v ∉ A := fun h => by
      have := List.nodup_cons.1 hnd
      exact this.1 (List.mem_append_right _ h)
    rw [he]
    simp only [stv_mainF, htk, hdr, Bool.and_eq_true]
    refine ⟨⟨?_, stv_permOk_blk n v A hvn hvA⟩, ?_⟩
    · rw [hv_edgeB_iff]
      have hSu : (stv_Sv n A).getD u false = true := by
        rw [stv_Sv, stv_getD_range]; simp [hun, huA]
      have hBv : (stv_blk n v).getD v false = true := by
        rw [stv_blk, stv_getD_range]; simp [hvn]
      rcases hadj with h | h
      · exact ⟨v, u, (hF _ h).2.2.2, Or.inr ⟨hBv, hSu⟩⟩
      · exact ⟨u, v, (hF _ h).2.2.2, Or.inl ⟨hSu, hBv⟩⟩
    · rw [stv_orV_blk]
      refine stv_main_ok rows F hF P Ls (v :: A) c hG' ?_ ?_ (by simp at hc; omega) ?_
      · exact List.nodup_middle.2 hnd
      · intro x hx; exact hlt x (by simp at hx ⊢; tauto)
      · intro t ht hP; have := hT t ht hP; simp at this ⊢; tauto

theorem stv_card (F : Finset (ℕ × ℕ)) : ∀ (Ls A : List ℕ), stv_Good F Ls A →
    (Ls ++ A).Nodup → ∃ G ⊆ F, Ls.length ≤ G.card ∧ ∀ e ∈ G, e.1 ∈ Ls ∨ e.2 ∈ Ls
  | [], _, _, _ => ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | v :: Ls, A, hG, hnd => by
    classical
    obtain ⟨⟨u, huA, hadj⟩, hG'⟩ := hG
    obtain ⟨G, hGF, hcard, hend⟩ := stv_card F Ls (v :: A) hG' (List.nodup_middle.2 hnd)
    have hvL : v ∉ Ls := fun h => (List.nodup_cons.1 hnd).1 (List.mem_append_left _ h)
    have huL : u ∉ Ls := fun h => by
      have := (List.nodup_append.1 (List.nodup_cons.1 hnd).2).2.2
      exact this u h u huA rfl
    obtain ⟨e, heF, hev⟩ : ∃ e ∈ F, (e.1 = v ∧ e.2 = u) ∨ (e.1 = u ∧ e.2 = v) := by
      rcases hadj with h | h
      · exact ⟨_, h, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨_, h, Or.inr ⟨rfl, rfl⟩⟩
    have heG : e ∉ G := fun h => by
      rcases hend e h with h1 | h1 <;> rcases hev with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;>
        simp_all
    refine ⟨insert e G, Finset.insert_subset heF hGF, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem heG]; simp; omega
    · intro e' he'
      rcases Finset.mem_insert.1 he' with rfl | h
      · rcases hev with ⟨h2, _⟩ | ⟨_, h3⟩
        · left; simp [h2]
        · right; simp [h3]
      · rcases hend e' h with h1 | h1
        · left; simp [h1]
        · right; simp [h1]

theorem stv_Good_append (F : Finset (ℕ × ℕ)) (z : ℕ) : ∀ (Ls A : List ℕ),
    stv_Good F (Ls ++ [z]) A ↔ stv_Good F Ls A ∧ ∃ u ∈ Ls.reverse ++ A, adjF F z u
  | [], A => by simp [stv_Good]
  | v :: Ls, A => by
    simp only [List.cons_append, stv_Good, stv_Good_append F z Ls (v :: A)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    tauto

theorem stv_nodup_le {l : List ℕ} {n : ℕ} (h : l.Nodup) (hlt : ∀ x ∈ l, x < n) :
    l.length ≤ n := by
  classical
  rw [← List.toFinset_card_of_nodup h]
  calc l.toFinset.card ≤ (Finset.range n).card :=
        Finset.card_le_card fun x hx => Finset.mem_range.2 (hlt x (List.mem_toFinset.1 hx))
    _ = n := Finset.card_range n

theorem stv_exists (rows : List (List SatSym)) (F : Finset (ℕ × ℕ))
    (hF : ∀ e ∈ F, IsEdge rows e) (t0 : ℕ) (ht0 : t0 < rows.length) :
    ∃ Ls : List ℕ, stv_Good F Ls [t0] ∧ (Ls ++ [t0]).Nodup ∧
      (∀ x ∈ Ls ++ [t0], x < rows.length) ∧
      ∀ y ∈ Ls ++ [t0], ∀ z, adjF F y z → z ∈ Ls ++ [t0] := by
  set n := rows.length
  suffices H : ∀ (m : ℕ) (Ls : List ℕ), stv_Good F Ls [t0] → (Ls ++ [t0]).Nodup →
      (∀ x ∈ Ls ++ [t0], x < n) → n - Ls.length = m →
      ∃ Ls : List ℕ, stv_Good F Ls [t0] ∧ (Ls ++ [t0]).Nodup ∧ (∀ x ∈ Ls ++ [t0], x < n) ∧
        ∀ y ∈ Ls ++ [t0], ∀ z, adjF F y z → z ∈ Ls ++ [t0] from
    H _ [] trivial (by simp) (by simpa using ht0) rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro Ls hG hnd hlt hm
    by_cases hcl : ∀ y ∈ Ls ++ [t0], ∀ z, adjF F y z → z ∈ Ls ++ [t0]
    · exact ⟨Ls, hG, hnd, hlt, hcl⟩
    · push Not at hcl
      obtain ⟨y, hy, z, hyz, hz⟩ := hcl
      have hzn : z < n := by
        rcases hyz with h | h
        · exact (hF _ h).2.1
        · exact (hF _ h).1
      have hlen := stv_nodup_le hnd hlt
      simp only [List.length_append, List.length_singleton] at hlen
      refine ih (n - (Ls.length + 1)) (by omega) (Ls ++ [z]) ?_ ?_ ?_
        (by simp)
      · refine (stv_Good_append F z Ls [t0]).2 ⟨hG, y, ?_, Or.symm hyz⟩
        simp at hy ⊢; tauto
      · rw [List.append_assoc, List.singleton_append]
        exact List.nodup_middle.2 (List.nodup_cons.2 ⟨hz, hnd⟩)
      · intro x hx
        simp only [List.append_assoc, List.singleton_append, List.mem_append,
          List.mem_cons] at hx
        rcases hx with h | rfl | h
        · exact hlt x (by simp [h])
        · exact hzn
        · exact hlt x (by simp_all)

/-! ## Correctness -/

theorem stv_lang_iff (w : List SatSym) :
    STLang w ↔ ∃ y : Str, y.length ≤ w.length ^ 2 ∧ stv_vres w y = true := by
  classical
  have hcl := length_clauses_le w
  unfold STLang stv_vres
  rcases hc : clauses w with _ | ⟨kr, _ | ⟨tr, rows⟩⟩
  · simp
  · simp
  · rw [hc] at hcl
    simp only [List.length_cons] at hcl
    set n := rows.length
    set P := tr.map isPos
    have hP : ∀ t, P.getD t false = true ↔ tr.getD t zero = pos := stv_getD_isPos tr
    constructor
    · rintro ⟨kr', tr', rows', he, F, hcard, hF, hconn⟩
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      by_cases hT : ∃ t, IsTerm tr rows t
      · obtain ⟨t0, ht0⟩ := hT
        obtain ⟨Ls, hG, hnd, hlt, hcl'⟩ := stv_exists rows F hF t0 ht0.1
        obtain ⟨G, hGF, hGc, -⟩ := stv_card F Ls [t0] hG hnd
        have hLc : Ls.length ≤ kr.length := hGc.trans ((Finset.card_le_card hGF).trans hcard)
        have hreach : ∀ x, Relation.ReflTransGen (adjF F) t0 x → x ∈ Ls ++ [t0] := by
          intro x h
          induction h with
          | refl => simp
          | tail _ hbc ih => exact hcl' _ ih _ hbc
        refine ⟨true :: (stv_blk n t0 ++ stv_enc n Ls), ?_, ?_⟩
        · have hl := stv_nodup_le hnd hlt
          simp only [List.length_append, List.length_singleton] at hl
          simp only [List.length_cons, List.length_append, stv_length_blk, stv_length_enc]
          have h1 : (Ls.length + 1) * (n + 1) ≤ w.length * w.length :=
            Nat.mul_le_mul (by omega) (by omega)
          nlinarith
        · have htk : hv_tk n (stv_blk n t0 ++ stv_enc n Ls) = stv_blk n t0 := by
            have := stv_tk_append (stv_blk n t0) (stv_enc n Ls)
            rwa [stv_length_blk] at this
          have hdr : (stv_blk n t0 ++ stv_enc n Ls).drop n = stv_enc n Ls := by
            have := List.drop_left (l₁ := stv_blk n t0) (l₂ := stv_enc n Ls)
            rwa [stv_length_blk] at this
          simp only [stv_restF, show rows.length = n from rfl, htk, hdr, ← stv_Sv_nil,
            stv_orV_blk, Bool.and_eq_true]
          refine ⟨stv_permOk_blk n t0 [] ht0.1 (by simp), ?_⟩
          refine stv_main_ok rows F hF P Ls [t0] kr.length hG hnd hlt hLc ?_
          intro t ht hPt
          exact hreach t (hconn t0 t ht0 ⟨ht, (hP t).1 hPt⟩)
      · refine ⟨[false], by simp; nlinarith, ?_⟩
        simp only [stv_restF, stv_tc_iff]
        intro t ht hPt
        exact absurd ⟨by simpa using ht, (hP t).1 hPt⟩ (fun h => hT ⟨t, h⟩)
    · rintro ⟨y, -, hy⟩
      refine ⟨kr, tr, rows, rfl, ?_⟩
      rcases y with _ | ⟨_ | _, y⟩
      · simp only [stv_restF, stv_tc_iff] at hy
        refine ⟨∅, by simp, by simp, fun a b ha _ => ?_⟩
        have := hy a (by simpa using ha.1) ((hP a).2 ha.2)
        rw [stv_getD_rep] at this; exact absurd this (by decide)
      · simp only [stv_restF, stv_tc_iff] at hy
        refine ⟨∅, by simp, by simp, fun a b ha _ => ?_⟩
        have := hy a (by simpa using ha.1) ((hP a).2 ha.2)
        rw [stv_getD_rep] at this; exact absurd this (by decide)
      · simp only [stv_restF, Bool.and_eq_true] at hy
        obtain ⟨hp, hm⟩ := hy
        obtain ⟨x, hx1, hx2⟩ := (hv_permOk_iff _ _).1 hp
        obtain ⟨F', h1, h2, h3⟩ := stv_sound rows P kr.length (y.drop n)
          (hv_orV (hv_tk n y) (List.replicate n false)) ∅ x
          (by rw [hv_length_orV, hv_length_tk]) (by simp)
          (by
            intro v hv
            rw [hv_getD_orV, stv_getD_rep, Bool.or_false, hx1] at hv
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
            rw [hv.2]) hm
        refine ⟨F', by simpa using h1, h2, fun a b ha hb => ?_⟩
        exact (stv_rtg_symm (h3 a ha.1 ((hP a).2 ha.2))).trans (h3 b hb.1 ((hP b).2 hb.2))

/-! ## Transfer to the official class -/

/-- **STEINER TREE ∈ NP** for the official class `NP`
(`Millennium.InNondeterministicPolynomialTime`). -/
theorem st_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym)
      STLang := by
  classical
  have hrun := fun z => ((stv_exec_ver z).mono (hv_Tver_le z.length)).runFor_toProg
  let S : Set Str :=
    {z | runFor ∅ (toProg stv_ver) (tb 11 z.length) (.run (init [z])) = .done true}
  have hS : S ∈ P ∅ := ⟨toProg stv_ver, 11, fun z => ⟨_, hrun z, by
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [z]).stk⟩) = _
    rw [hrun z]; simp⟩⟩
  have hR : Millennium.PolynomialTimeCheckingRelation (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string Bool) (fun w y => stv_vres w y = true) := by
    refine Pnp.TM2Hom.inPolynomialTime_of_code _ pc S hS _ (fun t => ?_)
    obtain ⟨w, y⟩ := t
    erw [flatMap_pair]
    show _ ↔ runFor ∅ _ _ (.run ⟨0, (init [_]).stk⟩) = _
    rw [hrun, dec_code]
    simp only [State.done.injEq]
  refine ⟨Bool, inferInstance, fun w y => stv_vres w y = true, 2, hR, fun w => ?_⟩
  rw [stv_lang_iff]
  simp only [Millennium.fin_encoding_string_encode]
  exact Iff.rfl

end Pnp.Karp.Steiner
