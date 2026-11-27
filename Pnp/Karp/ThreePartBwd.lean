import Pnp.Karp.ThreePartArith

/-!
# 3-PARTITION: a partition gives an exact cover (backward direction)
-/

namespace Pnp.Karp.ThreePart

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM

theorem tpb_fm_len {α : Type} (F : ℕ → List α) (k : ℕ) (hF : ∀ l, (F l).length = k) :
    ∀ m, ((List.range m).flatMap F).length = k * m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.flatMap_append]; simp [ih, hF]; ring

theorem tpb_fm_getD {α : Type} (F : ℕ → List α) (k : ℕ) (hF : ∀ l, (F l).length = k) (d : α) :
    ∀ m l j, l < m → j < k → ((List.range m).flatMap F).getD (k * l + j) d = (F l).getD j d := by
  intro m
  induction m with
  | zero => intro l j hl; omega
  | succ m ih =>
    intro l j hl hj
    have hlen := tpb_fm_len F k hF m
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
    · have : k * (l + 1) ≤ k * m := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact ih l j h hj
    · subst h
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
      simp [List.getD_eq_getElem?_getD]

theorem tpb_len (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) : (els q ts).length = 12 * ts.length + 9 * q := by
  unfold els
  rw [List.length_append, tpb_fm_len _ 12 (fun l => by simp [triBlk]),
    tpb_fm_len _ 3 (fun l => by simp [gadBlk])]
  ring

theorem tpb_E_tri (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (d : El) {i l j : ℕ} (hl : l < ts.length)
    (hj : j < 12) (hi : i = 12 * l + j) :
    (els q ts).getD i d = (triBlk l (ts.getD l (0, 0, 0))).getD j d := by
  subst hi
  have h12 : 12 * l + j < 12 * ts.length := by omega
  unfold els
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left
    (by rw [tpb_fm_len _ 12 (fun l => by simp [triBlk])]; omega), ← List.getD_eq_getElem?_getD]
  exact tpb_fm_getD _ 12 (fun l => by simp [triBlk]) d _ l j hl hj

theorem tpb_E_gad (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (d : El) {i u j : ℕ} (hu : u < 3 * q)
    (hj : j < 3) (hi : i = 12 * ts.length + 3 * u + j) :
    (els q ts).getD i d = (gadBlk q ts.length (u / q) (u % q)).getD j d := by
  subst hi
  unfold els
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right
    (by rw [tpb_fm_len _ 12 (fun l => by simp [triBlk])]; omega),
    tpb_fm_len _ 12 (fun l => by simp [triBlk]), ← List.getD_eq_getElem?_getD,
    show 12 * ts.length + 3 * u + j - 12 * ts.length = 3 * u + j by omega]
  exact tpb_fm_getD _ 3 (fun l => by simp [gadBlk]) d _ u j hu hj

theorem tpb_split {K q i : ℕ} (hi : i < 12 * K + 9 * q) :
    (∃ l j, l < K ∧ j < 12 ∧ i = 12 * l + j) ∨ ∃ u j, u < 3 * q ∧ j < 3 ∧ i = 12 * K + 3 * u + j := by
  by_cases h : i < 12 * K
  · exact Or.inl ⟨i / 12, i % 12, by omega, by omega, by omega⟩
  · exact Or.inr ⟨(i - 12 * K) / 3, (i - 12 * K) % 3, by omega, by omega, by omega⟩


theorem tpb_mem_ts {ts : List (ℕ × ℕ × ℕ)} {l : ℕ} (hl : l < ts.length) :
    ts.getD l (0, 0, 0) ∈ ts := by
  rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl

theorem tpb_ok (q : ℕ) (hq : 0 < q) (ts : List (ℕ × ℕ × ℕ))
    (hts : ∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (d : El) {i : ℕ}
    (hi : i < 12 * ts.length + 9 * q) : OkEl q (mT q ts) ((els q ts).getD i d) := by
  rcases tpb_split hi with ⟨l, j, hl, hj, rfl⟩ | ⟨u, j, hu, hj, rfl⟩
  · rw [tpb_E_tri q ts d hl hj rfl]
    have ht := hts _ (tpb_mem_ts hl)
    have : l < mT q ts := by unfold mT; omega
    generalize ts.getD l (0, 0, 0) = t at ht ⊢
    interval_cases j <;> simp [triBlk, OkEl, ht, this]
  · rw [tpb_E_gad q ts d hu hj rfl]
    have h1 : u / q < 3 := (Nat.div_lt_iff_lt_mul hq).2 (by omega)
    have h2 : u % q < q := Nat.mod_lt _ hq
    have h3 := Nat.div_add_mod' u q
    have h4 : ts.length + u / q * q + u % q < mT q ts := by unfold mT; omega
    interval_cases j <;> simp [gadBlk, OkEl, h1, h2, h4]

theorem tpb_v_al (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (d : El) {l c : ℕ} (s : Bool)
    (hl : l < ts.length) (hc : c < 3) :
    (els q ts).getD (12 * l + (3 + 2 * c + if s then 0 else 1)) d = .al c l s := by
  rw [tpb_E_tri q ts d hl (by split <;> omega) rfl]
  interval_cases c <;> cases s <;> rfl

theorem tpb_v_be (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (d : El) {l c : ℕ}
    (hl : l < ts.length) (hc : c < 3) :
    (els q ts).getD (12 * l + (9 + c)) d = .be c l (crd (ts.getD l (0, 0, 0)) c) := by
  rw [tpb_E_tri q ts d hl (by omega) rfl]
  interval_cases c <;> rfl

theorem tpb_v_cp (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (d : El) {p : ℕ} (hp : p < 3 * q) :
    (els q ts).getD (12 * ts.length + 3 * p) d = .cp (p / q) (p % q) true := by
  rw [tpb_E_gad q ts d hp (j := 0) (by omega) (by omega)]; rfl

theorem tpb_u_al (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (d : El) {i c t : ℕ} {s : Bool}
    (hi : i < 12 * ts.length + 9 * q) (h : (els q ts).getD i d = .al c t s) :
    (t < ts.length ∧ c < 3 ∧ i = 12 * t + (3 + 2 * c + if s then 0 else 1)) ∨
      (ts.length ≤ t ∧ s = false) := by
  rcases tpb_split hi with ⟨l, j, hl, hj, rfl⟩ | ⟨u, j, hu, hj, rfl⟩
  · rw [tpb_E_tri q ts d hl hj rfl] at h
    interval_cases j <;> simp [triBlk] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> simp [hl]
  · rw [tpb_E_gad q ts d hu hj rfl] at h
    interval_cases j <;> simp [gadBlk] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    right; simp; omega

theorem tpb_u_be (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (d : El) {i c t e : ℕ}
    (hi : i < 12 * ts.length + 9 * q) (ht : t < ts.length) (h : (els q ts).getD i d = .be c t e) :
    i = 12 * t + (9 + c) ∧ e = crd (ts.getD t (0, 0, 0)) c := by
  rcases tpb_split hi with ⟨l, j, hl, hj, rfl⟩ | ⟨u, j, hu, hj, rfl⟩
  · rw [tpb_E_tri q ts d hl hj rfl] at h
    interval_cases j <;> simp [triBlk] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> simp [crd]
  · rw [tpb_E_gad q ts d hu hj rfl] at h
    interval_cases j <;> simp [gadBlk] at h
    omega

theorem tpb_u_cp (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (d : El) {i c e : ℕ}
    (hi : i < 12 * ts.length + 9 * q) (h : (els q ts).getD i d = .cp c e true) :
    i = 12 * ts.length + 3 * (c * q + e) := by
  rcases tpb_split hi with ⟨l, j, hl, hj, rfl⟩ | ⟨u, j, hu, hj, rfl⟩
  · rw [tpb_E_tri q ts d hl hj rfl] at h
    interval_cases j <;> simp [triBlk] at h
  · rw [tpb_E_gad q ts d hu hj rfl] at h
    interval_cases j <;> simp [gadBlk] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Nat.div_add_mod', Nat.add_zero]


theorem tpb_p_be {G : List El} {c t e : ℕ} (hG : IsPat G) (h : El.be c t e ∈ G) :
    ∃ s, El.cp c e s ∈ G ∧ El.al c t s ∈ G ∧
      ∀ x ∈ G, x = .cp c e s ∨ x = .al c t s ∨ x = .be c t e := by
  rcases hG with ⟨c', e', t', s', hp⟩ | ⟨t', s', hp⟩
  · simp only [hp.mem_iff, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    simp at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨s', by simp, by simp, fun x hx => hx⟩
  · simp [hp.mem_iff] at h

theorem tpb_p_cp {G : List El} {c e : ℕ} {s : Bool} (hG : IsPat G) (h : El.cp c e s ∈ G) :
    ∃ t, El.al c t s ∈ G ∧ El.be c t e ∈ G := by
  rcases hG with ⟨c', e', t', s', hp⟩ | ⟨t', s', hp⟩
  · simp only [hp.mem_iff, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    simp at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨t', by simp, by simp⟩
  · simp [hp.mem_iff] at h

theorem tpb_p_al {G : List El} {c t : ℕ} {s : Bool} (hG : IsPat G) (h : El.al c t s ∈ G) :
    (∃ e, El.be c t e ∈ G) ∨ (El.al 0 t s ∈ G ∧ El.al 1 t s ∈ G ∧ El.al 2 t s ∈ G) := by
  rcases hG with ⟨c', e', t', s', hp⟩ | ⟨t', s', hp⟩
  · simp only [hp.mem_iff, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    simp at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨e', by simp⟩
  · simp only [hp.mem_iff, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    simp at h
    rcases h with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> simp

/-- The items of group `g`. -/
def tpb_G (E : List El) (f : ℕ → ℕ) (g : ℕ) : List El :=
  ((List.range E.length).filter fun i => f i = g).map fun i => E.getD i (.cp 0 0 false)

theorem tpb_mem_G {E : List El} {f : ℕ → ℕ} {g : ℕ} {x : El} :
    x ∈ tpb_G E f g ↔ ∃ j, j < E.length ∧ f j = g ∧ E.getD j (.cp 0 0 false) = x := by
  simp only [tpb_G, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq, and_assoc]

theorem tpb_covT (q p : ℕ) : ∀ (ts : List (ℕ × ℕ × ℕ)) (y : List Bool),
    covT q ts y p = ∑ l ∈ Finset.range ts.length,
      if (y.getD l false && decide (p = (ts.getD l (0, 0, 0)).1 ∨
        p = q + (ts.getD l (0, 0, 0)).2.1 ∨ p = 2 * q + (ts.getD l (0, 0, 0)).2.2)) then 1 else 0
  | [], _ => by simp [covT]
  | t :: ts, y => by
    rw [covT, tpb_covT q p ts y.tail, List.length_cons, Finset.sum_range_succ', add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      cases y <;> simp
    · cases y <;> simp


theorem tpb_st (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (f : ℕ → ℕ)
    (hG : ∀ j < 12 * ts.length + 9 * q, IsPat (tpb_G (els q ts) f (f j)))
    {l c : ℕ} (hl : l < ts.length) (hc : c < 3) :
    ∃ s : Bool, f (12 * l + (3 + 2 * c + if s then 0 else 1)) = f (12 * l + (9 + c)) ∧
      f (12 * l + (3 + 2 * c + if !s then 0 else 1)) ≠ f (12 * l + (9 + c)) ∧
      (∀ x ∈ tpb_G (els q ts) f (f (12 * l + (9 + c))),
        x = .cp c (crd (ts.getD l (0, 0, 0)) c) s ∨ x = .al c l s ∨
          x = .be c l (crd (ts.getD l (0, 0, 0)) c)) ∧
      ∀ c' < 3, f (12 * l + (3 + 2 * c' + if !s then 0 else 1)) =
        f (12 * l + (3 + 2 * c + if !s then 0 else 1)) := by
  have hn := tpb_len q ts
  have hb : 12 * l + (9 + c) < 12 * ts.length + 9 * q := by omega
  have hidx : ∀ (c' : ℕ) (s' : Bool), c' < 3 →
      12 * l + (3 + 2 * c' + if s' then 0 else 1) < 12 * ts.length + 9 * q := by
    intro c' s' hc'; split <;> omega
  obtain ⟨s, -, hal, hall⟩ := tpb_p_be (hG _ hb)
    (tpb_mem_G.2 ⟨_, by omega, rfl, tpb_v_be q ts _ hl hc⟩)
  obtain ⟨j, hj, hfj, hEj⟩ := tpb_mem_G.1 hal
  rcases tpb_u_al q ts _ (by omega) hEj with ⟨-, -, rfl⟩ | ⟨h1, -⟩
  swap; · omega
  have hne : f (12 * l + (3 + 2 * c + if !s then 0 else 1)) ≠ f (12 * l + (9 + c)) := by
    intro heq
    have := hall _ (tpb_mem_G.2 ⟨_, by have := hidx c (!s) hc; omega, heq,
      tpb_v_al q ts _ (!s) hl hc⟩)
    cases s <;> simp at this
  refine ⟨s, hfj, hne, hall, ?_⟩
  have hj' := hidx c (!s) hc
  have hm : El.al c l (!s) ∈
      tpb_G (els q ts) f (f (12 * l + (3 + 2 * c + if !s then 0 else 1))) :=
    tpb_mem_G.2 ⟨_, by omega, rfl, tpb_v_al q ts _ (!s) hl hc⟩
  rcases tpb_p_al (hG _ hj') hm with ⟨e', he'⟩ | ⟨h0, h1, h2⟩
  · obtain ⟨k, hk, hfk, hEk⟩ := tpb_mem_G.1 he'
    obtain ⟨rfl, -⟩ := tpb_u_be q ts _ (by omega) hl hEk
    exact absurd hfk.symm hne
  · have key : ∀ c' < 3, El.al c' l (!s) ∈
        tpb_G (els q ts) f (f (12 * l + (3 + 2 * c + if !s then 0 else 1))) := by
      intro c' hc'; interval_cases c' <;> assumption
    intro c' hc'
    obtain ⟨k, hk, hfk, hEk⟩ := tpb_mem_G.1 (key c' hc')
    rcases tpb_u_al q ts _ (by omega) hEk with ⟨-, -, rfl⟩ | ⟨h1, -⟩
    · exact hfk
    · omega

theorem tpb_unif (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (f : ℕ → ℕ)
    (hG : ∀ j < 12 * ts.length + 9 * q, IsPat (tpb_G (els q ts) f (f j)))
    {l c : ℕ} (hl : l < ts.length) (hc : c < 3) :
    f (12 * l + (3 + 2 * c + if true then 0 else 1)) = f (12 * l + (9 + c)) ↔
      f (12 * l + (3 + 2 * 0 + if true then 0 else 1)) = f (12 * l + (9 + 0)) := by
  have hn := tpb_len q ts
  obtain ⟨s, h1, h2, -, h4⟩ := tpb_st q ts f hG hl hc
  obtain ⟨s0, g1, g2, g3, -⟩ := tpb_st q ts f hG hl (c := 0) (by omega)
  have hs : s = s0 := by
    by_contra hne
    have hns : (!s) = s0 := by revert hne; cases s <;> cases s0 <;> decide
    have hf : f (12 * l + (3 + 2 * c + if !s then 0 else 1)) = f (12 * l + (9 + 0)) := by
      have := h4 0 (by omega); rw [hns] at this ⊢; rw [← this]; exact g1
    have hm := tpb_mem_G.2 ⟨_, by split <;> omega, hf, tpb_v_al q ts (.cp 0 0 false) (!s) hl hc⟩
    rcases g3 _ hm with h | h | h <;> simp at h
    obtain ⟨rfl, -⟩ := h
    rw [← hns] at g2
    simp only [Bool.not_not] at g2
    exact g2 h1
  subst hs
  cases s
  · simp only [Bool.not_false] at h2 g2
    exact iff_of_false h2 g2
  · exact iff_of_true h1 g1


theorem tpb_core (q : ℕ) (hq : 2 ≤ q) (ts : List (ℕ × ℕ × ℕ))
    (hts : ∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (f : ℕ → ℕ)
    (hG : ∀ j < 12 * ts.length + 9 * q, IsPat (tpb_G (els q ts) f (f j))) :
    ∃ y : List Bool, ∀ p < 3 * q, covT q ts y p = 1 := by
  have hn := tpb_len q ts
  have hq0 : 0 < q := by omega
  let Y : ℕ → Bool := fun l =>
    decide (f (12 * l + (3 + 2 * 0 + if true then 0 else 1)) = f (12 * l + (9 + 0)))
  refine ⟨(List.range ts.length).map Y, fun p hp => ?_⟩
  have hc : p / q < 3 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
  have he : p % q < q := Nat.mod_lt _ hq0
  have hpce : p / q * q + p % q = p := Nat.div_add_mod' p q
  generalize p / q = c at hc hpce
  generalize p % q = e at he hpce
  subst hpce
  have hdiv : (c * q + e) / q = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq0, Nat.div_eq_of_lt he, Nat.zero_add]
  have hmod : (c * q + e) % q = e := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]
  have hsel : ∀ l < ts.length, Y l = true → crd (ts.getD l (0, 0, 0)) c = e →
      f (12 * l + (9 + c)) = f (12 * ts.length + 3 * (c * q + e)) ∧
      ∀ x ∈ tpb_G (els q ts) f (f (12 * l + (9 + c))),
        x = .cp c e true ∨ x = .al c l true ∨ x = .be c l e := by
    intro l hl hy hce
    have h1 : f (12 * l + (3 + 2 * c + if true then 0 else 1)) = f (12 * l + (9 + c)) :=
      (tpb_unif q ts f hG hl hc).2 (by simpa [Y] using hy)
    have hb : 12 * l + (9 + c) < 12 * ts.length + 9 * q := by omega
    obtain ⟨s, hcp, -, hall⟩ := tpb_p_be (hG _ hb)
      (tpb_mem_G.2 ⟨_, by omega, rfl, hce ▸ tpb_v_be q ts _ hl hc⟩)
    have hs : s = true := by
      have := hall _ (tpb_mem_G.2 ⟨_, by simp; omega, h1, tpb_v_al q ts _ true hl hc⟩)
      simp at this
      exact this
    subst hs
    obtain ⟨k, hk, hfk, hEk⟩ := tpb_mem_G.1 hcp
    have := tpb_u_cp q ts _ (by omega) hEk
    subst this
    exact ⟨hfk.symm, hall⟩
  have ha : 12 * ts.length + 3 * (c * q + e) < 12 * ts.length + 9 * q := by omega
  have hva := tpb_v_cp q ts (.cp 0 0 false) hp
  rw [hdiv, hmod] at hva
  obtain ⟨t, hal, hbe⟩ := tpb_p_cp (hG _ ha) (tpb_mem_G.2 ⟨_, by omega, rfl, hva⟩)
  obtain ⟨j, hj, hfj, hEj⟩ := tpb_mem_G.1 hal
  rcases tpb_u_al q ts _ (by omega) hEj with ⟨htK, -, rfl⟩ | ⟨-, h⟩
  swap; · simp at h
  obtain ⟨k, hk, hfk, hEk⟩ := tpb_mem_G.1 hbe
  obtain ⟨rfl, hte⟩ := tpb_u_be q ts _ (by omega) htK hEk
  have hYt : Y t = true := by
    simp only [Y, decide_eq_true_eq]
    exact (tpb_unif q ts f hG htK hc).1 (hfj.trans hfk.symm)
  have hhit : ∀ l < ts.length, (c * q + e = (ts.getD l (0, 0, 0)).1 ∨
      c * q + e = q + (ts.getD l (0, 0, 0)).2.1 ∨ c * q + e = 2 * q + (ts.getD l (0, 0, 0)).2.2) ↔
      crd (ts.getD l (0, 0, 0)) c = e := by
    intro l hl
    have ht := hts _ (tpb_mem_ts hl)
    generalize ts.getD l (0, 0, 0) = x at ht ⊢
    clear hsel hva hYt hte hfj hfk hEj hEk hal hbe
    interval_cases c <;> simp [crd] <;> omega
  have hyg : ∀ l < ts.length, ((List.range ts.length).map Y).getD l false = Y l := by
    intro l hl; simp [List.getD_eq_getElem?_getD, hl]
  rw [tpb_covT, Finset.sum_eq_single_of_mem t (Finset.mem_range.2 htK)]
  · rw [if_pos]
    rw [hyg t htK, hYt, Bool.true_and, decide_eq_true_eq, hhit t htK]
    exact hte.symm
  · intro l hl hne
    rw [Finset.mem_range] at hl
    rw [if_neg]
    rw [hyg l hl]
    intro hh
    have hyl : Y l = true := Bool.and_eq_true_iff.1 hh |>.1
    have hcl := (hhit l hl).1 (of_decide_eq_true (Bool.and_eq_true_iff.1 hh).2)
    obtain ⟨hl1, -⟩ := hsel l hl hyl hcl
    obtain ⟨ht1, hallt⟩ := hsel t htK hYt hte.symm
    have hm : El.be c l e ∈ tpb_G (els q ts) f (f (12 * t + (9 + c))) :=
      tpb_mem_G.2 ⟨_, by omega, hl1.trans ht1.symm, hcl ▸ tpb_v_be q ts _ hl hc⟩
    rcases hallt _ hm with h | h | h <;> simp at h
    exact hne h


theorem cov_of_tp (q : ℕ) (hq : 2 ≤ q) (ts : List (ℕ × ℕ × ℕ))
    (hts : ∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) (h : TPLang (TPW q ts)) :
    ∃ y : List Bool, ∀ p < 3 * q, covT q ts y p = 1 := by
  obtain ⟨items, Bv, hc, -, -, f, hf, hsum⟩ := h
  have hn := tpb_len q ts
  have hcl : clauses (TPW q ts) = (els q ts).map (elRow q (mT q ts)) ++ [bRow q (mT q ts)] := by
    unfold TPW
    apply clauses_flatMap
    intro r hr
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨x, -, rfl⟩ | rfl
    · simp [elRow]
    · simp [bRow]
  rw [hcl] at hc
  obtain ⟨hi, hB⟩ := List.append_inj' hc.symm rfl
  have hBv : Bv = bRow q (mT q ts) := by simpa using hB
  subst hi hBv
  rw [List.length_map] at hf hsum
  refine tpb_core q hq ts hts f fun j hj => ?_
  have hg := hf j (by omega)
  have hs := hsum _ hg
  rw [tp_binSum_eq, List.length_map] at hs
  refine (tp_sum_iff q (mT q ts) hq _ fun x hx => ?_).1 ?_
  · obtain ⟨k, hk, -, rfl⟩ := tpb_mem_G.1 hx
    exact tpb_ok q (by omega) ts hts _ (by omega)
  · rw [← hs, tpb_G, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_filter, List.mem_range] at hi
    simp [List.getD_eq_getElem?_getD, hi.1, Function.comp]

end Pnp.Karp.ThreePart
