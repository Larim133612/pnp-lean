import Pnp.Algebrization.Interpolation
import Pnp.Oracle.BGS

/-!
# `P = NP` does not algebrize (Aaronson–Wigderson, one half of Thm 5.3)

Aaronson and Wigderson, *Algebrization: A New Barrier in Complexity Theory* (STOC 2008;
ACM TOCT 2009), Theorem 5.3: there are an oracle `A` and a multiquadratic extension `Ã`
of `A` with `NP^A ⊄ P^Ã`.  We prove it for the test language `LB A` of Baker–Gill–Solovay
(`Pnp.Oracle.BGS`), which lies in `NP^A` by `LB_mem_NP`.

The diagonalization mirrors `Pnp.Relativize.BGS`.  Stage `i` handles machine
`enum i = (prog, k)`:

* pick a length `n ≥ bound` with `tb k n < 2^n` and run `prog` on `0^n` for `tb k n` steps
  with the current algebraic oracle (as a Boolean oracle, `toOracle`);
* the run makes fewer than `2^n` queries; each well-formed query `encQ p j xs` names
  (by injectivity of `encQ`) a single point of a single field `ZMod p`.  For each prime
  `p`, the multiquadratic interpolation lemma `exists_vanishing_indicator`
  (A–W Lemma 4.2 style: a multiquadratic polynomial vanishing on `t` prescribed points
  that is the indicator of `z` on `{0,1}^n` exists for all but `t` Boolean `z`) excludes at
  most `|Y_p|` Boolean points, where `Y_p` is the set of queried points over `ZMod p`;
  a union bound gives a string `w ∈ {0,1}^n` that is not excluded for any prime;
* if the machine accepts, nothing changes; otherwise `w` is added to `A`, and at arity
  `n` every `Ã_{p,n}` becomes the vanishing indicator of `w` — which is `0` on every
  point the machine queried, exactly as before the stage;
* the next bound exceeds `n` and all query lengths, so later stages only touch arities
  that this stage's queries never mention.

Hence the final `Ã` answers every query of stage `i` as stage `i` did, the run transfers
(`runFor_eq_of_agree`), and machine `i` errs on `0^n`.
-/

namespace Pnp.Algebrize

open Pnp.Relativize MvPolynomial

/-! ### Injectivity of the query encoding -/

theorem bin_succ (n : ℕ) : bin (n + 1) = (n % 2 == 1) :: bin (n / 2) := by
  rw [bin]

theorem bin_zero : bin 0 = [] := by
  rw [bin]

/-- Binary digits determine the number. -/
theorem bin_injective : Function.Injective bin := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b h
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · rw [bin_zero, bin_succ] at h; exact absurd h (List.cons_ne_nil _ _).symm
  · rw [bin_zero, bin_succ] at h; exact absurd h (List.cons_ne_nil _ _)
  · rw [bin_succ, bin_succ] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    have h3 := ih (a / 2) (by omega) h2
    have h4 : a % 2 = b % 2 := by
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp_all
    omega

/-- The doubled-bit code followed by the terminator `false` is prefix-free. -/
theorem bits_prefix_free : ∀ (l l' : List Bool) (s s' : Str),
    (l.flatMap fun b => [true, b]) ++ [false] ++ s =
      (l'.flatMap fun b => [true, b]) ++ [false] ++ s' → l = l' ∧ s = s' := by
  intro l
  induction l with
  | nil =>
    intro l' s s' h
    cases l' with
    | nil => simpa using h
    | cons b l' => simp at h
  | cons b l ih =>
    intro l' s s' h
    cases l' with
    | nil => simp at h
    | cons b' l' =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc,
        List.cons.injEq, true_and] at h
      obtain ⟨rfl, h⟩ := h
      have := ih l' s s' (by simpa using h)
      exact ⟨by rw [this.1], this.2⟩

/-- `encNat` is prefix-free. -/
theorem encNat_append_inj {a b : ℕ} {s s' : Str} (h : encNat a ++ s = encNat b ++ s') :
    a = b ∧ s = s' := by
  unfold encNat at h
  obtain ⟨h1, h2⟩ := bits_prefix_free _ _ s s' h
  exact ⟨bin_injective h1, h2⟩


/-- A concatenation of `encNat` codes determines the list. -/
theorem flatten_encNat_inj : ∀ {xs ys : List ℕ},
    (xs.map encNat).flatten = (ys.map encNat).flatten → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys =>
      have := length_encNat_pos y
      have h' := congrArg List.length h
      simp only [List.map_nil, List.flatten_nil, List.length_nil, List.map_cons,
        List.flatten_cons, List.length_append] at h'
      omega
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have := length_encNat_pos x
      have h' := congrArg List.length h
      simp only [List.map_nil, List.flatten_nil, List.length_nil, List.map_cons,
        List.flatten_cons, List.length_append] at h'
      omega
    | cons y ys =>
      simp only [List.map_cons, List.flatten_cons] at h
      obtain ⟨hxy, hr⟩ := encNat_append_inj h
      rw [hxy, ih hr]

/-- The query encoding is injective. -/
theorem encQ_inj {p j p' j' : ℕ} {xs xs' : List ℕ} (h : encQ p j xs = encQ p' j' xs') :
    p = p' ∧ j = j' ∧ xs = xs' := by
  unfold encQ at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨h1, h⟩ := encNat_append_inj h
  obtain ⟨h2, h3⟩ := encNat_append_inj h
  exact ⟨h1, h2, flatten_encNat_inj h3⟩

/-- A query as a single triple. -/
def enc3 (t : ℕ × ℕ × List ℕ) : Str := encQ t.1 t.2.1 t.2.2

theorem enc3_injective : Function.Injective enc3 := by
  rintro ⟨p, j, xs⟩ ⟨p', j', xs'⟩ h
  obtain ⟨rfl, rfl, rfl⟩ := encQ_inj h
  rfl

/-! ### The points touched by a list of queries -/

/-- The well-formed queries `(p, j, xs)` occurring in `qs`. -/
noncomputable def D (qs : List Str) : Finset (ℕ × ℕ × List ℕ) :=
  qs.toFinset.preimage enc3 enc3_injective.injOn

theorem mem_D {qs : List Str} {t : ℕ × ℕ × List ℕ} : t ∈ D qs ↔ enc3 t ∈ qs := by
  simp [D]

theorem card_D_le (qs : List Str) : (D qs).card ≤ qs.length :=
  (Finset.card_le_card_of_injOn enc3 (fun t ht => by simpa [mem_D] using ht)
    enc3_injective.injOn).trans (List.toFinset_card_le qs)

/-- A list of naturals as a point of `(ZMod p)^m` (no length bookkeeping). -/
def ptm (p m : ℕ) (xs : List ℕ) : Fin m → ZMod p := fun k => ((xs.getD k 0 : ℕ) : ZMod p)

theorem pt_eq_ptm (p : ℕ) (xs : List ℕ) : pt p xs = ptm p xs.length xs := by
  funext k
  simp [pt, ptm, List.getD_eq_getElem?_getD]

/-- The points of `(ZMod p)^m` queried in `qs`. -/
noncomputable def Y (qs : List Str) (p m : ℕ) : Finset (Fin m → ZMod p) :=
  (((D qs).filter fun t => t.1 = p).filter fun t => t.2.2.length = m).image
    fun t => ptm p m t.2.2

theorem card_Y_le (qs : List Str) (p m : ℕ) :
    (Y qs p m).card ≤ ((D qs).filter fun t => t.1 = p).card :=
  Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _))

theorem ptm_mem_Y {qs : List Str} {p j : ℕ} {xs : List ℕ} (h : encQ p j xs ∈ qs) :
    ptm p xs.length xs ∈ Y qs p xs.length := by
  unfold Y
  refine Finset.mem_image.2 ⟨(p, j, xs), ?_, rfl⟩
  simpa [mem_D, enc3] using h

/-! ### Vanishing indicator polynomials -/

/-- `exists_vanishing_indicator` for the prime field `ZMod p` and the queried points. -/
theorem exists_vi (qs : List Str) (p m : ℕ) (hp : p.Prime) :
    ∃ Bad : Finset (Fin m → Bool), Bad.card ≤ (Y qs p m).card ∧ ∀ z ∉ Bad,
      ∃ q : MvPolynomial (Fin m) (ZMod p), (∀ i, q.degreeOf i ≤ 2) ∧
        (∀ y ∈ Y qs p m, eval y q = 0) ∧
        ∀ z' : Fin m → Bool, eval (boolPt z') q = if z' = z then 1 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact exists_vanishing_indicator m (Y qs p m)

/-- The exceptional Boolean points for prime `p` and arity `m`. -/
noncomputable def badSet (qs : List Str) (p m : ℕ) : Finset (Fin m → Bool) :=
  if hp : p.Prime then Classical.choose (exists_vi qs p m hp) else ∅

open Classical in
/-- A multiquadratic polynomial vanishing on the queried points and equal to the indicator
of `z` on the cube (or `0` if `z` is exceptional or `p` is not prime). -/
noncomputable def poly (qs : List Str) (p m : ℕ) (z : Fin m → Bool) :
    MvPolynomial (Fin m) (ZMod p) :=
  if hp : p.Prime then
    if hz : z ∉ Classical.choose (exists_vi qs p m hp) then
      Classical.choose ((Classical.choose_spec (exists_vi qs p m hp)).2 z hz)
    else 0
  else 0

theorem card_badSet_le (qs : List Str) (p m : ℕ) : (badSet qs p m).card ≤ (Y qs p m).card := by
  unfold badSet
  split_ifs with hp
  · exact (Classical.choose_spec (exists_vi qs p m hp)).1
  · simp

theorem poly_degreeOf (qs : List Str) (p m : ℕ) (z : Fin m → Bool) (k : Fin m) :
    (poly qs p m z).degreeOf k ≤ 2 := by
  unfold poly
  by_cases hp : p.Prime
  · rw [dif_pos hp]
    by_cases hz : z ∉ Classical.choose (exists_vi qs p m hp)
    · rw [dif_pos hz]
      exact (Classical.choose_spec ((Classical.choose_spec (exists_vi qs p m hp)).2 z hz)).1 k
    · rw [dif_neg hz, degreeOf_zero]; omega
  · rw [dif_neg hp, degreeOf_zero]; omega

theorem poly_spec {qs : List Str} {p m : ℕ} {z : Fin m → Bool} (hp : p.Prime)
    (hz : z ∉ badSet qs p m) :
    (∀ y ∈ Y qs p m, eval y (poly qs p m z) = 0) ∧
      ∀ z' : Fin m → Bool, eval (boolPt z') (poly qs p m z) = if z' = z then 1 else 0 := by
  unfold badSet at hz
  rw [dif_pos hp] at hz
  unfold poly
  rw [dif_pos hp, dif_pos hz]
  exact (Classical.choose_spec ((Classical.choose_spec (exists_vi qs p m hp)).2 z hz)).2

/-- A string read as a Boolean point of arity `m`. -/
def zf (w : Str) (m : ℕ) : Fin m → Bool := fun k => w.getD k false

theorem ofFn_eq_iff {w : Str} {m : ℕ} (hw : w.length = m) (z : Fin m → Bool) :
    List.ofFn z = w ↔ z = zf w m := by
  constructor
  · rintro rfl
    funext k
    simp [zf, List.getD_eq_getElem?_getD]
  · rintro rfl
    apply List.ext_getElem (by simp [hw])
    intro k h1 h2
    simp [zf, List.getD_eq_getElem?_getD, h2]

/-- Fewer than `2^n` queries leave a Boolean point outside every exceptional set. -/
theorem exists_good (qs : List Str) (n : ℕ) (h : qs.length < 2 ^ n) :
    ∃ w : Str, w.length = n ∧ ∀ p, zf w n ∉ badSet qs p n := by
  classical
  set PS := (D qs).image Prod.fst
  set U := PS.biUnion fun p => badSet qs p n
  have hU : U.card < (Finset.univ : Finset (Fin n → Bool)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    calc U.card ≤ ∑ p ∈ PS, (badSet qs p n).card := Finset.card_biUnion_le
      _ ≤ ∑ p ∈ PS, ((D qs).filter fun t => t.1 = p).card :=
          Finset.sum_le_sum fun p _ => (card_badSet_le qs p n).trans (card_Y_le qs p n)
      _ = (D qs).card := (Finset.card_eq_sum_card_image _ _).symm
      _ ≤ qs.length := card_D_le qs
      _ < 2 ^ n := h
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hU
  refine ⟨List.ofFn z, List.length_ofFn, fun p => ?_⟩
  rw [← (ofFn_eq_iff List.length_ofFn z).1 rfl]
  by_cases hp : p ∈ PS
  · exact fun hb => hz (Finset.mem_biUnion.2 ⟨p, hp, hb⟩)
  · have hY : Y qs p n = ∅ := by
      unfold Y
      rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
      intro t ht
      simp only [Finset.mem_filter] at ht
      exact absurd (Finset.mem_image.2 ⟨t, ht.1, ht.2⟩) hp
    have := card_badSet_le qs p n
    rw [hY, Finset.card_empty, Nat.le_zero, Finset.card_eq_zero] at this
    rw [this]
    exact Finset.notMem_empty _


/-! ### The diagonalization -/

namespace Diag

open BGS (enum enum_surjective exists_len)

/-- A stage of the construction: the algebraic oracle built so far and a length bound. -/
structure Stage where
  alg : AlgOracle
  bound : ℕ

/-- The input length used at a stage, for machine `pk`. -/
noncomputable def len (s : Stage) (pk : Prog × ℕ) : ℕ :=
  Classical.choose (exists_len s.bound pk.2)

theorem bound_le_len (s : Stage) (pk : Prog × ℕ) : s.bound ≤ len s pk :=
  (Classical.choose_spec (exists_len s.bound pk.2)).1

theorem tb_len_lt (s : Stage) (pk : Prog × ℕ) : tb pk.2 (len s pk) < 2 ^ len s pk :=
  (Classical.choose_spec (exists_len s.bound pk.2)).2

/-- The diagonal input. -/
noncomputable def inp (s : Stage) (pk : Prog × ℕ) : Str := List.replicate (len s pk) false

/-- The initial state the stage's machine is started in. -/
noncomputable def start (s : Stage) (pk : Prog × ℕ) : State := .run (init [inp s pk])

/-- The queries of the stage's machine on the diagonal input, with the current oracle. -/
noncomputable def qs (s : Stage) (pk : Prog × ℕ) : List Str :=
  queries (toOracle s.alg) pk.1 (tb pk.2 (len s pk)) (start s pk)

/-- The result of the stage's machine on the diagonal input, with the current oracle. -/
noncomputable def res (s : Stage) (pk : Prog × ℕ) : State :=
  runFor (toOracle s.alg) pk.1 (tb pk.2 (len s pk)) (start s pk)

theorem exists_good_stage (s : Stage) (pk : Prog × ℕ) :
    ∃ w : Str, w.length = len s pk ∧ ∀ p, zf w (len s pk) ∉ badSet (qs s pk) p (len s pk) :=
  exists_good _ _ (lt_of_le_of_lt (queries_length_le _ _ _ _) (tb_len_lt s pk))

/-- A string of the stage's length avoiding every exceptional set. -/
noncomputable def good (s : Stage) (pk : Prog × ℕ) : Str :=
  Classical.choose (exists_good_stage s pk)

theorem length_good (s : Stage) (pk : Prog × ℕ) : (good s pk).length = len s pk :=
  (Classical.choose_spec (exists_good_stage s pk)).1

theorem good_not_bad (s : Stage) (pk : Prog × ℕ) (p : ℕ) :
    zf (good s pk) (len s pk) ∉ badSet (qs s pk) p (len s pk) :=
  (Classical.choose_spec (exists_good_stage s pk)).2 p

open Classical in
/-- The polynomials installed at the stage's arity: `0` if the machine accepts, else the
vanishing indicator of `good s pk`. -/
noncomputable def newPoly (s : Stage) (pk : Prog × ℕ) (p m : ℕ) :
    MvPolynomial (Fin m) (ZMod p) :=
  if res s pk = .done true then 0 else poly (qs s pk) p m (zf (good s pk) m)

open Classical in
/-- The strings added at this stage: nothing if the machine accepts, else `good s pk`. -/
noncomputable def add (s : Stage) (pk : Prog × ℕ) : Set Str :=
  if res s pk = .done true then ∅ else {good s pk}

/-- The next stage. -/
noncomputable def Stage.next (s : Stage) (pk : Prog × ℕ) : Stage :=
  ⟨fun p m => if m = len s pk then newPoly s pk p m else s.alg p m,
    len s pk + 1 + ((qs s pk).map List.length).sum⟩

/-- The stages of the construction. -/
noncomputable def stage : ℕ → Stage
  | 0 => ⟨fun _ _ => 0, 0⟩
  | i + 1 => (stage i).next (enum i)

/-- Abbreviations for stage `i`. -/
noncomputable def A (i : ℕ) : Set Str := add (stage i) (enum i)
noncomputable def n (i : ℕ) : ℕ := len (stage i) (enum i)
noncomputable def G (i p : ℕ) : MvPolynomial (Fin (n i)) (ZMod p) :=
  newPoly (stage i) (enum i) p (n i)

/-- The final Boolean oracle. -/
def oracle : Oracle := {y | ∃ i, y ∈ A i}

/-- The final algebraic oracle: arity `m` is settled by stage `m + 1`. -/
noncomputable def algOracle : AlgOracle := fun p m => (stage (m + 1)).alg p m

theorem mem_A {i : ℕ} {y : Str} (h : y ∈ A i) :
    y = good (stage i) (enum i) ∧ res (stage i) (enum i) ≠ .done true := by
  unfold A add at h
  split_ifs at h with hr
  · exact h.elim
  · exact ⟨h, hr⟩

theorem length_of_mem_A {i : ℕ} {y : Str} (h : y ∈ A i) : y.length = n i := by
  rw [(mem_A h).1]
  exact length_good _ _

theorem bound_succ (i : ℕ) :
    (stage (i + 1)).bound = n i + 1 + ((qs (stage i) (enum i)).map List.length).sum := rfl

theorem bound_le_n (i : ℕ) : (stage i).bound ≤ n i := bound_le_len _ _

theorem bound_mono {i j : ℕ} (h : i ≤ j) : (stage i).bound ≤ (stage j).bound := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    have := bound_le_n j
    rw [bound_succ]
    omega

theorem n_lt_bound_succ (i : ℕ) : n i < (stage (i + 1)).bound := by
  rw [bound_succ]; omega

theorem qs_length_lt (i : ℕ) {q : Str} (hq : q ∈ qs (stage i) (enum i)) :
    q.length < (stage (i + 1)).bound := by
  rw [bound_succ]
  have : q.length ≤ ((qs (stage i) (enum i)).map List.length).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hq)
  omega

theorem n_strictMono : StrictMono n := by
  intro i j hij
  have h1 := n_lt_bound_succ i
  have h2 := bound_mono (show i + 1 ≤ j by omega)
  have h3 := bound_le_n j
  omega

theorem stage_alg_succ (i p m : ℕ) :
    (stage (i + 1)).alg p m =
      if m = n i then newPoly (stage i) (enum i) p m else (stage i).alg p m := rfl

/-- Stage `i` carries stage `j`'s polynomials at arity `n j`, for `j < i`. -/
theorem stage_alg_n {i j : ℕ} (h : j < i) (p : ℕ) : (stage i).alg p (n j) = G j p := by
  induction i with
  | zero => omega
  | succ i ih =>
    rw [stage_alg_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [if_neg (n_strictMono.injective.ne (by omega)), ih h]
    · rw [if_pos rfl]; rfl

/-- At arities that are not earlier stage lengths, stage `i` carries `0`. -/
theorem stage_alg_zero {i m : ℕ} (h : ∀ j < i, n j ≠ m) (p : ℕ) : (stage i).alg p m = 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [stage_alg_succ, if_neg (h i (by omega)).symm]
    exact ih fun j hj => h j (by omega)

/-- The final oracle at a stage length is that stage's polynomial. -/
theorem algOracle_n (j p : ℕ) : algOracle p (n j) = G j p :=
  stage_alg_n (Nat.lt_succ_of_le (n_strictMono.id_le j)) p

/-- The final oracle vanishes at arities that are no stage length. -/
theorem algOracle_zero {m : ℕ} (h : ∀ j, n j ≠ m) (p : ℕ) : algOracle p m = 0 :=
  stage_alg_zero (fun j _ => h j) p

/-- At every point queried at stage `i`, the stage's polynomial and the final one agree. -/
theorem agree_eval (i : ℕ) {p j : ℕ} {xs : List ℕ} (hp : p.Prime)
    (hq : encQ p j xs ∈ qs (stage i) (enum i)) :
    eval (ptm p xs.length xs) ((stage i).alg p xs.length) =
      eval (ptm p xs.length xs) (algOracle p xs.length) := by
  have hlen : xs.length < (stage (i + 1)).bound :=
    (length_lt_length_encQ p j xs).trans (qs_length_lt i hq)
  have hY := ptm_mem_Y hq
  generalize xs.length = m at hlen hY ⊢
  by_cases hex : ∃ j', n j' = m
  · obtain ⟨j', rfl⟩ := hex
    rcases lt_trichotomy j' i with h | rfl | h
    · rw [stage_alg_n h, algOracle_n]
    · rw [stage_alg_zero (fun j hj => (n_strictMono hj).ne) p, algOracle_n, map_zero]
      unfold G newPoly
      split_ifs
      · rw [map_zero]
      · exact ((poly_spec hp (good_not_bad _ _ p)).1 _ hY).symm
    · exfalso
      have h2 := bound_mono (show i + 1 ≤ j' by omega)
      have h3 := bound_le_n j'
      omega
  · push Not at hex
    rw [stage_alg_zero (fun j _ => hex j), algOracle_zero hex]

/-- The final algebraic oracle answers every query of stage `i` as stage `i` did. -/
theorem agree (i : ℕ) (q : Str) (hq : q ∈ qs (stage i) (enum i)) :
    q ∈ toOracle (stage i).alg ↔ q ∈ toOracle algOracle := by
  unfold toOracle answer
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, j, xs, hp, hxs, rfl, ha⟩
    refine ⟨p, j, xs, hp, hxs, rfl, ?_⟩
    rw [pt_eq_ptm] at ha ⊢
    rwa [← agree_eval i hp hq]
  · rintro ⟨p, j, xs, hp, hxs, rfl, ha⟩
    refine ⟨p, j, xs, hp, hxs, rfl, ?_⟩
    rw [pt_eq_ptm] at ha ⊢
    rwa [agree_eval i hp hq]

theorem run_oracle (i : ℕ) :
    runFor (toOracle algOracle) (enum i).1 (tb (enum i).2 (n i)) (start (stage i) (enum i)) =
      res (stage i) (enum i) :=
  (runFor_eq_of_agree _ _ _ (agree i)).symm

theorem mem_LB_iff (i : ℕ) : inp (stage i) (enum i) ∈ LB oracle ↔ ∃ y, y ∈ A i := by
  simp only [LB, inp, List.length_replicate, Set.mem_setOf_eq, oracle]
  constructor
  · rintro ⟨w, ⟨j, hj⟩, hl⟩
    have : j = i := n_strictMono.injective ((length_of_mem_A hj).symm.trans hl)
    subst this
    exact ⟨w, hj⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, ⟨i, hy⟩, length_of_mem_A hy⟩

theorem LB_oracle_not_mem_PA : LB oracle ∉ PA algOracle := by
  rintro ⟨p, k, hp⟩
  obtain ⟨i, hi⟩ := enum_surjective (p, k)
  obtain ⟨b, hrun, hb⟩ := hp (inp (stage i) (enum i))
  have hlen : (inp (stage i) (enum i)).length = n i := List.length_replicate
  rw [hlen, show p = (enum i).1 by rw [hi], show k = (enum i).2 by rw [hi]] at hrun
  have hres : res (stage i) (enum i) = .done b := by rw [← run_oracle]; exact hrun
  rw [mem_LB_iff] at hb
  by_cases hacc : res (stage i) (enum i) = .done true
  · have hA : A i = ∅ := by unfold A add; rw [if_pos hacc]
    have hbt : b = true := State.done.inj (hres.symm.trans hacc)
    obtain ⟨y, hy⟩ := hb.1 hbt
    rw [hA] at hy
    exact hy
  · have hy : good (stage i) (enum i) ∈ A i := by
      unfold A add; rw [if_neg hacc]; rfl
    exact hacc (hres.trans (by rw [hb.2 ⟨_, hy⟩]))

/-- The final algebraic oracle is a multiquadratic extension of the final oracle. -/
theorem isExtension : IsExtension oracle algOracle := by
  intro p hp m
  by_cases hex : ∃ j, n j = m
  · obtain ⟨j, rfl⟩ := hex
    rw [algOracle_n]
    refine ⟨fun k => ?_, fun z => ?_⟩
    · unfold G newPoly
      split_ifs
      · rw [degreeOf_zero]; omega
      · exact poly_degreeOf _ _ _ _ k
    · have hmem : List.ofFn z ∈ oracle ↔ (res (stage j) (enum j) ≠ .done true ∧
          z = zf (good (stage j) (enum j)) (n j)) := by
        constructor
        · rintro ⟨i, hi⟩
          have hij : i = j :=
            n_strictMono.injective (by rw [← length_of_mem_A hi, List.length_ofFn])
          subst hij
          obtain ⟨h1, h2⟩ := mem_A hi
          exact ⟨h2, (ofFn_eq_iff (length_good _ _) z).1 h1⟩
        · rintro ⟨h1, h2⟩
          refine ⟨j, ?_⟩
          unfold A add
          rw [if_neg h1]
          exact (ofFn_eq_iff (length_good _ _) z).2 h2
      unfold G newPoly
      by_cases hr : res (stage j) (enum j) = .done true
      · rw [if_pos hr, map_zero, if_neg]
        rw [hmem]
        exact fun h => h.1 hr
      · rw [if_neg hr]
        refine ((poly_spec hp (good_not_bad _ _ p)).2 z).trans ?_
        simp only [hmem, ne_eq, hr, not_false_eq_true, true_and]
        rfl
  · push Not at hex
    rw [algOracle_zero hex]
    refine ⟨fun k => by rw [degreeOf_zero]; omega, fun z => ?_⟩
    rw [map_zero, if_neg]
    rintro ⟨i, hi⟩
    exact hex i (by rw [← length_of_mem_A hi, List.length_ofFn])

end Diag

/-- **Aaronson–Wigderson** (one half of Thm 5.3): there is an oracle `A` with a
multiquadratic extension `Ã` such that `LB A ∉ P^Ã`. -/
theorem exists_ext_LB_not_mem_PA :
    ∃ (A : Oracle) (Ã : AlgOracle), IsExtension A Ã ∧ LB A ∉ PA Ã :=
  ⟨Diag.oracle, Diag.algOracle, Diag.isExtension, Diag.LB_oracle_not_mem_PA⟩

/-- `P = NP` does not algebrize: some `A, Ã` (with `Ã` extending `A`) have
`NP^A ⊄ P^Ã`. -/
theorem exists_ext_NP_not_subset_PA :
    ∃ (A : Oracle) (Ã : AlgOracle), IsExtension A Ã ∧ ¬ NP A ⊆ PA Ã := by
  obtain ⟨A, Ã, hext, hLB⟩ := exists_ext_LB_not_mem_PA
  exact ⟨A, Ã, hext, fun h => hLB (h (LB_mem_NP A))⟩

end Pnp.Algebrize
