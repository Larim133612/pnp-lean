import Pnp.Karp.ThreePartUArith

/-!
# Unary 3-PARTITION: the total size of the items

`tpu_total`: the items of `TPUW q ts` (triples in range) sum to exactly `m B`, where
`m = 4 K + 3 q` is the number of groups.  Each triple block consists of four intended groups
(`tpua_patA`, `tpua_patB`); the gadget blocks of a fixed element `e` over the three coordinates
sum digit-wise to three bounds.
-/

namespace Pnp.Karp.ThreePartU

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM Pnp.Karp.ThreePart

theorem tput_nv_map3 (R : ℕ) : ∀ l : List ℕ, nv R (l.map (3 * ·)) = 3 * nv R l
  | [] => by simp [nv]
  | d :: l => by simp only [List.map_cons, nv, tput_nv_map3 R l]; ring

theorem tput_sum_flatMap {α β : Type*} (F : β → ℕ) (g : α → List β) (c : ℕ) :
    ∀ L : List α, (∀ a ∈ L, ((g a).map F).sum = c) → ((L.flatMap g).map F).sum = L.length * c
  | [], _ => by simp
  | a :: L, h => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, h a (by simp),
      tput_sum_flatMap F g c L (fun b hb => h b (by simp [hb])), List.length_cons]
    ring

theorem tput_sum_const {α : Type*} (g : α → ℕ) (c : ℕ) :
    ∀ L : List α, (∀ a ∈ L, g a = c) → (L.map g).sum = L.length * c
  | [], _ => by simp
  | a :: L, h => by
    rw [List.map_cons, List.sum_cons, h a (by simp),
      tput_sum_const g c L (fun b hb => h b (by simp [hb])), List.length_cons]
    ring

/-- The gadget digits of a fixed element over the three coordinates. -/
theorem tput_gad_low (q M : ℕ) (hqM : q ≤ M) {e t0 t1 t2 : ℕ} (he : e < q) (h0 : t0 < M)
    (h1 : t1 < M) (h2 : t2 < M) :
    (nv (uR M) (udg q M (.cp 0 e true)) + nv (uR M) (udg q M (.al 0 t0 false)) +
        nv (uR M) (udg q M (.be 0 t0 e))) +
      (nv (uR M) (udg q M (.cp 1 e true)) + nv (uR M) (udg q M (.al 1 t1 false)) +
        nv (uR M) (udg q M (.be 1 t1 e))) +
      (nv (uR M) (udg q M (.cp 2 e true)) + nv (uR M) (udg q M (.al 2 t2 false)) +
        nv (uR M) (udg q M (.be 2 t2 e))) = 3 * nv (uR M) (tpua_bd M) := by
  rw [tpua_nv_add3 (uR M) (udg q M (.cp 0 e true)) (udg q M (.al 0 t0 false))
      (udg q M (.be 0 t0 e)) rfl rfl,
    tpua_nv_add3 (uR M) (udg q M (.cp 1 e true)) (udg q M (.al 1 t1 false))
      (udg q M (.be 1 t1 e)) rfl rfl,
    tpua_nv_add3 (uR M) (udg q M (.cp 2 e true)) (udg q M (.al 2 t2 false))
      (udg q M (.be 2 t2 e)) rfl rfl,
    tpua_nv_add3 (uR M)
      (tpua_z3 (udg q M (.cp 0 e true)) (udg q M (.al 0 t0 false)) (udg q M (.be 0 t0 e)))
      (tpua_z3 (udg q M (.cp 1 e true)) (udg q M (.al 1 t1 false)) (udg q M (.be 1 t1 e)))
      (tpua_z3 (udg q M (.cp 2 e true)) (udg q M (.al 2 t2 false)) (udg q M (.be 2 t2 e)))
      rfl rfl, ← tput_nv_map3]
  congr 1
  have hL : q ≤ uL M := by unfold uL; omega
  have hL' : M ≤ uL M := by unfold uL; omega
  simp only [udg, tpua_z3, tpua_bd, shI, shL, dv, ThreePart.st1, ThreePart.st2, List.map_cons,
    List.map_nil, List.cons.injEq]
  simp
  omega

theorem tput_dm {q c e : ℕ} (he : e < q) : (c * q + e) / q = c ∧ (c * q + e) % q = e :=
  (Nat.div_mod_unique (by omega)).mpr ⟨by rw [Nat.mul_comm]; omega, he⟩

theorem tput_sum_flatMap' {α β : Type*} (F : β → ℕ) (g : α → List β) :
    ∀ L : List α, ((L.flatMap g).map F).sum = (L.map fun a => ((g a).map F).sum).sum
  | [] => by simp
  | a :: L => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, tput_sum_flatMap' F g L,
      List.map_cons, List.sum_cons]

theorem tput_range3 (h : ℕ → ℕ) (q : ℕ) :
    ((List.range (3 * q)).map h).sum =
      ((List.range q).map fun e => h e + h (q + e) + h (2 * q + e)).sum := by
  rw [show 3 * q = q + (q + q) by ring, List.range_add, List.range_add, List.map_append,
    List.sum_append, List.map_map, List.map_append, List.sum_append, List.map_map]
  simp only [List.sum_map_add, Function.comp_def, two_mul, add_assoc]

/-- **The total size**: the items of `TPUW q ts` sum to `(4 K + 3 q) B`. -/
theorem tpu_total (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) (hts : ∀ t ∈ ts, t.1 < q ∧ t.2.1 < q ∧ t.2.2 < q) :
    ((els q ts).map (uval q (mT q ts))).sum = (4 * ts.length + 3 * q) * uB (mT q ts) := by
  have hMd : mT q ts = ts.length + 3 * q := rfl
  generalize mT q ts = M at hMd ⊢
  have hqM : q ≤ M := by omega
  have hU : ∀ x, uval q M x = nv (uR M) (udg q M x) + uR M ^ 8 := tpua_uval q M
  have hB := tpua_uB M
  unfold els
  rw [List.map_append, List.sum_append,
    tput_sum_flatMap (uval q M) _ (4 * uB M) (List.range ts.length), List.length_range,
    tput_sum_flatMap', tput_range3, tput_sum_const _ (3 * uB M) (List.range q), List.length_range]
  · ring
  · intro e he
    rw [List.mem_range] at he
    have hG : ∀ c u, u = c * q + e → ((gadBlk q ts.length (u / q) (u % q)).map (uval q M)).sum =
        nv (uR M) (udg q M (.cp c e true)) +
          nv (uR M) (udg q M (.al c (ts.length + c * q + e) false)) +
          nv (uR M) (udg q M (.be c (ts.length + c * q + e) e)) + 3 * uR M ^ 8 := by
      rintro c u rfl
      rw [(tput_dm (c := c) he).1, (tput_dm (c := c) he).2]
      simp only [gadBlk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hU]
      ring
    rw [hG 0 e (by ring), hG 1 (q + e) (by ring), hG 2 (2 * q + e) rfl]
    have := tput_gad_low q M hqM he (t0 := ts.length + 0 * q + e) (t1 := ts.length + 1 * q + e)
      (t2 := ts.length + 2 * q + e) (by omega) (by omega) (by omega)
    omega
  · intro l hl
    rw [List.mem_range] at hl
    rw [List.getD_eq_getElem _ _ hl]
    have ht := hts _ (List.getElem_mem hl)
    generalize ts[l] = t at ht
    have hl' : l < M := by omega
    simp only [triBlk, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hU]
    have p0 := tpua_patA q M hqM (s := false) (c := 0) (by omega) ht.1 hl'
    have p1 := tpua_patA q M hqM (s := false) (c := 1) (by omega) ht.2.1 hl'
    have p2 := tpua_patA q M hqM (s := false) (c := 2) (by omega) ht.2.2 hl'
    have p3 := tpua_patB q M (s := true) hl'
    omega

end Pnp.Karp.ThreePartU
