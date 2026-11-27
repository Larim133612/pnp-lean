import Pnp.Karp.BinPacking
import Pnp.Karp.ThreeDM

/-!
# 3-PARTITION: the language and the reduction instance

## The language (numbers in binary, as for SUBSET SUM / PARTITION / BIN PACKING)

An instance is a word `w` over `SatSym`, read as its rows `clauses w = items ++ [Bv]`: the
items (sizes `bv r` in binary, least significant bit first) and the bound `B = bv Bv`.
`TPLang w` holds iff the number of items is `3 m`, every size `a` satisfies `B/4 < a < B/2`,
and the items can be split into `m` groups (`f i < m` is the group of item `i`) each of total
size exactly `B` (Garey–Johnson's 3-PARTITION; the size condition forces every group to have
exactly three items).

## The reduction (from 3-DIMENSIONAL MATCHING, our own digit construction)

Fix `q` (the size of each of `X, Y, Z`) and a list `ts` of `K` triples.  Every item is a
number in base `4` whose digits are `0` or `1`, plus a leading digit `1`; the bound `B` has all
digits `1` and the leading digit `3`.  Three items sum to `B` iff their digit supports partition
the positions (no carries, since three digits sum to at most `3`).  The positions (`digs`):
three index blocks `I_c` of length `q`, three tag blocks `L_c` of length `M = K + 3 q`, two state
positions `s₁, s₂`, and the leading position.

The items (`El`):
* `cp c e s`: a copy of element `e` of coordinate `c` (`c = 0, 1, 2` for `X, Y, Z`), actual
  (`s = true`) or dummy;
* `al c t s`: the "linking" item of coordinate `c` with tag `t` and state `s`;
* `be c t e`: the "complement" item of coordinate `c`, tag `t` and element `e`.

The only triples of items whose supports partition the positions (`q ≥ 2`) are
`{cp c e s, al c t s, be c t e}` and `{al 0 t s, al 1 t s, al 2 t s}`.

For the triple number `l` of `ts` with coordinates `(a, b, c)` (tag `l`), the instance has the
dummy copies `cp 0 a false, cp 1 b false, cp 2 c false`, the six items `al c' l s` and the three
items `be 0 l a, be 1 l b, be 2 l c` (`triBlk`).  For every element `e < q` of coordinate `c`
(tag `K + c q + e`) it has the actual copy `cp c e true`, `al c (K + c q + e) false` and
`be c (K + c q + e) e` (`gadBlk`).  A matched triple takes the actual copies with the `true`
linking items and puts its three `false` linking items together; an unmatched triple takes its
own dummy copies; the dummy copies of the matched triples go to the gadget groups.
-/

namespace Pnp.Karp.ThreePart

open Pnp.CookLevin SatSym Pnp.Karp.Clique Pnp.Karp.SubsetSum Pnp.Karp.BinPacking
  Pnp.Karp.ThreeDM

/-! ## The language -/

/-- **3-PARTITION** over `SatSym` (see the module docstring for the encoding). -/
def TPLang : Millennium.Language (List SatSym) := fun w =>
  ∃ items Bv, clauses w = items ++ [Bv] ∧ items.length % 3 = 0 ∧
    (∀ r ∈ items, bv Bv < 4 * bv r ∧ 2 * bv r < bv Bv) ∧
    ∃ f : ℕ → ℕ, (∀ i < items.length, f i < items.length / 3) ∧
      ∀ g < items.length / 3, binSum items f g = bv Bv

/-! ## The items of the reduction -/

/-- The items: copies, linking items and complement items. -/
inductive El
  | cp (c e : ℕ) (s : Bool)
  | al (c t : ℕ) (s : Bool)
  | be (c t e : ℕ)
  deriving DecidableEq

/-- The one-hot block of length `n` with `true` at `e`. -/
def ohB (n e : ℕ) : List Bool := (List.range n).map fun i => decide (i = e)

/-- The complement of the one-hot block. -/
def coB (n e : ℕ) : List Bool := (List.range n).map fun i => decide (i ≠ e)

/-- The index block `I_{c'}` of an item. -/
def blkI (q : ℕ) : El → ℕ → List Bool
  | .cp c e _, c' => if c' = c then ohB q e else List.replicate q false
  | .al c _ _, c' => if c' = (c + 2) % 3 then List.replicate q true else List.replicate q false
  | .be c _ e, c' =>
      if c' = c then coB q e
      else if c' = (c + 1) % 3 then List.replicate q true else List.replicate q false

/-- The tag block `L_{c'}` of an item. -/
def blkL (M : ℕ) : El → ℕ → List Bool
  | .cp _ _ _, _ => List.replicate M false
  | .al c t _, c' =>
      if c' = c then ohB M t
      else if c' = (c + 1) % 3 then coB M t else List.replicate M false
  | .be c t _, c' =>
      if c' = c then coB M t
      else if c' = (c + 1) % 3 then ohB M t else List.replicate M true

/-- The state position `s₁`. -/
def st1 : El → Bool
  | .cp c _ s => (c = 0 && s) || (c = 1 && !s)
  | .al c _ s => (c = 0 && !s) || (c = 1 && s)
  | .be c _ _ => c = 2

/-- The state position `s₂`. -/
def st2 : El → Bool
  | .cp c _ s => (c = 1 && s) || (c = 2 && !s)
  | .al c _ s => (c = 1 && !s) || (c = 2 && s)
  | .be c _ _ => c = 0

/-- The base-`4` digits of an item, least significant first (the last one is the leading
digit `1`); there are `3 q + 3 M + 3` of them. -/
def digs (q M : ℕ) (x : El) : List Bool :=
  blkI q x 0 ++ blkI q x 1 ++ blkI q x 2 ++ blkL M x 0 ++ blkL M x 1 ++ blkL M x 2 ++
    [st1 x, st2 x, true]

/-- The binary row of an item (a base-`4` digit `b` is printed as the bits `b, 0`). -/
def elRow (q M : ℕ) (x : El) : List SatSym :=
  (digs q M x).flatMap fun b => [if b then pos else zero, zero]

/-- The row of the bound: all base-`4` digits `1`, the leading digit `3`. -/
def bRow (q M : ℕ) : List SatSym :=
  (List.replicate (3 * q + 3 * M + 2) [pos, zero]).flatten ++ [pos, pos]

/-- The coordinate `c` of a triple. -/
def crd (t : ℕ × ℕ × ℕ) : ℕ → ℕ
  | 0 => t.1
  | 1 => t.2.1
  | _ => t.2.2

/-- The twelve items of the triple number `l`. -/
def triBlk (l : ℕ) (t : ℕ × ℕ × ℕ) : List El :=
  [.cp 0 t.1 false, .cp 1 t.2.1 false, .cp 2 t.2.2 false,
    .al 0 l true, .al 0 l false, .al 1 l true, .al 1 l false, .al 2 l true, .al 2 l false,
    .be 0 l t.1, .be 1 l t.2.1, .be 2 l t.2.2]

/-- The three items of element `e` of coordinate `c` (tag `K + c q + e`). -/
def gadBlk (q K c e : ℕ) : List El :=
  [.cp c e true, .al c (K + c * q + e) false, .be c (K + c * q + e) e]

/-- All items of the instance: the triple blocks, then the gadget blocks
(`u = c q + e` for `u < 3 q`). -/
def els (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) : List El :=
  (List.range ts.length).flatMap (fun l => triBlk l (ts.getD l (0, 0, 0))) ++
    (List.range (3 * q)).flatMap fun u => gadBlk q ts.length (u / q) (u % q)

/-- The tag-block length `M = K + 3 q`. -/
def mT (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) : ℕ := ts.length + 3 * q

/-- The **3-PARTITION** instance of the triples `ts` over `[0, q)`. -/
def TPW (q : ℕ) (ts : List (ℕ × ℕ × ℕ)) : List SatSym :=
  ((els q ts).map (elRow q (mT q ts)) ++ [bRow q (mT q ts)]).flatMap (· ++ [sep])

/-- The **3-PARTITION** instance of the formula `w`, via its 3DM triples (M46). -/
def TPI (w : List SatSym) : List SatSym := TPW (qB w) (tris w)

end Pnp.Karp.ThreePart
