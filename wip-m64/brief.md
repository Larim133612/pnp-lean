# M64 brief: unary 3-PARTITION (strong NP-completeness) in pnp-lean

Repo: Lean 4.31 + Mathlib, project Pnp. Toolchain on PATH via `export PATH=$HOME/.elan/bin:$PATH`.
Your working copy is given in your task (a copy of the repo with `.lake` shared/copied; build files
with `lake env lean Pnp/Karp/<File>.lean` or `lake build Pnp.Karp.<File>`; NEVER run a full
`lake build` of everything unless needed, and never `lake clean`). Do NOT git commit/push.
No `sorry`/`admit`/new axioms. Only standard axioms allowed.

## New definitions (already written, file `Pnp/Karp/ThreePartU.lean`, read it first)

`TPULang` (unary 3-PARTITION: rows `items ++ [Bv]`, value of a row = its length, `unSum`),
`TPUW q ts`, `TPUI w = TPUW (qB w) (tris w)`, item values `uval q M x = nv (uR M) (udg q M x ++ [1])`,
bound `uB M`, digits `dv`, shapes `shI`, `shL`, `uL M = 3M+1`, `uR M = 9 uL M + 1`, `uRow n = replicate n pos`.
The items `els q ts` and `El`, `st1`, `st2`, `mT` are from M63 (`Pnp/Karp/ThreePart.lean`).
Do not change `ThreePartU.lean` (other people build on it); if you really need a change, say so in
your final report instead.

## Model files from M63 (binary 3-PARTITION) to imitate

* `Pnp/Karp/ThreePartProg.lean`: reduction program `tpp_redCmd` computing `tpp_F` with
  `tpp_F (DMI w) = TPI w` (`tpp_F_DMI`), `tpp_F_computable`, and `sat_le_tp_of` composing with the
  3DM printer `DMI` (`mg_computable`, `Pnp/Karp/ThreeDMProg.lean`) via `Pnp.TM2Comp.comp`.
* `Pnp/Karp/ThreePartVer.lean` + `ThreePartNP.lean`: verifier `tpv_ver` and `tp_in_np`
  (certificate as for BIN PACKING, `Pnp/Karp/BinPackingVer.lean`).
* The `Struct` command language: `Pnp/Oracle/Struct.lean`, `StructLib.lean`; `FunBridge`.

## Targets

Agent PROG (file `Pnp/Karp/ThreePartUProg.lean`, prefix `tpup_` for all new names, namespace
`Pnp.Karp.ThreePartU`):
```
theorem tpup_F_DMI (w : List SatSym) : tpup_F (DMI w) = TPUI w
theorem tpup_F_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (Millennium.fin_encoding_string SatSym).encode (Millennium.fin_encoding_string SatSym).encode tpup_F)
theorem sat_le_tpu_of (h : ∀ w, SATLang w ↔ TPULang (TPUI w)) :
    Millennium.PolynomialTimeReducible (Millennium.fin_encoding_string SatSym)
      (Millennium.fin_encoding_string SatSym) SATLang TPULang
```
Hint: the input `DMI w` has rows `replicate q zero :: triRows w` (see `tpp_F_DMI`). The program can
precompute unary stacks `P_d = false^(R^d)`, `d ≤ 8`, and for each item print, for each digit `d`, that
many copies of `P_d` (then `P_8` for the leading 1); order of printing inside a row does not matter
since the row is `replicate (value) pos`. For the digit of a one-hot block with one-hot position `e`
(length `n`): `L + 1 + e` copies = `L+1` copies plus one per `false` before the `true`;
the complement digit `2L - n + (n-1-e)` = `2L-n` copies plus one per `false` after the `true`
(M63's program already keeps such prefix/suffix stacks `PRE`, `SUF`, `GP`, `GS`).
You may restructure freely; the time bound may be any `tb k` (`tb k n = (n+2)^k`).
Values are about `R^8` with `R = 27M+10`, `M = K + 3q` ≤ input length, so the output has length
O(n^10) and the time bound needs a correspondingly larger exponent.

Agent VER (files `Pnp/Karp/ThreePartUVer.lean`, `Pnp/Karp/ThreePartUNP.lean`, prefix `tpuv_`):
```
theorem tpu_in_np :
    Millennium.InNondeterministicPolynomialTime (Millennium.fin_encoding_string SatSym) TPULang
```
In unary, a value is a row length, so sums are lengths of concatenations and comparisons are
length comparisons (simpler than the binary adder of M63). Reuse M63 / BIN PACKING verifier
machinery where convenient.

Report at the end: the files, the main theorem names, any lemma you changed elsewhere (should be none),
time bound used, and the `#print axioms` output of your main theorem.
