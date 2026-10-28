module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.LowerBounds

/-!
# Alternating and odd-characteristic values in E.1.14

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, E.1.14(3), (6), (7), printed p.214.
The standing setup is finite SQTK `G`, simple `L = F*(G)`, `T ∈ Syl₂(G)`,
and `G = LT`. The three cases are `L ≃ A₇`, `L ≃ PSL₂(q)` for odd `q > 5`,
and `L ≃ PSL₃(p)` or `PSU₃(p)` for an odd prime `p`.

The primality of the last parameter comes from the cited Theorem C,
A.2.3(2), printed p.33. In the unitary case `p` is the fixed-field order,
not the order `p²` of the matrix field. The source cites Aschbacher,
*GF(2)-representations of finite groups*, Lemmas 4.8, 4.10, and 4.11 for
the upper generation results. Any use of those proofs must retain the corrected
local tau convention in E.1.2(E2), explained on printed p.209.

At present this module exports the concrete even-order witnesses and the
minimum argument. The rank-one E-generation proofs for the full almost-simple
extensions remain to be supplied; no source-numbered value theorem is claimed
by the conditional minimum argument.
-/
