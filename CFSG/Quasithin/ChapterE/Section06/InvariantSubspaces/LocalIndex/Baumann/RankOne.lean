module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.RankOne.Native

/-!
# Reductions for the natural rank-one Baumann core bound

The local hypotheses of B.6.10 are expressed inside H. Independently of
the natural-module calculation, `block_eq_thompson_commutator` proves
[L,J(R)] = L and `baumann_conjugateClosure_eq` identifies the precise
L-conjugate closure in B.6.10(2) with L·Baum(R). Its Sylow conclusion then
gives Q ≤ Baum(R) by `localCore_le_baumann_of_conjugateClosure_sylow`.

The natural-module Sylow theorem B.6.10 is still an upstream obligation.
In particular, this module does not yet establish `RankOneCoreInput` for
either the L₂(2^n) or A₃ alternatives. Final assembly remains here once
that theorem and its actual model hypotheses are available.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.6.10,
printed p.117, and C.5.3–4, printed pp.154–155.
-/
