module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.AlternatingFixedSpace.FourDimensional
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.AlternatingFixedSpace.FourDimensionalSummands
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.AlternatingFixedSpace.Permutation
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.AlternatingFixedSpace.Symplectic

/-!
# Small alternating-module fixed-space witnesses

The descendants construct elements outside every Sylow two-subgroup fixing
its entire fixed space, for all four binary permutation sections in degrees
six and seven, for the concrete natural Sp₄(2) and Sp₄(2)' actions, and
for every faithful four-dimensional A₇ action.
The central-section theorems also cover the genuine A₆/S₆ extensions and
trivial summands allowed by B.5.1. Their inputs are actual equivariant maps,
central kernels and trivial quotients; no splitting or fixed-space
conclusion is included among those structural hypotheses.

The four-dimensional A₇ calculation uses faithfulness and stabilizer
counting, without identifying inequivalent actions by dimension.
`FourDimensionalSummands` lifts it through central kernels and trivial
supplements, covering the allowed trivial summands for this alternative.
These results do not assert that the supplied models exhaust B.5.6 or the
groups in F.6.18. The classification comparison and mixed-branch assembly belong to
`Recognition`. Its `SeedCriterion` transports each constructed witness
through a group equivalence and an intertwining linear equivalence.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.3.3, B.4.2, B.5.1 and Lemma 15.4.18, printed
pp.84,86,99,1163.
-/
