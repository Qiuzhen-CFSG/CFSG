module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.FinalProducts.HaBlocks
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.FinalProducts.RightBlocks

/-!
# The final two products in the degree-1792 right expression

This module exports the unconditional checks `RightCertificate.ha_checked`
and `RightCertificate.right_checked` for all 1792 rows of HA = H*A and R = HA*B.
The imported certificates check every scalar sum and digit parity in the kernel
and compose bounded row intervals. They use the unchanged packed XOR definition
of H, the fixed HA rows and the original right-row array.

The matrices A and B follow the original, untransposed ATLAS convention, with
column j at bit j. See `source/README.md` for the exact factorization and source
attribution, and the two block directories for reproduction and measurements.
`FinalProducts.Consumer` applies both checks to the exact right-expression
assembly, with the two expansion checks and three earlier products explicit.
-/
