module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.ActualStraightening
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RankOne.Transport

/-!
# Opposite-root straightening and transport of the truncated algebra

Both divided-power identities hold on arbitrary integral eigenvectors for the
direct diagonal `diag(z,z⁻¹)`, including zero vectors. All binomial coefficients
are formed in ℤ before casting. The actual supplied root parameters are related
to the compatible chart by explicit nonzero scalar rescalings.

Equal-index straightening and Vandermonde put the required torus binomials in
the truncated opposite-root algebra. Extracting the coefficient of a conjugated
root curve then proves transport by every point of either actual simple root.
The truncation length is arbitrary, covering `q=2^n` including `n=1`, and no
irreducibility, PBW spanning, or representation-degree bound is assumed.
The supplied SL₂ chart is the only additional geometric witness.

Sources: Steinberg, *Representations of algebraic groups* (1963), §§2–3;
GLS3 1.3.5(a), 1.12.1. The stored source coroot is the inverse of the direct
diagonal; all weights here use the direct left-action convention.
-/
