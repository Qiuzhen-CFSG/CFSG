module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerRigidity.TwistedCertificate

/-!
# Unsquared normalizer rigidity at the first J₄ involution

An ambient matrix normalizing the literal J₄ group and commuting with its
first involution normalizes that involution's centralizer C. Self-normalization
of the action on Q = O₂(C) supplies a conjugator in C. After correcting by it,
the displacement is a central character of the actual quotient C/Q. The seed
relation fixes the certified generator Y and leaves only X ↦ aX as a possible
nontrivial action. A checked polynomial identity in the actual binary matrices
excludes that twist. The remaining matrix centralizes C, so the proved local
commutant puts it, and hence the original matrix, in the literal matrix group.

No power of the original matrix is substituted. The result is an intrinsic
input toward Aschbacher–Smith, `refs/quasithin.pdf`, printed pp.1172–1173,
16.1.5(9) and 16.1.6. The ATLAS matrix provenance is in `Janko4/Model/Data.lean`;
GLS3 Table 5.3i is motivation, not a proof hypothesis.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator

/-- Every ambient normalizer commuting with the first involution belongs to
the actual J₄ matrix group, without squaring or taking any further power. -/
theorem centralizingNormalizer_mem (u : BinaryMatrixˣ)
    (hun : u ∈ Subgroup.normalizer (matrixGroup : Set BinaryMatrixˣ))
    (hua : u * matrixUnitA = matrixUnitA * u) : u ∈ matrixGroup :=
  NormalizerRigidity.mem_of_noTwistedUnit
    NormalizerRigidity.TwistedCertificate.no_twisted_unit u hun hua

end Janko4.OuterReduction.FixedGenerator
