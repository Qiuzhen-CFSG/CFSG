module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalReduction

/-!
# Square membership for the centralizing J₄ matrix normalizer

The exact local reduction uses the actual centralizer of `matrixUnitA`
inside `matrixGroup`. Its two independent inputs are a calculation of the
local normalizer's action and a binary matrix commutant calculation.
Together they supply membership of `u²` in the literal generated subgroup.

Both inputs remain hypotheses here; the unconditional theorem
`centralizingNormalizerSquares` is not yet established. This is independent
of the ambient implementation of automorphisms in `FixedGenerator.Reduction`.
Source motivation: GLS3, Table 5.3i; Aschbacher–Smith, printed pp.33 and 510.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator

/-- Local action and ambient centralizer control suffice for square membership. -/
theorem centralizingNormalizerSquares_of_local
    (hact : NormalizerSquares.LocalNormalizerActionSquares)
    (hcent : NormalizerSquares.LocalMatrixCentralizer) :
    CentralizingNormalizerSquares := by
  intro u hun hua
  exact NormalizerSquares.square_mem_of_local hact hcent u
    (NormalizerSquares.normalizes_involutionCentralizer u hun hua) hua

/-- The independent local group and linear algebra calculations imply the
requested matrix-normalizer statement. Neither input is asserted here. -/
theorem centralizingNormalizerSquares_of_local_commutant
    (hact : NormalizerSquares.LocalNormalizerActionSquares)
    (hcomm : NormalizerSquares.LocalMatrixCommutant) :
    CentralizingNormalizerSquares :=
  centralizingNormalizerSquares_of_local hact
    (NormalizerSquares.localMatrixCentralizer_of_commutant hcomm)

end Janko4.OuterReduction.FixedGenerator
