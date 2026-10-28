module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Reduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Representatives
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder

/-!
# Involution coverage in the binary J₄ model

The checked reduction `involution_coverage_of_max1_fusion` transfers coverage
from the concrete ATLAS local subgroup to the model. Its remaining inputs are
the subgroup order and `Max1InvolutionFusion`, besides the model order.
Both proposed representatives have certified order two. The proposed model
order remains an explicit input, as in the other prime coverage branches.
-/

public section
namespace Janko4.Simplicity

/-- Involution coverage from the checked local order and fusion certificates.
The model order is retained as an explicit hypothesis until the independent
coset-counting certificate is assembled. -/
theorem covers_two
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hcard : Nat.card Model = 86775571046077562880) :
    CoversPrime (primeRepresentative (a hA) (b hB)) 2 :=
  involution_coverage_of_max1_fusion hA hB hcard
    (Cardinality.max1Subgroup_card hA hB) (max1InvolutionFusion hA hB)

end Janko4.Simplicity
