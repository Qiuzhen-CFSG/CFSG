module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.RepresentativeOrders.Data

/-!
# The base words for the O'Nan order certificates

Explicit products from the preserved ATLAS matrices (`refs/original/onan/`)
certify the words in `ONG1-cycW1` by kernel reduction. Repeated squaring
assembles the scalar power without evaluating a large nested matrix expression.
-/

namespace ONan.Simplicity.RepresentativeOrderData

set_option maxRecDepth 4096
set_option maxHeartbeats 0

public theorem c_eq : matrixA * matrixB = SimplicityData.ab := by
  apply Matrix.ext
  unfold SimplicityData.ab
  decide +kernel

public theorem d_eq : SimplicityData.ab * matrixB = PrimeNormalData.d := by
  apply Matrix.ext
  unfold SimplicityData.ab PrimeNormalData.d
  decide +kernel

public theorem w20_eq : SimplicityData.ab * PrimeNormalData.d = w20 := by
  apply Matrix.ext
  unfold SimplicityData.ab PrimeNormalData.d w20
  decide +kernel

end ONan.Simplicity.RepresentativeOrderData
