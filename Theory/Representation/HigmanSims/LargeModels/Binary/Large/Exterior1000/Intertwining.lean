module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.Bridge
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.Rows840
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.AChecks
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000.Intertwining.BChecks

/-!
# The exterior-square(56) invariant-row identities

Both ambient packed matrices are proved equal to the actual exterior-minor
matrices, in the literal source coordinates. The lift tree is exactly U.
`AChecks.products` and `BChecks.products` certify all 1000 rows for each
generator; the matrix bridges assemble these into the two unconditional
identities below. The target matrices are the literal published generators,
as `targetA_eq` and `targetB_eq` state.

This module has no dependency on the top-level Exterior1000 consumer, so the
parent can import the unconditional intertwining identities. The
separate `Intertwining.Consumer` module checks the actual descent application.

Source: R. A. Wilson et al., ATLAS HSG1-f2r56B0/HSG1-f2r1000B0 and the fixed
section1000 candidate; see `Intertwining/source/README.md` for the proof
boundaries, source attribution, generation, and successful measurements.
-/

public section

namespace Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000

/-- The literal lift matrix intertwines the first exterior and target generators. -/
theorem u_mul_ambientA : U * ambientA = targetA * U :=
  Intertwining.matrixA_of_products Intertwining.AChecks.products

/-- The literal lift matrix intertwines the second exterior and target generators. -/
theorem u_mul_ambientB : U * ambientB = targetB * U :=
  Intertwining.matrixB_of_products Intertwining.BChecks.products

end Representation.HigmanSims.LargeModels.Binary.Large.Exterior1000
