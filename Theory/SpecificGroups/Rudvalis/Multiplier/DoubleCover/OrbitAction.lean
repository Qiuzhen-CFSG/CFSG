module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.OrbitAction.Certificates
public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover.Geometry

/-!
# Equivariance of the marked Rudvalis projective orbit

Both original ATLAS covering matrices send every published labelled vector to
an invertible scalar multiple of the vector at its original permutation image.
The two generator equations are checked on all 4060 labels by finite arithmetic.
No transpose, inverse matrix, relabelling, or recognition premise is used.

This supplies the orbit certificate in `scalarKernel_of_geometry`; only the
independent concrete frame-rigidity certificate remains in that application.
The covering construction contributes to Aschbacher–Smith I.1.3(1), printed
p.407 of `refs/quasithin.pdf`. See `OrbitAction/source/README.md` for provenance.
-/

namespace Rudvalis.Multiplier.DoubleCover

/-- The published matrices act on all 4060 lines by the published permutations. -/
public theorem orbitEquivariance : OrbitEquivariance := by
  constructor
  · intro i
    exact OrbitAction.actionA i.val i.isLt
  · intro i
    exact OrbitAction.actionB i.val i.isLt

/-- Discharge the literal orbit premise of the paired-group kernel calculation. -/
public theorem scalarKernel_of_frameRigidity (hframe : FrameRigidity) : ScalarKernel :=
  scalarKernel_of_geometry orbitEquivariance hframe

end Rudvalis.Multiplier.DoubleCover
