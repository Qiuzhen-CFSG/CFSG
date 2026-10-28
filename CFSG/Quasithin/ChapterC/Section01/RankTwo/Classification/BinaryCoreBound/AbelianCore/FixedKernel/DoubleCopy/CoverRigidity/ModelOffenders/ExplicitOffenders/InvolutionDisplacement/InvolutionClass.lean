module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.ExplicitOffenders.ActorProducts

/-!
# The binary three-dimensional involution class

Every nonidentity involution of the actual SL₃(2) matrix group is conjugate
to the elementary transvection with off-diagonal entry (0,1). The kernel
checks the finite matrix calculation. The intertwining equation avoids
computing matrix inverses in the certificate.

This supplies conjugacy for the independent cover-displacement argument
supporting Aschbacher–Smith C.1.34(2),(5), printed pp.136–137, and the
universal covering in I.1.5–6, printed p.408.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders.InvolutionDisplacement

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The unique nonidentity involution class of the literal binary matrix group. -/
theorem involution_conjugate_transvection : ∀ g : MatrixGroup, g ^ 2 = 1 → g ≠ 1 →
    ∃ c : MatrixGroup, g * c = c *
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) := by
  decide +kernel

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders.InvolutionDisplacement
