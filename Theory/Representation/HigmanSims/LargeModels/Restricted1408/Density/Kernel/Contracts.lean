module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Bridge
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.NormalForm

/-!
# Independent numerical certificates for the exact right kernel

The first certificate identifies the proposed packed table with the literal
matrix. The second identifies its homogeneous solutions with those of the
explicit codimension-one normal form. They are independent: elimination can
work on the proposed table while its two matrix products are checked.
Neither certificate is asserted by these definitions. `Kernel.lean` retains
assembly, and must discharge both before exporting `kernelCertificate`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData
open Thompson.InvolutionCentralizer.AlternatingQuotient.MatrixCertificates

/-- Every proposed row is the row of the literal `1 + B + A*B + B*A`. -/
def RowTableCertificate : Prop := checkRange rowCheck 0 1408 = true

/-- The explicit row form determined by the unchanged published seed. -/
def kernelNormalForm : PackedBinaryRows.State :=
  PackedBinaryRows.normalState 1407 3037566777681267535834465479477380210446177044093850219542017719937461953016038750181753272333662566324377528990954025738249985938610247160176175638580520348176498059831193934536735574962891405363127719209003405508515098615267758094552103906262663260137666912768254730890609589573719963388200362861770965963113113402544595261017349602099599066548935105647282472801271845992658676808526609012602330107685271989261917926201689

/-- The proposed packed table and explicit normal form have the same solutions. -/
def ReductionCertificate : Prop :=
  ∀ w : Vector, PackedBinaryRows.stateSolutions 1408 kernelNormalForm w ↔
    PackedBinaryRows.stateSolutions 1408 state0000 w

/-- Interpretation of the normal form in the actual published coordinates. -/
theorem kernelNormalForm_solutions (w : Vector) :
    PackedBinaryRows.stateSolutions 1408 kernelNormalForm w ↔ w = w 0 • kernelVector := by
  apply PackedBinaryRows.normalState_solutions 1407 3037566777681267535834465479477380210446177044093850219542017719937461953016038750181753272333662566324377528990954025738249985938610247160176175638580520348176498059831193934536735574962891405363127719209003405508515098615267758094552103906262663260137666912768254730890609589573719963388200362861770965963113113402544595261017349602099599066548935105647282472801271845992658676808526609012602330107685271989261917926201689
  decide +kernel

end Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData
