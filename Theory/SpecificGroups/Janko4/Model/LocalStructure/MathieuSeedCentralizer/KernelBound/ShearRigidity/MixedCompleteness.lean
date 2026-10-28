module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.Definitions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Calibration
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.CheckedMixed
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.MixedCompleteness.Recovery

/-!
# Assembly of the complete seed mixed-kernel upper bound

Every coefficient vector with zero upper-block restriction is reconstructed
from the 626 displayed coefficient-kernel vectors. Their certified mixed
images lie in the literal 616-generator span. Calibration of all 1221 original
exterior generators identifies these numerical maps with the actual transported
forms, so the reconstruction covers the entire mixed-kernel space. All finite
premises are discharged by kernel-checked identities.

Source: `MixedCompleteness/source/README.md` and `ShearRigidity/source/README.md`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity

/-- The checked mixed images reduce full containment to calibration and recovery. -/
theorem mixedKernelSpace_le_mixedSpan_of_calibration_and_recovery
    (hc : ∀ i, MixedCompleteness.Calibration i)
    (hr : ∀ i, MixedCompleteness.RecoveryCheck i) :
    Coordinates.mixedKernelSpace ≤ mixedSpan :=
  MixedCompleteness.mixedKernelSpace_le_of_checks hc hr MixedCompleteness.allMixedChecks

/-- The mixed image of every transported exterior form with zero upper block
lies in the span of the 616 published mixed matrices. -/
theorem mixedKernelSpace_le_mixedSpan : Coordinates.mixedKernelSpace ≤ mixedSpan :=
  mixedKernelSpace_le_mixedSpan_of_calibration_and_recovery
    MixedCompleteness.allCalibrations MixedCompleteness.allRecoveryChecks

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity
