module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.PackedImages

/-!
# Relation certificates for the candidate images

The finite point checks below are kernel reductions on certified packed maps.
They establish the actual group equations needed by cyclic and coset collection.
Source and witness conventions: `Images`, Parrott (1972), §5, p.683.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.SecondExtension
open RelativeSecondBlockLayers Atlas1600OrderCertificate

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_power_1 : packedImage 1 ^ 2 = 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_power_2 : packedImage 2 ^ 2 = 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_power_3 : packedImage 3 ^ 4 = 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_power_4 : packedImage 4 ^ 2 = 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_power_5 : packedImage 5 ^ 4 = 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_power_6 : packedImage 6 ^ 2 = 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_power_7 : packedImage 7 ^ 4 = 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_power_8 : packedImage 8 ^ 2 = 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

end Tits.AmalgamRigidity.SecondExtension
