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
theorem image_inverse_0 :
    word packedImage (inverseIndex 0).1 * rep packedImage (inverseIndex 0).2 =
      packedGen 0 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_inverse_1 :
    word packedImage (inverseIndex 1).1 * rep packedImage (inverseIndex 1).2 =
      packedGen 1 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_inverse_2 :
    word packedImage (inverseIndex 2).1 * rep packedImage (inverseIndex 2).2 =
      packedGen 2 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_inverse_3 :
    word packedImage (inverseIndex 3).1 * rep packedImage (inverseIndex 3).2 =
      packedGen 3 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_inverse_4 :
    word packedImage (inverseIndex 4).1 * rep packedImage (inverseIndex 4).2 =
      packedGen 4 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_inverse_5 :
    word packedImage (inverseIndex 5).1 * rep packedImage (inverseIndex 5).2 =
      packedGen 5 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_inverse_6 :
    word packedImage (inverseIndex 6).1 * rep packedImage (inverseIndex 6).2 =
      packedGen 6 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_inverse_7 :
    word packedImage (inverseIndex 7).1 * rep packedImage (inverseIndex 7).2 =
      packedGen 7 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_inverse_8 :
    word packedImage (inverseIndex 8).1 * rep packedImage (inverseIndex 8).2 =
      packedGen 8 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

end Tits.AmalgamRigidity.SecondExtension
