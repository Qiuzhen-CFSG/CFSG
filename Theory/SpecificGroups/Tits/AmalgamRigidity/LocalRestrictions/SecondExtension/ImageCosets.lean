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
theorem image_step_0 (i : Fin 3) :
    rep packedImage i * packedImage 0 =
      word packedImage (SecondOrder.factor 0 i) * rep packedImage (SecondOrder.dest 0 i) := by
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_step_1 (i : Fin 3) :
    rep packedImage i * packedImage 1 =
      word packedImage (SecondOrder.factor 1 i) * rep packedImage (SecondOrder.dest 1 i) := by
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_step_2 (i : Fin 3) :
    rep packedImage i * packedImage 2 =
      word packedImage (SecondOrder.factor 2 i) * rep packedImage (SecondOrder.dest 2 i) := by
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_step_3 (i : Fin 3) :
    rep packedImage i * packedImage 3 =
      word packedImage (SecondOrder.factor 3 i) * rep packedImage (SecondOrder.dest 3 i) := by
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_step_4 (i : Fin 3) :
    rep packedImage i * packedImage 4 =
      word packedImage (SecondOrder.factor 4 i) * rep packedImage (SecondOrder.dest 4 i) := by
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_step_5 (i : Fin 3) :
    rep packedImage i * packedImage 5 =
      word packedImage (SecondOrder.factor 5 i) * rep packedImage (SecondOrder.dest 5 i) := by
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_step_6 (i : Fin 3) :
    rep packedImage i * packedImage 6 =
      word packedImage (SecondOrder.factor 6 i) * rep packedImage (SecondOrder.dest 6 i) := by
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_step_7 (i : Fin 3) :
    rep packedImage i * packedImage 7 =
      word packedImage (SecondOrder.factor 7 i) * rep packedImage (SecondOrder.dest 7 i) := by
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_step_8 (i : Fin 3) :
    rep packedImage i * packedImage 8 =
      word packedImage (SecondOrder.factor 8 i) * rep packedImage (SecondOrder.dest 8 i) := by
  apply Equiv.ext
  revert i
  apply allFin₂
  decide +kernel

end Tits.AmalgamRigidity.SecondExtension
