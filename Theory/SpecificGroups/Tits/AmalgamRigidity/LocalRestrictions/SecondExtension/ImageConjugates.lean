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
theorem image_conjugate_2_1 : packedImage 2 * packedImage 1 * (packedImage 2)⁻¹ =
      packedImage 1 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_3_1 : packedImage 3 * packedImage 1 * (packedImage 3)⁻¹ =
      packedImage 1 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_3_2 : packedImage 3 * packedImage 2 * (packedImage 3)⁻¹ =
      packedImage 2 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_4_1 : packedImage 4 * packedImage 1 * (packedImage 4)⁻¹ =
      packedImage 1 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_4_2 : packedImage 4 * packedImage 2 * (packedImage 4)⁻¹ =
      packedImage 2 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_4_3 : packedImage 4 * packedImage 3 * (packedImage 4)⁻¹ =
      packedImage 1 * packedImage 2 * packedImage 3 ^ 3 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_5_1 : packedImage 5 * packedImage 1 * (packedImage 5)⁻¹ =
      packedImage 1 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_5_2 : packedImage 5 * packedImage 2 * (packedImage 5)⁻¹ =
      packedImage 1 * packedImage 3 ^ 2 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_5_3 : packedImage 5 * packedImage 3 * (packedImage 5)⁻¹ =
      packedImage 1 * packedImage 3 ^ 3 * packedImage 4 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_5_4 : packedImage 5 * packedImage 4 * (packedImage 5)⁻¹ =
      packedImage 1 * packedImage 2 * packedImage 3 ^ 2 * packedImage 4 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_6_1 : packedImage 6 * packedImage 1 * (packedImage 6)⁻¹ =
      packedImage 2 * packedImage 3 ^ 2 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_6_2 : packedImage 6 * packedImage 2 * (packedImage 6)⁻¹ =
      packedImage 2 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_6_3 : packedImage 6 * packedImage 3 * (packedImage 6)⁻¹ =
      packedImage 1 * packedImage 2 * packedImage 3 ^ 3 * packedImage 4 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_6_4 : packedImage 6 * packedImage 4 * (packedImage 6)⁻¹ =
      packedImage 4 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_6_5 : packedImage 6 * packedImage 5 * (packedImage 6)⁻¹ =
      packedImage 1 * packedImage 4 * packedImage 5 ^ 3 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_7_1 : packedImage 7 * packedImage 1 * (packedImage 7)⁻¹ =
      packedImage 2 * packedImage 4 * packedImage 5 ^ 2 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_7_2 : packedImage 7 * packedImage 2 * (packedImage 7)⁻¹ =
      packedImage 1 * packedImage 3 ^ 2 * packedImage 4 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_7_3 : packedImage 7 * packedImage 3 * (packedImage 7)⁻¹ =
      packedImage 5 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_7_4 : packedImage 7 * packedImage 4 * (packedImage 7)⁻¹ =
      packedImage 2 * packedImage 3 ^ 2 * packedImage 4 * packedImage 5 ^ 2 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_7_5 : packedImage 7 * packedImage 5 * (packedImage 7)⁻¹ =
      packedImage 3 ^ 3 * packedImage 5 ^ 2 * packedImage 6 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_7_6 : packedImage 7 * packedImage 6 * (packedImage 7)⁻¹ =
      packedImage 1 * packedImage 2 * packedImage 3 ^ 2 * packedImage 4 * packedImage 6 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_8_1 : packedImage 8 * packedImage 1 * (packedImage 8)⁻¹ =
      packedImage 2 * packedImage 3 ^ 2 * packedImage 4 * packedImage 5 ^ 2 * packedImage 7 ^ 2 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_8_2 : packedImage 8 * packedImage 2 * (packedImage 8)⁻¹ =
      packedImage 2 * packedImage 4 * packedImage 6 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_8_3 : packedImage 8 * packedImage 3 * (packedImage 8)⁻¹ =
      packedImage 1 * packedImage 3 ^ 3 * packedImage 5 ^ 3 * packedImage 7 ^ 3 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_8_4 : packedImage 8 * packedImage 4 * (packedImage 8)⁻¹ =
      packedImage 4 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_8_5 : packedImage 8 * packedImage 5 * (packedImage 8)⁻¹ =
      packedImage 2 * packedImage 4 * packedImage 7 ^ 3 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_8_6 : packedImage 8 * packedImage 6 * (packedImage 8)⁻¹ =
      packedImage 6 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
theorem image_conjugate_8_7 : packedImage 8 * packedImage 7 * (packedImage 8)⁻¹ =
      packedImage 1 * packedImage 3 ^ 2 * packedImage 5 ^ 3 * packedImage 6 := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Equiv.ext
  apply allFin
  decide +kernel

end Tits.AmalgamRigidity.SecondExtension
