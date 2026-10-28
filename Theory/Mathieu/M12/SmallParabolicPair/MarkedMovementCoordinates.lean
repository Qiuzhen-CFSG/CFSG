module
public import Theory.GroupTheory.QuaternionSwapModel.MarkedCubic
public import Theory.Mathieu.M12.SmallParabolicPair.SwapCoreCoordinates

/-!
# The marked plane in the concrete M₁₂ quaternion core

The coordinate plane used by the diagonal-cubic movement calculation maps
to the existing natural four under the comparison preserving both quaternion
embeddings. Its second generator maps to `z * v`, so the generated subgroup
is exactly the original `<z,v>`. This identifies the mark only; it does not
identify either outer parabolic or the whole-overlap Thompson subgroup.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

namespace Sporadic.Mathieu.M12SmallPair.MarkedMovementCoordinates
open Subgroup QuaternionSwapModel.MarkedCubic

private noncomputable def coreMap : QuaternionSwapModel.QK →* M12 :=
  core.subtype.comp SwapCoreCoordinates.coreEquiv.toMonoidHom

private def central : QuaternionSwapModel.QK :=
  ⟨QuaternionSwapModel.z, QuaternionSwapModel.Z_le_QK
    ((QuaternionSwapModel.mem_Z _).mpr (Or.inr rfl))⟩

private def diagonal : QuaternionSwapModel.QK :=
  ⟨QuaternionSwapModel.projection (QuaternionSwapModel.diagonalRaw (QuaternionGroup.xa 0)),
    markedPlane_le_QK (by
      rw [markedPlane_eq_closure]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩

private theorem coreMap_central : coreMap central = z :=
  SwapCoreCoordinates.coreEquiv_marked

private theorem coreMap_diagonal : coreMap diagonal = z * v := by
  have hdiag : diagonal =
      (⟨QuaternionSwapModel.leftEmbedding (QuaternionGroup.xa 0),
        (show QuaternionSwapModel.leftFactor ≤ QuaternionSwapModel.QK from le_sup_left)
          ⟨_, rfl⟩⟩ : QuaternionSwapModel.QK) *
      ⟨QuaternionSwapModel.rightEmbedding (QuaternionGroup.xa 0),
        (show QuaternionSwapModel.rightFactor ≤ QuaternionSwapModel.QK from le_sup_right)
          ⟨_, rfl⟩⟩ := by
    apply Subtype.ext
    exact diagonal_eq_product _
  rw [hdiag, map_mul]
  change (SwapCoreCoordinates.coreEquiv _ : M12) * (SwapCoreCoordinates.coreEquiv _ : M12) = _
  rw [SwapCoreCoordinates.coreEquiv_left, SwapCoreCoordinates.coreEquiv_right]
  decide +kernel

private theorem restricted_plane : markedPlane.subgroupOf QuaternionSwapModel.QK =
    Subgroup.closure ({central, diagonal} : Set QuaternionSwapModel.QK) := by
  apply (map_injective (f := QuaternionSwapModel.QK.subtype)
    QuaternionSwapModel.QK.subtype_injective)
  rw [map_subgroupOf_eq_of_le markedPlane_le_QK, MonoidHom.map_closure]
  simpa only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype,
    central, diagonal] using markedPlane_eq_closure

/-- The movement calculation uses the original natural four under the
comparison that fixes the two specified quaternion-factor embeddings. -/
public theorem markedPlane_image :
    (markedPlane.subgroupOf QuaternionSwapModel.QK).map
      (core.subtype.comp SwapCoreCoordinates.coreEquiv.toMonoidHom) = natural := by
  change (markedPlane.subgroupOf QuaternionSwapModel.QK).map coreMap = natural
  rw [restricted_plane, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, coreMap_central, coreMap_diagonal]
  change Subgroup.closure ({z, z * v} : Set M12) = Subgroup.closure ({z, v} : Set M12)
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact (Subgroup.mul_mem_cancel_left
        (Subgroup.closure ({z, z * v} : Set M12))
        (Subgroup.subset_closure (Set.mem_insert _ _))).mp
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

end Sporadic.Mathieu.M12SmallPair.MarkedMovementCoordinates
