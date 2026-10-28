module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.DesignFlag.Coordinates

/-!
# Equality of the native design and module stabilizers

The fifteen pair-points of the marked hexad span the native six-space, and
their endpoints recover the hexad. The already proved endpoint compatibility
therefore identifies their literal stabilizers in the original matrix group.
This discharges the native design/module comparison needed in 14.4.12.
-/

@[expose] public section
noncomputable section
open Matrix Subgroup Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open CoreProjectiveAction Representation.BinaryOffender
open scoped Matrix Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.DesignFlag
open OrbitCertificates ActorCatalogue.Native ActorCatalogue.NativeParabolics

theorem column_mem_iff (v : BinarySpace) :
    referenceColumnToRow v ∈ rowSpace ↔ v ∈ parabolicSpace := by
  rw [rowSpace_eq_map]
  constructor
  · rintro ⟨w, hw, he⟩
    exact referenceColumnToRow_injective he ▸ hw
  · exact fun hv => Submodule.mem_map_of_mem hv

theorem action_scalarLine (g : Group) (i : Fin 231) {w : BinarySpace}
    (hw : w ∈ scalarLine (projectiveVector i)) :
    Matrix.vecMul w ((g.val⁻¹ : Matrix12ˣ) : Matrix12) ∈
      scalarLine (projectiveVector (pairAction (designProjection g).val i)) := by
  have h := referenceProjection_compatible g⁻¹ i
  have hp : ((referenceProjection g⁻¹ : m22DesignAut) : Equiv.Perm (Fin 22)) =
      (referenceProjection g).val⁻¹ := congrArg Subtype.val (map_inv referenceProjection g)
  rw [hp, inv_inv, referenceProjection_eq_designProjection] at h
  rw [← h]
  exact Set.mem_image_of_mem (rightRow g.val⁻¹) hw

private theorem stable_of_hexad (g : Group) (hg : g ∈ hexadPreimage markedHexad)
    (v : BinarySpace) (hv : v ∈ parabolicSpace) : representation g v ∈ parabolicSpace := by
  have hhex : markedHexad.image (designProjection g).val = markedHexad := hg
  have hb (j : Fin 6) : representation g (orbitColumns j) ∈ parabolicSpace := by
    apply (column_mem_iff _).mp
    change referenceColumnToRow (action g (orbitColumns j)) ∈ rowSpace
    rw [referenceColumnToRow_action]
    apply (scalarLine_mem_iff _ (action_scalarLine g (columnPair j)
      (orbitColumns_scalarLine j))).mpr
    rw [pairAction_spec]
    calc
      (endpointPair (columnPair j)).image (designProjection g).val ⊆
          markedHexad.image (designProjection g).val := Finset.image_mono _ (columnPair_subset j)
      _ = markedHexad := hhex
  rw [← orbit_range_eq] at hv
  obtain ⟨u, rfl⟩ := hv
  have he : orbitEmbedding u = ∑ j, u j • orbitColumns j := by
    ext i
    simp [orbitEmbedding, Matrix.mulVec, dotProduct, orbitMatrix, mul_comm]
  rw [he, map_sum]
  exact Submodule.sum_mem _ fun j _ => by rw [map_smul]; exact parabolicSpace.smul_mem _ (hb j)

theorem hexadPreimage_le_parabolic : hexadPreimage markedHexad ≤ parabolic := by
  intro g hg v
  constructor
  · intro hv
    have h := stable_of_hexad g⁻¹ ((hexadPreimage markedHexad).inv_mem hg)
      (representation g v) hv
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using h
  · exact stable_of_hexad g hg v

private theorem hexad_covered : ∀ a ∈ markedHexad, ∃ i : Fin 231,
    a ∈ endpointPair i ∧ endpointPair i ⊆ markedHexad := by decide +kernel

theorem parabolic_le_hexadPreimage : parabolic ≤ hexadPreimage markedHexad := by
  intro g hg
  have hinc (i : Fin 231) (hi : endpointPair i ⊆ markedHexad) :
      endpointPair (pairAction (designProjection g).val i) ⊆ markedHexad := by
    have hw : projectiveVector i ∈ rowSpace :=
      (scalarLine_mem_iff i (Or.inl rfl)).mpr hi
    rw [rowSpace_eq_map] at hw
    obtain ⟨v, hv, he⟩ := hw
    have hm : referenceColumnToRow (representation g v) ∈ rowSpace :=
      (column_mem_iff _).mpr ((hg v).mpr hv)
    change referenceColumnToRow (action g v) ∈ rowSpace at hm
    rw [referenceColumnToRow_action, he] at hm
    exact (scalarLine_mem_iff _ (action_scalarLine g i (Or.inl rfl))).mp hm
  change markedHexad.image (designProjection g).val = markedHexad
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨i, hai, hi⟩ := hexad_covered a ha
    apply hinc i hi
    rw [pairAction_spec]
    exact Finset.mem_image.mpr ⟨a, hai, rfl⟩
  · rw [Finset.card_image_of_injective _ (designProjection g).val.injective]

theorem parabolic_eq_hexadPreimage : parabolic = hexadPreimage markedHexad :=
  le_antisymm parabolic_le_hexadPreimage hexadPreimage_le_parabolic

theorem markedHexad_mem : markedHexad ∈ m22Blocks := by decide +kernel

/-- The actual design parabolic has the already computed six-dimensional orbit. -/
theorem markedHexad_orbitSpan :
    Homogeneous.orbitSpan representation (hexadPreimage markedHexad)
      (binaryLine markedVector) = parabolicSpace := by
  rw [← parabolic_eq_hexadPreimage, ← parabolicSpace_eq_orbitSpan]

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.DesignFlag
