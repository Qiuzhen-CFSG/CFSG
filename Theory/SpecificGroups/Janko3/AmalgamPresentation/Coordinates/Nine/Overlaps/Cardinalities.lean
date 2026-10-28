module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.ProjectiveIntersection
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.Kernel

/-! Full raw overlaps are the complete projective preimages, retaining the cubic kernel. -/
public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup OverlapTables SourceRecognition.CubicNormalizerModel

private theorem projection_overlap (i : Fin 4) :
    projection (overlapElement i) = Matrix.ProjGenLinGroup.mk (overlapMatrix i) := by
  rw [overlapElement_coordinates]
  rfl

/-- The first raw overlap has exactly the computed projective image. -/
theorem rawPair_map_projection : rawPair.map projection = Pair.subgroup := by
  rw [rawPair,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
    projection_overlap,projection_overlap]
  unfold Pair.subgroup
  congr 1
  ext x
  simp [Pair.generator]

/-- The second raw overlap has exactly the computed projective image. -/
theorem rawThird_map_projection : rawThird.map projection = Third.subgroup := by
  rw [rawThird,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
    projection_overlap,projection_overlap]
  unfold Third.subgroup
  congr 1
  ext x
  simp [Third.generator]

theorem rawPair_eq_comap : rawPair = Pair.subgroup.comap projection := by
  rw [←rawPair_map_projection]
  exact (comap_map_eq_self kernel_le_rawPair).symm

theorem rawThird_eq_comap : rawThird = Third.subgroup.comap projection := by
  rw [←rawThird_map_projection]
  exact (comap_map_eq_self kernel_le_rawThird).symm

private def preimageCoordinates (H : Subgroup P) : H.comap projection ≃ Z × H where
  toFun x := (x.val.left,⟨x.val.right,x.property⟩)
  invFun x := ⟨⟨x.1,x.2⟩,x.2.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

private theorem preimage_card (H : Subgroup P) : Nat.card (H.comap projection) = 3 * Nat.card H := by
  rw [Nat.card_congr (preimageCoordinates H),Nat.card_prod]
  congr 1
  simp [Z,Nat.card_eq_fintype_card,Fintype.card_multiplicative]

/-- The literal original order-sixty overlap. -/
theorem rawPair_card : Nat.card rawPair = 60 := by
  rw [rawPair_eq_comap,preimage_card,Pair.subgroup_card]

/-- The literal original order-180 overlap. -/
theorem rawThird_card : Nat.card rawThird = 180 := by
  rw [rawThird_eq_comap,preimage_card,Third.subgroup_card]

/-- The two literal full overlaps meet in exactly thirty elements. -/
theorem rawPair_inf_rawThird_card : Nat.card (rawPair ⊓ rawThird : Subgroup Canonical) = 30 := by
  rw [rawPair_eq_comap,rawThird_eq_comap,←comap_inf,preimage_card,intersection_card]

/-- Restriction to the actual projective complement gives the original projective image. -/
def rawThirdComplementEquiv :
    (rawThird ⊓ (SemidirectProduct.inr : P →* Canonical).range : Subgroup Canonical) ≃* Third.subgroup where
  toFun x := ⟨x.val.right,by
    exact rawThird_eq_comap.le x.property.1⟩
  invFun x := ⟨SemidirectProduct.inr x.val,by
    constructor
    · rw [rawThird_eq_comap]
      exact x.property
    · exact ⟨x.val,rfl⟩⟩
  left_inv x := by
    obtain ⟨p,hp⟩ := x.property.2
    apply Subtype.ext
    change SemidirectProduct.inr x.val.right = x.val
    rw [←hp]
    rfl
  right_inv x := rfl
  map_mul' x y := rfl

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
