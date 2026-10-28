module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.BitCoordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.NativeImage

/-!
# Identifying the native rank-defect locus

Binary coordinates cover the actual elementary eight, and the concrete
isotropic subgroup has precisely the code detected by the four-dimensional
image certificate. The layer equations and generator displacement table are
retained explicitly until the checked layer assembly supplies them.
Source: KW (1988), Corollary 2.3.6.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry.Loewy
open GeneratorCertificates Subgroup
attribute [local irreducible] modelGroup matrixA matrixB

theorem maskElement_mem_isotropic_iff (m : Fin 256) :
    maskElement m ∈ isotropicSubgroup ↔ isotropicCode m := by
  rw [maskElement,coordinates_mem_isotropicSubgroup_iff]
  rfl

theorem maskElement_range : Set.range maskElement = (nativeEight 0 : Set Model) := by
  ext x
  constructor
  · rintro ⟨m,rfl⟩
    exact maskElement_mem m
  · intro hx
    obtain ⟨⟨a,b⟩,hab⟩ := eightCoordinates_surjective 0 (Additive.ofMul ⟨x,hx⟩)
    obtain ⟨m,ha,hb⟩ := exists_mask_coordinates a b
    refine ⟨m,?_⟩
    have he : maskCoordinates m = (a,b) := Prod.ext ha hb
    unfold maskElement
    rw [he,hab]
    rfl

/-- The literal defect locus is exactly the concrete isotropic sixteen once
its canonical layers and generator table have been identified. -/
theorem nativeDefectSet_eq_isotropic_of_layers
    (hthree : layer (nativeEight 0) 3 = rowSpan layer3Rows)
    (hfour : layer (nativeEight 0) 4 = rowSpan layer4Rows)
    (hzero : layer (nativeEight 0) 5 = ⊥)
    (hgen : ∀ i : Fin 32, ∀ j : Fin 8,
      displacement (nativeGenerator j) (decode (layer3Rows.get i)) =
        decode (combine layer4Rows ((thirdActions.get j).get i))) :
    nativeDefectSet = (isotropicSubgroup : Set Model) := by
  ext x
  by_cases hx : x ∈ nativeEight 0
  · change x ∈ (nativeEight 0 : Set Model) at hx
    rw [← maskElement_range] at hx
    obtain ⟨m,rfl⟩ := hx
    change (maskElement m ∈ nativeEight 0 ∧
      movedBy (nativeEight 0) 3 (maskElement m) ≠ layer (nativeEight 0) 4) ↔ _
    rw [and_iff_right (maskElement_mem m)]
    change (¬ movedBy (nativeEight 0) 3 (maskElement m) = layer (nativeEight 0) 4) ↔ _
    rw [not_congr (movedBy_maskElement_eq_layer4_iff hthree hfour hzero hgen m),
      not_not]
    exact (maskElement_mem_isotropic_iff m).symm
  · have hi : x ∉ isotropicSubgroup := fun h => hx (isotropicSubgroup_le h)
    change (x ∈ nativeEight 0 ∧ _) ↔ x ∈ isotropicSubgroup
    exact ⟨fun h => (hx h.1).elim, fun h => (hi h).elim⟩

end Janko4.LocalStructure.ElementaryEightGeometry.Loewy
