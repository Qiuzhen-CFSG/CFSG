module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessHeld.RectangleComparison
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFlags

/-! Whole rectangle normalizer comparisons preserve their actual mutual
intersection. The marked kernel map preserves the common sixteen, whose
ambient normalizer is the intersection of the two whole normalizers. -/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld
open UniquenessLinear
variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
  {z : G} {z' : G'} (F : MarkedCentralizer z) (F' : MarkedCentralizer z')

theorem plane_normalizer_equiv_rectangle_intersection
    (e : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F')
    (he : ∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
      inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) :
    ((sourceThreeSpaceNormalizer F).subgroupOf (sourcePlaneNormalizer F)).map e.toMonoidHom =
      (sourceThreeSpaceNormalizer F').subgroupOf (sourcePlaneNormalizer F') := by
  let D := (F.threeSpace ⊓ F.plane).subgroupOf (sourcePlaneNormalizer F)
  let D' := (F'.threeSpace ⊓ F'.plane).subgroupOf (sourcePlaneNormalizer F')
  have hD : D.map e.toMonoidHom = D' := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hx' : (x : G) ∈ F.threeSpace ∧ (x : G) ∈ F.plane := hx
      have hh := he ⟨x, hx'.2⟩
      change e x = _ at hh
      change e x ∈ D'
      rw [hh]
      exact ⟨(planeMarkingEquiv_mem_pullback F F' Model.threeSpace _).mpr hx'.1,
        (planeMarkingEquiv F F' ⟨x, hx'.2⟩).property⟩
    · intro y hy
      have hy' : (y : G') ∈ F'.threeSpace ∧ (y : G') ∈ F'.plane := hy
      let a := (planeMarkingEquiv F F').symm ⟨y, hy'.2⟩
      have ha : (a : G) ∈ F.threeSpace := (planeMarkingEquiv_mem_pullback F F' Model.threeSpace a).mp
        (by rw [(planeMarkingEquiv F F').apply_symm_apply]; exact hy'.1)
      refine ⟨inclusion F.plane.le_normalizer a, ⟨ha, a.property⟩, ?_⟩
      change e (inclusion F.plane.le_normalizer a) = y
      rw [he]
      exact congrArg (inclusion F'.plane.le_normalizer)
        ((planeMarkingEquiv F F').apply_symm_apply ⟨y, hy'.2⟩)
  have hN (P : MarkedCentralizer z) :
      normalizer (((P.threeSpace ⊓ P.plane).subgroupOf (sourcePlaneNormalizer P)) :
        Set (sourcePlaneNormalizer P)) = (sourceThreeSpaceNormalizer P).subgroupOf (sourcePlaneNormalizer P) := by
    rw [← subgroupOf_normalizer_eq (show P.threeSpace ⊓ P.plane ≤ sourcePlaneNormalizer P from
      inf_le_right.trans P.plane.le_normalizer), inf_comm P.threeSpace P.plane,
      SourceGeometry.planes_intersection_normalizer]
    ext x
    exact and_iff_right x.property
  have hN' : normalizer (D' : Set (sourcePlaneNormalizer F')) =
      (sourceThreeSpaceNormalizer F').subgroupOf (sourcePlaneNormalizer F') := by
    rw [← subgroupOf_normalizer_eq (show F'.threeSpace ⊓ F'.plane ≤ sourcePlaneNormalizer F' from
      inf_le_right.trans F'.plane.le_normalizer), inf_comm F'.threeSpace F'.plane,
      SourceGeometry.planes_intersection_normalizer]
    ext x
    exact and_iff_right x.property
  rw [← hN F, map_equiv_normalizer_eq, hD, hN']

/-- The forty-five-point whole normalizer comparison retains the common
rectangle-normalizer intersection as well as the prescribed kernel marking. -/
theorem exists_plane_normalizer_overlap_equiv
    (h : (F.fusion F.plane).ncard=45) (h' : (F'.fusion F'.plane).ncard=45) :
    ∃ e : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F',
      (∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
        inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) ∧
      ((sourceThreeSpaceNormalizer F).subgroupOf (sourcePlaneNormalizer F)).map e.toMonoidHom =
        (sourceThreeSpaceNormalizer F').subgroupOf (sourcePlaneNormalizer F') := by
  obtain ⟨e,he,_⟩ := exists_plane_normalizer_equiv F F' h h'
  exact ⟨e,he,plane_normalizer_equiv_rectangle_intersection F F' e he⟩

end Theory.GroupTheory.TransvectionFive.UniquenessHeld
