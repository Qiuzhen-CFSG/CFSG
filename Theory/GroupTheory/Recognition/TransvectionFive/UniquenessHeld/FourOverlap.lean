module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessHeld.RectangleOverlap
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalIsomorphisms

/-! The same whole rectangle map preserves every intrinsic noncentral four
and its whole normalizer intersection. Thus the prescribed rectangle map
simultaneously retains the overlaps with the second rectangle and all six
possible noncentral-four locals; equality of the local maps remains separate. -/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld
open UniquenessLinear UniquenessMathieu.SourceNormalizer
open UniquenessLinear.PlaneTensor
open UniquenessLinear.PlaneCensus (Code)
variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
  {z : G} {z' : G'} (F : MarkedCentralizer z) (F' : MarkedCentralizer z')

omit [Finite G] in
private theorem mem_four_element (i : Fin 6) (x : Code) :
    element F x∈planeFour F i ↔ x∈Sextet.line i := by
  rw [mem_planeFour]
  constructor
  · rintro ⟨y,hy,he⟩
    exact element_injective F he ▸ hy
  · exact fun hx => ⟨x,hx,rfl⟩

omit [Finite G] [Finite G'] in
private theorem plane_marking_four (i : Fin 6) (a : F.plane) :
    (planeMarkingEquiv F F' a:G')∈planeFour F' i ↔ (a:G)∈planeFour F i := by
  obtain ⟨x,rfl⟩ := (sourceEquiv F).surjective a
  rw [planeMarkingEquiv_element]
  exact (mem_four_element F' i x).trans (mem_four_element F i x).symm

omit [Finite G] [Finite G'] in
/-- The actual marked rectangle map preserves the literal intersection with
the full ambient normalizer of each intrinsic four-group. -/
theorem plane_normalizer_equiv_four_intersection
    (e : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F')
    (he : ∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
      inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) (i : Fin 6) :
    ((normalizer (planeFour F i : Set G)).subgroupOf (sourcePlaneNormalizer F)).map e.toMonoidHom =
      (normalizer (planeFour F' i : Set G')).subgroupOf (sourcePlaneNormalizer F') := by
  let D := (planeFour F i).subgroupOf (sourcePlaneNormalizer F)
  let D' := (planeFour F' i).subgroupOf (sourcePlaneNormalizer F')
  have hD : D.map e.toMonoidHom=D' := by
    apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      have hx' : (x:G)∈planeFour F i := hx
      have hh := he ⟨x,planeFour_le F i hx'⟩
      change e x=_ at hh
      change e x∈D'
      rw [hh]
      exact (plane_marking_four F F' i _).mpr hx'
    · intro y hy
      have hy' : (y:G')∈planeFour F' i := hy
      let a := (planeMarkingEquiv F F').symm ⟨y,planeFour_le F' i hy'⟩
      have ha : (a:G)∈planeFour F i := (plane_marking_four F F' i a).mp
        (by rw [(planeMarkingEquiv F F').apply_symm_apply]; exact hy')
      refine ⟨inclusion F.plane.le_normalizer a,ha,?_⟩
      change e (inclusion F.plane.le_normalizer a)=y
      rw [he]
      exact congrArg (inclusion F'.plane.le_normalizer)
        ((planeMarkingEquiv F F').apply_symm_apply ⟨y,planeFour_le F' i hy'⟩)
  rw [subgroupOf_normalizer_eq ((planeFour_le F i).trans F.plane.le_normalizer),
    map_equiv_normalizer_eq,hD,
    ← subgroupOf_normalizer_eq ((planeFour_le F' i).trans F'.plane.le_normalizer)]

/-- One whole normalizer equivalence preserves the rectangle overlap and
all six four-normalizer overlaps with the prescribed original markings. -/
theorem exists_plane_normalizer_all_overlaps_equiv
    (h : (F.fusion F.plane).ncard=45) (h' : (F'.fusion F'.plane).ncard=45) :
    ∃ e : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F',
      (∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
        inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) ∧
      ((sourceThreeSpaceNormalizer F).subgroupOf (sourcePlaneNormalizer F)).map e.toMonoidHom =
        (sourceThreeSpaceNormalizer F').subgroupOf (sourcePlaneNormalizer F') ∧
      ∀ i : Fin 6,
        ((normalizer (planeFour F i : Set G)).subgroupOf (sourcePlaneNormalizer F)).map e.toMonoidHom =
          (normalizer (planeFour F' i : Set G')).subgroupOf (sourcePlaneNormalizer F') := by
  obtain ⟨e,he,hI⟩ := exists_plane_normalizer_overlap_equiv F F' h h'
  exact ⟨e,he,hI,plane_normalizer_equiv_four_intersection F F' e he⟩

end Theory.GroupTheory.TransvectionFive.UniquenessHeld
