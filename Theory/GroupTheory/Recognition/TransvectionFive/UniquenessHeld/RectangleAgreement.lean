module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessHeld.OtherRectangle
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalIsomorphisms
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceColumn
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LinePlane

/-! Both prescribed rectangle markings are restrictions of the same whole
centralizer comparison. Thus the actual two normalizer comparisons agree on
the common sixteen. Their discrepancy on the full overlap centralizes that
sixteen and consequently lies in the original marked Sylow subgroup.

This is a reduction of the agreement problem in source 44.2. It does not
assert that the discrepancy is a principal cocycle or that the maps already
agree on the whole overlap. -/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld
open UniquenessLinear
variable {G G' : Type*} [Group G] [Group G']
  {z : G} {z' : G'} (F : MarkedCentralizer z) (F' : MarkedCentralizer z')

private theorem plane_marking_model (a : F.plane) :
    F'.equiv ⟨planeMarkingEquiv F F' a, F'.pullback_le _
      (planeMarkingEquiv F F' a).property⟩ =
      F.equiv ⟨a, F.pullback_le _ a.property⟩ := by
  have h := (F'.pullbackEquiv Model.plane Model.plane_le_centralizer).apply_symm_apply
    ((F.pullbackEquiv Model.plane Model.plane_le_centralizer) a)
  exact Subtype.ext (congrArg (fun x : Model.plane => (x : SL)) h)

private theorem three_marking_model (a : F.threeSpace) :
    F'.equiv ⟨threeSpaceMarkingEquiv F F' a, F'.pullback_le _
      (threeSpaceMarkingEquiv F F' a).property⟩ =
      F.equiv ⟨a, F.pullback_le _ a.property⟩ := by
  apply dualCentralizer.injective
  exact plane_marking_model (oppositeMarking F) (oppositeMarking F')
    (MulEquiv.subgroupCongr (oppositeMarking_plane F).symm a)

/-- The two prescribed restrictions agree on every original element of the
common sixteen, including its full marking and not just its subgroup image. -/
theorem rectangle_markings_agree (a : G) (ha : a ∈ F.plane) (hb : a ∈ F.threeSpace) :
    (planeMarkingEquiv F F' ⟨a,ha⟩ : G') =
      (threeSpaceMarkingEquiv F F' ⟨a,hb⟩ : G') := by
  have h := (plane_marking_model F F' ⟨a,ha⟩).trans
    (three_marking_model F F' ⟨a,hb⟩).symm
  exact congrArg Subtype.val (F'.equiv.injective h)

private theorem three_marking_mem_pullback (A : Subgroup SL) (a : F.threeSpace) :
    (threeSpaceMarkingEquiv F F' a : G') ∈ F'.pullback A ↔
      (a : G) ∈ F.pullback A := by
  rw [F'.mem_pullback_iff A ⟨threeSpaceMarkingEquiv F F' a,
    F'.pullback_le _ (threeSpaceMarkingEquiv F F' a).property⟩,
    F.mem_pullback_iff A ⟨a,F.pullback_le _ a.property⟩,
    three_marking_model]

variable [Finite G] [Finite G']

/-- The second normalizer comparison preserves the same whole overlap. -/
theorem threeSpace_normalizer_equiv_rectangle_intersection
    (e : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F')
    (he : ∀ a : F.threeSpace, e (inclusion F.threeSpace.le_normalizer a) =
      inclusion F'.threeSpace.le_normalizer (threeSpaceMarkingEquiv F F' a)) :
    ((sourcePlaneNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)).map e.toMonoidHom =
      (sourcePlaneNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F') := by
  let D := (F.plane ⊓ F.threeSpace).subgroupOf (sourceThreeSpaceNormalizer F)
  let D' := (F'.plane ⊓ F'.threeSpace).subgroupOf (sourceThreeSpaceNormalizer F')
  have hD : D.map e.toMonoidHom = D' := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      have hx' : (x : G) ∈ F.plane ∧ (x : G) ∈ F.threeSpace := hx
      have hh := he ⟨x,hx'.2⟩
      change e x = _ at hh
      change e x ∈ D'
      rw [hh]
      exact ⟨(three_marking_mem_pullback F F' Model.plane _).mpr hx'.1,
        (threeSpaceMarkingEquiv F F' ⟨x,hx'.2⟩).property⟩
    · intro y hy
      have hy' : (y : G') ∈ F'.plane ∧ (y : G') ∈ F'.threeSpace := hy
      let a := (threeSpaceMarkingEquiv F F').symm ⟨y,hy'.2⟩
      have ha : (a : G) ∈ F.plane := (three_marking_mem_pullback F F' Model.plane a).mp
        (by rw [(threeSpaceMarkingEquiv F F').apply_symm_apply]; exact hy'.1)
      refine ⟨inclusion F.threeSpace.le_normalizer a, ⟨ha,a.property⟩, ?_⟩
      change e (inclusion F.threeSpace.le_normalizer a) = y
      rw [he]
      exact congrArg (inclusion F'.threeSpace.le_normalizer)
        ((threeSpaceMarkingEquiv F F').apply_symm_apply ⟨y,hy'.2⟩)
  have hN : normalizer (D : Set (sourceThreeSpaceNormalizer F)) =
      (sourcePlaneNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F) := by
    rw [← subgroupOf_normalizer_eq (show F.plane ⊓ F.threeSpace ≤
      sourceThreeSpaceNormalizer F from inf_le_right.trans F.threeSpace.le_normalizer),
      SourceGeometry.planes_intersection_normalizer]
    ext x
    exact and_iff_left x.property
  have hN' : normalizer (D' : Set (sourceThreeSpaceNormalizer F')) =
      (sourcePlaneNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F') := by
    rw [← subgroupOf_normalizer_eq (show F'.plane ⊓ F'.threeSpace ≤
      sourceThreeSpaceNormalizer F' from inf_le_right.trans F'.threeSpace.le_normalizer),
      SourceGeometry.planes_intersection_normalizer]
    ext x
    exact and_iff_left x.property
  rw [← hN,map_equiv_normalizer_eq,hD,hN']

omit [Finite G] [Finite G'] in
/-- Arbitrary whole local maps extending the prescribed markings agree
elementwise on the original common sixteen. -/
theorem rectangle_maps_agree_on_common_kernel
    (r : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F')
    (hr : ∀ a : F.plane, r (inclusion F.plane.le_normalizer a) =
      inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a))
    (s : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F')
    (hs : ∀ a : F.threeSpace, s (inclusion F.threeSpace.le_normalizer a) =
      inclusion F'.threeSpace.le_normalizer (threeSpaceMarkingEquiv F F' a))
    (a : G) (ha : a ∈ F.plane) (hb : a ∈ F.threeSpace) :
    (r ⟨a,F.plane.le_normalizer ha⟩ : G') =
      (s ⟨a,F.threeSpace.le_normalizer hb⟩ : G') := by
  have h₁ := congrArg Subtype.val (hr ⟨a,ha⟩)
  have h₂ := congrArg Subtype.val (hs ⟨a,hb⟩)
  exact h₁.trans ((rectangle_markings_agree F F' a ha hb).trans h₂.symm)

omit [Finite G] [Finite G'] in
/-- The discrepancy of the two whole local maps centralizes the marked
common sixteen on every element of the full normalizer overlap. -/
theorem rectangle_maps_displacement_centralizes_common_kernel
    (r : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F')
    (hr : ∀ a : F.plane, r (inclusion F.plane.le_normalizer a) =
      inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a))
    (s : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F')
    (hs : ∀ a : F.threeSpace, s (inclusion F.threeSpace.le_normalizer a) =
      inclusion F'.threeSpace.le_normalizer (threeSpaceMarkingEquiv F F' a))
    (g : G) (hgP : g ∈ sourcePlaneNormalizer F) (hgT : g ∈ sourceThreeSpaceNormalizer F) :
    (r ⟨g,hgP⟩ : G') * (s ⟨g,hgT⟩ : G')⁻¹ ∈
      centralizer ((F'.plane ⊓ F'.threeSpace : Subgroup G') : Set G') := by
  apply mem_centralizer_iff.mpr
  intro x hx
  let a := (planeMarkingEquiv F F').symm ⟨x,hx.1⟩
  have haT : (a : G) ∈ F.threeSpace := (planeMarkingEquiv_mem_pullback F F'
    Model.threeSpace a).mp (by rw [(planeMarkingEquiv F F').apply_symm_apply]; exact hx.2)
  have haP : (a : G) ∈ F.plane := a.property
  have huP : g⁻¹ * a * g ∈ F.plane := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp
      ((sourcePlaneNormalizer F).inv_mem hgP) a).mp haP
  have huT : g⁻¹ * a * g ∈ F.threeSpace := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp
      ((sourceThreeSpaceNormalizer F).inv_mem hgT) a).mp haT
  have hu := rectangle_maps_agree_on_common_kernel F F' r hr s hs
    (g⁻¹*a*g) huP huT
  have hra : (r ⟨a,F.plane.le_normalizer haP⟩ : G') = x := by
    have h := congrArg Subtype.val (hr a)
    exact h.trans (congrArg Subtype.val ((planeMarkingEquiv F F').apply_symm_apply ⟨x,hx.1⟩))
  have hsa : (s ⟨a,F.threeSpace.le_normalizer haT⟩ : G') = x :=
    (rectangle_maps_agree_on_common_kernel F F' r hr s hs a haP haT).symm.trans hra
  change (r ((⟨g,hgP⟩ : sourcePlaneNormalizer F)⁻¹ *
      ⟨a,F.plane.le_normalizer haP⟩ * ⟨g,hgP⟩) : G') =
    (s ((⟨g,hgT⟩ : sourceThreeSpaceNormalizer F)⁻¹ *
      ⟨a,F.threeSpace.le_normalizer haT⟩ * ⟨g,hgT⟩) : G') at hu
  simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,hra,hsa] at hu
  have hh := congrArg (fun y : G' => (r ⟨g,hgP⟩ : G') * y *
    (s ⟨g,hgT⟩ : G')⁻¹) hu
  group at hh
  simpa only [mul_assoc,zpow_neg_one] using hh

omit [Finite G] in
/-- The remaining discrepancy is already contained in the target's literal
marked Sylow subgroup. No correction or innerness premise is assumed. -/
theorem rectangle_maps_displacement_in_sylow
    (r : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F')
    (hr : ∀ a : F.plane, r (inclusion F.plane.le_normalizer a) =
      inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a))
    (s : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F')
    (hs : ∀ a : F.threeSpace, s (inclusion F.threeSpace.le_normalizer a) =
      inclusion F'.threeSpace.le_normalizer (threeSpaceMarkingEquiv F F' a))
    (g : G) (hgP : g ∈ sourcePlaneNormalizer F) (hgT : g ∈ sourceThreeSpaceNormalizer F) :
    (r ⟨g,hgP⟩ : G') * (s ⟨g,hgT⟩ : G')⁻¹ ∈ (sourceSylow F' : Subgroup G') :=
  UniquenessMathieu.OctadSource.planes_centralizer_le F'
    (rectangle_maps_displacement_centralizes_common_kernel F F' r hr s hs g hgP hgT)

/-- The actual forty-five fusion counts give whole local maps, with the
entire overlap preserved and its discrepancy constrained to the marked Sylow.
The first map also retains the other actual rectangle. -/
theorem exists_rectangle_maps_with_sylow_displacement
    (hP : (F.fusion F.plane).ncard = 45) (hT : (F.fusion F.threeSpace).ncard = 45)
    (hP' : (F'.fusion F'.plane).ncard = 45) (hT' : (F'.fusion F'.threeSpace).ncard = 45) :
    ∃ (r : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F')
      (s : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F'),
      (∀ a : F.plane, r (inclusion F.plane.le_normalizer a) =
        inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) ∧
      (∀ a : F.threeSpace, s (inclusion F.threeSpace.le_normalizer a) =
        inclusion F'.threeSpace.le_normalizer (threeSpaceMarkingEquiv F F' a)) ∧
      ((sourceThreeSpaceNormalizer F).subgroupOf (sourcePlaneNormalizer F)).map r.toMonoidHom =
        (sourceThreeSpaceNormalizer F').subgroupOf (sourcePlaneNormalizer F') ∧
      ((sourcePlaneNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)).map s.toMonoidHom =
        (sourcePlaneNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F') ∧
      (F.threeSpace.subgroupOf (sourcePlaneNormalizer F)).map r.toMonoidHom =
        F'.threeSpace.subgroupOf (sourcePlaneNormalizer F') ∧
      (∀ (a : G) (ha : a ∈ F.plane) (hb : a ∈ F.threeSpace),
        (r ⟨a,F.plane.le_normalizer ha⟩ : G') =
          (s ⟨a,F.threeSpace.le_normalizer hb⟩ : G')) ∧
      ∀ (g : G) (hgP : g ∈ sourcePlaneNormalizer F) (hgT : g ∈ sourceThreeSpaceNormalizer F),
        (r ⟨g,hgP⟩ : G') * (s ⟨g,hgT⟩ : G')⁻¹ ∈ (sourceSylow F' : Subgroup G') := by
  obtain ⟨r,hr,_⟩ := exists_plane_normalizer_equiv F F' hP hP'
  obtain ⟨s,hs⟩ := exists_threeSpace_normalizer_equiv F F' hT hT'
  exact ⟨r,s,hr,hs,plane_normalizer_equiv_rectangle_intersection F F' r hr,
    threeSpace_normalizer_equiv_rectangle_intersection F F' s hs,
    plane_normalizer_equiv_other_rectangle F F' r hr,
    rectangle_maps_agree_on_common_kernel F F' r hr s hs,
    rectangle_maps_displacement_in_sylow F F' r hr s hs⟩

end Theory.GroupTheory.TransvectionFive.UniquenessHeld
