module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.PlaneSplitting
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalIsomorphisms
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalIsomorphisms

/-! The actual forty-five-point normalizers are determined by their marked
rectangle actions. The quotient comparison is the faithful six-bit action,
and the splitting is the normalizer of the actual cubic lift. This supplies
the first two local comparisons in source 44.2; compatibility with the other
Held locals and ambient uniqueness remain further mathematical obligations. -/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld
open UniquenessLinear UniquenessMathieu.SourceNormalizer
open UniquenessLinear.PlaneTensor
variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
  {z : G} {z' : G'} (F : MarkedCentralizer z) (F' : MarkedCentralizer z')

private def quotientEquiv (h : (F.fusion F.plane).ncard = 45)
    (h' : (F'.fusion F'.plane).ncard = 45) : planeQuotient F ≃* planeQuotient F' :=
  (MulEquiv.ofBijective (planeSextetRepresentation F h)
    ⟨planeSextetRepresentation_injective F h, planeSextetRepresentation_surjective F h⟩).trans
    (MulEquiv.ofBijective (planeSextetRepresentation F' h')
      ⟨planeSextetRepresentation_injective F' h', planeSextetRepresentation_surjective F' h'⟩).symm

private theorem quotientEquiv_mark (h : (F.fusion F.plane).ncard = 45)
    (h' : (F'.fusion F'.plane).ncard = 45) (q : planeQuotient F) :
    planeSextetRepresentation F' h' (quotientEquiv F F' h h' q) =
      planeSextetRepresentation F h q :=
  (MulEquiv.ofBijective (planeSextetRepresentation F' h')
    ⟨planeSextetRepresentation_injective F' h', planeSextetRepresentation_surjective F' h'⟩).apply_symm_apply _

/-- The whole normalizer comparison extends the literal rectangle marking
and intertwines the actual quotient actions on all six-bit vectors. -/
theorem exists_plane_normalizer_equiv (h : (F.fusion F.plane).ncard = 45)
    (h' : (F'.fusion F'.plane).ncard = 45) :
    ∃ e : planeNormalizer F ≃* planeNormalizer F',
      (∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
        inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) ∧
      ∀ n, planeSextetRepresentation F' h' (QuotientGroup.mk (e n)) =
        planeSextetRepresentation F h (QuotientGroup.mk n) := by
  let q := quotientEquiv F F' h h'
  have ha : ∀ (n : planeNormalizer F) (a : F.plane),
      planeMarkingEquiv F F' (F.plane.normalizerMonoidHom n a) =
        planeQuotientAction F' (q (QuotientGroup.mk n)) (planeMarkingEquiv F F' a) := by
    intro n a
    obtain ⟨x,rfl⟩ := (sourceEquiv F).surjective a
    have he : F.plane.normalizerMonoidHom n (sourceEquiv F x) =
        sourceEquiv F (quotientCodeAction F (QuotientGroup.mk n) x) := by
      apply Subtype.ext
      change (n : G) * element F x * (n : G)⁻¹ =
        element F (quotientCodeAction F (QuotientGroup.mk n) x)
      rw [quotientCodeAction_mk, normalizerAction_element]
    rw [he, planeMarkingEquiv_element, planeMarkingEquiv_element]
    obtain ⟨n',hn'⟩ := QuotientGroup.mk'_surjective
      (F'.plane.subgroupOf (planeNormalizer F')) (q (QuotientGroup.mk n))
    have hm : planeSextetRepresentation F' h' (QuotientGroup.mk n') =
        planeSextetRepresentation F h (QuotientGroup.mk n) := by
      change planeSextetRepresentation F' h' ((QuotientGroup.mk' _) n') = _
      rw [hn']
      exact quotientEquiv_mark F F' h h' _
    have hv := congrArg (fun r : Sextet.symmetryGroup => r.val x) hm
    rw [planeSextetRepresentation_val, planeSextetRepresentation_val] at hv
    rw [← hn']
    apply Subtype.ext
    change element F' (quotientCodeAction F (QuotientGroup.mk n) x) =
      (planeQuotientAction F' (QuotientGroup.mk n') (sourceEquiv F' x) : G')
    rw [← hv, planeQuotientAction_mk_apply, quotientCodeAction_mk,
      normalizerAction_element]
    rfl
  obtain ⟨X,_,hX⟩ := UniquenessMathieu.OctadSource.plane_splits_of_forty_five F h
  obtain ⟨X',_,hX'⟩ := UniquenessMathieu.OctadSource.plane_splits_of_forty_five F' h'
  obtain ⟨e,he,hq⟩ := split_normalizer_equiv F.plane F'.plane
    (planeMarkingEquiv F F') q (planeQuotientAction F')
    (fun n b => by apply Subtype.ext; exact planeQuotientAction_mk_apply F' n b)
    ha (planeQuotientAction_injective F') ⟨_,hX⟩ ⟨_,hX'⟩
  exact ⟨e,he,fun n => by rw [hq]; exact quotientEquiv_mark F F' h h' _⟩

/-- Applying the same action comparison to the opposite markings gives the
second whole normalizer, with its prescribed original rectangle restriction. -/
theorem exists_threeSpace_normalizer_equiv
    (h : (F.fusion F.threeSpace).ncard = 45)
    (h' : (F'.fusion F'.threeSpace).ncard = 45) :
    ∃ e : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F',
      ∀ a : F.threeSpace, e (inclusion F.threeSpace.le_normalizer a) =
        inclusion F'.threeSpace.le_normalizer (threeSpaceMarkingEquiv F F' a) := by
  obtain ⟨e,he,_⟩ := exists_plane_normalizer_equiv (oppositeMarking F) (oppositeMarking F')
    (by simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using h)
    (by simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using h')
  let c := MulEquiv.subgroupCongr
    (congrArg (fun P : Subgroup G => normalizer (P : Set G)) (oppositeMarking_plane F).symm)
  let c' := MulEquiv.subgroupCongr
    (congrArg (fun P : Subgroup G' => normalizer (P : Set G')) (oppositeMarking_plane F'))
  refine ⟨c.trans (e.trans c'), fun a => ?_⟩
  change c' (e (c (inclusion F.threeSpace.le_normalizer a))) = _
  rw [show c (inclusion F.threeSpace.le_normalizer a) =
    inclusion (oppositeMarking F).plane.le_normalizer
      (MulEquiv.subgroupCongr (oppositeMarking_plane F).symm a) from
        normalizerCongr_inclusion _ _ _ a, he]
  exact normalizerCongr_inclusion _ _ (oppositeMarking_plane F') _

end Theory.GroupTheory.TransvectionFive.UniquenessHeld
