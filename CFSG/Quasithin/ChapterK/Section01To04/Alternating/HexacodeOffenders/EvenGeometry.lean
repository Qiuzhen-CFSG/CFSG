module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.EvenGeometry.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.EvenGeometry.Sylow

/-!
# The even hexacode offender calculation

The concrete Sylow two-subgroup has exactly two elementary four-groups.
Their fixed spaces have binary dimensions two and four, respectively, so
their action ratios are two and one. The second fixes its F₄ plane
pointwise and acts quadratically. Rank and fixed-space bounds exclude all
other offenders in this Sylow subgroup.

The plane-kernel argument classifies every best offender in the whole
cover. Quasisimplicity and the concrete offender then give generation of
the even cover and quadratic ratio one. This proves the even model input
to `HexacodeOffenders.conclusion_of_even_and_outer`; the independent outer
exclusion is not used here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, K.1.3,
printed p.453 (PDF p.464).
-/

public section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry
open SylowModel

theorem lineGroup_rank : rank lineGroup = 2 := by
  rw [rank, SylowModel.lineGroup_card]
  decide

theorem planeGroup_rank : rank planeGroup = 2 := by
  rw [rank, SylowModel.planeGroup_card]
  decide

theorem lineGroup_fixedCodim : fixedCodim Hexacode.evenAction lineGroup = 4 := by
  have h := fixedCodim_add_finrank Hexacode.evenAction lineGroup
  rw [hexacode_finrank, lineFixed_finrank] at h
  omega

theorem planeGroup_fixedCodim : fixedCodim Hexacode.evenAction planeGroup = 2 := by
  have h := fixedCodim_add_finrank Hexacode.evenAction planeGroup
  rw [hexacode_finrank, planeFixed_finrank] at h
  omega

/-- The line-fixing four-group has source action ratio two. -/
theorem lineGroup_ratio : actionRatio Hexacode.evenAction lineGroup = 2 := by
  rw [actionRatio, lineGroup_fixedCodim, lineGroup_rank]
  symm
  apply (ENNReal.eq_div_iff (by norm_num) (by simp)).mpr
  norm_num

/-- The plane-fixing four-group has source action ratio one. -/
theorem planeGroup_ratio : actionRatio Hexacode.evenAction planeGroup = 1 := by
  rw [actionRatio, planeGroup_fixedCodim, planeGroup_rank]
  exact ENNReal.div_self (by norm_num) (by simp)

/-- The actual plane-fixing subgroup is an offender. -/
theorem planeGroup_offender : IsOffender Hexacode.evenAction planeGroup := by
  refine ⟨⟨?_, planeGroup_elementary⟩, ?_⟩
  · intro h
    have hc := SylowModel.planeGroup_card
    rw [h, card_bot] at hc
    omega
  · rw [planeGroup_fixedCodim, planeGroup_rank]

/-- Its displacements lie in its pointwise fixed plane. -/
theorem planeGroup_quadratic : IsQuadratic Hexacode.evenAction planeGroup := by
  nth_rw 1 [offender_eq_kernel planeGroup planeGroup_offender]
  exact planeKernel_quadratic _ (fixedSpace_scalar_stable planeGroup) planeFixed_finrank

theorem planeGroup_best : IsBestOffender Hexacode.evenAction planeGroup :=
  planeGroup_offender.isBest_of_not_strong Hexacode.evenAction no_strong

/-- The plane is two-dimensional over the contract's actual four-element field,
and its literal pointwise kernel is the displayed subgroup. -/
theorem planeGroup_fieldPlane :
    Module.finrank ChapterB.QuasisimpleSource.BinaryField.four.Carrier
      (fixedPlane planeGroup) = 2 ∧
    planeGroup = subspaceKernel Hexacode.evenAction
      (((fixedPlane planeGroup).restrictScalars (ZMod 2)).comap
        modelCoordinates.toLinearMap) ⊤ := by
  refine ⟨fixedPlane_finrank planeGroup planeGroup_offender, ?_⟩
  rw [fixedPlane_comap]
  exact offender_eq_kernel planeGroup planeGroup_offender

/-- The source's unique offender in the Sylow group is the plane-fixing four-group. -/
theorem offender_in_sylow_iff (A : Subgroup HexEvenAutomorphisms)
    (hAT : A ≤ sylowGroup) : IsOffender Hexacode.evenAction A ↔ A = planeGroup := by
  constructor
  · intro hA
    obtain ⟨_, hc, _, hd⟩ := offender_dimensions A hA
    rcases fourGroup_exhaustion A hA.1.2 hAT hc with h | h
    · rw [h, lineFixed_finrank] at hd
      omega
    · exact h
  · rintro rfl
    exact planeGroup_offender

/-- The full even-cover endpoint, with no representation-recognition or outer premise. -/
theorem modelCalculation : ModelCalculation Hexacode.evenAction ⊤ :=
  model_of_four planeGroup planeGroup_elementary SylowModel.planeGroup_card planeFixed_finrank

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry
