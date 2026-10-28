module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowData

/-!
# The marked isomorphism from the actual local quotient to the star group

Conjugation descends through the abelian normal closure. The descended map
onto its image is bijective because both finite groups have certified order
244823040. Composing with the star comparison gives an actual multiplicative
equivalence, and its generator equations identify the two proposed involution
representatives. Thus conjugacy in the star group transfers to the precise
quotient used by `OutsideReduction`.

Source: the literal ATLAS `J4G1-max1W1` words documented in
`Cardinality.Subgroup`, and the kernel and image certificates in `LocalOrder`.
No splitting, abstract M24 identification, or J4 simplicity is used.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
public section
namespace Janko4.Simplicity.Max1Fusion.QuotientInvolutions
open Cardinality Cardinality.QuotientCount Cardinality.QuotientCount.Image
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

private theorem kernel_le_rangeRestrict_ker :
    localKernel hA hB ≤ (action hA hB).rangeRestrict.ker := by
  intro n hn
  apply Subtype.ext
  exact localKernel_le_action_ker_certified hA hB hn

private def quotientAction : LocalQuotient hA hB →* ActionImage hA hB :=
  QuotientGroup.lift (localKernel hA hB) (action hA hB).rangeRestrict
    (kernel_le_rangeRestrict_ker hA hB)

private theorem quotientAction_bijective : Function.Bijective (quotientAction hA hB) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  constructor
  · exact QuotientGroup.lift_surjective_of_surjective _ _
      (action hA hB).rangeRestrict_surjective (kernel_le_rangeRestrict_ker hA hB)
  · rw [localQuotient_card hA hB, actionImage_card hA hB]

/-- The actual quotient, with its actual action, is the concrete star group. -/
noncomputable def quotientStarEquiv : LocalQuotient hA hB ≃* StarGroup :=
  (MulEquiv.ofBijective (quotientAction hA hB) (quotientAction_bijective hA hB)).trans
    (actionImageEquivStarGroup hA hB)

@[simp] theorem quotientStarEquiv_x :
    quotientStarEquiv hA hB (QuotientGroup.mk' (localKernel hA hB) (localX hA hB)) =
      starFirst := by
  apply Subtype.ext
  exact actionImageEquivStarGroup_x hA hB

@[simp] theorem quotientStarEquiv_y :
    quotientStarEquiv hA hB (QuotientGroup.mk' (localKernel hA hB) (localY hA hB)) =
      starSecond := by
  apply Subtype.ext
  exact actionImageEquivStarGroup_y hA hB

@[simp] theorem quotientStarEquiv_xy_seven :
    quotientStarEquiv hA hB
      (QuotientGroup.mk' (localKernel hA hB) ((localX hA hB * localY hA hB)^7)) =
      (starFirst * starSecond)^7 := by
  simp only [map_pow, map_mul, quotientStarEquiv_x, quotientStarEquiv_y]

/-- Transport star-group conjugacy to the actual quotient. The star-group
coverage premise is a separate finite certificate, not inferred from its order. -/
theorem quotient_coverage_of_star_coverage
    (hstar : ∀ w : StarGroup, orderOf w = 2 → ∃ g : StarGroup,
      starFirst = g * w * g⁻¹ ∨ (starFirst * starSecond)^7 = g * w * g⁻¹) :
    ∀ w : LocalQuotient hA hB, orderOf w = 2 → ∃ g : LocalQuotient hA hB,
      QuotientGroup.mk' (localKernel hA hB) (localX hA hB) = g * w * g⁻¹ ∨
      QuotientGroup.mk' (localKernel hA hB) ((localX hA hB * localY hA hB)^7) =
        g * w * g⁻¹ := by
  intro w hw
  let e := quotientStarEquiv hA hB
  obtain ⟨g, hg⟩ := hstar (e w) ((e.orderOf_eq w).trans hw)
  refine ⟨e.symm g, ?_⟩
  rcases hg with hg | hg
  · left
    apply e.injective
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, e,
      quotientStarEquiv_x] using hg
  · right
    apply e.injective
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, e,
      quotientStarEquiv_xy_seven] using hg

end Janko4.Simplicity.Max1Fusion.QuotientInvolutions
