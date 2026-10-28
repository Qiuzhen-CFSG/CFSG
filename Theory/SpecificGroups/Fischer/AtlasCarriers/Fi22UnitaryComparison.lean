module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22CentralizerAction
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinaryFaithfulness
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinaryTransvections
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison
public import Theory.SpecificGroups.ClassicalUnitary.SixDimensionalBinaryGeneration

/-!
# Comparing the Fi22 fixed-point image with U₆(2)

A labeling of the ATLAS involution's fixed points by the isotropic lines
of GF(4)⁶ together with a singleton transports its permutation image.
Equality with the projective unitary action image, and faithfulness of that
unitary action, then give a multiplicative equivalence of the two groups.

The checked Schreier and coordinate certificates in `Fi22TransvectionComparison`
identify the relabeled image with the unitary transvection permutation group.
`SixDimensionalBinaryGeneration` proves that these transvections generate the
projective matrix group, and `SixDimensionalBinaryFaithfulness` proves that
its isotropic-point action is faithful. The resulting `unitaryComparison`
has no additional premises and intertwines the two actual actions.

This establishes the fixed-point image identification needed for the Fi22
centralizer entry of GLS3 Table 5.3t
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`). The parent centralizer assembly combines
it with the separate involution-order and action-kernel certificates.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi22

open Theory.SpecificGroups

/-- The concrete ATLAS action transported by a specified labeling. -/
noncomputable def relabeledFixedPointAction
    (e : FixedPointsA ≃ U6Two.PointWithSingleton) :
    centralizerA →* Equiv.Perm U6Two.PointWithSingleton :=
  e.permCongrHom.toMonoidHom.comp fixedPointAction

theorem relabeledFixedPointAction_apply
    (e : FixedPointsA ≃ U6Two.PointWithSingleton)
    (g : centralizerA) (p : FixedPointsA) :
    relabeledFixedPointAction e g (e p) = e (fixedPointAction g p) := by
  change e (fixedPointAction g (e.symm (e p))) = _
  rw [e.symm_apply_apply]

theorem relabeledFixedPointAction_range
    (e : FixedPointsA ≃ U6Two.PointWithSingleton) :
    (relabeledFixedPointAction e).range =
      fixedPointAction.range.map e.permCongrHom.toMonoidHom :=
  MonoidHom.range_comp _ _

/-- Assembly from an equality of permutation images and explicit faithfulness. -/
noncomputable def unitaryComparisonOfActionImages
    (e : FixedPointsA ≃ U6Two.PointWithSingleton)
    (hfaithful : Function.Injective U6Two.isotropicAction)
    (himages : (relabeledFixedPointAction e).range =
      U6Two.isotropicActionWithSingleton.range) :
    FixedPointImage ≃* U6Two.Carrier :=
  (e.permCongrHom.subgroupMap fixedPointAction.range).trans <|
    (MulEquiv.subgroupCongr ((relabeledFixedPointAction_range e).symm.trans himages)).trans
      (MonoidHom.ofInjective
        (U6Two.isotropicActionWithSingleton_injective_iff.mpr hfaithful)).symm

/-- The assembled group equivalence intertwines the two specified actions. -/
theorem unitaryComparisonOfActionImages_intertwines
    (e : FixedPointsA ≃ U6Two.PointWithSingleton)
    (hfaithful : Function.Injective U6Two.isotropicAction)
    (himages : (relabeledFixedPointAction e).range =
      U6Two.isotropicActionWithSingleton.range)
    (g : FixedPointImage) (p : FixedPointsA) :
    U6Two.isotropicActionWithSingleton
      (unitaryComparisonOfActionImages e hfaithful himages g) (e p) = e (g.val p) := by
  have h := MonoidHom.apply_ofInjective_symm
    (U6Two.isotropicActionWithSingleton_injective_iff.mpr hfaithful)
    ((MulEquiv.subgroupCongr ((relabeledFixedPointAction_range e).symm.trans himages))
      (e.permCongrHom.subgroupMap fixedPointAction.range g))
  change U6Two.isotropicActionWithSingleton
    (unitaryComparisonOfActionImages e hfaithful himages g) =
      e.permCongrHom g.val at h
  rw [h]
  change e (g.val (e.symm (e p))) = _
  rw [e.symm_apply_apply]

/-- The transvection route: combine generation in the matrix model with an
actual comparison of the two permutation groups. Geometric faithfulness is
discharged by `U6Two.isotropicAction_injective`. -/
noncomputable def unitaryComparisonOfTransvectionImages
    (e : FixedPointsA ≃ U6Two.PointWithSingleton)
    (hgen : U6Two.transvectionSubgroup = ⊤)
    (himages : (relabeledFixedPointAction e).range =
      U6Two.transvectionPermutationSubgroup) :
    FixedPointImage ≃* U6Two.Carrier :=
  unitaryComparisonOfActionImages e U6Two.isotropicAction_injective
    (himages.trans (U6Two.transvectionPermutationSubgroup_eq_range_of_generation hgen))

/-- The transvection construction preserves the specified permutation actions. -/
theorem unitaryComparisonOfTransvectionImages_intertwines
    (e : FixedPointsA ≃ U6Two.PointWithSingleton)
    (hgen : U6Two.transvectionSubgroup = ⊤)
    (himages : (relabeledFixedPointAction e).range =
      U6Two.transvectionPermutationSubgroup)
    (g : FixedPointImage) (p : FixedPointsA) :
    U6Two.isotropicActionWithSingleton
      (unitaryComparisonOfTransvectionImages e hgen himages g) (e p) = e (g.val p) :=
  unitaryComparisonOfActionImages_intertwines e U6Two.isotropicAction_injective
    (himages.trans (U6Two.transvectionPermutationSubgroup_eq_range_of_generation hgen)) g p

/-- The explicit fixed-point labeling identifies the full ATLAS action image
with the full projective unitary action image. -/
theorem relabeledFixedPointAction_labelingEquiv_range :
    (relabeledFixedPointAction TransvectionComparison.Labeling.labelingEquiv).range =
      U6Two.isotropicActionWithSingleton.range := by
  rw [relabeledFixedPointAction_range, TransvectionComparison.labelingEquiv_image_eq,
    U6Two.transvectionPermutationSubgroup_eq_range]

/-- The concrete Fi22 fixed-point image is multiplicatively equivalent to the
projective image of the identity-form special unitary group over GF(4). -/
noncomputable def unitaryComparison : FixedPointImage ≃* U6Two.Carrier :=
  unitaryComparisonOfActionImages TransvectionComparison.Labeling.labelingEquiv
    U6Two.isotropicAction_injective relabeledFixedPointAction_labelingEquiv_range

/-- The unconditional comparison preserves the actual labeled permutation action. -/
theorem unitaryComparison_intertwines (g : FixedPointImage) (p : FixedPointsA) :
    U6Two.isotropicActionWithSingleton (unitaryComparison g)
      (TransvectionComparison.Labeling.labelingEquiv p) =
        TransvectionComparison.Labeling.labelingEquiv (g.val p) :=
  unitaryComparisonOfActionImages_intertwines TransvectionComparison.Labeling.labelingEquiv
    U6Two.isotropicAction_injective relabeledFixedPointAction_labelingEquiv_range g p

/-- The equivalence needed by the Fi22 involution-centralizer quotient assembly. -/
theorem nonempty_unitaryComparison : Nonempty (FixedPointImage ≃* U6Two.Carrier) :=
  ⟨unitaryComparison⟩

end Sporadic.Fischer.Fi22
