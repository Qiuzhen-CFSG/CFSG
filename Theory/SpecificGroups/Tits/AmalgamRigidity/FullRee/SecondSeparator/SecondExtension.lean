module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.Endpoint
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.Graph
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.Compatibility
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.WeylVerification

/-!
# Extension of the short separator to the full second endpoint

The certified literal Weyl equations and the short separator's compatibility
give an actual automorphism of the full second endpoint through the bounded
graph construction. The inclusion is exactly `coordinateAmalgam.right`, and
the construction sends the specified Weyl lift to its product with root 7.
The final theorem discharges every relation premise and gives the commuting
square on the entire coordinate Sylow group.

Source: Shinoda (1975), pp.81–83; Parrott (1972), p.683;
Aschbacher–Smith F.1.11–12, pp.262–263.
-/

@[expose] public section
noncomputable section
namespace Tits.AmalgamRigidity.FullRee
open ReeTwo
namespace SecondExtension

/-- The prescribed images on the entire Sylow subgroup. -/
def imageInclusion : SylowModel →* Endpoint :=
  inclusion.comp SecondSeparator.separator.toMonoidHom

/-- The proposed Weyl image in the literal endpoint. -/
def imageReflection : Endpoint := reflection * inclusion (SylowModel.root 7)

/-- The proposed images generate the whole endpoint, independently of their
relation checks: the separator is onto the Sylow group, which also contains
the factor correcting the Weyl element. -/
theorem images_generate :
    Subgroup.closure (insert imageReflection (Set.range imageInclusion)) = ⊤ := by
  let H := Subgroup.closure (insert imageReflection (Set.range imageInclusion))
  have hi (x : SylowModel) : inclusion x ∈ H := by
    obtain ⟨y, rfl⟩ := SecondSeparator.separator.surjective x
    exact Subgroup.subset_closure (Or.inr ⟨y, rfl⟩)
  have hr : reflection ∈ H := by
    have hs : imageReflection ∈ H := Subgroup.subset_closure (Or.inl rfl)
    have he : reflection = imageReflection * (inclusion (SylowModel.root 7))⁻¹ := by
      simp only [imageReflection, mul_inv_cancel_right]
    rw [he]
    exact H.mul_mem hs (H.inv_mem (hi _))
  apply top_unique
  rw [← endpoint_generated]
  exact (Subgroup.closure_le _).mpr (by rintro x (rfl | ⟨x, rfl⟩); exact hr; exact hi x)

end SecondExtension

/-- The literal word relations produce the full-endpoint extension. -/
theorem separator_extends_of_weyl_relations
    (hsource : SecondExtension.WeylRelations SecondExtension.inclusion SecondExtension.reflection) :
    ∃ a : MulAut ExceptionalParabolics.FullRee.second, ∀ x : SylowModel,
      a (coordinateAmalgam.right x) = coordinateAmalgam.right (SecondSeparator.separator x) := by
  obtain ⟨a, ha, _⟩ := SecondExtension.exists_aut_of_relations
    SecondExtension.inclusion SecondExtension.imageInclusion
    SecondExtension.reflection SecondExtension.imageReflection hsource hsource.separator
    SecondExtension.endpoint_generated SecondExtension.images_generate
    ExceptionalParabolics.FullRee.second_card
  exact ⟨a, ha⟩

/-- The short Sylow involution extends to the literal full Ree second endpoint,
along its verified marked inclusion. All Weyl equations are discharged. -/
theorem separator_extends :
    ∃ a : MulAut ExceptionalParabolics.FullRee.second, ∀ x : SylowModel,
      a (coordinateAmalgam.right x) = coordinateAmalgam.right (SecondSeparator.separator x) :=
  separator_extends_of_weyl_relations SecondExtension.weyl_relations

end Tits.AmalgamRigidity.FullRee
