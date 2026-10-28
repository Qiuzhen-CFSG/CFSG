module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.BlockAction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.ClassicalModel
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A concrete involution-centralizer quotient in sporadic Suz

The actual degree-1782 carrier contains the involution `word ^ 6`. The two
checked centralizing words generate `numerator`, whose action on 27 explicit
pairs surjects onto `BlockGroup`. The faithful quadratic action and certified
generation theorem identify this exact image with the canonical `PΩ⁻₆(2)`.
Composing these maps gives the required surjection. The first isomorphism
theorem identifies the quotient by its kernel, normal inside the numerator.

The target is the orthogonal commutator subgroup modulo its scalar subgroup;
no full-isometry quotient or splitting is needed. This construction requires
no ambient simplicity or additional model-comparison hypothesis.
Source: ATLAS SuzG1-p1782B0; GLS3 Table 5.3o; Aschbacher--Smith A.2.19,
printed pp.40--41. See `CentralizerSection/source/README.md` for conventions.
-/

public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection

/-- The literal quotient by the kernel of the action on pairs. -/
noncomputable def blockQuotientEquiv : numerator ⧸ blockAction.ker ≃* BlockGroup :=
  QuotientGroup.quotientKerEquivOfSurjective blockAction blockAction_surjective

/-- The action of the two centralizing words, in the canonical projective
minus orthogonal model. -/
noncomputable def quotientMap :
    numerator →* ClassicalGroup.POmegaMinus 3 (ZMod 2) :=
  blockEquivPOmegaMinus.toMonoidHom.comp blockAction

/-- The literal centralizing subgroup maps onto the entire canonical target. -/
theorem quotientMap_surjective : Function.Surjective quotientMap :=
  blockEquivPOmegaMinus.surjective.comp blockAction_surjective

/-- The canonical orthogonal section, with the kernel normal in `numerator`. -/
noncomputable def quotientEquiv :
    numerator ⧸ quotientMap.ker ≃* ClassicalGroup.POmegaMinus 3 (ZMod 2) :=
  QuotientGroup.quotientKerEquivOfSurjective quotientMap quotientMap_surjective

end Sporadic.LeechRelated.Suz.CentralizerSection
