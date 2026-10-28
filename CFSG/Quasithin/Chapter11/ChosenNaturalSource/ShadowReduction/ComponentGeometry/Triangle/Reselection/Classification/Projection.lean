module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FullNormalizer
public import Theory.GroupTheory.SimpleSectionSolvableReduction

/-!
# The canonical component projection of the chosen triangle module

The component action image and the original conjugation action have the same
linear operators. Thus their full linear normalizers, including their FF
conditions, agree. On a simple two-core quotient the canonical component
projection is an isomorphism. Adjoining an offender preserves this marking,
also after restricting to the actual offender subgroup used in B.5.1.

This is the actor transport needed before comparing the two field-four rows
in 11.0.2 and 11.4.1. It does not classify the chosen module.
Source: Aschbacher--Smith, 3.2.8, p.582; 11.0.2, pp.759--760.
-/

-- These declarations share large dependent action types. Serial elaboration
-- avoids repeatedly expanding the same instances in parallel.
set_option Elab.async false

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
open Chapter12.Section02
private theorem actionImage_comp_surjective {P Q W : Type*} [Group P] [Group Q]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) P W) (f : Q →* P) (hf : Function.Surjective f) :
    actionImage (σ.comp f) = actionImage σ := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f x, Units.ext rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, Units.ext rfl⟩


private theorem normalizer_ff_iff_of_image_eq {P Q W : Type*} [Group P] [Group Q]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) P W) (σ : Representation (ZMod 2) Q W)
    (he : actionImage ρ = actionImage σ) :
    IsFFModule (normalizerRepresentation ρ) ↔ IsFFModule (normalizerRepresentation σ) := by
  unfold normalizerRepresentation linearNormalizer
  rw [he]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The action projection, specified on the original component elements. -/
@[expose] def componentProjection : L →* D.componentImage :=
  (restrictedActionSurjection (reducedRepresentation (L ⊔ (T : Subgroup G))) D.space
    (L.subgroupOf (L ⊔ (T : Subgroup G))) D.irrPlus.invariant).comp
      (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm.toMonoidHom

omit [Finite G] in
theorem componentProjection_surjective : Function.Surjective (componentProjection D) :=
  (restrictedActionSurjection_surjective _ _ _ D.irrPlus.invariant).comp
    (subgroupOfEquivOfLe le_sup_left).symm.surjective

omit [Finite G] in
theorem componentProjection_action (l : L) :
    D.seedComponentAction (componentProjection D l) = D.chosenAction l := by
  ext v
  rfl

theorem componentProjection_core : pCore 2 L ≤ (componentProjection D).ker := by
  intro l hl
  apply ((subspaceImageRepresentation_injective _ _).comp
    D.componentImage.subtype_injective)
  exact (componentProjection_action D l).trans (D.chosenAction_core hl)

/-- Factorization by the original two-core, with its original quotient map. -/
@[expose] def quotientComponentProjection : (L ⧸ pCore 2 L) →* D.componentImage :=
  QuotientGroup.lift _ (componentProjection D) (componentProjection_core D)

theorem quotientComponentProjection_mk (l : L) :
    quotientComponentProjection D (QuotientGroup.mk' (pCore 2 L) l) =
      componentProjection D l := (rfl)

theorem quotientComponentProjection_surjective :
    Function.Surjective (quotientComponentProjection D) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (componentProjection_surjective D)
    (componentProjection_core D)

theorem quotientComponentProjection_action (q : L ⧸ pCore 2 L) :
    D.seedComponentAction (quotientComponentProjection D q) = D.quotientAction q := by
  refine Quotient.inductionOn q ?_
  intro l
  exact componentProjection_action D l

/-- The faithful image has exactly the source's simple acting quotient. -/
@[expose] def quotientComponentEquiv (hs : IsSimpleGroup (L ⧸ pCore 2 L)) :
    (L ⧸ pCore 2 L) ≃* D.componentImage := by
  letI := hs
  exact MulEquiv.ofBijective (quotientComponentProjection D)
    ⟨(quotientComponentProjection D).injective_of_surjective_of_simple
      (quotientComponentProjection_surjective D), quotientComponentProjection_surjective D⟩

theorem quotientComponentEquiv_mk (hs : IsSimpleGroup (L ⧸ pCore 2 L))
    (l : L) : quotientComponentEquiv D hs (QuotientGroup.mk' (pCore 2 L) l) =
      componentProjection D l := (rfl)

omit [Finite G] in
/-- Replacing the source actor by its faithful image changes no operators. -/
theorem actionImage_eq : actionImage D.chosenAction = actionImage D.seedComponentAction := by
  have he : D.chosenAction = D.seedComponentAction.comp (componentProjection D) :=
    MonoidHom.ext (fun l => (componentProjection_action D l).symm)
  rw [he]
  exact actionImage_comp_surjective _ _ (componentProjection_surjective D)

omit [Finite G] in
theorem fullNormalizer_eq : linearNormalizer D.chosenAction = linearNormalizer D.seedComponentAction := by
  unfold linearNormalizer
  rw [actionImage_eq D]

omit [Finite G] in
/-- The FF hypothesis is on the full normalizer of the original module. -/
theorem fullNormalizer_ff_iff :
    IsFFModule (normalizerRepresentation D.chosenAction) ↔
      IsFFModule (normalizerRepresentation D.seedComponentAction) :=
  normalizer_ff_iff_of_image_eq _ _ (actionImage_eq D)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
