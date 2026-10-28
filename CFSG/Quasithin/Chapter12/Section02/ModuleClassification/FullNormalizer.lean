module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.NormalizerSupplement

/-!
# The full-normalizer classification input on the chosen Irr⁺ space

The generic offender supplement is constructed from the original component
image, using its original conjugation operators. A full-normalizer FF
witness supplies all six B.5.1 clauses on the unchanged chosen space.
The conclusion uses one canonical supplement action and its exact instances.
Source: Aschbacher--Smith 3.2.8 and 12.2.2, pp.582 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual component image acting on the unchanged chosen space. -/
@[expose] def seedComponentAction : Representation (ZMod 2) D.componentImage D.space :=
  D.seedRepresentation.comp D.componentImage.subtype

/-- Every actual offender in the full normalizer gives all six B.5.1 clauses
on its generated supplement, with no new FF assumption on the seed. -/
theorem normalizer_offender_source_conclusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (A : Subgroup (linearNormalizer D.seedComponentAction))
    (hA : IsOffender
      (normalizerRepresentation D.seedComponentAction) A) :
    ModuleClassification.NormalizerConclusion D.seedComponentAction A := by
  let σ := D.seedComponentAction
  have hi₀ : IsIrrPlus D.seedRepresentation D.componentImage ⊤ := by
    simpa only [Submodule.comap_subtype_self] using
      D.irrPlus.isIrrPlus.restricted (reducedRepresentation (L ⊔ (T : Subgroup G)))
        D.irrPlus.invariant le_rfl
  have hi : IsIrrPlus σ ⊤ ⊤ := by
    apply hi₀.of_intertwining D.seedRepresentation σ (topEquiv (G := D.componentImage)).symm.toMonoidHom
      (topEquiv (G := D.componentImage)).symm.surjective LinearMap.id (fun _ _ he => he)
    · intro g v
      rfl
    · exact Submodule.map_id _
  let := D.componentImage_quasisimple h.quasisimple
  exact ModuleClassification.normalizer_source_of_irrPlus σ
    ((subspaceImageRepresentation_injective _ _).comp D.componentImage.subtype_injective)
    hi ((D.seed_sqtk h (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)).subgroup D.componentImage)
    A hA

/-- The source's full-normalizer FF assumption supplies a classified
supplement on the original space; no offender is moved into the seed actor. -/
theorem full_normalizer_source_conclusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hff : IsFFModule
      (normalizerRepresentation D.seedComponentAction)) :
    ∃ A : Subgroup (linearNormalizer D.seedComponentAction),
      IsOffender (normalizerRepresentation D.seedComponentAction) A ∧
      ModuleClassification.NormalizerConclusion D.seedComponentAction A := by
  obtain ⟨A,hA⟩ := hff
  exact ⟨A,hA,D.normalizer_offender_source_conclusion h A hA⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
