module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.LinearAction.Labels
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection

/-!
# A faithful degree-36 action of the full binary symplectic group

The full matrix group acts on all 36 even quadratic refinements of its natural
six-space by inverse substitution. Transport along the checked point marking
gives `linearAction`, whose three generator values are exactly the existing
Co₃ fixed-point tables. Faithfulness follows by recovering every vector
coordinate from the base form and the six basis-parameter forms.

The final applications discharge the action and marking premises of the actual
`pointGroupEquiv` and `symplecticQuotientMap`. Only full matrix generation,
owned independently by the generation task, remains explicit there.
Source: GLS3 Table 5.3j; Aschbacher--Smith A.2.19, printed pp.40–41.
The adapted refinement proofs retain the ATLAS attribution and license in
`LinearAction/source/`; the shared matrices, point tables and assembly are unchanged.
-/

@[expose] public section
noncomputable section
namespace Sporadic.LeechRelated.Co3.CentralizerSection
open LinearAction

/-- The action of every symplectic matrix, in the fixed 36-point marking. -/
def linearAction : LinearData.Sp →* Equiv.Perm (Fin 36) :=
  pointFormEquiv.symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom LinearData.Sp EvenRefinement)

/-- Faithfulness requires no assumption about generation by the marked matrices. -/
theorem linearAction_injective : Function.Injective linearAction :=
  pointFormEquiv.symm.permCongrHom.injective.comp MulAction.toPerm_injective

theorem linearAction_pointForm (g : LinearData.Sp) (j : Fin 36) :
    pointForm (linearAction g j) = g • pointForm j := by
  change pointFormEquiv (pointFormEquiv.symm (g • pointFormEquiv j)) = _
  exact pointFormEquiv.apply_symm_apply _

theorem linearAction_generator (i : Fin 3) :
    linearAction (LinearData.generator i) = Tables.pointGenerator i := by
  apply Equiv.ext
  intro j
  apply pointForm_injective
  rw [linearAction_pointForm, generator_pointForm]

/-- The literal quadratic-function action is Q(x) ↦ Q(g⁻¹x). -/
theorem linearAction_quadratic (g : LinearData.Sp) (j : Fin 36) (x : V) :
    q₀ x + beta x (pointParameter (linearAction g j)) =
      q₀ (g⁻¹ • x) + beta (g⁻¹ • x) (pointParameter j) := by
  exact congrArg (fun Q : EvenRefinement => Q.val.val x) (linearAction_pointForm g j)

/-- The exact generator images now discharge the marking premise in the image comparison. -/
theorem linearAction_range_of_generation
    (hgenerate : Subgroup.closure (Set.range LinearData.generator) = ⊤) :
    linearAction.range = pointGroup :=
  linearAction_range linearAction linearAction_generator hgenerate

/-- The original point-image comparison, with only matrix generation still required. -/
def pointGroupEquivOfGeneration
    (hgenerate : Subgroup.closure (Set.range LinearData.generator) = ⊤) :
    pointGroup ≃* LinearData.Sp :=
  pointGroupEquiv linearAction linearAction_injective linearAction_generator hgenerate

/-- Apply the proved faithful action to the literal central quotient map. -/
def symplecticQuotientMapOfGeneration
    (hgenerate : Subgroup.closure (Set.range LinearData.generator) = ⊤) :
    numerator →* SymplecticQuotient :=
  symplecticQuotientMap linearAction linearAction_injective linearAction_generator hgenerate

theorem symplecticQuotientMapOfGeneration_surjective
    (hgenerate : Subgroup.closure (Set.range LinearData.generator) = ⊤) :
    Function.Surjective (symplecticQuotientMapOfGeneration hgenerate) :=
  symplecticQuotientMap_surjective linearAction linearAction_injective
    linearAction_generator hgenerate

end Sporadic.LeechRelated.Co3.CentralizerSection
