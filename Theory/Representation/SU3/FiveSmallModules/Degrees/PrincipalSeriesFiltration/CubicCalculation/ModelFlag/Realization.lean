module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Certificate
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Quotients
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CosetCardinality

/-!
# The concrete cubic SU₃(5) principal-series flag

The literal canonical Borel has 126 cosets. This completes the checked
transversal and generation certificate, yielding an actual equivariant
coordinate comparison for every original characteristic-two coefficient
field and every nontrivial cubic character. The coefficient scalar is the
inverse value of that character on a generating torus element; the two
actors are the inverse checked generators and their matrices are transposed.
The field, group, and upper-Borel identifications are already proved in the
coordinate comparison, not assumed here.

The uniform matrix certificate then supplies a rank-21 square-zero
intertwiner. Its image and kernel give the actual stages with successive
quotient dimensions 21, 84, 21. `model_flags` has no additional premises.
The imported quotient-coordinate API applies definitionally to these flags;
`model_flags_quotientEquiv` makes that application explicit. Simplicity of
those literal quotient actions remains with the separate consumer.

This assembly is a descendant of `ModelFlag` because the independent matrix
certificate itself imports the conditional construction in that module.
Source motivation: Guralnick–Malle, Proposition 4.3, p.10;
Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public noncomputable section
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
universe v

namespace ModelFlag

/-- The completed induction coordinates, over the unchanged coefficient field. -/
def modelCoordinates {K : Type v} [Field K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1) :
    Coordinates χ :=
  (FiniteGroup.certificate_of_canonical_card
    SevenRestriction.Twenty.canonical_borel_coset_card
    FiniteGroup.representatives_separate).coordinates
      SevenRestriction.Twenty.canonical_borel_coset_card χ hne hcube

end ModelFlag

/-- The concrete image/kernel flag for every original finite coefficient field. -/
def model_flags : ModelFlags.{v} :=
  fun K _ _ _ χ hne hcube =>
    (ModelFlag.modelCoordinates (K := K) χ hne hcube).flag ModelFlag.matrix_relations

/-- Explicit stages for the flag used by the separate simplicity consumer. -/
theorem model_flags_stage {K : Type v} [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1) (m : ℕ) :
    (model_flags K χ hne hcube).stage m =
      ModelFlag.imageKernelStage
        ((ModelFlag.modelCoordinates χ hne hcube).intertwiner ModelFlag.matrix_relations) m := rfl

variable {K : Type v} [Field K] [Finite K] [CharP K 2]
  (χ : standardBorel modelForm →* Kˣ) (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1)

/-- Coordinates on each literal quotient of the completed flag. The target
stages are the fixed matrix image and kernel, by `matrixStage_one` and
`matrixStage_two`; their generator actions are `matrixQuotient_actor_mk`. -/
def model_flags_quotientEquiv (m : ℕ) :
    (((model_flags K χ hne hcube).stage (m + 1)).toSubmodule ⧸
      (within ((model_flags K χ hne hcube).stage m)
        ((model_flags K χ hne hcube).stage (m + 1))).toSubmodule) ≃ₗ[K]
    (((ModelFlag.modelCoordinates χ hne hcube).matrixStage ModelFlag.matrix_relations
        (m + 1)).toSubmodule ⧸
      (within ((ModelFlag.modelCoordinates χ hne hcube).matrixStage ModelFlag.matrix_relations m)
        ((ModelFlag.modelCoordinates χ hne hcube).matrixStage ModelFlag.matrix_relations
          (m + 1))).toSubmodule) :=
  (ModelFlag.modelCoordinates χ hne hcube).quotientEquiv ModelFlag.matrix_relations m

/-- The completed quotient comparison intertwines the entire actual group. -/
theorem model_flags_quotientEquiv_action (m : ℕ) (g : standardGroup modelForm)
    (x : ((model_flags K χ hne hcube).stage (m + 1)).toSubmodule ⧸
      (within ((model_flags K χ hne hcube).stage m)
        ((model_flags K χ hne hcube).stage (m + 1))).toSubmodule) :
    model_flags_quotientEquiv χ hne hcube m
      ((within ((model_flags K χ hne hcube).stage m)
        ((model_flags K χ hne hcube).stage (m + 1))).quotientRepresentation g x) =
    (within ((ModelFlag.modelCoordinates χ hne hcube).matrixStage ModelFlag.matrix_relations m)
      ((ModelFlag.modelCoordinates χ hne hcube).matrixStage ModelFlag.matrix_relations
        (m + 1))).quotientRepresentation g (model_flags_quotientEquiv χ hne hcube m x) :=
  (ModelFlag.modelCoordinates χ hne hcube).quotientEquiv_action ModelFlag.matrix_relations m g x

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
