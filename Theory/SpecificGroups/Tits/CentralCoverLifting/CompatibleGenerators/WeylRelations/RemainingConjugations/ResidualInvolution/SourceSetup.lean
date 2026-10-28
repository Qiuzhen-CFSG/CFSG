module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ThreeRelations
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.Inputs

/-!
# The two remaining central errors

After the three conjugation equations and VIII(r₃) have been proved, only
VI(r₁,r₈) and VII(r₃) retain central errors. This module specializes the
signed-word inputs to precisely that situation in `NormalizedPresentation`.
The braid error is retained; no exact braid equation is assumed.

Source: Parrott (1972), §5, p.683, using a⁻¹*b⁻¹*a*b for commutators.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution

/-- The replay inputs hold for the actual normalized generators, under only
 the original power/root hypothesis. -/
theorem normalized_residual_source
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ResidualSource (normalizedContext hroot) := by
  intro j
  have h := (normalized_source hroot j).eq
  constructor
  cases j <;> simpa [residualCoeff, sourceCoeff, Context.scalar, normalizedContext,
    relatorValue, weyl_vii_s4_relation hroot, weyl_vii_s3_relation hroot,
    weyl_viii_s2_relation hroot, weyl_vii_r3_defect_square hroot] using h

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
