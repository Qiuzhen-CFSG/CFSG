module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ThreeRelations
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.SourceSetup
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.Certificate07

/-!
# Vanishing of the final normalized conjugation error

The checked word certificate reduces two expressions to the same word s₄s₆;
their central coefficients differ by the inverse of the VII(r₃) error.
Cancellation therefore makes that error trivial. The replay uses the already
proved three remaining conjugations and VIII(r₃), retaining the braid error.
Every replay input is supplied by the literal normalized presentation under
precisely the power/root hypothesis.

This proves r₁ r₃ r₁ = s₇ r₇ and applies it to the four-equation consumer.
Source: Parrott (1972), §5, p.683. The commutator remains a⁻¹*b⁻¹*a*b;
no splitting, multiplier theorem, or exact braid equation is assumed.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators
open RemainingConjugations RemainingConjugations.ResidualInvolution

/-- The last central conjugation error vanishes under only the power/root
relations, giving the literal source equation r₁ r₃ r₁ = s₇ r₇. -/
theorem weyl_vii_r3_relation
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    FreeGroup.lift normalizedGenerator (parrottRelator .vii_r3) = 1 := by
  have h := (n3071 (normalizedContext hroot) (normalized_residual_source hroot)).scalar_eq_one
  have hv := congrArg (fun z : Subgroup.center NormalizedPresentation =>
    (z : NormalizedPresentation)) h
  simpa [Context.scalar, normalizedContext, relatorValue] using hv

/-- Application to the four remaining normalized Weyl conjugations, discharging
 the sole outstanding premise of the existing assembly theorem. -/
theorem weyl_remaining_conjugation_relations_via_residual
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ∀ j, isRemainingWeylConjugation j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 :=
  weyl_remaining_conjugation_relations_of_vii_r3 hroot (weyl_vii_r3_relation hroot)

end Tits.CentralCoverLifting.CompatibleGenerators
