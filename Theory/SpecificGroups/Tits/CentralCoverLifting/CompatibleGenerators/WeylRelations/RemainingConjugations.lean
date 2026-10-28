module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.OddOrder
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ThreeRelations
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution

/-!
# The remaining normalized Weyl conjugation calculation

VII(s₄), VII(s₃), VII(r₃), and VIII(s₂) hold under precisely the power/root
hypothesis. The first checked word calculation proves three equations and
bounds the remaining central error by an involution. The residual calculation
then kills that error by cancellation. We assemble these results into the
four conjugation equations required by the Weyl-seed consumer, without an
exact braid equation, splitting, or multiplier hypothesis.

Source: Parrott (1972), §5, p.683. The imported proofs use the actual
normalized presentation, its correction words, and a checked replay of
central word identities.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators

/-- All four remaining normalized Weyl conjugation equations follow from the
power/root relations. This discharges `hconj` in the Weyl-seed assembly. -/
theorem weyl_remaining_conjugation_relations
    (hroot : ∀ j, isPowerRootRelator j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1) :
    ∀ j, isRemainingWeylConjugation j = true →
      FreeGroup.lift normalizedGenerator (parrottRelator j) = 1 :=
  weyl_remaining_conjugation_relations_of_vii_r3 hroot (weyl_vii_r3_relation hroot)

end Tits.CentralCoverLifting.CompatibleGenerators
