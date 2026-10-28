module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.SourceWords

/-!
# Word inputs retaining the two residual central errors

All source equations are exact except for the central VI(r₁,r₈) and VII(r₃)
errors. These are inputs to a generic word calculation; `SourceSetup`
supplies them for the literal normalized presentation.

Source: Parrott (1972), §5, p.683.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution

@[expose] def residualCoeff : ParrottRelatorIndex → Coeff
  | .vi_r1_r8 => (1, 0, 0, 0, 0, 0, 0)
  | .vii_r3 => (0, 0, 0, 0, 1, 0, 0)
  | _ => 0

/-- All source equations, with the two remaining errors left explicit. -/
@[expose] def ResidualSource {G : Type*} [Group G] (D : Context G) : Prop :=
  ∀ j, D.Holds (residualCoeff j) (sourceWord j) []

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
