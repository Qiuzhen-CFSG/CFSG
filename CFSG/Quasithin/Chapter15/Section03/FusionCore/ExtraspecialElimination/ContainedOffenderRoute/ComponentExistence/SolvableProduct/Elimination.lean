module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Rank

/-!
# Eliminate the two-S₃ alternative for the contained actor

The supplied two-factor module alternative and actual S₃ identifications
construct a solvable star factor for the selected actor. Its cubic generation
uses a nontrivial projection of that actor; its moved rank is derived from
the decomposition modulo global fixed vectors; and normality of the conjugate
span bounds the factor's ambient orbit by two. The saturated lift therefore
has every field required by the proved local solvable-factor contradiction.

This closes the two-S₃ branch of B.5.6(3) for `PlacedInput`. Exhaustiveness
of the classification and the other branches remain with component existence.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),
printed p.105, and proof of 15.3.49(i), printed pp.1143–1144.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)

/-- The actual contained actor cannot have the two-S₃ source alternative.
All rank, orbit, cubic-generation and saturated-lift premises are discharged. -/
theorem not_two_symmetricThree (c : TwoFactorCase (starAction d))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3)) :
    False :=
  d.no_solvableStarFactor (of_two_symmetricThree d c e₁ e₂)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct
