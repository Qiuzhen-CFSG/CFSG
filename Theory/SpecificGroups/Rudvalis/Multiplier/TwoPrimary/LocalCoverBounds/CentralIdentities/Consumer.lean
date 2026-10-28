module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.CentralIdentities
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds

/-!
# Application of the proved central identities to actual max4 covers

The collection premise of `max4CoverBounds_of_presentation` is now discharged
in F/[F,R]. Only faithfulness of the literal marked presentation remains with
its independent producer and the local-cover assembly owner. The final
ambient application also retains the independent marked involution lift.

Source: Aschbacher–Smith I.1.3(1), printed p.407.
-/

public section
namespace Rudvalis.Multiplier.TwoPrimary
open PerfectCentralCovering LocalPresentation LocalPresentation.CentralKernel

/-- The central collection premise is discharged; presentation faithfulness
remains the independent model comparison obligation. -/
theorem max4CoverBounds_of_faithful_presentation
    (hi : Function.Injective modelMap) : Max4CoverBounds :=
  max4CoverBounds_of_presentation hi collectionIdentities

/-- The actual ambient reduction with its central-identity premise discharged. -/
theorem kernel_card_le_two_of_faithful_presentation
    (hi : Function.Injective modelMap) (hlift : FirstInvolutionLift)
    {E : Type} [Group E] [Finite E] (c : Cover E Model)
    (hp : IsPGroup 2 c.toMonoidHom.ker) : Nat.card c.toMonoidHom.ker ≤ 2 :=
  kernel_card_le_two_of_presentation hi collectionIdentities hlift c hp

end Rudvalis.Multiplier.TwoPrimary
