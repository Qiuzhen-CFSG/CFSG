module

public import Theory.SpecificGroups.Rudvalis.Multiplier.OddPrimary
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.Reduction
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.FirstInvolutionLift

/-!
# Rudvalis two-primary multiplier upper bound

Every finite perfect central cover of the actual Rudvalis model has kernel
of order at most two. The odd-primary calculation makes the kernel a
two-group. Restriction to the concrete perfect odd-index max4 subgroup
preserves the whole kernel, and the proved local cover calculation makes
it elementary abelian. Ambient involution fusion supplies the marked
involutory lift, so the sharper local bound applies.

Both local inputs are discharged here. In particular, four does not divide
the order of the canonical universal kernel. No simplicity hypothesis or
multiplier-dependent covering theorem is needed for this upper bound.

Source: Aschbacher--Smith I.1.3(1), printed p.407. The exact cyclic-order-two
assembly remains in the parent `Multiplier` module.
-/

namespace Rudvalis.Multiplier
open PerfectCentralCovering TwoPrimary

/-- Conditional source assembly from the two local calculations. -/
public theorem universal_kernel_not_four_dvd_of_local_bounds
    (hlocal : Max4CoverBounds) (hlift : FirstInvolutionLift) :
    ¬ 4 ∣ Nat.card (universalProjection Model).ker := by
  have hb := kernel_card_le_two_of_local_bounds hlocal hlift (universalCover Model)
    (kernel_isPGroup (universalProjection Model)
      (universalProjection_surjective Model) (universalProjection_ker_le_center Model))
  change Nat.card (universalProjection Model).ker ≤ 2 at hb
  intro hd
  have hle := Nat.le_of_dvd Nat.card_pos hd
  omega

/-- Every finite perfect central cover of the actual Rudvalis model has
kernel of order at most two, with both local calculations discharged. -/
public theorem kernel_card_le_two
    {E : Type} [Group E] [Finite E] (c : Cover E Model) :
    Nat.card c.toMonoidHom.ker ≤ 2 := by
  let : Group.IsPerfect E := c.isPerfect
  exact kernel_card_le_two_of_local_bounds max4CoverBounds firstInvolutionLift c
    (kernel_isPGroup c.toMonoidHom c.surjective c.ker_le_center)

/-- The two-primary upper bound for the actual Rudvalis universal kernel,
supplying the remaining upper-bound premise in the I.1.3(1) assembly. -/
public theorem universal_kernel_not_four_dvd :
    ¬ 4 ∣ Nat.card (universalProjection Model).ker := by
  have hb := kernel_card_le_two (universalCover Model)
  change Nat.card (universalProjection Model).ker ≤ 2 at hb
  intro hd
  have hle := Nat.le_of_dvd Nat.card_pos hd
  omega

end Rudvalis.Multiplier
