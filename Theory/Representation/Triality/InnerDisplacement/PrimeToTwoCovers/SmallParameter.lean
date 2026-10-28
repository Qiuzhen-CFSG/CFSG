module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.Reduction
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount
public import Mathlib.Tactic.NormNum.Prime

/-!
# Odd central primes at the smallest triality parameter

The genuine fixed Bruhat cell count gives |³D₄(2)| = 2¹² · 3⁴ · 7² · 13.
Thus its Sylow thirteen subgroups have prime order, and transfer excludes
thirteen from every finite perfect central cover. Only the three- and
seven-primary local calculations remain in the exponent-one reduction.

This isolates the small parameter in the multiplier assertion of GLS3
§6.1. There is no triality odd-multiplier exception at this parameter.
The order used here is proved from the literal graph-field carrier,
not supplied by a family tag or a multiplier table.
-/

public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers

open PerfectCentralCovering
open PerfectCentralCovering.OddSylow

private theorem card_at_two : Nat.card (Standard.BinaryCarrier 1 (by decide)) =
    2 ^ 12 * 3 ^ 4 * 7 ^ 2 * 13 := by
  rw [Standard.ConcreteBruhat.FixedCellCount.card_carrier 1 (by decide),
    Standard.ConcreteBruhat.FixedCellCount.card_borel]
  norm_num [Standard.binaryParameters_q]

/-- The prime-thirteen Sylow geometry at q = 2 follows from the actual
Bruhat count, with no torus or covering premise. -/
theorem thirteen_geometry_at_two : Geometry 13 (Standard.BinaryCarrier 1 (by decide)) := by
  let : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  apply geometry_of_not_square_dvd_card
  rw [card_at_two]
  norm_num

/-- Every finite perfect central cover of the smallest triality group
has center of order prime to thirteen. -/
theorem not_thirteen_dvd_center_at_two {R : Type*} [Group R] [Finite R]
    [Group.IsPerfect R]
    (hmodel : Standard.IsTrialityGroupAt 2 (R ⧸ Subgroup.center R)) :
    ¬ 13 ∣ Nat.card (Subgroup.center R) := by
  let : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨e⟩ := (Standard.isTrialityGroupAt_two_iff _).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact thirteen_geometry_at_two.not_dvd_card_kernel (by decide) (centralQuotientCover e)

/-- At n = 1 only the local three- and seven-primary witnesses remain.
All other primes are excluded, including thirteen. -/
theorem center_isTwoGroup_at_two_of_three_seven_geometry {R : Type*}
    [Group R] [Finite R] [Group.IsPerfect R]
    (hmodel : Standard.IsTrialityGroupAt 2 (R ⧸ Subgroup.center R))
    (hthree : Geometry 3 (Standard.BinaryCarrier 1 (by decide)))
    (hseven : Geometry 7 (Standard.BinaryCarrier 1 (by decide))) :
    IsPGroup 2 (Subgroup.center R) := by
  apply center_isTwoGroup_of_sylow_geometry 1 (by decide) (by simpa using hmodel)
  intro p hp hp2 hdiv
  rw [card_at_two] at hdiv
  have hprime := (Fact.out : p.Prime)
  rcases hprime.dvd_mul.mp hdiv with hdiv | h13
  · rcases hprime.dvd_mul.mp hdiv with hdiv | h7
    · rcases hprime.dvd_mul.mp hdiv with h2 | h3
      · exact (hp2 ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
          (hprime.dvd_of_dvd_pow h2))).elim
      · have heq : p = 3 := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_three).mp
          (hprime.dvd_of_dvd_pow h3)
        subst p
        exact hthree
    · have heq : p = 7 := (Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp
        (hprime.dvd_of_dvd_pow h7)
      subst p
      exact hseven
  · have heq : p = 13 := (Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp h13
    subst p
    exact thirteen_geometry_at_two

end Triality.InnerDisplacement.PrimeToTwoCovers
