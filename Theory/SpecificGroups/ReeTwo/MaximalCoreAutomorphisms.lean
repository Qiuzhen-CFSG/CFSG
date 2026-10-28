module

public import Theory.SpecificGroups.ReeTwo.MaximalCoreCoordinates
public import Theory.SpecificGroups.ReeTwo.MaximalCoreFrattini
public import Theory.SpecificGroups.ReeTwo.SylowEighthPower
public import Theory.GroupTheory.PGroup.FourQuotientPowerFiber

/-!
# Automorphism reduction for the four core-character kernels

The parity and root-3 coordinates give a quotient of order four. Two
structural facts suffice to prove that the automorphisms of each kernel
form a two-group: the coordinate kernel lies in the Frattini subgroup,
and elements with nontrivial eighth power form the fiber with both
coordinates nontrivial. The general power-fiber theorem then makes the
coordinate kernel characteristic and controls both the quotient action
and its kernel.

The conditional assembly interface is retained below. The final theorem
discharges both structural facts using the coordinate Frattini proof and
the six-coordinate calculation of eighth powers.

Source: Shinoda (1975), (2.3), pp. 81–83, for the coordinate model; the
automorphism argument uses Burnside's Frattini kernel theorem.
-/

namespace ReeTwo.SylowModel

/-- The two intrinsic coordinate facts imply the desired automorphism theorem
for all four core-character kernels. -/
public theorem maximalCore_isPGroup_mulAut_of_frattini_and_eighth_power
    (hfrattini : ∀ a b : ZMod 2,
      (maximalCoreQuotient a b).ker ≤ frattini (maximalCore a b))
    (hpower : ∀ x : SylowModel, x ^ 8 ≠ 1 ↔
      character x = FiveFour.generator 2 ∧ rootThreeCharacter x = FiveFour.generator 2)
    (a b : ZMod 2) : IsPGroup 2 (MulAut (maximalCharacter a b 1).ker) := by
  apply MonoidHom.isPGroup_mulAut_of_four_quotient_power_fiber
    (maximalCore_isPGroup a b) (maximalCoreQuotient a b)
    (maximalCoreQuotient_surjective a b) maximalCoreQuotient_card
    (hfrattini a b) (FiveFour.generator 2, FiveFour.generator 2) (by decide) 8
  intro x
  have hp : x ^ 8 = 1 ↔ (x : SylowModel) ^ 8 = 1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  refine (not_congr hp).trans ((hpower x).trans ?_)
  change _ ↔ (character (x : SylowModel), rootThreeCharacter (x : SylowModel)) = _
  constructor
  · rintro ⟨h₁, h₂⟩
    exact Prod.ext h₁ h₂
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Each of the four maximal kernels with nonzero core-character coefficient
has a two-group of automorphisms. -/
public theorem maximalCore_isPGroup_mulAut (a b : ZMod 2) :
    IsPGroup 2 (MulAut (maximalCharacter a b 1).ker) :=
  maximalCore_isPGroup_mulAut_of_frattini_and_eighth_power
    maximalCoreQuotient_ker_le_frattini eighth_power_ne_one_iff a b

end ReeTwo.SylowModel
