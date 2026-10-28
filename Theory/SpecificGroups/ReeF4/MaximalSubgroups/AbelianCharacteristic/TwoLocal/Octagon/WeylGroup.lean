module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Setup
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.WeylGroup.Rotation
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.WeylGroup.Presentation

/-!
# The marked relative Weyl group of the Ree octagon

The two actual orbit reflections generate the quotient of the fixed normalizer
words by its relative Borel intersection. Their product has eighth power one,
whereas its fourth power negates every root and cannot belong to the fixed
torus. The marked dihedral presentation therefore gives an actual multiplicative
equivalence with `DihedralGroup 8`, sending the linear and Suzuki classes to
`sr 0` and `sr 1`, respectively.

Source: GLS3 2.3.2(d) and 2.3.4(a,b), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
open Subgroup LargeLocalSeeds Parabolics SectionGeometry.BNPair
attribute [local instance] borel_inf_normalizerWords_normal

set_option linter.unusedVariables false in
/-- The actual Ree Weyl quotient is dihedral of order sixteen, with both
relative simple reflections identified in the prescribed order. The word
calculation also covers the binary endpoint; the stated bound is retained
for the octagon interface. -/
theorem hasOctagonalWeylGroup (m : ℕ) (hm : 1 ≤ m) : HasOctagonalWeylGroup m := by
  have hgen := simpleReflections_generate_of_normalizerWords m
    (normalizerWords_le_fixedTorus_sup_weylSubgroup m)
  rw [simpleReflections_eq_pair] at hgen
  exact MarkedWeyl.markedEquiv_of_involutions
    (simpleReflection m .linear) (simpleReflection m .suzuki)
    (simpleReflection_sq m .linear) (simpleReflection_sq m .suzuki)
    (MarkedWeyl.relativeRotation_pow_eight m)
    (MarkedWeyl.relativeRotation_pow_four_ne_one m) hgen

end ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
