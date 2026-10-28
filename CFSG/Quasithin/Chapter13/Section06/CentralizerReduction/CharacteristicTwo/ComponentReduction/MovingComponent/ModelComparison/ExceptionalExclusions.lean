module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.Inputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.ExceptionalExclusions.G2
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.ExceptionalExclusions.Ree

/-!
# The exceptional comparisons for the moving component

The intrinsic order and root-subgroup arguments exclude all four genuine
nonnormal-component carriers for both G₂ and Ree F₄. They retain the
octonion isomorphism and the supplied Ree exceptional endomorphism. The
uniform theorem matches `source_comparison_of_uniform_exclusions`; its
finite, simple and perfect inputs are already supplied by that consumer.

Source: Aschbacher–Smith, 1.1.5(3a,b), pp.501–503, 1.2.1(3), p.504,
and the moving-component comparison in 13.6.6, p.927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison

/-- The two exceptional families cannot occur in the genuine nonnormal list. -/
theorem exceptional_exclusions (Q : Type*) [Group Q] [Finite Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q] : ExceptionalExclusions Q where
  g2 _ hm hmodel := g2_not_nonnormal hm hmodel
  ree _ hn hmodel := ree_not_nonnormal hn hmodel

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
