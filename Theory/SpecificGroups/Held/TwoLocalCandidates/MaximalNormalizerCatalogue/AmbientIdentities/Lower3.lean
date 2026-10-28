module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Checks3
import Mathlib.Tactic.FinCases

/-!
# Conjugation for the distinguished max4 row

The individual point checks are cached in `Checks3`. The certified four-point
base turns them into equalities in Held. Source: the literal ATLAS action and
GLS3 Table 5.3p, with the unchanged conjugator and row words from `LowerData`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities

-- Keep word evaluation out of the conversion of finite indices.
attribute [local irreducible] mappedGenerator rowGenerator rowProduct conjugateFactors

set_option maxRecDepth 16384 in
public theorem conjugation_3 (t : Fin 2) (j : Fin 6) :
    mappedGenerator 3 t * rowGenerator 3 j * (mappedGenerator 3 t)⁻¹ =
      rowProduct 3 (conjugateFactors 3 t j) := by
  fin_cases t <;> fin_cases j
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_0_0 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_0_1 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_0_2 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_0_3 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_0_4 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_0_5 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_1_0 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_1_1 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_1_2 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_1_3 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_1_4 x
  · apply eq_of_four_point_images
    intro x
    exact Checks3.check_1_5 x

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities
