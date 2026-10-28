module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.RootAlignment
-- Internal specification of the two hidden layout tables. The private import
-- is confined to these proofs; no existing definition body is exposed or changed.
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.RootAlignment

/-!
# The order of the positive Ree blocks

These equations expose the indices of the already constructed root layout,
without exposing its geometric proof data. They fix the parameter order for
the center exponent calculation. Indices are zero based.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

namespace ReeF4.NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

theorem positive_pair_indices : positiveRootWordLayout.pairIndex = ![7, 1, 5, 3] := by
  rfl

theorem positive_quartet_indices :
    positiveRootWordLayout.quartetIndex = ![0, 4, 6, 2] := by
  rfl

end ReeF4.NormalizedRootCentralizers.CenterExponent
