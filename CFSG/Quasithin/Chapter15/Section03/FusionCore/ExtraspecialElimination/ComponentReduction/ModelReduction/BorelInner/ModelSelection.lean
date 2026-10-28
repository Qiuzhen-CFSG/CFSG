module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Transport

/-!
# Preparations for the model selection in 15.3.49(k)

`ModelSelection.Transport` constructs the actual two-core quotient maps,
the Sylow intersections and normalizer quotient equivalence, and the whole
finite family of conjugate components. Its solvability equivalence reduces
the required assertion about N_{L₀}(T₀) to the intrinsic star normalizer.

The source model-selection theorem remains to be assembled from the full
FF classification, the A.3.18 exceptional exclusions, and the concrete Borel
calculations. No surviving Lie alternative or Borel solvability is asserted
from `SourceSetup` in this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1143–1144, proof of 15.3.49(k).
-/
