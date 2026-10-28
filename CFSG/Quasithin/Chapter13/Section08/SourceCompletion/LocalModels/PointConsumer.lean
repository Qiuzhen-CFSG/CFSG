module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.Point
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.SourceAssembly

/-!
# The actual point-model input to the solvable 13.8.5 branch

The compatible local quotient and original action on V supply the
universal marked point-model alternative consumed by the two-factor
contradiction. This discharges that earlier-source field for every
standing 13.8 local configuration; no chosen point-model witness is
assumed. The remaining local residual and normalizer clauses of
13.2.2 and 13.5.5 are separate source results.

Source: Aschbacher–Smith, 13.2.2 and 13.8.5, pp.877–878,947.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Solvable.TwoFactors
open TransvectionRecognition.Component.ModelExtension

variable {G : Type*} [Group G] [Finite G]

/-- The literal universal `EarlierMarkedModels` input, derived from the
original component quotient and natural module action. -/
theorem earlier_marked_models : EarlierMarkedModels (G := G) := by
  intro T L V V₁ V₂ V₃ M G₁ s
  exact local_point_models s

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
