module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.SpecificGroups.BinaryLinear.FourResidual

/-!
# The remaining A.3.6 catalogue obligation

This proposition isolates a model comparison, not an additional source
hypothesis: a C-component satisfying the complete A.3.6 conclusion cannot
have SL₄(2) as a proper homomorphic image. In the simple case this is
immediate. The three-cover, natural SL₂(p), and nilpotent SL₂(5) cases
require genuine comparisons of their simple quotients with SL₄(2).

The intrinsic-model assembly applies this contract to the literal image
in the two-core quotient, after proving the SQTK and C-component premises
of universal A.3.6. The contract is not proved in this module.

Source: Aschbacher–Smith, A.3.6, pp.43–45, used in 13.6.23, p.933.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
universe u

/-- An outstanding comparison of the actual A.3.6 models. Its proof must
eliminate every nonsimple alternative, not assume an intrinsic marking. -/
def A36RankFourRecognition : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (B : Subgroup X),
    B.IsCComponent → Chapter1.Section02.A36Conclusion B →
      ∀ f : B →* SL(4, ZMod 2), Function.Surjective f → Function.Injective f

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
