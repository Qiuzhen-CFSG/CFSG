module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Original
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Models

/-!
# Earlier source inputs for the field-component exclusions

This boundary fixes the original local A₆ action, its common Sylow flag,
the genuine F.9 applicability and the earlier local source statements.
The component normality, generated-overgroup reduction and concrete model
catalogue are the inputs from 13.8.16–17. All groups and quotient maps are
the literal ones used by the later field and small-cover arguments.

No field exclusion, small-cover exclusion, L₁-containment, H=KT, or module
generation conclusion is included. The parent field task owns their assembly;
the original section owner supplies the preceding source inputs.
Source: Aschbacher–Smith, §13.8 through 13.8.17, printed pp.946–953.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
open TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry LinearThree.Geometry.ExternalComponentAction
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

/-- Inputs to 13.8.19–21, before any of their conclusions. The catalogue
uses K/O₂(K); H* always means the distinct quotient H/O₂(H). -/
structure SourceContext (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ H K : Subgroup G) where
  localSetup : LocalSetup T L V V₁ V₂ V₃ M G₁
  maximal : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L
  f9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis
  centralizer : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G)
  noncentral_core : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥
  earlier1339 : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁
  component : RankReduction.SourceSetup KnownSimple.IsKnownSimple H K (one L T V₁) M G₁ T
  catalogue : Components.Models.ComponentModel (K ⧸ pCore 2 K)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
