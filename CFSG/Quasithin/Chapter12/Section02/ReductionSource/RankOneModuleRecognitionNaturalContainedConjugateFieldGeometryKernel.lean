module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryClosure

/-!
# The field residual's two-core on the Chapter 12 layer

The literal O²(N_L(U)) and N_L(U) have two-cores centralizing B, by
faithfulness on the field-fixed plane. Relative normality of the residual
in N_G(U), when supplied by the local-component argument, propagates this
to the full closure B_U. No ambient normality is imposed.

The remaining relative-normality premise belongs to the final owner
qt-d-1222-rankone-recognition-natural-contained. Source: Aschbacher–Smith,
6.1.14(5), printed p.671.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L U : Subgroup G} {n : ℕ}

/-- The two literal cores in the source both centralize the original B. -/
theorem source_field_fixedSpace_core_centralizes
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n)
    (hUne : U ≠ ⊥) (hn : 2 < n) :
    (L ⊓ normalizer (U : Set G)).pCoreIn 2 ≤ centralizer (commutatorLayer T L : Set G) ∧
      (fieldLocalResidual L U).pCoreIn 2 ≤ centralizer (commutatorLayer T L : Set G) :=
  field_fixedSpace_core_centralizes hnatural hfield hUne hn

/-- The source residual's core centralizes B_U once its relative normality
from the local-component argument is supplied. -/
theorem source_field_fixedSpace_core_centralizes_closure
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n)
    (hUne : U ≠ ⊥) (hn : 2 < n)
    (hN : ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal) :
    (fieldLocalResidual L U).pCoreIn 2 ≤
      centralizer (fieldModuleClosure (commutatorLayer T L) U : Set G) :=
  field_fixedSpace_core_centralizes_closure hnatural hfield hUne hn hN
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
