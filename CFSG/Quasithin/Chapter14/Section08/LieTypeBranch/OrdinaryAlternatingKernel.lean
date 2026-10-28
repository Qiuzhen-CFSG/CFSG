module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalAlternatingFiveSource
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryKernelRows

/-!
# The A5 constituent contradiction at the ordinary counterexample

The actual ordinary setup supplies the source F.9 hypothesis and its reduced
module. The genuine earlier 13.3.2 A5 constituent classification excludes every
centralized A5 component in the plus kernel. Together with the already excluded
PSL3 row, this proves plus-kernel faithfulness once the separate source
centralization conclusion is supplied. No central-quotient module mark is assumed.

Source: Aschbacher--Smith 13.3.2(3), 13.7.4(1), pp.885 and937--938.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion Chapter13.Section07
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The original ordinary counterexample excludes the centralized A5 kernel row
using the genuine source constituent classification. -/
theorem original_six_plus_kernel_no_centralized_alternatingFive
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup G₁) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map G₁.subtype ≤ PlusAction.kernel
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁))
    (hp : IsPPerfect 2 (J.map G₁.subtype))
    (hcomm : ⁅J.map G₁.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁⁆ ≤
      (J.map G₁.subtype).pCoreIn 2)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (ha : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    False := by
  obtain ⟨h,hU,hne⟩ := original_six_full_span_inputs_of_plane_noncentral d hmax eL hV hm
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [←d.first_normalizer]
  exact PlusAction.Original.source_primitive_alternatingFive_false_of_modules d
    (hypothesis1221_of_maximal_natural_six d hmax eL) h hU eL hne hm'
    J hJ hs hJC hp hcomm hB ha modules

/-- The remaining A5 source centralization is the only kernel-row input after
applying the genuine earlier component and constituent classifications. -/
theorem original_six_plus_kernel_eq_of_alternating_centralization
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hcentral : ∀ J : Subgroup G₁, J.IsCComponent → IsSimpleGroup (J ⧸ pCore 2 J) →
      J.map G₁.subtype ≤ PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) →
      Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) →
      ⁅J.map G₁.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁⁆ ≤
        (J.map G₁.subtype).pCoreIn 2) :
    PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) = G₁.pCoreIn 2 := by
  by_contra hk
  obtain ⟨J,hJC,hp,_,_,_,hJ,hs,_,_,ha⟩ :=
    original_six_plus_kernel_alternatingFive_branch d hmax eL hV hm hk hB h1332
  exact original_six_plus_kernel_no_centralized_alternatingFive d hmax eL hV hm J hJ hs
    hJC hp (hcentral J hJ hs hJC ha) hB ha modules

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
