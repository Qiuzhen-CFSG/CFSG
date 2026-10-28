module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryPlusKernelFaithful
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryAlternatingKernelAt
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalAlternatingFiveCentralizationAt
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalAlternatingFiveCentralization
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryAlternatingKernel

/-!
# Faithfulness of the ordinary plus action from local earlier inputs

Apply the actual point-residual centralization theorem to each remaining A₅
kernel component. Its local chosen-constituent classification feeds the
ordinary row contradiction, proving that the literal plus kernel is O₂(G₁).
The original plane, Baumann and 13.3.2 inputs retain their source owners.
Source: Aschbacher–Smith 13.7.4(1), printed pp.937–938.
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

/-- The original plus action is faithful modulo the actual two-core, with all
primitive kernel branches discharged from their genuine earlier source inputs. -/
theorem original_six_plus_kernel_eq_of_source_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L) :
    PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) = G₁.pCoreIn 2 := by
  obtain ⟨h,hU,hne⟩ := original_six_full_span_inputs_of_plane_noncentral d hmax eL hV hm
  apply original_six_plus_kernel_eq_of_alternating_centralization_at d hmax eL hV hm hB h1332 modules
  intro J hJ hs hJC ha
  exact PlusAction.Original.source_primitive_alternatingFive_centralized_at d
    (hypothesis1221_of_maximal_natural_six d hmax eL) h hU eL hne
    J hJ hs hJC hB ha modules

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
