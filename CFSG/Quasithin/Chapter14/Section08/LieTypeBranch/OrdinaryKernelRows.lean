module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalLinearThree
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySixFullSpan

/-!
# The remaining plus-kernel row at the maximal ordinary counterexample

The maximal Theorem D counterexample supplies Hypothesis12.2.1. Its
nonabelian full span and plane noncentrality supply F.9, the abelian seed
span and seed-core noncentrality. The source PSL₃(2) kernel contradiction
therefore applies with its centralization and local-escape premises proved.
Together with the earlier five-model list and the cubic exclusion, only
the A₅ kernel actor remains.

The original plane noncentrality, Baumann normalizer bound and
Source1332OneTwo are retained for their earlier-source producers. The
remaining A₅ module mark is not inferred from a group order.
Source: Aschbacher–Smith 13.7.4(1), printed pp.937–938.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion
open Chapter13.Section07
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The actual ordinary counterexample has no PSL₃(2) component in its plus kernel. -/
theorem original_six_plus_kernel_no_linearThree
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup G₁) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map G₁.subtype ≤ PlusAction.kernel
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁))
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (hl : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 2) : False := by
  obtain ⟨h,hU,hne⟩ := original_six_full_span_inputs_of_plane_noncentral d hmax eL hV hm
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [←d.first_normalizer]
  exact PlusAction.Original.source_primitive_linearThree_false_of_source d
    (hypothesis1221_of_maximal_natural_six d hmax eL) h hU eL hne hm'
    J hJ hs hJC hB hl

/-- A nonfaithful plus kernel at the actual maximal source must contain the
remaining A₅ actor, on the unchanged component and quotient maps. -/
theorem original_six_plus_kernel_alternatingFive_branch
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) ≠ G₁.pCoreIn 2)
    (hB : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁
    ∃ J : Subgroup G₁, let K := J.map G₁.subtype
      K ≤ PlusAction.kernel F ∧ IsPPerfect 2 K ∧ K ≠ ⊥ ∧ ¬ F.L₁ ≤ K ∧
      K ⊓ centralizer (PlusAction.fixedLayer F : Set G) = K.pCoreIn 2 ∧
      J.IsCComponent ∧ IsSimpleGroup (J ⧸ pCore 2 J) ∧
      J.Normal ∧ G₁ ≤ normalizer (K : Set G) ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨h,hU,hne⟩ := original_six_full_span_inputs_of_plane_noncentral d hmax eL hV hm
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [←d.first_normalizer]
  exact PlusAction.Original.source_ordinary_kernel_alternatingFive_branch d
    (hypothesis1221_of_maximal_natural_six d hmax eL) h hU eL hne hm' hV hk hB h1332

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
