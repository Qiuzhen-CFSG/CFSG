module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Complete
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryCriticalGeometry

/-!
# The ordinary critical geometry with Baumann control discharged

In the nonabelian full-span branch the original maximal natural-six choice
supplies F.9 and the abelian seed span. The complete native symplectic argument
therefore bounds the normalizer of the actual Baumann subgroup. Identifying
the two definitions of the point residual applies this bound to the existing
plus-kernel and nonabelian-exclusion theorems on their literal source groups.

Consequently the original full span is abelian, and its Section 13.8 critical
pair needs only the earlier plane noncentrality, 13.3.2 component and module
classifications, and the choice of a member of Hz. Baumann control is no longer
an independent premise in these source applications.

Source: Aschbacher--Smith 13.7.4(1), 13.7.8, 13.7.15--21 and 13.8.2--8,
printed pp.937--949, using the original MS93 symplectic argument.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion Chapter13.Section07
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The actual source Baumann bound, with both F.9 and the native symplectic
core-identification input discharged. -/
theorem original_six_baumann_normalizer_le
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥) :
    normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M := by
  obtain ⟨h,hU,_⟩ := original_six_full_span_inputs_of_plane_noncentral d hmax eL hV hm
  have hres : (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ =
      sourceOne L T V₁ := by
    have hh := Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking.normalizer_residual_eq
      L V₁ (T : Subgroup G) T.isPGroup' d.normalizes_L
    change sourceOne L T V₁ =
      (pResidual 2 (L ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
        (L ⊓ normalizer (V₁ : Set G)).subtype at hh
    have hn : normalizer (V₁ : Set G) = centralizer (V₁ : Set G) :=
      h.normalizer_point_eq
    rw [hn] at hh
    exact hh.symm
  rw [hres]
  exact PlusAction.OriginalBaumann.source_baumann_normalizer_le d
    (hypothesis1221_of_maximal_natural_six d hmax eL) h hU hV

/-- The ordinary plus kernel is the two-core, without a separate Baumann
normalizer hypothesis. -/
theorem original_six_plus_kernel_eq
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) = G₁.pCoreIn 2 :=
  original_six_plus_kernel_eq_of_source d hmax eL hV hm
    (original_six_baumann_normalizer_le d hmax eL hV hm) h1332 modules

/-- The ordinary nonabelian full-span branch is excluded with Baumann control
supplied on the original point residual. -/
theorem original_six_nonabelian_false
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    False :=
  original_six_nonabelian_false_of_source d hmax eL hV hm
    (original_six_baumann_normalizer_le d hmax eL hV hm) h1332 modules

/-- The original full span is abelian from the earlier plane and component
inputs; there is no residual Baumann premise. -/
theorem original_six_full_span_abelian
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    IsMulCommutative (conjugateSpanBy V G₁) := by
  by_contra hV
  exact original_six_nonabelian_false d hmax eL hV hm h1332 modules

/-- The actual Section 13.8 critical pair, with its abelian full span,
F.9 applicability and Baumann control derived internally. -/
theorem original_six_critical_geometry
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hH : H ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M) :
    ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) H V,
      Odd c.path.length ∧
        Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c V₃ V₁ ∧
        ¬ ⁅c.Ugamma V₃,V⁆ ≤ c.Aone V₁ :=
  d.exists_earlierGeometry (original_six_full_span_abelian d hmax eL hm h1332 modules)
    (original_six_f9_of_source d hmax eL hm hH)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
