module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBaumannSource
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryNonabelianExclusionAt
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Complete
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryCriticalGeometry

/-!
# Ordinary abelian full span and critical geometry from local inputs

The existing native Baumann theorem controls the literal point residual in
the contrary nonabelian branch. Apply the local plus-kernel and component
exclusions to prove abelianness of the full span. Together with the original
F.9 construction this supplies the odd critical path and reoriented geometry.
Only the original plane and local 13.3.2 inputs remain; their producers are
qt-d-13314-ordinary-blocks and qt-d-1332-source, with final discharge in
qt-d-1378-source and qt-d-1381-source.
Source: Aschbacher–Smith 13.7.8 and 13.8.2–8, printed pp.940–949.
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

/-- The ordinary plus kernel is the two-core, without a separate Baumann
normalizer hypothesis. -/
theorem original_six_plus_kernel_eq_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L) :
    PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁) = G₁.pCoreIn 2 :=
  original_six_plus_kernel_eq_of_source_at d hmax eL hV hm
    (original_six_baumann_normalizer_le d hmax eL hV hm) h1332 modules

/-- The ordinary nonabelian full-span branch is excluded with Baumann control
supplied on the original point residual. -/
theorem original_six_nonabelian_false_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hV : ¬ IsMulCommutative (Chapter13.Section08.Source.VH G₁ V))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L) :
    False :=
  original_six_nonabelian_false_of_source_at d hmax eL hV hm
    (original_six_baumann_normalizer_le d hmax eL hV hm) h1332 modules

/-- The original full span is abelian from the earlier plane and component
inputs; there is no residual Baumann premise. -/
theorem original_six_full_span_abelian_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L) :
    IsMulCommutative (conjugateSpanBy V G₁) := by
  by_contra hV
  exact original_six_nonabelian_false_at d hmax eL hV hm h1332 modules

/-- The actual Section 13.8 critical pair, with its abelian full span,
F.9 applicability and Baumann control derived internally. -/
theorem original_six_critical_geometry_at
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (hH : H ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M) :
    ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) H V,
      Odd c.path.length ∧
        Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c V₃ V₁ ∧
        ¬ ⁅c.Ugamma V₃,V⁆ ≤ c.Aone V₁ :=
  d.exists_earlierGeometry (original_six_full_span_abelian_at d hmax eL hm h1332 modules)
    (original_six_f9_of_source d hmax eL hm hH)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
