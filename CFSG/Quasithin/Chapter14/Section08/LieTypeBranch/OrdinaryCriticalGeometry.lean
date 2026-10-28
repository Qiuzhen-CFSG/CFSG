module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryNonabelianExclusion
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EarlierGeometry

/-!
# From the ordinary source exclusion to the Section 13.8 critical geometry

The completed nonabelian full-span exclusion makes the original V-span in
G₁ abelian. The maximal ordinary A₆ choice supplies Hypothesis 12.2.1,
and the source plane noncentrality constructs F.9 for each original H in Hz.
The point-normalizer/centralizer equality and the two definitions of L₁ are
compared before applying F.9; the selected H, flag and ambient inclusions
remain unchanged.

These two conclusions feed the actual Section 13.8 critical-pair theorem.
It supplies the odd track, all earlier geometry and the nontrivial endpoint
commutator without separate abelian-closure, F.9 or geometric premises.
The genuine earlier plane noncentrality, Baumann normalizer bound and
13.3.2 component and module classifications remain explicit. Selection of
an original H in Hz remains with its earlier-source producer.

Source: Aschbacher–Smith, 13.5.7, 13.7.8 and 13.8.2–8, printed pp.917,
940–941 and 946–949, combined manuscript of 1 March 2004.
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

/-- The original full span is abelian once the genuine earlier ordinary
source inputs are supplied. -/
theorem original_six_full_span_abelian_of_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hBnormal : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u}) :
    IsMulCommutative (conjugateSpanBy V G₁) := by
  by_contra hV
  exact original_six_nonabelian_false_of_source d hmax eL hV hm hBnormal h1332 modules

/-- F.9 applies to every original member of Hz, with maximality and all
local hypotheses supplied on the literal source groups. -/
theorem original_six_f9_of_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M) :
    (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis := by
  let D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have heq : G₁ = D.Gz := d.first_normalizer.trans
    (le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.line_card)
      (Subgroup.centralizer_le_normalizer _))
  have d' : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz := heq ▸ d
  have hl : D.L₁ = sourceOne L T V₁ := by
    have hh := Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking.normalizer_residual_eq L V₁ (T : Subgroup G) T.isPGroup' d.normalizes_L
    change sourceOne L T V₁ =
      (pResidual 2 (L ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
        (L ⊓ normalizer (V₁ : Set G)).subtype at hh
    rw [← d.first_normalizer] at hh
    change (pResidual 2 (L ⊓ D.Gz : Subgroup G)).map (L ⊓ D.Gz).subtype = _
    rw [← heq]
    exact hh.symm
  have hH' : H ∈ Chapter13.Section08.Source.Hz D.L₁ T D.Gz M := by
    rw [hl, ← heq]
    exact hH
  apply OrdinarySource.f9_of_plane_noncentral d' eL
    (hypothesis1221_of_maximal_natural_six d' hmax eL) hH'
  change ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥
  rwa [← d.first_normalizer]

/-- The actual Section 13.8 critical pair and its geometry, with the full
abelian span and F.9 input discharged by the ordinary source proofs. -/
theorem original_six_critical_geometry_of_source
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hBnormal : normalizer (ChapterB.baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hH : H ∈ Chapter13.Section08.Source.Hz (sourceOne L T V₁) T G₁ M) :
    ∃ c : Chapter13.Section08.CriticalGeometry.CriticalPair L (T : Subgroup G) H V,
      Odd c.path.length ∧
        Chapter13.Section08.CriticalGeometry.Reorientation.EarlierGeometry c V₃ V₁ ∧
        ¬ ⁅c.Ugamma V₃,V⁆ ≤ c.Aone V₁ := by
  exact d.exists_earlierGeometry (original_six_full_span_abelian_of_source d hmax eL hm hBnormal h1332 modules)
    (original_six_f9_of_source d hmax eL hm hH)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
