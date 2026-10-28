module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.LocalAlternatives.OriginalBaumann
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.ClassificationConsequences

/-!
# The classified original Rudvalis Baumann countercase

The original Data supplies the actual Baumann MS pair and four noncentral
two-chief factors in the literal F.Li L 1. The natural-point exclusions
reduce the independent five-way classification to the natural or doubled
natural core on that same pair. No chief-count upper bound is assumed.

Task qt-d-14710-baumann retains the chief-factor comparison and Earlier14710;
qt-rank-two-ms93 owns the explicit classifier and qt-d-14775-source owns
final Rudvalis assembly. Structural1222 and the original alternating-five
module source retain their separate producers.

Source: Aschbacher--Smith C.1.37, p.143; 14.7.10, p.1045; 14.7.67(4), p.1070.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Chapter12.Section08 CriticalFusion.Source ChapterC.NaturalPointControl
open ResidualNormalizer.LocalControl.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Apply the point exclusions to the literal Rudvalis countercase. Both
surviving module alternatives and the four-factor series retain their
original subgroups; the chief-factor comparison remains to be proved. -/
theorem baumann_classified_countercase (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (binary : BinaryMSClassification KnownSimple.IsKnownSimple.{u})
    (escape : ¬ normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤
      normalizer (L : Set G)) :
    letI := seed_normal d.natural structural
    letI := seed_elementary d.natural
    ∃ a : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
      a.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      Nonempty (ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple a.LJ a.BJ) ∧
      (∃ e : (a.LJ ⧸ pCore 2 a.LJ) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        HasSectionModel a.LJ (msQ a.LJ a.BJ) ⊥ (linearThreeActor e)
          (Representation.specialLinearNatural (k := ZMod 2) 3) ∨
        HasSectionModel a.LJ (msQ a.LJ a.BJ) ⊥ (linearThreeActor e)
          ((Representation.specialLinearNatural (k := ZMod 2) 3).prod
            (Representation.specialLinearNatural (k := ZMod 2) 3))) ∧
      ∃ s : NoncentralChiefRefinement.ChiefSeries (F.Li L 1),
        s.head = ⊥ ∧ s.last = ⊤ ∧ 4 ≤ s.noncentralTwoCount := by
  let := seed_normal d.natural structural
  let := seed_elementary d.natural
  obtain ⟨a,ha,⟨h⟩,hs⟩ := baumann_ms_countercase d structural modules escape
  exact ⟨a,ha,⟨h⟩,natural_or_double_of_classification binary a h,hs⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
