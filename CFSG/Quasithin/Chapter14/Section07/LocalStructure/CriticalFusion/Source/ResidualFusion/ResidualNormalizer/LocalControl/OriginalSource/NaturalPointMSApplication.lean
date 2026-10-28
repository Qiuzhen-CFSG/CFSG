module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.NaturalPointMS
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.LocalAlternatives.OriginalBaumann

/-!
# The original Baumann countercase without an MS classifier premise

The Rudvalis datum supplies the actual natural-point action, Baumann radical,
and MS pair. The natural-point source theorem constructs the natural or
doubled-natural commutator core on that same pair. Independently, the original
module source gives a complete chief series of the literal L₁ with at least
four noncentral two-factors.

The existing Baumann owner retains the chief-factor upper bound and 14.7.10
assembly. Structural 12.2.2 and the alternating-five module input keep their
original producers; the full classification endpoint is unchanged.

Source: Aschbacher--Smith C.1.37, p.143; 14.7.10, p.1045;
and 14.7.67(4), p.1070.
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
original subgroups. The natural-point implication discharges the MS classification;
the chief-factor comparison remains independent. -/
theorem baumann_classified_countercase_of_msInput (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
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
  exact ⟨a,ha,⟨h⟩,natural_or_double_of_msInput a h,hs⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
