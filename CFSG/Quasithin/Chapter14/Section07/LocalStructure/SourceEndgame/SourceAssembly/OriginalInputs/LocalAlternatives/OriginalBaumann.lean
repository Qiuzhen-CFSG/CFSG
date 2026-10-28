module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.LocalAlternatives
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.ClassificationInput
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple

/-!
# The original Baumann countercase in the Rudvalis application

Apply the natural-point MS reduction to the literal Data used by the Rudvalis
source assembly. Known-simple Theorems A and C discharge uniqueness. If the
required Baumann normalizer containment fails, the resulting binary MS input
uses exactly the original R₁. Independently, the original module source and
the constructed upper marking give a complete chief series of the same L₁
with at least four noncentral two-factors.

Thus the remaining classification application must exclude this precise MS
countercase. No chief-factor bound or MS alternative is assumed or asserted.
Task qt-d-14710-baumann retains this deduction and Earlier14710; the independent
classifier is qt-rank-two-ms93, and final 14.7.75 assembly is qt-d-14775-source.

Source: Aschbacher--Smith 14.7.10 and the application in 14.7.67(4), printed
pp.1045 and 1070; C.1.37, printed pp.141--143.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
open Subgroup Chapter12.Section08 CriticalFusion.Source
open ChapterC.NaturalPointControl
open ResidualNormalizer.LocalControl.OriginalSource
open CriticalFusion.Source.Rechoice.Goldschmidt
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem knownSimple_uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
  intro X _ _ hX S B hB
  exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hB

/-- The literal Rudvalis datum supplies an MS input if Baumann control fails.
Only the original earlier structural theorem remains explicit. -/
theorem baumann_msInput_of_escape (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : ¬ normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤
      normalizer (L : Set G)) :
    letI := seed_normal d.natural structural
    letI := seed_elementary d.natural
    ∃ a : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
      a.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      Nonempty (ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple a.LJ a.BJ) :=
  msInput_of_normalizer_escape d.natural structural knownSimple_uniqueness F escape

/-- The countercase needed by Rudvalis recognition has both the genuine MS
input and four chief factors in the literal L₁. The earlier module theorem
and coordinated upper marking construct the four factors. -/
theorem baumann_ms_countercase (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (escape : ¬ normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤
      normalizer (L : Set G)) :
    letI := seed_normal d.natural structural
    letI := seed_elementary d.natural
    ∃ a : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
      a.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      Nonempty (ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple a.LJ a.BJ) ∧
      ∃ s : NoncentralChiefRefinement.ChiefSeries (F.Li L 1),
        s.head = ⊥ ∧ s.last = ⊤ ∧ 4 ≤ s.noncentralTwoCount := by
  let := seed_normal d.natural structural
  let := seed_elementary d.natural
  obtain ⟨a, ha, hMS⟩ := baumann_msInput_of_escape d structural escape
  refine ⟨a, ha, hMS, ?_⟩
  let d' := LeftChiefFactors.BorelRefinements.upperRemark d structural
  have hcomm := d'.U_core_commutator_eq_point_of_source1332 modules structural
    knownSimple_uniqueness
  exact d'.exists_residual_four_chief_factors structural knownSimple_uniqueness
    (LeftChiefFactors.BorelRefinements.upperRemark_upperMarking d structural) hcomm

/-- The same countercase satisfies the exact existing C.1.34 classifier API;
the quotient equivalence is supplied by the constructed binary MS input. -/
theorem baumann_smallMS_countercase (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (escape : ¬ normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤
      normalizer (L : Set G)) :
    letI := seed_normal d.natural structural
    letI := seed_elementary d.natural
    ∃ a : NaturalAction (V.subgroupOf (L ⊔ (T : Subgroup G))),
      a.R = (F.Ri L 1).subgroupOf (L ⊔ (T : Subgroup G)) ∧
      Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.SmallMSPair
        KnownSimple.IsKnownSimple a.LJ a.BJ ∧
      Nonempty ((a.LJ ⧸ pCore 2 a.LJ) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      ∃ s : NoncentralChiefRefinement.ChiefSeries (F.Li L 1),
        s.head = ⊥ ∧ s.last = ⊤ ∧ 4 ≤ s.noncentralTwoCount := by
  let := seed_normal d.natural structural
  let := seed_elementary d.natural
  obtain ⟨a, ha, ⟨hMS⟩, hs⟩ := baumann_ms_countercase d structural modules escape
  exact ⟨a, ha, smallMSPair_of_input hMS, ⟨hMS.quotientEquiv⟩, hs⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FullSource
