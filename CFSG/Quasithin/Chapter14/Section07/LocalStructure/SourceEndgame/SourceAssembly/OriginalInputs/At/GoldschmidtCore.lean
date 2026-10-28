module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.NormalizerProjection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.ThompsonNormality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.FullSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.GoldschmidtSize.Complete

/-!
# The original Goldschmidt core and rank-three contradiction

The three literal Borel intervals contribute five noncentral binary chief
factors in the left vertex, hence order at least 1024. The proved Gol80
bound excludes a trivial core. Relative Thompson normality at G,T and
the actual normalizer projection give Thompson escape. Adequate B.5 and
full F.6 recognition now mark both parabolics of the original quotient;
H.5.5 makes its point-generated span have rank three.
Only the earlier structural and faithful-family source inputs remain.
Source: Aschbacher–Smith 14.7.70, pp.1074–1075.
-/
public noncomputable section
open Subgroup NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion
open Chapter12.Section08 QuotientComparison
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)
  (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)

include structural

/-- Count directly in the actual left vertex, retaining the literal source sections. -/
theorem left_order_ge_1024_at (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) : 1024 ≤ Nat.card (left c) := by
  have hc := d.sectionCentralizer_from_flag
  obtain ⟨X,aX,mX,hs⟩ := CriticalIntersections.exists_sourceDuality d hc
  let := aX
  let := mX
  obtain ⟨duality⟩ := hs
  obtain ⟨s,hs0,hs1⟩ := exists_chiefSeries (⊥ : NormalNode (left c)) ⊤ bot_le
  have hn := LeftChiefFactors.leftChief_count d c
    (LeftChiefFactors.BorelRefinements.compatibleBorel_of_upperMarking_at d structural mark)
    hc duality hcomm s hs0 hs1
  calc
    1024 = (4 : ℕ)^5 := by norm_num
    _ ≤ 4^s.noncentralTwoCount := Nat.pow_le_pow_right (by decide) hn
    _ ≤ Nat.card (left c) := s.four_pow_noncentralTwoCount_le_card hs0 hs1

/-- Both original quotient actions give the actual Goldschmidt triple. -/
theorem triple_at (geometry : Geometry d c) : ChapterF.IsGoldschmidtTriple (left c) (right c) := by
  apply geometry.triple_of_left_quotient
  let e := subgroupOfEquivOfLe (show group F L ≤ I c from le_sup_left)
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (LeftChiefFactors.leftQuotientEquiv_at d structural)⟩

/-- The checked amalgam bound forces the nontrivial original core. -/
theorem coreFacts_at (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) :
    CoreFacts c ∧ pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) := by
  have ht := triple_at d c structural geometry
  have hn : pCore 2 (I c) ≠ ⊥ := by
    intro hz
    have hs := ht.card_le_384 hz
    have hl := left_order_ge_1024_at d c structural mark hcomm
    omega
  exact ⟨⟨ht,hn,VI_elementary d c hn,core_centralizes_VI d c⟩,geometry.core_identification⟩

/-- Thompson escape from the original core uses only the same G,T input. -/
theorem thompson_escape_at (geometry : Geometry d c) (core : CoreFacts c) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2 := by
  intro hJ
  have hJT : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hn := Chapter14.Section03.ThompsonSourceAt.thompson_normal d.natural F structural
    (hJ.trans (ThompsonWitness.core_le_R₁ c))
  have hLT : L ⊔ (T : Subgroup G) ≤
      normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hJT.trans le_sup_right)).mp hn
  have hu := (d.natural.maximal_unique_at structural).2
  have hNM := normalizer_le_of_unique_maximalTwoLocal
    (J := L ⊔ (T : Subgroup G))
    (fun N hN hLN => Set.mem_singleton_iff.mp (hu ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN,hLN⟩))
    (T.isPGroup'.to_le hJT) (ThompsonWitness.thompson_ne_bot d) hLT
  exact ThompsonWitness.ProjectionEscape.NormalizerStructureAt.normalizer_escape d geometry core
    ((Y_le_I c).trans ((I_normalizes_thompson_of_le_core c hJ).trans hNM))

/-- The original plus action now supplies its actual small subnormal witness. -/
theorem core_and_small_at
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (geometry : Geometry d c) (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) :
    CoreFacts c ∧ pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) ∧
      SmallSubnormal c := by
  obtain ⟨core,hcore⟩ := coreFacts_at d c structural geometry mark hcomm
  have alternative := ThompsonWitness.nontrivial_adequate_alternative d c geometry core b5
    (thompson_escape_at d c structural geometry core)
  exact ⟨core,hcore,ThompsonWitness.ComponentSelection.smallSubnormal_of_adequate
    d c geometry core faithful alternative⟩

/-- Full F.6 and H.5.5 on the literal bang and plus quotients give rank three. -/
theorem primeRank_VI_at
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (sourceF : FSource.SourceClassificationInput KnownSimple.IsKnownSimple.{u})
    (geometry : Geometry d c) (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) : primeRank 2 (VI c) = 3 := by
  obtain ⟨core,_,small⟩ := core_and_small_at d c structural faithful b5 geometry mark hcomm
  obtain ⟨recognition⟩ := FullSource.bangRecognition d c sourceF geometry core small
  obtain ⟨_,⟨parabolics⟩⟩ := core_and_marking_of_bangRecognition c core recognition
  exact PointModule.primeRank_VI d c core parabolics geometry
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion
