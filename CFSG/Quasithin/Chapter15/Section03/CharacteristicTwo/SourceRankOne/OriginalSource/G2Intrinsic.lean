module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.G2Marking

/-!
# The original G₂ contradiction from the whole natural core

The original star marking already identifies the intrinsic two-core quotient.
Consequently a natural model of the whole short-group core suffices: no ambient
block classification or MS alternatives are needed. The original V₂ injects
into the central quotient, and its parabolic has order 96. The proved binary
plane geometry gives the required simultaneous coordinates, then the whole-core
commutator and cocycle calculations give the contradiction.

Whole-core shortness and naturality remain explicit. A natural constituent
inside the center does not imply either assertion.
Source: Aschbacher–Smith 15.3.31 and C.1.30–32, printed pp.1132,135–136.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.CentralCover
open CentralCover.BlockModels MarkedModelAssembly MarkedModelAssembly.G2Coordinates
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The actual original parabolic has order 96 in any marking of the intrinsic
G₂ quotient. Its original star-map equation supplies the comparison. -/
theorem source_g2_parabolic_card
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L G2.Actor
      Parabolics.g2DerivedParabolic)
    (e : (c.L ⧸ pCore 2 c.L) ≃* G2.Actor) :
    Nat.card (((d.M ⊓ c.L).subgroupOf c.L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)))) = 96 := by
  obtain ⟨q, hq⟩ := source_g2_quotient_marking s m
  let f := m.equiv.trans (q.symm.trans e)
  have ha : e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L)) =
      f.toMonoidHom.comp (componentMap d c) := by
    apply MonoidHom.ext
    intro l
    change e (QuotientGroup.mk' (pCore 2 c.L) l) =
      e (q.symm (m.equiv (componentMap d c l)))
    rw [← hq, q.symm_apply_apply]
  rw [ha, ← map_map, componentMap_parabolic_image, card_map_of_injective f.injective]
  have hc : Nat.card (Parabolics.g2DerivedParabolic m.node) = 96 := by
    rcases m with ⟨e, i, h⟩
    fin_cases i
    · change Nat.card ((Atlas.G2.LieParabolicSetup.parabolic₁ (F := ZMod 2)).subgroupOf _) = 96
      rw [Atlas.G2.LieParabolicSetup.parabolic₁_binary]
      exact card_derivedFirst
    · change Nat.card ((Atlas.G2.LieParabolicSetup.parabolic₂ (F := ZMod 2)).subgroupOf _) = 96
      exact card_derivedSecond
  rw [← m.intersection, card_map_of_injective m.equiv.injective] at hc
  exact hc

/-- Whole-core shortness and its natural quotient model suffice for the
original G₂ contradiction, without an MS classification or an ambient block. -/
theorem source_g2_false_of_natural_core
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (m : Parabolics.RankTwoParabolicMarking d I c.L G2.Actor
      Parabolics.g2DerivedParabolic)
    (hs : ChapterC.IsShort c.L)
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction G2.action)) : False := by
  let cm := centerModel hs G2.action model
  let W := quotientPlane cm d.V₂
  let P := ((d.M ⊓ c.L).subgroupOf c.L).map cm.actorMap
  have hi : Function.Injective (planeMap cm s.plane_le_coreCenter) :=
    planeMap_injective cm s.plane_le_coreCenter s.contains (s.line.plane_fixed_trivial d)
  have hW : Nat.card W = 4 :=
    (quotientPlane_card cm s.plane_le_coreCenter hi).trans (d.action.card_plane _)
  have hP : Nat.card P = 96 := source_g2_parabolic_card s m model.quotientIso
  have hPW : P ≤ BlockModels.planeStabilizer G2.action W := by
    apply quotientPlane_stabilized cm s.plane_le_coreCenter
    rw [s.component_parabolic]
    exact inf_le_right
  obtain ⟨f, e, he, _, hPe⟩ := G2PlaneGeometry.geometry W P hW hP hPW
  let model' := recoordinate model f e he
  have hmark : ((d.M ⊓ c.L).subgroupOf c.L).map
      (model'.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) =
        BlockModels.planeStabilizer G2.action G2.markedPlane := by
    rw [map_map] at hPe
    exact hPe
  exact ContainedCoreModels.g2_excluded s hs model' hmark

/-- Literal original15.3.31 consumer of the remaining whole-core G₂ input. -/
theorem source_lemma_15_3_31_g2_natural_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (m : Parabolics.RankTwoParabolicMarking d I c.L G2.Actor
      Parabolics.g2DerivedParabolic)
    (hs : ChapterC.IsShort c.L)
    (model : ChapterC.BlockModuleModel c.L (multiplicativeAction G2.action)) : False := by
  obtain ⟨s⟩ := source_smallData hG d hempty hM hu hmany hshadow hI hf c
  exact source_g2_false_of_natural_core s m hs model

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
