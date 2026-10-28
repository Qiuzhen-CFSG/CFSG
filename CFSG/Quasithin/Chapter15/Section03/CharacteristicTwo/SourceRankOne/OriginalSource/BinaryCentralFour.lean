module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinaryAbelian
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.CentralElimination
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalCentralFour

/-!
# Consuming the transported four-group at the original source pair

The literal distance-eight factor is included from the characteristic
replacement into the original outside group I. Its elementary structure and
order are supplied by the preceding source inputs and (4.5.1). If the original
two-core fixes this factor, the component and two-core generation theorem
makes it central in I. The actual Sylow subgroup, MS3 and order-four central
omega from SourceData then give the source31 contradiction.

The original-two-core action is an explicit remaining transport premise.
Centrality in the replacement alone does not discharge it. This consumer
therefore does not assert an unconditional classification of the original pair.

Source: Aschbacher--Smith C.1.34(4), printed pp.136--137, and 15.3.31,
printed p.1132; Meierfrankenfeld--Stellmacher (1993), (4.4), (4.5.1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration EightGeometry.NaturalModule.Recognition
  SmallExtension SmallExtension.CentralCover SmallExtension.CentralCover.LinearThree ChapterC
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I}

/-- The actual source hypotheses exclude the transported factor once the original
two-core is proved to fix it. -/
theorem source_binary_distance_eight_false_of_fixedFactor_centralizes_core
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (t : BinaryMS.MS93.InputSetup (source_binaryMSInput s e))
    (common : BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : BinaryMS.MS93.DistanceEight.CoreFactors.Earlier
      t.reduction.radical t.geometry)
    (hc : t.reducedCentralFour ≤ centralizer (pCore 2 I : Set I)) : False := by
  let C := t.reducedCentralFour.map I.subtype
  let := t.reducedCentralFour_elementary common earlier
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map I.subtype
  have hcard : Nat.card C = 4 := by
    rw [card_map_of_injective I.subtype_injective]
    exact t.reducedCentralFour_card common earlier
  have hcentral : C ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (c.L ⊔ d.S) := by
    rw [← s.generated]
    exact map_mono (t.reducedCentralFour_le_center_of_centralizes_core earlier hc)
  have hS : Chapter1.IsSylowIn 2 d.S (c.L ⊔ d.S) :=
    s.generated ▸ ⟨s.sylow, s.sylow_eq⟩
  have hms : MSNoCharacteristicNormal c.L d.S := by
    intro A hA hn
    by_contra hne
    exact s.characteristic A hA hne (s.generated ▸ hn)
  have hbound : Nat.card (omegaCenterIn d.S) ≤ 4 := by
    change Nat.card (centralOmegaIn d.S) ≤ 4
    rw [← s.omega.1, s.omega.2]
  exact MarkedMS.no_central_four hS hms hbound hcard hcentral

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
