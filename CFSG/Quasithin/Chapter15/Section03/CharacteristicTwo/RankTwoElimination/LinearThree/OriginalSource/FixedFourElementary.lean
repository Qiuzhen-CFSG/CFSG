module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FixedFourRadical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalCenterElementary
public import Theory.ElementaryAbelian.Injective

/-!
# The elementary premise at the original fixed-factor consumer

The large-distance MS calculation proves elementarity of the complete
commutator-core center. Include that center through the actual LS subgroup;
the component commutator comparison identifies its image with the original
core center. Its component-fixed subgroup is therefore elementary too.
The original radical-action theorem now needs only the still-unproved
order-four assertion, in addition to the preceding path facts.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5)(iv), printed pp.895--900;
Aschbacher--Smith 15.3.23, printed pp.1128--1129.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- Elementarity on the literal original fixed factor, with the same LS
input and characteristic replacement used by the large-distance branch. -/
theorem coreFixed_elementary_of_MS93 (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry) :
    IsElementaryAbelian 2 (coreFixed L) := by
  let := t.original_core_center_elementary common earlier
  have hsource : IsElementaryAbelian 2 (sourceCenter (L.subgroupOf (L ⊔ d.S))) :=
    IsElementaryAbelian.map (BinaryMS.commutatorCore (L.subgroupOf (L ⊔ d.S))).subtype
  let := hsource
  have hambient : IsElementaryAbelian 2 (coreCenter L) := by
    rw [← sourceCenter_map_subtype (show L ≤ L ⊔ d.S from le_sup_left) b.component]
    exact IsElementaryAbelian.map (L ⊔ d.S).subtype
  let := hambient
  have hle : coreFixed L ≤ coreCenter L := by
    rintro x ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext (hc y (((commutatorCore_le L).trans (L.pCoreIn_le 2)) y.property))
  exact IsElementaryAbelian.of_injective (inclusion hle) (inclusion_injective hle)

/-- The genuine MS path data discharge the elementary structure premise
at the original R-action consumer. Only order four remains to be collected. -/
theorem radical_centralizes_coreFixed_of_MS93 (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (h : ResidualSourceData d L e) (hg : ResidualGeometry d L)
    (b : BinaryMS.Input κ (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (hcard : Nat.card (coreFixed L) = 4) :
    d.R ≤ centralizer (coreFixed L : Set G) := by
  let := coreFixed_elementary_of_MS93 d L b t common earlier
  exact radical_centralizes_coreFixed d L e h hg hcard

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
