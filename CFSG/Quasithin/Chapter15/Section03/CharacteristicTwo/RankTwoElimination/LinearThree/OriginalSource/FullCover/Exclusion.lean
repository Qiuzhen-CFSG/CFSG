module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FullCover.Actions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.FullCoreCover.MarkedPair
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DoubleDualQuotient.Transport

/-!
The intrinsic nonabelian distance-four source constructs the full core cover
and exact doubled-dual central quotient under a common component marking.
Transport to the literal component in LS and the original residual action
calculation eliminate this branch of 15.3.23. All residual and parabolic
premises are obtained from the original source hypotheses.
Source: Aschbacher–Smith, 15.3.23, printed p.1129; MS93(4.6.12).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open ComponentIntersection OutsideStructure CoreActions Extension.SourceCases
open ChapterA.Section05To06 RankTwo ChapterC
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual binary MS distance-four source produces both weak-center layers
with the same marking and contradicts the original exchanged residuals. -/
theorem contradiction_of_nonabelian_distance_four_sylow_input
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    {κ : GroupClass.{u}}
    (b : BinaryMS.Input κ (c.L.subgroupOf (c.L ⊔ d.S))
      (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : BinaryMS.MS93.InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : t.geometry.b t.reduction.radical = 4)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL}
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (hE : IsEvenCharacteristicAt d.T) (hne : ⁅d.V,YL d c.L⁆ ≠ ⊥)
    (hi : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hunique : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ (d.T : Subgroup G)) d.M) : False := by
  obtain ⟨f,n,he⟩ := t.fullCore_cover_quotient_same_marking hc hb
  let eL : c.L.subgroupOf (c.L ⊔ d.S) ≃* c.L := subgroupOfEquivOfLe le_sup_left
  exact FullCover.contradiction d hI c (f.comap eL.symm) (n.comap eL.symm)
    (BinaryMS.NaturalCenterDoubleDualQuotient.same_marking_comap f n he eL.symm)
    h hg hE hne hi hC hunique

/-- The original source data exclude distance four for every setup of the
literal binary MS input at LS. Only the preceding elementary-span, Thompson
commutator and radical-saturation source outputs are retained. -/
theorem source_nonabelian_binary_distance_ne_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I)
    (hrank : primeRank 3 d.Yplus = 2)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (helem : IsElementaryAbelian 2 (d.componentSpan c.L))
    (hJR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hsat : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple (c.L.subgroupOf (c.L ⊔ d.S))
      (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : BinaryMS.MS93.InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S)))) :
    t.geometry.b t.reduction.radical ≠ 4 := by
  intro hb
  let := helem
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨hnc,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne
    hBaum hI c hrank e helem hJR hsat
  have hC : centralizer (d.V : Set G) ≤ d.M :=
    (Subgroup.centralizer_le_normalizer _).trans
      (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).ge
  have hunique := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne).2.2.2.2.1
  exact contradiction_of_nonabelian_distance_four_sylow_input d hI c b t hc hb h hg
    (hG.evenCharacteristic d.T) hnc
    (d.action.planeStabilizer_index_two d.T d.sylow_le 1) hC hunique
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
