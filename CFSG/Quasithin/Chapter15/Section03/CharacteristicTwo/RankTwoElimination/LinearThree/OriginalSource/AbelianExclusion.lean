module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.Exclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.AbelianQuotient

/-!
# The abelian core in the original PSL₃(2) exclusion

The proved binary MS quotient theorem suffices for the abelian branch of
15.3.23. Its fixed kernel has order at most two, whereas the moving plane
has order four. The resulting residual centralization feeds the original
conjugate-core contradiction without an additional classification premise.

Source: Aschbacher–Smith, 15.3.23, printed p.1129.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open ComponentIntersection OutsideStructure CoreActions Extension.SourceCases
open ChapterA.Section05To06 RankTwo
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal binary MS input and its abelian core produce the
centralization required by the original conjugate-core contradiction. -/
theorem contradiction_of_abelian_sylow_input (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    {κ : GroupClass.{u}}
    (b : ChapterC.BinaryMS.Input κ (c.L.subgroupOf (c.L ⊔ d.S))
      (d.S.subgroupOf (c.L ⊔ d.S)))
    (hc : IsMulCommutative (sourceQ (c.L.subgroupOf (c.L ⊔ d.S))))
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL}
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (hi : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hunique : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ (d.T : Subgroup G)) d.M) : False := by
  have hUQ : movingPlane d c.L ≤ commutatorCore c.L :=
    (movingPlane_le_coreCenter d c hg.component_normalized h.core_le h.radical).trans
      (map_subtype_le _)
  obtain ⟨hQ, hL⟩ := AbelianQuotient.YC_centralizes_of_binary_sylow_input c b hc
    (movingPlane d c.L) hg.plane_card hUQ hg.plane_centralized
  exact contradiction_of_residual_centralization d c h hg hi hC hunique hQ hL

/-- In the original rank-two branch, abelianness of the actual binary
commutator core is impossible. All binary MS premises are constructed. -/
theorem contradiction_from_selection_of_abelian_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (hrank : primeRank 3 d.Yplus = 2)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (helem : IsElementaryAbelian 2 (d.componentSpan c.L))
    (hJR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hsat : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (hc : IsMulCommutative (sourceQ (c.L.subgroupOf (c.L ⊔ d.S)))) : False := by
  let := helem
  obtain ⟨hne, hBaum, _⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨hnc, h, hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne
    hBaum hI c hrank e helem hJR hsat
  have h11 := source_lemma_15_3_11 hG d hempty hM hu hmany hne hBaum I hI
  have hchar := h11.characteristic_exclusion c.L (component_le c) (by
    simpa only [YL, ComponentIntersection.intersectionResidual, hg.first_choice] using hnc)
    c.outside
  let b := Fourth.sylowInput d c (outside_sqtk hG d hI) hf h11.sylow
    hg.component_normalized hchar e
  have hC : centralizer (d.V : Set G) ≤ d.M :=
    (Subgroup.centralizer_le_normalizer _).trans
      (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).ge
  have hunique := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne).2.2.2.2.1
  exact contradiction_of_abelian_sylow_input d c b hc h hg
    (d.action.planeStabilizer_index_two d.T d.sylow_le 1) hC hunique

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
