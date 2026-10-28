module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Selected

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.Fourth
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer

/-!
# The original PSL₃(2) component exclusion

The residual calculation proves first choice and S-normalization of L.
We apply C.1.34 in LS with its genuine Sylow subgroup S, where the central
omega bound eliminates case four. The derived moving plane eliminates case
five. The compatible natural layers in the remaining cases control the
conjugate of Q = [O₂(L),L], and local uniqueness gives the contradiction.

The original 15.3.11–12 hypotheses supply every parabolic and residual
premise. The earlier elementary span, Thompson commutator and radical
saturation are explicit pending their characteristic-two assembly; the full
C.1.34 implication remains a Chapter C dependency.

Source: Aschbacher–Smith, 15.3.23, printed pp.1128–1129.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open ComponentIntersection OutsideStructure
open CoreActions Extension.SourceCases
open ChapterA.Section05To06 RankTwo
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_outside_stabilizer (d : LocalData G)
    (hi : (d.S.subgroupOf (d.T : Subgroup G)).index = 2) :
    ∃ t : G, t ∈ (d.T : Subgroup G) ∧ t ∉ d.S := by
  by_contra! h
  have ht : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := by
    apply top_unique
    intro t _
    exact h t t.property
  rw [ht, index_top] at hi
  omega

/-- The original residual and Sylow-three actions turn actual core and
component centralization into the final conjugate-core contradiction. -/
theorem contradiction_of_residual_centralization (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL}
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (hi : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hunique : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ (d.T : Subgroup G)) d.M)
    (hQ : YC d c.L ≤ centralizer (commutatorCore c.L : Set G))
    (hL : YC d c.L ≤ centralizer (c.L : Set G)) : False := by
  obtain ⟨M, g, hstd, hM⟩ := h.parabolic
  let P : Sylow 3 d.Y := Classical.choice inferInstance
  have hCP := NaturalActions.SylowAction.sylow_centralizer_of_parabolic d c e
    hg.component_normalized (le_sup_right.trans hg.component_residual_normalized)
    hg.generation hL M hstd g hM P
  have hTY : (d.T : Subgroup G) ≤ normalizer (d.Y : Set G) :=
    d.sylow_le.trans (OutsideStructure.LocalBranches.m_normalizes_y d)
  have hquot : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y) := by
    apply IsPGroup.of_card (n := 2)
    rw [← hg.first_choice]
    exact h.quotient_card
  obtain ⟨t₀, ht₀, ht₀S⟩ := exists_outside_stabilizer d hi
  obtain ⟨t, ht, htS, he, _, hbound⟩ := exists_conjugate_core_le_of_actions d c
    hi h.core_le h.radical hg.component_normalized hg.first_choice.symm hg.generation
    hTY hquot hQ P hCP t₀ ht₀ ht₀S (hg.exchange t₀ ht₀ ht₀S)
  exact contradiction_of_conjugate_core_control d c hi h.radical h.core_le hC
    hg.component_normalized hg.generation t ht htS he (Or.inr hbound) hunique

/-- The one- and two-natural-layer alternatives give the required conjugate
core containment through the actual residual and Sylow-three actions. -/
theorem contradiction_of_natural_layer (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [IsElementaryAbelian 2 (d.componentSpan c.L)]
    {e e' : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL}
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (hi : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hunique : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ (d.T : Subgroup G)) d.M)
    {a : ℕ} (ha : a = 1 ∨ a = 2)
    (m : LayerModel c.L (commutatorCore c.L) ⊥ e' (NaturalCopies (ZMod 2) a)) :
    False := by
  have hUQ : movingPlane d c.L ≤ commutatorCore c.L :=
    (movingPlane_le_coreCenter d c hg.component_normalized h.core_le h.radical).trans
      (map_subtype_le _)
  obtain ⟨hQ, hL⟩ := NaturalActions.YC_centralizes_of_order_four d c ha m
    hg.plane_card hUQ hg.plane_centralized
  exact contradiction_of_residual_centralization d c h hg hi hC hunique hQ hL

/-- The natural-center/dual-quotient alternative gives centralization of L
by the exchanged core, using the derived moving-plane normalizer. -/
theorem contradiction_of_three_layers (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    {e e' : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL}
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (hE : IsEvenCharacteristicAt d.T) (hnc : ⁅d.V, YL d c.L⁆ ≠ ⊥)
    (hi : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hunique : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ (d.T : Subgroup G)) d.M)
    (m : LayerModel c.L (coreCenter c.L) ⊥ e' (NaturalCopies (ZMod 2) 1))
    (n : LayerModel c.L (commutatorCore c.L) (coreCenter c.L) e'
      (DualCopies (ZMod 2) 2)) : False := by
  have hUZ := movingPlane_le_coreCenter d c hg.component_normalized h.core_le h.radical
  have hpar := componentParabolic_eq_planeNormalizer_of_source d hI c e h hE hnc
  obtain ⟨t, ht, htS⟩ := exists_outside_stabilizer d hi
  have he := hg.exchange t ht htS
  have hbound := ThreeLayer.conjugate_core_centralizes d c m n hi h.core_le h.radical
    (le_sup_right.trans hg.component_residual_normalized) hg.plane_card hUZ
    hg.plane_centralized hpar t ht he
  exact contradiction_of_conjugate_core_control d c hi h.radical h.core_le hC
    hg.component_normalized hg.generation t ht htS he (Or.inl hbound) hunique

/-- Source 15.3.23 for the original characteristic-two rank-two branch.
All local residual, parabolic, factorization and conjugate-core premises are
constructed. The binary C.1.34 implication at this literal LS input and the three
preceding C.2.7/15.3.16 outputs are the explicit earlier-source dependencies. -/
theorem contradiction_of_original_of_binary_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hne : d.Mc ≠ d.M)
    (hBaum : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (classification : ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)) →
      ∀ P : Sylow 2 (c.L ⊔ d.S : Subgroup G),
        d.S.subgroupOf (c.L ⊔ d.S) ≤ (P : Subgroup (c.L ⊔ d.S : Subgroup G)) →
        ∃ e' : ((c.L.subgroupOf (c.L ⊔ d.S)) ⧸
          pCore 2 (c.L.subgroupOf (c.L ⊔ d.S))) ≃* Matrix.PSL3Two.SL,
          Alternatives (ZMod 2) 1 (c.L.subgroupOf (c.L ⊔ d.S))
            (d.S.subgroupOf (c.L ⊔ d.S)) P e')
    (hrank : primeRank 3 d.Yplus = 2)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (helem : IsElementaryAbelian 2 (d.componentSpan c.L))
    (hJR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hsat : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R) : False := by
  let := helem
  obtain ⟨hnc, h, hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne
    hBaum hI c hrank e helem hJR hsat
  have h11 := source_lemma_15_3_11 hG d hempty hM hu hmany hne hBaum I hI
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  have hE := hG.evenCharacteristic d.T
  have hC : centralizer (d.V : Set G) ≤ d.M := by
    exact (Subgroup.centralizer_le_normalizer _).trans
      (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).ge
  have hunique := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne).2.2.2.2.1
  have hchar := h11.characteristic_exclusion c.L (component_le c) (by
    simpa only [YL, ComponentIntersection.intersectionResidual, hg.first_choice] using hnc)
    c.outside
  have hc := Fourth.component_in_join d c (le_sup_right.trans hI.1.2)
  obtain ⟨P, hP, e', hcases, _⟩ := Fourth.source_cases_of_sylow_classification d c classification
    (outside_sqtk hG d hI) hf h11.sylow hg.component_normalized hchar e hi
    (d.action.card_centralInvolutions d.T d.sylow_le)
    (d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1)
  rcases hcases with hs | hfive
  · cases hs with
    | one hb hm =>
      obtain ⟨m⟩ := hm
      have m' := ambientLayer (show c.L ≤ c.L ⊔ d.S from le_sup_left) m
      rw [sourceQ_map_subtype le_sup_left hc, Subgroup.map_bot] at m'
      exact contradiction_of_natural_layer d c h hg hi hC hunique (Or.inl rfl) m'
    | two hm hr =>
      obtain ⟨m⟩ := hm
      have m' := ambientLayer (show c.L ≤ c.L ⊔ d.S from le_sup_left) m
      rw [sourceQ_map_subtype le_sup_left hc, Subgroup.map_bot] at m'
      exact contradiction_of_natural_layer d c h hg hi hC hunique (Or.inr rfl) m'
    | three hn hm hr =>
      obtain ⟨n⟩ := hn
      obtain ⟨m⟩ := hm
      have n' := ambientLayer (show c.L ≤ c.L ⊔ d.S from le_sup_left) n
      have m' := ambientLayer (show c.L ≤ c.L ⊔ d.S from le_sup_left) m
      rw [sourceCenter_map_subtype le_sup_left hc, Subgroup.map_bot] at n'
      rw [sourceQ_map_subtype le_sup_left hc, sourceCenter_map_subtype le_sup_left hc] at m'
      exact contradiction_of_three_layers d hI c h hg hE hnc hi hC hunique n' m'
  · exact fifthCase_impossible_in_local_group d c hg.component_normalized h.core_le
      h.radical (c.L ⊔ d.S) le_sup_left hc P hP.le (d.S.subgroupOf (c.L ⊔ d.S))
      e' h.image hg.factors hfive

/-- The universal C.1.34 source implication specializes to the precise binary
classification contract used by `contradiction_of_original_of_binary_source`. -/
theorem contradiction_of_original
    (classification : UniversalClassification.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hne : d.Mc ≠ d.M)
    (hBaum : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hrank : primeRank 3 d.Yplus = 2)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (helem : IsElementaryAbelian 2 (d.componentSpan c.L))
    (hJR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hsat : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R) : False := by
  exact contradiction_of_original_of_binary_source hG d hempty hM hu hmany hne
    hBaum hI hf c (Fourth.binary_classification_of_universal classification)
    hrank e helem hJR hsat

/-- The selected local data supply both the distinct-local and Baumann controls;
only the original 15.3.13 assumptions and preceding source inputs remain. -/
theorem contradiction_from_selection_of_binary_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (classification : ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)) →
      ∀ P : Sylow 2 (c.L ⊔ d.S : Subgroup G),
        d.S.subgroupOf (c.L ⊔ d.S) ≤ (P : Subgroup (c.L ⊔ d.S : Subgroup G)) →
        ∃ e' : ((c.L.subgroupOf (c.L ⊔ d.S)) ⧸
          pCore 2 (c.L.subgroupOf (c.L ⊔ d.S))) ≃* Matrix.PSL3Two.SL,
          Alternatives (ZMod 2) 1 (c.L.subgroupOf (c.L ⊔ d.S))
            (d.S.subgroupOf (c.L ⊔ d.S)) P e')
    (hrank : primeRank 3 d.Yplus = 2)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (helem : IsElementaryAbelian 2 (d.componentSpan c.L))
    (hJR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hsat : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R) : False := by
  obtain ⟨hne, hBaum, _⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  exact contradiction_of_original_of_binary_source hG d hempty hM hu hmany hne hBaum
    hI hf c classification hrank e helem hJR hsat

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
