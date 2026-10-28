module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeLargeDistance
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction.SectionKernel

/-!
# The literal cubic-centralizer placement in original 15.3.23

The original hypotheses construct the residual product, compatible component
parabolic and first-choice geometry. Every Sylow three-subgroup P of Y has
C_S(P) contained in O₂(LS). Frattini adjustment supplies t in T minus S which
normalizes P, preserves C_S(P), and exchanges Y_L with Y_C.

These are source consequences independent of the binary MS classification.
The final consumer reduces the conjugate-core contradiction to the literal
bound Q ≤ O₂(Y_L) C_S(P). That decomposition is not inferred from mere
plane fixation or P-invariance. Its whole-core source argument remains
necessary in any application outside the proved natural-core cases.

Source: Aschbacher–Smith, 15.3.23, final paragraph, printed p.1129.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open CoreActions NaturalActions.SylowAction
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The source residual geometry places every literal cubic centralizer in
O₂(LS), independently of the action of Y_C on the commutator core. -/
theorem sylow_centralizer_le_core_of_residual_geometry (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL}
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (P : Sylow 3 d.Y) :
    d.S ⊓ centralizer (sylowThree d P : Set G) ≤ (c.L ⊔ d.S).pCoreIn 2 := by
  obtain ⟨M,g,hstd,hM⟩ := h.parabolic
  have hCP := sylow_centralizer_of_parabolic_section d c e hg.component_normalized
    (le_sup_right.trans hg.component_residual_normalized) hg.generation M hstd g hM P
  exact (le_inf inf_le_left hCP).trans
    (S_sectionCentralizer_le_core d c.L hg.component_normalized
      (h.core_le.trans (R_le_S d h.radical)))

/-- The original Frattini representative exchanges the residuals and
preserves the literal centralizer factor already placed in O₂(LS). -/
theorem exists_cubic_frattini_placement (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL}
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (hi : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (P : Sylow 3 d.Y) :
    ∃ t : G, t ∈ (d.T : Subgroup G) ∧ t ∉ d.S ∧
      (YL d c.L).conjBy t = YC d c.L ∧
      t ∈ normalizer (sylowThree d P : Set G) ∧
      t ∈ normalizer (d.S ⊓ centralizer (sylowThree d P : Set G) : Subgroup G) ∧
      d.S ⊓ centralizer (sylowThree d P : Set G) ≤ (c.L ⊔ d.S).pCoreIn 2 := by
  have houtside : ∃ t : G, t ∈ (d.T : Subgroup G) ∧ t ∉ d.S := by
    by_contra! hn
    have htop : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := by
      apply top_unique
      intro t _
      exact hn t t.property
    rw [htop, index_top] at hi
    omega
  obtain ⟨t₀,ht₀,ht₀S⟩ := houtside
  have hTY : (d.T : Subgroup G) ≤ normalizer (d.Y : Set G) :=
    d.sylow_le.trans (OutsideStructure.LocalBranches.m_normalizes_y d)
  have hquot : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y) := by
    apply IsPGroup.of_card (n := 2)
    rw [← hg.first_choice]
    exact h.quotient_card
  obtain ⟨t,ht,htS,he,htP⟩ := exists_exchange_normalizing_sylow d c.L
    hg.first_choice.symm hTY (le_sup_right.trans hg.component_residual_normalized)
    h.radical P hquot t₀ ht₀ ht₀S (hg.exchange t₀ ht₀ ht₀S)
  exact ⟨t,ht,htS,he,htP,normalizes_sylow_centralizer d P hi t ht htP,
    sylow_centralizer_le_core_of_residual_geometry d c h hg P⟩

/-- Only the genuine cubic decomposition of Q remains in the final
source paragraph; all Frattini and quotient-centralizer premises are proved. -/
theorem conjugate_core_le_of_cubic_decomposition (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL}
    (h : ResidualSourceData d c.L e) (hg : ResidualGeometry d c.L)
    (hi : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (P : Sylow 3 d.Y)
    (hQ : commutatorCore c.L ≤ (YL d c.L).pCoreIn 2 ⊔
      (d.S ⊓ centralizer (sylowThree d P : Set G))) :
    ∃ t : G, t ∈ (d.T : Subgroup G) ∧ t ∉ d.S ∧
      (YL d c.L).conjBy t = YC d c.L ∧
      t ∈ normalizer (sylowThree d P : Set G) ∧
      (commutatorCore c.L).conjBy t ≤ (c.L ⊔ d.S).pCoreIn 2 := by
  obtain ⟨t,ht,htS,he,htP,htC,hCP⟩ := exists_cubic_frattini_placement d c h hg hi P
  refine ⟨t,ht,htS,he,htP,?_⟩
  have hm := map_mono (f := (MulAut.conj t).toMonoidHom) hQ
  have hfixed := mem_normalizer_iff_map_conj_eq.mp htC
  change (d.S ⊓ centralizer (sylowThree d P : Set G)).map
    (MulAut.conj t).toMonoidHom = _ at hfixed
  rw [Subgroup.map_sup, hfixed] at hm
  change (commutatorCore c.L).conjBy t ≤ ((YL d c.L).pCoreIn 2).conjBy t ⊔ _ at hm
  rw [conjugate_YL_core d c.L t he] at hm
  have hCS : (YC d c.L).pCoreIn 2 ≤ d.S :=
    le_sup_right.trans (residual_cores_le_S d c.L h.normalizes_component
      (RankTwo.planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice) h.radical)
  have hCK : (YC d c.L).pCoreIn 2 ≤ Chapter4.sectionCentralizer c.L :=
    ((YC d c.L).pCoreIn_le 2).trans
      ((ComponentIntersection.centralizerResidual_le _ _).trans inf_le_right)
  exact hm.trans (sup_le ((le_inf hCS hCK).trans
    (S_sectionCentralizer_le_core d c.L hg.component_normalized
      (h.core_le.trans (R_le_S d h.radical)))) hCP)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource LinearThree.CoreActions
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
include hG hempty hM hu hmany hI htwo hf e

/-- Original 15.3.23 supplies the adjusted outside element and its literal
cubic centralizer in O₂(LS), with no MS or core-action premise. -/
theorem binary_three_cubic_frattini_placement (P : Sylow 3 d.Y) :
    ∃ t : G, t ∈ (d.T : Subgroup G) ∧ t ∉ d.S ∧
      (YL d c.L).conjBy t = YC d c.L ∧
      t ∈ normalizer (sylowThree d P : Set G) ∧
      t ∈ normalizer (d.S ⊓ centralizer (sylowThree d P : Set G) : Subgroup G) ∧
      d.S ⊓ centralizer (sylowThree d P : Set G) ≤ (c.L ⊔ d.S).pCoreIn 2 := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  exact exists_cubic_frattini_placement d c h hg
    (d.action.planeStabilizer_index_two d.T d.sylow_le 1) P

/-- The literal cubic decomposition feeds the existing actual conjugate-core
consumer. Every other hypothesis of the source's last paragraph is supplied
from the original characteristic-two rank-two setup. -/
theorem source_lemma_15_3_23_of_cubic_decomposition
    (hdecomp : ∃ P : Sylow 3 d.Y,
      commutatorCore c.L ≤ (YL d c.L).pCoreIn 2 ⊔
        (d.S ⊓ centralizer (sylowThree d P : Set G))) : False := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  let := hW
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨P,hQ⟩ := hdecomp
  have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
  obtain ⟨t,ht,htS,he,_,hbound⟩ :=
    conjugate_core_le_of_cubic_decomposition d c h hg hi P hQ
  have hC : centralizer (d.V : Set G) ≤ d.M :=
    (Subgroup.centralizer_le_normalizer _).trans
      (InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1).ge
  have hunique := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne).2.2.2.2.1
  exact contradiction_of_conjugate_core_control d c hi h.radical h.core_le hC
    hg.component_normalized hg.generation t ht htS he (Or.inr hbound) hunique

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
