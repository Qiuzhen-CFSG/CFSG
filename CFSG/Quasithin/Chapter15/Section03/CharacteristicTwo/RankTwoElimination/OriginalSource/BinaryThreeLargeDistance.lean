module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThree
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FullCover.Exclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction

/-!
# The original PSL₃(2) branch at large distance

The original residual geometry constructs the binary MS input in the literal
subgroup LS. Its abelian commutator core and nonabelian distance-four cases
are already excluded by the source action calculations. The common MS93
reduction and parity of the critical distance leave only distance greater
than four. The original Sylow S is still a full Sylow subgroup in LS, and
15.3.8 gives its central omega order four; both are transported through the
literal subgroup inclusions for the shared large-distance consumer.

The remaining large-distance contradiction is explicit. This module does
not assert the full binary MS classification or discharge the separate path
replacement and original-two-core action arguments.

Source: Aschbacher–Smith 15.3.8 and 15.3.23 (the latter on printed
pp.1128–1129); Meierfrankenfeld–Stellmacher (1993), Sections 3–4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterA.Section05To06 ChapterC ComponentIntersection OutsideStructure
open LinearThree.OriginalSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
include hG hempty hM hu hmany hI in
/-- The original Sylow embeds as the full Sylow subgroup in LS. -/
theorem binary_three_exists_marked_sylow :
    ∃ P : Sylow 2 (c.L ⊔ d.S : Subgroup G),
      d.S.subgroupOf (c.L ⊔ d.S) = (P : Subgroup (c.L ⊔ d.S : Subgroup G)) := by
  have h11 := source_lemma_15_3_11_from_selection hG d hempty hM hu hmany I hI
  have hS : Chapter1.IsSylowIn 2 d.S I := h11.sylow
  have hSI : d.S ≤ I := (Chapter1.isSylowIn_iff.mp hS).2.1
  have hSyl : Chapter1.IsSylowIn 2 d.S (c.L ⊔ d.S) :=
    hS.restrict le_sup_right (sup_le (component_le c) hSI)
  obtain ⟨P,hP⟩ := hSyl
  refine ⟨P,?_⟩
  apply map_injective (c.L ⊔ d.S).subtype_injective
  exact (map_subgroupOf_eq_of_le le_sup_right).trans hP.symm

/-- Source 15.3.8 on the literal local Sylow subgroup used by the MS input. -/
theorem binary_three_local_omega_card :
    Nat.card (omega₁ (center (d.S.subgroupOf (c.L ⊔ d.S))) (p := 2)) = 4 := by
  have hcard : Nat.card (centralOmegaIn d.S) = 4 := by
    let _ := d.action.elementary_fixedPlane d.S
    rw [← fixedPlane_eq_centralOmegaIn d.T d.V d.S inf_le_left
      (d.action.planeStabilizer_index_two d.T d.sylow_le 1)
      (d.action.card_centralInvolutions d.T d.sylow_le)
      (d.action.fixedPlane_le_stabilizer d.T d.sylow_le
        (localModule_le d.T d.sylow_le) 1)
      (d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1)]
    exact d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1
  have hcardS : Nat.card (omega₁ (center d.S) (p := 2)) = 4 := by
    simpa only [centralOmegaIn,omegaOneAmbient,
      card_map_of_injective d.S.subtype_injective,
      card_map_of_injective (center d.S).subtype_injective] using hcard
  let ec := centerCongr (subgroupOfEquivOfLe (show d.S ≤ c.L ⊔ d.S from le_sup_right))
  have homega : (omega₁ (center (d.S.subgroupOf (c.L ⊔ d.S))) (p := 2)).map
      ec.toMonoidHom = omega₁ (center d.S) (p := 2) := ec.map_omega 2 1
  rw [← homega,card_map_of_injective ec.injective] at hcardS
  exact hcardS


include hG hempty hM hu hmany hI htwo hf e

/-- The actual LS pair leaves only the nonabelian large-distance branch.
The preceding source proofs discharge the abelian and distance-four cases. -/
theorem source_lemma_15_3_23_of_large_distance
    (hlarge : ∀ (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
      (t : BinaryMS.MS93.InputSetup b),
      ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))) →
      4 < t.geometry.b t.reduction.radical → False) : False := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  have hrank := rankTwoCase_three_rank hG d hI htwo
  by_cases hc : IsMulCommutative
      (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S)))
  · exact source_lemma_15_3_23_of_abelian_core hG d hempty hM hu hmany hI htwo hf c e hc
  · obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
      hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
    obtain ⟨hnc,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne
      hBaum hI c hrank eSL hW hJ hcore
    have h11 := source_lemma_15_3_11 hG d hempty hM hu hmany hne hBaum I hI
    have hchar := h11.characteristic_exclusion c.L (component_le c) (by
      simpa only [YL,ComponentIntersection.intersectionResidual,hg.first_choice] using hnc)
      c.outside
    let b := Fourth.sylowInput d c (outside_sqtk hG d hI) hf h11.sylow
      hg.component_normalized hchar eSL
    obtain ⟨t⟩ := BinaryMS.MS93.exists_setup b hc
    obtain ⟨common⟩ := t.commonFacts hc
    have hfour := source_nonabelian_binary_distance_ne_four
      hG d hempty hM hu hmany hI c hrank eSL hW hJ hcore b t hc
    have heven := t.geometry.even (BinaryMS.MS93.alpha t.reduction.radical) rfl
    change Even (t.geometry.b t.reduction.radical) at heven
    obtain ⟨n,hn⟩ := heven
    exact hlarge b t hc (by have := common.large_distance; omega)

/-- Original 15.3.23 specialized to a full Sylow binary MS input with small
central omega. This is the literal consumer of the shared large-distance
source argument; no separate classification or local marking is assumed. -/
theorem source_lemma_15_3_23_of_small_sylow_large_distance
    (hlarge : ∀ (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
      (P : Sylow 2 (c.L ⊔ d.S : Subgroup G)),
      d.S.subgroupOf (c.L ⊔ d.S) = (P : Subgroup (c.L ⊔ d.S : Subgroup G)) →
      Nat.card (omega₁ (center (d.S.subgroupOf (c.L ⊔ d.S))) (p := 2)) ≤ 4 →
      ∀ (t : BinaryMS.MS93.InputSetup b),
      ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))) →
      4 < t.geometry.b t.reduction.radical → False) : False := by
  apply source_lemma_15_3_23_of_large_distance hG d hempty hM hu hmany hI htwo hf c e
  intro b t hc hb
  obtain ⟨P,hP⟩ := binary_three_exists_marked_sylow hG d hempty hM hu hmany hI c
  exact hlarge b P hP (binary_three_local_omega_card d c).le t hc hb

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
