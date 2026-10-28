module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.FixedLineFive
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.FixedLineJanko
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.ThreeResidual

/-!
# The remaining fixed-line embedding input for the original source

The original middle-node marking supplies the fixed line, natural module,
common Sylow subgroup and unique normal containing C-component. The proved
L₅(2), M₂₄ and J₄ action calculations exclude all three proper rows in the
printed A.3.12 application. Once their exhaustiveness is supplied at this
literal containing subgroup, L is itself a normal C-component. The proved
A₈ rank and outer-action calculation then identifies its three-residual.

The proper-row implication remains explicit: unique containment alone does
not provide an embedding classification. No universal A.3.12 or A.3.18
hypothesis is used by these conditional original-source consumers.

Source: Aschbacher–Smith 15.3.32(3), printed p.1133; A.3.12 and A.3.18,
printed pp.47–48 and 51–52.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration EightGeometry
variable {G : Type*} [Group G] [Finite G]

/-- At the actual fixed-line centralizer, the three proper A₈-section rows
are already excluded. The sole premise is their exhaustiveness for a proper
containing component, restricted to this original source configuration. -/
theorem source_fixedLine_containing_component_eq_of_proper_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (mark : Parabolics.MiddleNodeFlagMarking d I c.L)
    (hproper : ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)) → c.L < K →
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model))
    (K : Subgroup G)
    (hK : K ∈ Chapter1.cComponentsIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G))) (hLK : c.L ≤ K) :
    c.L = K := by
  by_contra hne
  rcases hproper K hK (lt_of_le_of_ne hLK hne) with h5 | h24 | hJ4
  · exact source_fixedLine_containing_component_not_linearFive
      hG d hempty hM hu hmany hshadow hI hf c mark K hK hLK h5
  · exact source_fixedLine_containing_component_not_mathieu
      hG d hempty hM hu hmany hshadow hI hf c mark K hK hLK h24
  · exact source_fixedLine_containing_component_not_janko
      hG d hempty hM hu hmany hshadow hI hf c mark K hK hLK hJ4

/-- Once L is a C-component of its fixed-line centralizer, source normality
and the proved A₈ three-residual calculation give the literal residual
identity. No outer-action or residual assumption is added. -/
theorem source_fixedLine_residual_of_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (mark : Parabolics.MiddleNodeFlagMarking d I c.L)
    (hcomponent : (c.L.subgroupOf
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G))).IsCComponent) :
    c.L = RankOne.threeResidualIn (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)) := by
  obtain ⟨a⟩ := source_lieSieve_input hG d hempty hM hu hmany hshadow hI hf c
  obtain ⟨_,_,hc,_,hfixed,hcard,_⟩ :=
    source_lemma_15_3_32_1_2 hG d hempty hM hu hmany hshadow hI hf c mark
  obtain ⟨_,_,K,_,hn,_,huK,_,_⟩ :=
    source_fixedLine_normal_component_data hG d hempty hM hu hmany hshadow hI hf c mark
  have he := huK _ hcomponent le_rfl
  exact ComponentExtension.component_eq_fixedLine_residual_of_normal_component hG d c
    a.generated hfixed hcard a.sylow a.sylow_eq hc.symm mark.equiv mark.component
    hcomponent (he.symm ▸ hn)

/-- The exact original15.3.32(3) callback, with only the restricted proper
A₈-section embedding implication remaining. All three candidate exclusions,
normality, quotient transport and residual generation are internal. -/
theorem source_lemma_15_3_32_3_of_proper_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (mark : Parabolics.MiddleNodeFlagMarking d I c.L)
    (hproper : ∀ K : Subgroup G, K ∈ Chapter1.cComponentsIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)) → c.L < K →
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    c.L = RankOne.threeResidualIn (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)) := by
  obtain ⟨K,⟨hK,hLK⟩,_⟩ :=
    source_fixedLine_containing_component hG d hempty hM hu hmany hshadow hI hf c mark
  have he := source_fixedLine_containing_component_eq_of_proper_models
    hG d hempty hM hu hmany hshadow hI hf c mark hproper K hK hLK
  exact source_fixedLine_residual_of_component hG d hempty hM hu hmany hshadow hI hf c mark
    (he.symm ▸ hK.2)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
