module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.FixedLineComponent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.NormalizedTransport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.NormalizedLocal

/-!
# Excluding J₄ from the original fixed-line component

The original marked S₈ action is non-inner on the A₈ section. Intersecting
the full fixed-line Sylow subgroup with the containing component, then
factoring its two-core, preserves both the local section and normalization.
The normalized J₄ theorem therefore contradicts that same marked action.
The conclusion concerns the literal component of the original ambient group,
with all original local-data hypotheses and no model-action premise.

Source: Aschbacher–Smith15.3.32(3), printed p.1133, using A.3.12(17).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration EightGeometry
open ComponentExtension.EmbeddingReduction
open Chapter1 Chapter1.Terminal Chapter1.Terminal.LinearFourActions
variable {G : Type*} [Group G] [Finite G]

/-- The actual fixed-line containing component cannot have the J₄ two-core quotient. -/
theorem source_fixedLine_containing_component_not_janko
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (mark : Parabolics.MiddleNodeFlagMarking d I c.L)
    (K : Subgroup G)
    (hK : K ∈ Chapter1.cComponentsIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)))
    (hLK : c.L ≤ K) : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) := by
  let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
  obtain ⟨T, hT, D, hD, hDn, hLD, hunique, hnoninner, _⟩ :=
    source_fixedLine_normal_component_data hG d hempty hM hu hmany hshadow hI hf c mark
  have he : K.subgroupOf C = D := hunique _ hK.2 (comap_mono hLK)
  rintro ⟨eK⟩
  have hlarge : Nonempty ((XiQuotient D) ≃* Janko4.Model) := by
    rw [← he]
    let e := subgroupOfEquivOfLe hK.1
    exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans eK⟩
  obtain ⟨a⟩ := source_lieSieve_input hG d hempty hM hu hmany hshadow hI hf c
  obtain ⟨_, _, hc, _, hfixed, _, _⟩ :=
    source_lemma_15_3_32_1_2 hG d hempty hM hu hmany hshadow hI hf c mark
  have h11 : ∀ J ∈ d.Hplus, Chapter1.IsSylowIn 2 d.S J := by
    intro J hJ
    exact (OutsideStructure.source_lemma_15_3_11_from_selection
      hG d hempty hM hu hmany J hJ).sylow
  have hLC : c.L ≤ C := hLK.trans hK.1
  have hSC : d.S ≤ C := hT ▸ map_subtype_le (T : Subgroup C)
  have hTeq : (T : Subgroup C) = d.S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hSC]
    exact hT
  have hB : c.L.subgroupOf C ∈ Chapter1.L C T := by
    rw [hTeq]
    exact (Chapter1.mem_LIn_iff_subgroupOf hSC hLC).mp
      (component_mem_fixedLine_local_family d hI.1 c a.normal a.generated hfixed h11)
  have hSL : d.S ≤ normalizer (c.L : Set G) :=
    (show d.S ≤ I from a.generated ▸ le_sup_right).trans
      ((normal_subgroupOf_iff_le_normalizer (component_le c)).mp a.normal)
  have hTB : (T : Subgroup C) ≤ normalizer (c.L.subgroupOf C : Set C) := by
    rw [hTeq, ← subgroupOf_normalizer_eq hLC]
    exact comap_mono hSL
  obtain ⟨U, hU, hnU⟩ := exists_image_normalized_local_sylow T hB.1 hTB hLD hD
  have hsmall : ClassicalGroup.IsPSL (XiQuotient (c.L.subgroupOf C)) 4 2 :=
    isPSL_subgroupOf hLC
      (componentCore_isPSL d c a.sylow a.sylow_eq hc.symm mark.equiv mark.component)
  exact hnoninner (JankoFourStabilizer.twoStabilizerActsInner_of_normalized_local
    hlarge.some _ U (hsmall.of_mulEquiv (imageSectionEquiv hLD).symm) hU hnU)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
