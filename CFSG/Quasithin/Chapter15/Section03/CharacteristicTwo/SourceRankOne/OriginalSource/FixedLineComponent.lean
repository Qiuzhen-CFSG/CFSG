module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.FixedLine
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.MarkedContradiction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.MathieuTwentyFourStabilizer.LocalSection

/-!
# Normality and the M₂₄ exclusion for the original fixed-line component

The original local data supply the full common Sylow subgroup and its literal
local C-component. Source1.2.4 makes the unique containing component normal.
The marked S₈ action forces non-inner action on the smaller A₈ section.
If the containing quotient were M₂₄, its proved octad local-section theorem
would give inner stabilizer action, a contradiction. The final theorem keeps
the containing component in the original ambient group.

The restricted proper-embedding sieve and the remaining L₅(2) and J₄
exclusions are separate from these conclusions.

Source: Aschbacher–Smith15.3.32(3), printed p.1133, using1.2.4 andA.3.12(14).
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration EightGeometry
open ComponentExtension.EmbeddingReduction
open Chapter1 Chapter1.Terminal Chapter1.Terminal.LinearFourActions
variable {G : Type*} [Group G] [Finite G]

/-- The actual containing component is normal, has non-inner marked Sylow action,
and cannot have M₂₄ as its intrinsic two-core quotient. -/
theorem source_fixedLine_normal_component_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (mark : Parabolics.MiddleNodeFlagMarking d I c.L) :
    let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
    ∃ T : Sylow 2 C, (T : Subgroup C).map C.subtype = d.S ∧
      ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
        (∀ D : Subgroup C, D.IsCComponent → c.L.subgroupOf C ≤ D → D = K) ∧
        ¬ TwoStabilizerActsInner (twoQuotientImage (c.L.subgroupOf C) K) ∧
        ¬ Nonempty ((XiQuotient K) ≃* Sporadic.Mathieu.M24) := by
  let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
  change ∃ T : Sylow 2 C, _
  obtain ⟨a⟩ := source_lieSieve_input hG d hempty hM hu hmany hshadow hI hf c
  obtain ⟨_, _, hc, _, hfixed, hcard, _⟩ :=
    source_lemma_15_3_32_1_2 hG d hempty hM hu hmany hshadow hI hf c mark
  have h11 : ∀ J ∈ d.Hplus, Chapter1.IsSylowIn 2 d.S J := by
    intro J hJ
    exact (OutsideStructure.source_lemma_15_3_11_from_selection
      hG d hempty hM hu hmany J hJ).sylow
  have hLC : c.L ≤ C := (component_le c).trans
    (overgroup_le_fixedLine_centralizer d c a.generated hfixed)
  obtain ⟨T, hT⟩ := fixedLine_centralizer_sylow d hI.1 c a.generated hfixed hcard h11
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
  obtain ⟨K, ⟨hK, hBK, hKn⟩, _⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (fixedLine_centralizer_quotient_sqtk hG d hcard) T hB hTB
  have hunique : ∀ D : Subgroup C, D.IsCComponent → c.L.subgroupOf C ≤ D → D = K := by
    obtain ⟨K', ⟨hK', hBK'⟩, huniq⟩ :=
      Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
        (fun _ _ _ => ChapterA.Section03.SourceComponents.containment_knownSimple)
        (fixedLine_centralizer_quotient_sqtk hG d hcard) T hB
    intro D hD hBD
    exact (huniq D ⟨hD, hBD⟩).trans (huniq K ⟨hK, hBK⟩).symm
  have hnoninner : ¬ TwoStabilizerActsInner (twoQuotientImage (c.L.subgroupOf C) K) :=
    contradiction_of_containing_image_inner d c hLC a.normal a.generated
      a.sylow a.sylow_eq T hT hc.symm mark.equiv mark.component K hBK hKn
  refine ⟨T, hT, K, hK, hKn, hBK, hunique, hnoninner, ?_⟩
  rintro ⟨eK⟩
  obtain ⟨U, hU⟩ := exists_image_local_sylow T hB.1 hTB hBK hK
  have hsmall : ClassicalGroup.IsPSL (XiQuotient (c.L.subgroupOf C)) 4 2 :=
    isPSL_subgroupOf hLC
      (componentCore_isPSL d c a.sylow a.sylow_eq hc.symm mark.equiv mark.component)
  exact hnoninner (MathieuTwentyFourStabilizer.twoStabilizerActsInner_of_local_section
    eK _ U (hsmall.of_mulEquiv (imageSectionEquiv hBK).symm) hU)


/-- The actual containing component cannot have the M₂₄ two-core quotient. -/
theorem source_fixedLine_containing_component_not_mathieu
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
    (hLK : c.L ≤ K) : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) := by
  let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
  obtain ⟨T, hT, D, hD, hDn, hLD, hunique, _, hno⟩ :=
    source_fixedLine_normal_component_data hG d hempty hM hu hmany hshadow hI hf c mark
  have he : K.subgroupOf C = D := hunique _ hK.2 (comap_mono hLK)
  rintro ⟨eK⟩
  apply hno
  rw [← he]
  let e := subgroupOfEquivOfLe hK.1
  exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans eK⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
