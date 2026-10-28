module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.FixedLineResidual
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.Catalogue
/-!
# The original fixed-line residual identity

The actual fixed-line centralizer is SQTK, and its marked local component
has the A₈ two-core quotient. The restricted containing-component theorem
leaves only equality, PSL₅(2), M₂₄ and J₄. The three proved marked-action
exclusions remove all proper rows. Thus the smaller component is itself a
normal C-component, and the existing residual calculation proves15.3.32(3).

Every subgroup, centralizer and quotient map is the original one. There is
no embedding-list, outer-action or residual callback in the final theorem.

Source: Aschbacher–Smith15.3.32(3), printed p.1133, using A.3.12 and A.3.18,
printed pp.47–48 and51–52.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration EightGeometry
open ComponentExtension.EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G]
/-- Exhaustiveness of the three proper A₈ rows at the literal source centralizer. -/
theorem source_fixedLine_proper_models
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
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G))) (hLK : c.L < K) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) := by
  let C := centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)
  obtain ⟨T, hT, D, hD, hDn, hLD, hunique, hnoninner, _⟩ :=
    source_fixedLine_normal_component_data hG d hempty hM hu hmany hshadow hI hf c mark
  obtain ⟨a⟩ := source_lieSieve_input hG d hempty hM hu hmany hshadow hI hf c
  obtain ⟨_, _, hc, _, hfixed, hcard, _⟩ :=
    source_lemma_15_3_32_1_2 hG d hempty hM hu hmany hshadow hI hf c mark
  have h11 : ∀ J ∈ d.Hplus, Chapter1.IsSylowIn 2 d.S J := by
    intro J hJ
    exact (OutsideStructure.source_lemma_15_3_11_from_selection
      hG d hempty hM hu hmany J hJ).sylow
  have hLC : c.L ≤ C := hLK.le.trans hK.1
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
  have hsmall : ClassicalGroup.IsPSL (((c.L.subgroupOf C) ⧸ pCore 2 (c.L.subgroupOf C))) 4 2 :=
    isPSL_subgroupOf hLC
      (componentCore_isPSL d c a.sylow a.sylow_eq hc.symm mark.equiv mark.component)
  rcases ChapterA.Section03.SourceEmbeddings.AlternatingEight.restricted_containing_models
    (fixedLine_centralizer_sqtk hG d hcard) T hB.1 hK.2 (comap_mono hLK.le) hTB hsmall
      with he | h5 | h24 | hJ4
  · have he' := congrArg (fun A : Subgroup C => A.map C.subtype) he
    rw [map_subgroupOf_eq_of_le hLC, map_subgroupOf_eq_of_le hK.1] at he'
    exact (hLK.ne he').elim
  · let e := subgroupOfEquivOfLe hK.1
    exact .inl (h5.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm)
  · let e := subgroupOfEquivOfLe hK.1
    exact .inr (.inl ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans h24.some⟩)
  · let e := subgroupOfEquivOfLe hK.1
    exact .inr (.inr ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans hJ4.some⟩)
/-- The actual smaller component equals every containing C-component. -/
theorem source_fixedLine_containing_component_eq
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
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G))) (hLK : c.L ≤ K) :
    c.L = K :=
  source_fixedLine_containing_component_eq_of_proper_models hG d hempty hM hu hmany hshadow
    hI hf c mark (source_fixedLine_proper_models hG d hempty hM hu hmany hshadow hI hf c mark)
    K hK hLK

/-- Original15.3.32(3), with every proper embedding and residual premise discharged. -/
theorem source_lemma_15_3_32_3
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (mark : Parabolics.MiddleNodeFlagMarking d I c.L) :
    c.L = RankOne.threeResidualIn (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G)) :=
  source_lemma_15_3_32_3_of_proper_models hG d hempty hM hu hmany hshadow hI hf c mark
    (source_fixedLine_proper_models hG d hempty hM hu hmany hshadow hI hf c mark)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
