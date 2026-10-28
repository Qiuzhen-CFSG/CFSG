module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.Source1331.Source318
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ChiefFactors
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import Theory.GroupTheory.TwoLocalUniquenessControl
/-!
# The actual reduced commutator at the maximal normalizer

For a maximal faithful local component normalized by T, the genuine A/C
uniqueness theorem makes M=N_G(L) the unique maximal two-local over LT.
The complete A.3.6 common structure gives central two-chief factors above
O₂(L). A.4.11 then proves U=[R₂(M),L] is nontrivial. Its original inclusion
makes U elementary abelian, normal in M and contained in O₂(M); uniqueness
identifies its full ambient normalizer with M.

This applies also to the selected nonquasisimple counterexample in13.1.7.
No chosen module, quotient-model list or assertion of XiStar membership is
assumed. The canonical3.1.8 source input occurs only in counterexample
selection, not in the reduced commutator theorem.
Source: Aschbacher--Smith, setup of13.1.7 and13.1.8(2), pp.868--869,
using1.2.7, A.3.6 and A.4.11.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.Section02 Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original V-hat=R₂(N_G(L)), included in G. -/
def normalizerReduced (L : Subgroup G) : Subgroup G :=
  (reducedTwoSubgroup (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype

/-- The original U=[V-hat,L] in the proof of13.1.7. -/
def normalizerMoved (L : Subgroup G) : Subgroup G := ⁅normalizerReduced L, L⁆

omit [Finite G] in
theorem normalizerReduced_eq (L : Subgroup G) : normalizerReduced L =
    (reducedTwoSubgroup (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype := by rfl

omit [Finite G] in
theorem normalizerMoved_eq (L : Subgroup G) : normalizerMoved L =
    ⁅(reducedTwoSubgroup (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype, L⁆ := by rfl

private theorem faithful_component_moved {H : Type u} [Group H] [Finite H]
    (hq : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H))
    (A : Subgroup H) (hA : A.IsCComponent)
    (hf : ChapterA.Section04.IsFaithfulSignalizerType A) :
    ⁅reducedTwoSubgroup H, A⁆ ≠ ⊥ := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  let := pCore_isNilpotent (p := 2) (G := H)
  have hc := h36 _ hq (pCore_quotient_pCore_eq_bot 2)
    (A.map (QuotientGroup.mk' (pCore 2 H))) (hA.map_quotient (pCore 2 H))
  have hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 A) :=
    (hasCentralPChiefFactorsAbove_iff_quotient _).mpr
      (hasCentralTwoChiefFactors_cComponent_twoCore_quotient hA hc.2)
  exact ChapterA.Section04.reduced_commutator_ne_bot_of_intrinsicModule_ne_bot A
    hA.subnormal hf.1.2.1 hchief hf.2

theorem faithful_maximal_normalizer_moved
    {T : Sylow 2 G} {L : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hL : FaithfulMaximalLocal T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsElementaryAbelian 2 (normalizerMoved L) ∧ normalizerMoved L ≠ ⊥ ∧
      normalizerMoved L ≤ (normalizer (L : Set G)).pCoreIn 2 ∧
      normalizer (normalizerMoved L : Set G) = normalizer (L : Set G) := by
  let M := normalizer (L : Set G)
  let A := L.subgroupOf M
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl hTL)
      (le_componentOrbit L T)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hG T hL.1
  have hm : IsMaximalTwoLocal M := by simpa only [he] using hu.normalizer_maximal
  have hj : L ⊔ (T : Subgroup G) ≤ M := sup_le L.le_normalizer hTL
  have hM : M ∈ HOver G ((L ⊔ (T : Subgroup G) : Subgroup G) : Set G) :=
    ⟨mem_H_of_isTwoLocal hm.1, fun _ hx => hj hx⟩
  have hA : A.IsCComponent := hu.component M hM
  let e : A ≃* L := subgroupOfEquivOfLe L.le_normalizer
  have hf : ChapterA.Section04.IsFaithfulSignalizerType A := by
    refine ⟨⟨?_, hL.2.1.2.1.of_surjective e.symm.toMonoidHom e.symm.surjective, ?_⟩, ?_⟩
    · exact hA.ne_bot
    · apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_generalizedFitting_equiv, pCore_map_iso]
      exact hL.2.1.2.2
    · intro hz
      apply hL.2.2
      have hmap : A.map M.subtype = L := map_subgroupOf_eq_of_le L.le_normalizer
      rw [← hmap, ChapterA.Section04.intrinsicSignalizerModule_map_of_injective
        M.subtype M.subtype_injective, hz, Subgroup.map_bot]
  let U := ⁅reducedTwoSubgroup M, A⁆
  have hne : U ≠ ⊥ := faithful_component_moved
    (uniqueness_local_quotient_sqtk hG hM.1) A hA hf
  have hem : U.map M.subtype = normalizerMoved L := by
    rw [map_commutator, map_subgroupOf_eq_of_le L.le_normalizer]
    rfl
  let : IsElementaryAbelian 2 (reducedTwoSubgroup M) :=
    isPReduced_reducedPSubgroup.elementary
  have hUle : U ≤ reducedTwoSubgroup M := commutator_le_left _ _
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUle
  have hElem : IsElementaryAbelian 2 (normalizerMoved L) := hem ▸ IsElementaryAbelian.map M.subtype
  have hUne : normalizerMoved L ≠ ⊥ := by
    rw [← hem]
    exact fun hb => hne ((U.map_eq_bot_iff_of_injective M.subtype_injective).mp hb)
  have hcore : normalizerMoved L ≤ M.pCoreIn 2 := by
    rw [← hem]
    exact map_mono (hUle.trans (reducedPSubgroup_le_pCore 2 M))
  have hnU : M ≤ normalizer (normalizerMoved L : Set G) := by
    rw [← hem]
    apply le_normalizer_iff.mpr
    intro g hg u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨(⟨g,hg⟩ : M)*v*(⟨g,hg⟩ : M)⁻¹, ?_, rfl⟩
    exact (inferInstance : U.Normal).conj_mem v hv ⟨g,hg⟩
  refine ⟨hElem, hUne, hcore, le_antisymm ?_ hnU⟩
  apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
  · simpa only [he] using hu.normalizer_unique
  · exact hElem.isPGroup
  · exact hUne
  · exact hj.trans hnU
end CFSG.Quasithin.Chapter13.Section01

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01
universe v
variable {G : Type v} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The same selected counterexample carries the literal nontrivial U of
13.1.8, with its full ambient normalizer and original two-core containment. -/
theorem Hypothesis1331.nonquasisimple_reduced_module_data
    (h : Hypothesis1331 T L₀) (h318 : Chapter3.SourceTheorem318One G)
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ K ∈ LStar G T, L₀ ≤ K ∧ FaithfulMaximalLocal T K ∧
      K ∈ nonquasisimpleFaithful T ∧
      IsElementaryAbelian 2 (normalizerMoved K) ∧ normalizerMoved K ≠ ⊥ ∧
      normalizerMoved K ≤ (normalizer (K : Set G)).pCoreIn 2 ∧
      normalizer (normalizerMoved K : Set G) = normalizer (K : Set G) ∧
      IsMaximalTwoLocal (normalizer (K : Set G)) ∧
      L₀ ⊔ (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ∀ H : Subgroup G, IsMaximalTwoLocal H → L₀ ⊔ (T : Subgroup G) ≤ H →
        H = normalizer (K : Set G) := by
  obtain ⟨K, hK, hLK, hf, hnon, hmax, hjoin, hu, _⟩ :=
    h.maximal_counterexample_of_source318 h318 hn
  obtain ⟨he, hne, hc, hnorm⟩ := faithful_maximal_normalizer_moved
    h.qtke hf (le_sup_right.trans hjoin)
  exact ⟨K, hK, hLK, hf, hnon, he, hne, hc, hnorm, hmax, hjoin, hu⟩
end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
