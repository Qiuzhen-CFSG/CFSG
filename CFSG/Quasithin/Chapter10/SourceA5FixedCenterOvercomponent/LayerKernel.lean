module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.ActorFiveExclusion
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# Faithfulness of the contained-layer head

When the ambient centralizer has trivial odd core, its C-component is
ordinary or has F* equal to its two-core. The contained natural A₅ layer
excludes an ordinary component. Its normal closure is [O₂(I),I], whose
centralizer is consequently exactly O₂(I). This identifies the actual
head with the faithful actor used in small-chief recognition.

Source: Aschbacher–Smith 10.2.1, printed p.743, using A.3.3 and C.1.11.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal natural-layer closure has exactly the two-core as action kernel. -/
theorem source_a5_overcomponent_layer_centralizer_eq_core
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) X)
    (ho : pPrimeCore 2 X = ⊥)
    (hU : (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I) :
    centralizer (normalClosure ((blockU (L.subgroupOf I)).map
      (L.subgroupOf I).subtype : Set I) : Set I) = pCore 2 I := by
  let K := L.subgroupOf I
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hK : IsAlternatingBlock K 5 := hL.of_mulEquiv (subgroupOfEquivOfLe hLI).symm
  have hnq : ¬ IsQuasisimple I := by
    intro hq
    let := hq
    have hUZ : blockU K ≤ center K := by
      intro u hu
      have hh := IsQuasisimple.pCore_le_center 2 (hU (mem_map_of_mem K.subtype hu))
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (mem_center_iff.mp hh k)
    have hz : blockU K ⊓ center K = ⊥ := by
      rw [←blockFixed_map,hK.blockFixed_eq_bot,Subgroup.map_bot]
    exact hK.2.1.blockU_ne_bot (by rwa [inf_eq_left.mpr hUZ] at hz)
  have hf : generalizedFitting I = pCore 2 I := by
    rcases hI.component_or_generalizedFitting_eq_pCore ho with hcomp | hf
    · let := hcomp.2
      exact (hnq (IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hIX))).elim
    · have he := congrArg (Subgroup.map (subgroupOfEquivOfLe hIX).toMonoidHom) hf
      simpa only [map_generalizedFitting_equiv, pCore_map_iso] using he
  obtain ⟨S,_,hSK⟩ := source_containing_component_sylow hLI hIX hI hS
  have hs := hK.normalClosure_layer_split K S hSK hU
  have hw := hK.normalClosure_layer_eq_blockU K S hSK hU
    (hK.normalClosure_eq_top_in_cComponent hIX hI K)
  apply le_antisymm
  · rw [hw]
    exact centralizer_blockU_le_of_fitting hf
  · exact le_centralizer_iff.mp hs.2.1

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
