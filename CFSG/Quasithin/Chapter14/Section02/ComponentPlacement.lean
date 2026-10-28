module
public import CFSG.Quasithin.Chapter14.Section02.KOneSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels

/-!
# Original component placement for 14.2.9

Every actual C-component of an outside H belongs to L(G,T). The empty
faithful-family theorem places it in the distinguished Mc. Apply original
1.2.4 inside Mc, using its actual Sylow subgroup and two-core quotient, to
obtain the unique containing C-component. Original 14.1.6 gives the unique
maximal two-local overgroup of that component together with T. If T
normalizes the starting component, the containing component is normal in
Mc. The same result applies to the K₁ supplied by the exchanged source
branch; no containing-component certificate is assumed.

Source: Aschbacher--Smith 14.2.9, its use of 1.2.4, and 14.1.6(2),
printed pp.505, 977 and 983.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter1 Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

theorem source_outside_component_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K : Subgroup H) (hK : K.IsCComponent) :
    ∃ Kc : Subgroup G, Kc ∈ cComponentsIn Mc ∧ K.map H.subtype ≤ Kc ∧
      (∀ D ∈ cComponentsIn Mc, K.map H.subtype ≤ D → D = Kc) ∧
      Mc ⊓ normalizer (K.map H.subtype : Set G) ≤ normalizer (Kc : Set G) ∧
      ((Kc.subgroupOf Mc).Normal ∨
        (normalizer (Kc.subgroupOf Mc : Set Mc)).index = 2 ∧
          NonnormalCComponentModel ((Kc.subgroupOf Mc) ⧸ pCore 2 (Kc.subgroupOf Mc))) ∧
      maximalTwoLocalOvergroups (Kc ⊔ (T : Subgroup G)) = {Mc} ∧
      ((T : Subgroup G) ≤ normalizer (K.map H.subtype : Set G) →
        (Kc.subgroupOf Mc).Normal) := by
  have hA := fun (X : Type _) [Group X] [Finite X] => ChapterA.Section02.theoremA_knownSimple (G := X)
  have hC := fun (X : Type _) [Group X] [Finite X] => ChapterA.Section02.theoremC_knownSimple (G := X)
  have hlocal : K.map H.subtype ∈ L G (T : Subgroup G) := by
    apply (lemma_1_2_6 T hH.1.1).2
    apply (lemma_1_2_6 T hH.1.1).1
    refine ⟨map_subtype_le K,?_⟩
    simpa only [subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hK
  have hHMc : H ≤ Mc :=
    ((source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2).trans
      (InitialSource.centralizer_le_partner T hu)
  have hKMc : K.map H.subtype ≤ Mc := (map_subtype_le K).trans hHMc
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := by
    have hm : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu.symm ▸ Set.mem_singleton Mc
    exact ⟨hm.1,(le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)).trans hm.2⟩
  have hTMc : (T : Subgroup G) ≤ Mc := hMc.2
  have hKM : (K.map H.subtype).subgroupOf Mc ∈ L Mc (T.subtype hTMc) :=
    (mem_LIn_iff_subgroupOf hTMc hKMc).mp ⟨hKMc,hlocal⟩
  have hsq := hG.twoLocal_sqtk hMc.1.1
  have hsqQ := ChapterE.Structure.sqtk_two_quotient hsq (pCore 2 Mc) pCore_isPGroup
  obtain ⟨C,hCcomp,hunique⟩ := lemma_1_2_4_containment_of_A_3_12
    (containment_of_theoremsAC hA hC) hsqQ (T.subtype hTMc) hKM
  let Kc := C.map Mc.subtype
  have hKc : Kc ∈ cComponentsIn Mc := by
    refine ⟨map_subtype_le C,?_⟩
    simpa only [Kc,subgroupOf,comap_map_eq_self_of_injective Mc.subtype_injective] using hCcomp.1
  have hKC : K.map H.subtype ≤ Kc := by
    have hh := map_mono (f := Mc.subtype) hCcomp.2
    rwa [map_subgroupOf_eq_of_le hKMc] at hh
  have huniq : ∀ D ∈ cComponentsIn Mc, K.map H.subtype ≤ D → D = Kc := by
    intro D hD hKD
    have he := hunique (D.subgroupOf Mc) ⟨hD.2,comap_mono hKD⟩
    have hh := congrArg (Subgroup.map Mc.subtype) he
    rwa [map_subgroupOf_eq_of_le hD.1] at hh
  have hnC : Mc ⊓ normalizer (K.map H.subtype : Set G) ≤ normalizer (Kc : Set G) := by
    have hn := cComponent_le_normalizer_of_unique hCcomp.1 hCcomp.2
      (fun D hD hKD => hunique D ⟨hD,hKD⟩)
      (le_rfl : normalizer ((K.map H.subtype).subgroupOf Mc : Set Mc) ≤ _)
    have hn' : normalizer ((K.map H.subtype).subgroupOf Mc : Set Mc) ≤
        normalizer (Kc.subgroupOf Mc : Set Mc) := by
      simpa only [Kc,subgroupOf,comap_map_eq_self_of_injective Mc.subtype_injective] using hn
    rw [← subgroupOf_normalizer_eq hKMc,← subgroupOf_normalizer_eq hKc.1] at hn'
    intro x hx
    exact hn' (show (⟨x,hx.1⟩ : Mc) ∈ (normalizer (K.map H.subtype : Set G)).subgroupOf Mc from hx.2)
  refine ⟨Kc,hKc,hKC,huniq,hnC,
    proposition_1_2_1_three_index_knownSimple hsqQ hKc.2,
    InitialSource.component_unique_maximal_overgroup hA hC hG T hempty hMc hu hKc,?_⟩
  intro hn
  have hnM : (T.subtype hTMc : Subgroup Mc) ≤
      normalizer ((K.map H.subtype).subgroupOf Mc : Set Mc) := by
    rw [← subgroupOf_normalizer_eq hKMc]
    exact comap_mono hn
  obtain ⟨D,hD,_⟩ := lemma_1_2_4_containment_normality_source hsqQ (T.subtype hTMc) hKM hnM
  have he := hunique D ⟨hD.1,hD.2.1⟩
  have hc : C.Normal := he ▸ hD.2.2
  simpa only [Kc,subgroupOf,comap_map_eq_self_of_injective Mc.subtype_injective] using hc
end CFSG.Quasithin.Chapter14.Section02
