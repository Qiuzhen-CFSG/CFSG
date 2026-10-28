module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveSylow
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
/-!
# The normal overcomponent in the original marked-five wreath branch

When the generated group has nontrivial two-core, the actual subgroup
S=N_T(K₁) is Sylow.  The original wreath component K₁ then belongs to its
local component family: its restriction to K₁S is a C-component and the
ambient two-core is contained in S.  The proved source version of 1.2.4
constructs a normal C-component L₁ containing K₁.  Since YRc and S lie in M,
this gives G₀=L₁(G₀∩M), with L₁ outside M.

The final theorem combines this branch with the previously constructed
literal F.1.1 configuration when the two-core is trivial.  The mixed DGS85
exclusion and subsequent characteristic-two quotient analysis remain
separate source steps; neither is used as a substitute for this construction.

Source: Aschbacher--Smith, original 15.2.4, printed p.1106; 1.2.4, p.505.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem normal_overcomponent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {W H K S : Subgroup G} (hK : K ∈ Chapter1.cComponentsIn H)
    (hSH : S ≤ H) (hKW : K ≤ W) (hSyl : Chapter1.IsSylowIn 2 S W)
    (hSN : S ≤ normalizer (K : Set G)) (hcore : pCore 2 W ≠ ⊥) :
    ∃ L : Subgroup G, L ∈ Chapter1.cComponentsIn W ∧ K ≤ L ∧
      W ≤ normalizer (L : Set G) := by
  obtain ⟨P,hP⟩ := hSyl
  have hSW : S ≤ W := hP ▸ map_subtype_le _
  have hP' : (P : Subgroup W) = S.subgroupOf W := by
    rw [←hP]
    exact (comap_map_eq_self_of_injective W.subtype_injective _).symm
  have hWH : W ∈ Chapter1.H G := by
    exact fun hb => hcore ((map_eq_bot_iff_of_injective _ W.subtype_injective).mp hb)
  have hcoreS : W.pCoreIn 2 ≤ S := hP ▸ pCoreIn_le_sylow W P
  have hcoreKS : W.pCoreIn 2 ≤ (K ⊔ S).pCoreIn 2 :=
    (le_inf (hcoreS.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 (sup_le hKW hSW))
  have hlocal : K ∈ Chapter1.L G S :=
    ⟨hK.2.subgroupOf_of_le le_sup_left (sup_le hK.1 hSH),
      Chapter1.IsSylowIn.restrict ⟨P,hP⟩ le_sup_right (sup_le hKW hSW),
      fun hb => hWH (bot_unique (hb ▸ hcoreKS))⟩
  have hlocal' : K.subgroupOf W ∈ Chapter1.L W (P : Subgroup W) := by
    rw [hP']
    exact (Chapter1.mem_LIn_iff_subgroupOf hSW hKW).mp ⟨hKW,hlocal⟩
  have hSN' : (P : Subgroup W) ≤ normalizer (K.subgroupOf W : Set W) := by
    rw [hP',←subgroupOf_normalizer_eq hKW]
    exact comap_mono hSN
  obtain ⟨D,⟨hD,hKD,hDN⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hWH) P hlocal' hSN'
  have hDmap : (D.map W.subtype).subgroupOf W = D :=
    comap_map_eq_self_of_injective W.subtype_injective _
  refine ⟨D.map W.subtype,⟨map_subtype_le _,hDmap.symm ▸ hD⟩,?_,?_⟩
  · simpa only [map_subgroupOf_eq_of_le hKW] using map_mono (f := W.subtype) hKD
  · exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp (hDmap.symm ▸ hDN)

/-- The literal marked-five configuration has the source normal overcomponent. -/
theorem source_dihedral_five_nontrivial_core_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H K : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.cComponentsIn H) (hout : ¬ K ≤ M)
    (hi : ((T : Subgroup G) ⊓ normalizer (K : Set G)).relIndex (T : Subgroup G) = 2)
    (hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) ⊓ normalizer (K : Set G)) :
    let L₀ := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
      (M ⊓ Mc).pCoreIn 2
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated ![L₀,K] S
    pCore 2 W ≠ ⊥ → Chapter1.IsSylowIn 2 S W ∧
      ∃ L₁ : Subgroup G, L₁ ∈ Chapter1.cComponentsIn W ∧ K ≤ L₁ ∧ ¬ L₁ ≤ M ∧
        W ≤ normalizer (L₁ : Set G) ∧ W = L₁ ⊔ (W ⊓ M) := by
  intro L₀ S W hcore
  have hSyl := source_dihedral_five_nontrivial_core_sylow
    hG T hempty hM hJ hu hmany hV l hd hout hi hJS hcore
  have hKW : K ≤ W := le_sup_right.trans le_sup_left
  have hSW : S ≤ W := le_sup_right
  have hSM : S ≤ M := inf_le_left.trans hM.1.2
  have hL₀W : L₀ ≤ W := le_sup_left.trans le_sup_left
  have hL₀M : L₀ ≤ M := sup_le
    (source_caseIIResidual_le T hM.1.2 (map_subtype_le _))
    ((pCoreIn_le 2 (M ⊓ Mc)).trans inf_le_left)
  obtain ⟨L₁,hL₁,hKL,hN⟩ := normal_overcomponent hG hK
    (inf_le_left.trans hTH) hKW hSyl inf_le_right hcore
  refine ⟨hSyl,L₁,hL₁,hKL,fun hLM => hout (hKL.trans hLM),hN,?_⟩
  apply le_antisymm
  · exact sup_le (sup_le ((le_inf hL₀W hL₀M).trans le_sup_right)
      (hKL.trans le_sup_left)) ((le_inf hSW hSM).trans le_sup_right)
  · exact sup_le hL₁.1 inf_le_left

/-- The actual wreath configuration supplies the source component in the nontrivial-core branch. -/
theorem source_HStar_wreath_five_complete_local_configuration
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let L₀ := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
      (M ⊓ Mc).pCoreIn 2
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![L₀,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      normalizer (S : Set G) ≤ M ∧
      generalizedFitting (ChapterF.Source.generated L S ⊓ M : Subgroup G) =
        pCore 2 (ChapterF.Source.generated L S ⊓ M : Subgroup G) ∧
      ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (∀ i : Fin 2, generalizedFitting (ChapterF.Source.parabolic L S i) =
        pCore 2 (ChapterF.Source.parabolic L S i)) ∧
      (pCore 2 (ChapterF.Source.generated L S) = ⊥ → ChapterF.Source.HypothesisF11 L S) ∧
      (pCore 2 (ChapterF.Source.generated L S) ≠ ⊥ →
        Chapter1.IsSylowIn 2 S (ChapterF.Source.generated L S) ∧
        ∃ L₁ : Subgroup G, L₁ ∈ Chapter1.cComponentsIn (ChapterF.Source.generated L S) ∧
          K ≤ L₁ ∧ ¬ L₁ ≤ M ∧
          ChapterF.Source.generated L S ≤ normalizer (L₁ : Set G) ∧
          ChapterF.Source.generated L S = L₁ ⊔ (ChapterF.Source.generated L S ⊓ M)) := by
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  obtain ⟨K,hK,heK,hout,hi,hJS,hNS,hfit,hB,hchar,hfree⟩ :=
    source_HStar_wreath_five_mixed_configuration hG T hempty hM hJ hu hmany hV hcases hH he
  exact ⟨K,hK,heK,hout,hi,hJS,hNS,hfit,hB,hchar,hfree,
    source_dihedral_five_nontrivial_core_component hG T hempty hM hJ hu hmany hV l hd
      hH.1.1.2 hK hout hi hJS⟩

end CFSG.Quasithin.Chapter15.Section02
