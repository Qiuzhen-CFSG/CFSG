module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingActionMarking
public import Theory.SpecificGroups.SymmetricFive.TranspositionNormalizer
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingGlobalSource
public import CFSG.Quasithin.Chapter2.Section04.CoreElementarySource
/-!
# The original alternating-five Sylow index

The marked symmetric-five action sends a maximal elementary subgroup meeting
`O₂(H)` in index two to a transposition. Its mixed normalizer escapes `M`.
The elementary-core obstruction then removes the mixed alternative in C.6,
giving the actual Sylow index and Thompson equality used in 2.4.29.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
2.4.27 and the beginning of 2.4.29 (printed pp. 544–545).
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_mixed_normalizer_escape
    (d : MinimalBlockSetup M) (hsingle : d.L0 = d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (A : Subgroup G)
    (hmax : A ∈ elementaryAbelianMaxSubgroups ((d.S : Subgroup d.H).map d.H.subtype))
    (hi : (twoCore d.H).relIndex A = 2) :
    ¬ d.H ⊓ normalizer ((twoCore d.H ⊔ A : Subgroup G) : Set G) ≤ M := by
  obtain ⟨q,hq,hker,t,ht,he⟩ := d.single_alternating_transposition_action hsingle hA A hmax hi
  have hAH : A ≤ d.H := hmax.1.trans (map_subtype_le _)
  have hAS : A.subgroupOf d.H ≤ d.S := by
    intro a ha
    obtain ⟨s,hs,hsa⟩ := hmax.1 ha
    exact (d.H.subtype_injective hsa) ▸ hs
  have htP : t ∈ d.S.mapSurjective hq :=
    (map_mono hAS) (he.symm ▸ mem_zpowers t)
  have hSB : (d.S : Subgroup d.H) ≤ M.subgroupOf d.H := by
    intro s hs
    exact d.full_pair.1.1.2.1 (mem_map_of_mem d.H.subtype hs)
  have hn := Theory.SpecificGroups.SymmetricFive.TranspositionNormalizer.quotient_normalizer_not_le
    q hq d.S (M.subgroupOf d.H) (A.subgroupOf d.H) hSB d.intersection_maximal.ne_top t htP ht he
  have hcore : (twoCore d.H).subgroupOf d.H = pCore 2 d.H := by
    change ((pCore 2 d.H).map d.H.subtype).comap d.H.subtype = pCore 2 d.H
    exact comap_map_eq_self_of_injective d.H.subtype_injective _
  have hWH : twoCore d.H ⊔ A ≤ d.H := sup_le (map_subtype_le _) hAH
  have hW : (twoCore d.H ⊔ A).subgroupOf d.H = q.ker ⊔ A.subgroupOf d.H := by
    rw [subgroupOf_sup (show twoCore d.H ≤ d.H from map_subtype_le _) hAH,hcore,hker]
  intro hout
  apply hn
  intro n hn
  rw [←hW,←subgroupOf_normalizer_eq hWH] at hn
  exact hout ⟨n.property,hn⟩

theorem MinimalBlockSetup.single_alternating_sylow_index_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    S.relIndex (T : Subgroup G) = 2 ∧ ChapterB.baumann S = elementaryAbelianMaxJ S ∧
      elementaryAbelianMaxJ (T : Subgroup G) = elementaryAbelianMaxJ S := by
  obtain ⟨hi,hb,hJ,hcase⟩ := d.single_alternating_global_source hG T hST hsingle hA
  obtain ⟨hJS,hfam,_⟩ := d.single_alternating_family_action hG T hST hsingle hA
  rcases hcase with hN | ⟨_,_,A,hmax,hAQ,hcard⟩
  · rw [hN] at hi hJ
    exact ⟨hi,hb,hJ⟩
  have hJH : elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤ d.H :=
    (sSup_le fun B hB => hB.1).trans (map_subtype_le _)
  have hRN : elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤
      normalizer ((twoCore d.H ⊔ A : Subgroup G) : Set G) :=
    (le_inf (hJH.trans (le_normalizer_twoCore d.H)) (hfam A hmax)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hlt := d.mixed_normalizer_card_lt hG T hM hTM hu hST hJS A hmax hAQ hRN
    (d.single_alternating_mixed_normalizer_escape hsingle hA A hmax hAQ)
  exact (Nat.not_lt_of_ge hcard hlt).elim
end CFSG.Quasithin.Chapter2
