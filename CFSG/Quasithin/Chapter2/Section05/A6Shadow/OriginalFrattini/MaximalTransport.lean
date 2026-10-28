module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.OriginalFrattini.Setup
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.MaximalSylow
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Transport
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.Generation
public import Mathlib.Algebra.Group.Subgroup.Order

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

theorem EarlierSetup.sylow_isCoatom_of_image (d : EarlierSetup κ G)
    (hmax : IsCoatom (d.imageSylow : Subgroup AlternatingSix.ShadowLocal.AutA6)) :
    IsCoatom (d.S.subgroupOf d.H) := by
  have hSyl : (d.sylow : Subgroup d.H) = d.S.subgroupOf d.H := by
    rw [← d.sylow_eq, subgroupOf, comap_map_eq_self_of_injective d.H.subtype_injective]
  have hk : d.action.ker ≤ (d.sylow : Subgroup d.H) := by
    rw [hSyl, d.action_kernel]
    exact subgroupOf_mono d.H d.sc_le_s
  have hm := isCoatom_comap_of_surjective d.action_surjective hmax
  change IsCoatom (((d.sylow : Subgroup d.H).map d.action).comap d.action) at hm
  rwa [comap_map_eq_self hk, hSyl] at hm

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini

namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement A6Shadow.Frattini A6Shadow.OriginalFrattini
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.alternating_six_sylow_isCoatom_of_model
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6) :
    IsCoatom (((S : Subgroup H).map H.subtype).subgroupOf H) := by
  obtain ⟨d, hH, _, hS, _, _, _, _, _⟩ :=
    original_earlier_setup c hG hempty hgen hb hstar eK
  have hm := d.sylow_isCoatom_of_image
    (AlternatingSix.ShadowLocal.sylow_isCoatom d.imageSylow)
  have hm' : IsCoatom (((S : Subgroup H).map H.subtype).subgroupOf d.H) := hS ▸ hm
  exact hH ▸ hm'

theorem MathieuSourceSetup.alternating_six_rank_one_of_component_centralizers
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (t x : G) (ht : t ∈ twoCore H) (ht2 : orderOf t = 2)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hcomponents : ∀ i : G, i ∈ twoCore H → orderOf i = 2 →
      IsComponent (centralizer ({i} : Set G)) (K.subgroupOf (centralizer {i})))
    (hCt : H ⊓ centralizer ({MulAut.conj x t} : Set G) =
      (S : Subgroup H).map H.subtype)
    (hout : ∀ i : G, i ∈ twoCore H → orderOf i = 2 → i ≠ t →
      ¬ K ⊓ centralizer ({MulAut.conj x i} : Set G) ≤ (S : Subgroup H).map H.subtype)
    (htxK : MulAut.conj x t ∈ K)
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype) :
    primeRank 2 (twoCore H) = 1 := by
  let D := K.subgroupOf H
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D ((subgroupOfEquivOfLe c.component_le).trans eK) c.component
  have hmax := MathieuSourceSetup.alternating_six_sylow_isCoatom_of_model
    c hG hempty hgen hb hstar eK
  have hcentral := A6Shadow.centralizer_eq_of_original_component
    c hG hempty hgen hb hstar t ht2 ht htZ eK
  have hSC : twoCore H ≤ centralizer (K : Set G) := by
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact inf_le_right
  exact A6ShadowRankOne.primeRank_eq_one_of_component_centralizers
    hG.quasithin K H ((S : Subgroup H).map H.subtype) (twoCore H) t x eK
    c.component_le (map_subtype_le _) hcentral hSC (isPGroup_pCoreIn 2 H)
    ht ht2 hcomponents hmax hCt hout htxK (by simpa only [pow_two] using hx2)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
