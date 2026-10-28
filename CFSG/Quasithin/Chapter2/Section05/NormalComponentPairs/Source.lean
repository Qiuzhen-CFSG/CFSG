module

public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.FourConstruction
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.NormalizerIdentification
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallFourSource
public import Theory.GroupTheory.CentralizerNormalSupplement

/-!
# Original normal-component pairs are four-group normalizers

The source component is centerless, normal and supplements the original
Sylow subgroup. Its centralizer is consequently a normal two-subgroup and
lies in that Sylow. The actual model theorem then puts every four-group
centralizer in the same Sylow. Applying the moving central projection and
the largest-pair normalizer argument gives both literal normalizer identities.
All marking, rank and centralizer premises are discharged on the original
Chapter 2 tuple; no pair-classification conclusion is an input.
Source: Aschbacher--Smith 2.5.8(2), 2.5.12(1), printed pp.556--558.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open ClassificationModels
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentSelection ComponentRefinement
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

/-- The whole source component centralizer lies in the original Sylow. -/
theorem normal_component_centralizer_le_source_sylow
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) :
    H ⊓ centralizer (K : Set G) ≤ (S : Subgroup H).map H.subtype := by
  have hc := ComponentSelection.MathieuSourceSetup.component_center_eq_bot c hG hempty hgen
  let e := subgroupOfEquivOfLe c.component_le
  have hz : center (K.subgroupOf H) = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    have he := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center K at he
    rw [hc] at he
    exact (mem_bot.mp he).trans (map_one e).symm
  have hg : K.subgroupOf H ⊔ (S : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le c.component_le, ← hgen,
      ← MonoidHom.range_eq_map, range_subtype]
  have hh := centralizer_le_sylow_of_normal_centerless_sup (K.subgroupOf H) S hz hg
  intro x hx
  refine ⟨⟨x,hx.1⟩,hh ?_,rfl⟩
  intro k hk
  exact Subtype.ext (hx.2 k hk)

/-- Original 2.5.12(1): every largest pair below S is its actual four normalizer. -/
theorem largest_pair_four_normalizers_of_source
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H)
    (hUS : U ≤ (S : Subgroup H).map H.subtype) :
    ∃ E : Subgroup G, E ≤ (S : Subgroup H).map H.subtype ⊓ K ∧ IsKleinFour E ∧
      L = H ⊓ normalizer (E : Set G) ∧
      U = (S : Subgroup H).map H.subtype ⊓ normalizer (E : Set G) ∧ E ≤ twoCore L := by
  obtain ⟨E,hES,hE,hLN,hEc⟩ := largest_pair_exists_normal_four_of_source
    c hG hempty hgen hb hp hUS
  let := hE
  have hm := ComponentSelection.MathieuSourceSetup.small_remaining_component c hG hempty hgen hb
  have hC := ComponentSelection.MathieuSourceSetup.four_centralizer_le_source_sylow c hm
    (normal_component_centralizer_le_source_sylow c hG hempty hgen) E
    (hES.trans inf_le_left) (hES.trans inf_le_right)
  have hn := largest_pair_eq_four_normalizer hp hUS (S.isPGroup'.map H.subtype)
    (c.sylow_lt.le.trans c.sylow_le) (map_subtype_le _) ((hES.trans inf_le_right).trans c.component_le)
    hLN hC
  exact ⟨E,hES,hE,hn.1,hn.2,hEc⟩

end CFSG.Quasithin.Chapter2.Section05
