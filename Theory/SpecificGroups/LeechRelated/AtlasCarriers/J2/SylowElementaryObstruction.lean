module

public import Theory.GroupTheory.UniqueElementarySubgroups
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer

/-!
# The Hall–Janko Sylow has no unique elementary sixteen

A unique elementary sixteen would be characteristic, hence normal. The
checked Hall–Janko Sylow calculation puts every normal elementary subgroup
inside its distinguished four-group. These orders contradict one another.
Source: the sporadic exclusion in Aschbacher–Smith F.6.18, printed p.310.
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.J2
open Theory.GroupTheory ExceptionalParabolics Seed

theorem not_unique_sylow_elementary_sixteen :
    ¬ ∃! E : Subgroup s, IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  rintro ⟨E, ⟨hE,hc⟩,hu⟩
  let := hE
  let : E.Characteristic := characteristic_of_unique_elementary_subgroup E hE hc hu
  let : E.Normal := inferInstance
  let W := E.map s.subtype
  have hWs : W ≤ s := map_subtype_le E
  have hWn : (W.subgroupOf s).Normal := by
    have he : W.subgroupOf s = E := by
      exact comap_map_eq_self_of_injective s.subtype_injective E
    rw [he]
    infer_instance
  have hWe : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hb := card_le_of_le (RankOneFourNormalizer.normal_elementary_le_four W hWs hWn hWe)
  rw [RankOneFourNormalizer.card_four, card_map_of_injective s.subtype_injective, hc] at hb
  omega
end Sporadic.LeechRelated.J2

namespace Sporadic.LeechRelated.J2
open Theory.GroupTheory ExceptionalParabolics

theorem sylow_not_unique_elementary_sixteen (P : Sylow 2 Carrier) :
    ¬ ∃! E : Subgroup P, IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  intro h
  exact not_unique_sylow_elementary_sixteen
    (existsUnique_elementary_subgroup_of_equiv
      (P.equiv (SecondParabolic.sylow FirstParabolic.card_l₁)) h)
end Sporadic.LeechRelated.J2
