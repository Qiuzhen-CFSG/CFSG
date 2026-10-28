module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer
/-!
# Normal elementary subgroups of Hall–Janko Sylow subgroups

Transport the supplied normal elementary subgroup to the certified Sylow.
Its ambient image lies in the distinguished four-group by the existing
literal word calculation, hence has order at most four.

Source: GLS3 Table 5.3g; the local A₈ exclusion in Aschbacher–Smith A.3.12,
printed pp.47–48.
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.J2
open ExceptionalParabolics
theorem sylow_normal_elementary_card_le_four (P : Sylow 2 Carrier) (E : Subgroup P) (hn : E.Normal)
    (he : IsElementaryAbelian 2 E) : Nat.card E ≤ 4 := by
  let a : P ≃* Seed.s := P.equiv (SecondParabolic.sylow FirstParabolic.card_l₁)
  let R := E.map a.toMonoidHom
  let : R.Normal := hn.map a.toMonoidHom a.surjective
  let : IsElementaryAbelian 2 E := he
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.map _
  let W := R.map Seed.s.subtype
  have hWn : (W.subgroupOf Seed.s).Normal := by
    have hRW : W.subgroupOf Seed.s = R :=
      comap_map_eq_self_of_injective Seed.s.subtype_injective R
    rw [hRW]
    infer_instance
  have hWe : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hb := card_le_of_le (RankOneFourNormalizer.normal_elementary_le_four
    W (map_subtype_le R) hWn hWe)
  rw [RankOneFourNormalizer.card_four,
    card_map_of_injective Seed.s.subtype_injective,
    card_map_of_injective a.injective] at hb
  exact hb
end Sporadic.LeechRelated.J2
