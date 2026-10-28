module
public import Theory.GroupTheory.CharacteristicNormalizerClosure
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The intersection of a controlled subgroup with a subnormal block

The characteristic-normalizer closure contains the original Sylow subgroup.
The two-core of any subnormal subgroup therefore lies in its intersection
with the controlled subgroup. If the quotient by that two-core has prime
order and the subgroup lies outside the controlled subgroup, this
intersection equals the two-core.

Source: Aschbacher–Smith C.1.29, printed p.134; this gives the A₃ Borel.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.LocalC129
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem sylow_le_of_characteristic_control (S : Sylow 2 G) (N : Subgroup G)
    (hN : (S : Subgroup G).characteristicNormalizerClosure ≤ N) :
    (S : Subgroup G) ≤ N := by
  by_cases hs : (S : Subgroup G) = ⊥
  · rw [hs]; exact bot_le
  · exact (S : Subgroup G).le_normalizer.trans
      ((normalizer_le_characteristicNormalizerClosure_self _ hs).trans hN)

theorem core_le_control_intersection (S : Sylow 2 G) (N L : Subgroup G)
    (hN : (S : Subgroup G).characteristicNormalizerClosure ≤ N)
    (hL : L.IsSubnormal) : pCore 2 L ≤ N.subgroupOf L := by
  have hh : (pCore 2 L).map L.subtype ≤ N :=
    (pCoreIn_le_of_subnormal 2 hL).trans
      ((pCore_isPGroup.le_sylow_of_normal S).trans
        (sylow_le_of_characteristic_control S N hN))
  exact map_le_iff_le_comap.mp hh

theorem prime_quotient_intersection_eq_core (S : Sylow 2 G) (N L : Subgroup G)
    (hN : (S : Subgroup G).characteristicNormalizerClosure ≤ N)
    (hL : L.IsSubnormal) (hout : ¬ L ≤ N)
    (hp : (Nat.card (L ⧸ pCore 2 L)).Prime) : N.subgroupOf L = pCore 2 L := by
  let q := QuotientGroup.mk' (pCore 2 L)
  have hk : q.ker ≤ N.subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    exact core_le_control_intersection S N L hN hL
  let : Fact (Nat.card (L ⧸ pCore 2 L)).Prime := ⟨hp⟩
  have hne : (N.subgroupOf L).map q ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.comap q) he
    rw [comap_map_eq_self hk, comap_top] at hh
    exact hout (subgroupOf_eq_top.mp hh)
  have he := ((N.subgroupOf L).map q).eq_bot_or_eq_top_of_prime_card.resolve_right hne
  have hh := congrArg (Subgroup.comap q) he
  rw [comap_map_eq_self hk] at hh
  change N.subgroupOf L = q.ker at hh
  simpa only [q, QuotientGroup.ker_mk'] using hh

end CFSG.Quasithin.ChapterC.LocalC129

