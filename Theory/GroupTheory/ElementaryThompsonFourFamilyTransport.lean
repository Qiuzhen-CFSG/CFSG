module
public import Theory.GroupTheory.ElementaryThompsonFourFamily
public import Theory.ElementaryAbelian.Injective
/-!
# Ambient transport of a four-member elementary square

Subgroup inclusion preserves the intersections, relative indices and crossing
commutators in the C.6.1 count. Elementary subgroups pull back along it.

Source: Aschbacher–Smith C.6.1, printed p.165.
-/
public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G]
theorem FourFamilyGeometry.map_subtype (S : Subgroup G) (Q Q' P P' I : Subgroup S)
    (h : FourFamilyGeometry (⊤ : Subgroup S) Q Q' P P' I) :
    FourFamilyGeometry S (Q.map S.subtype) (Q'.map S.subtype)
      (P.map S.subtype) (P'.map S.subtype) (I.map S.subtype) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro B hBS hB
    let : IsElementaryAbelian 2 B := hB
    have hi : IsElementaryAbelian 2 (B.subgroupOf S) := IsElementaryAbelian.subgroupOf hBS
    rcases h.cover (B.subgroupOf S) le_top hi with hh | hh | hh | hh
    · exact Or.inl ((map_subgroupOf_eq_of_le hBS).symm ▸ map_mono hh)
    · exact Or.inr (Or.inl ((map_subgroupOf_eq_of_le hBS).symm ▸ map_mono hh))
    · exact Or.inr (Or.inr (Or.inl ((map_subgroupOf_eq_of_le hBS).symm ▸ map_mono hh)))
    · exact Or.inr (Or.inr (Or.inr ((map_subgroupOf_eq_of_le hBS).symm ▸ map_mono hh)))
  · rw [←Subgroup.map_inf _ _ _ S.subtype_injective,h.opposite_first]
  · rw [←Subgroup.map_inf _ _ _ S.subtype_injective,h.opposite_second]
  · simpa only [relIndex_map_map_of_injective _ _ S.subtype_injective] using h.adjacent_left
  · simpa only [relIndex_map_map_of_injective _ _ S.subtype_injective] using h.adjacent_right
  · simpa only [card_map_of_injective S.subtype_injective] using h.core_card
  · rw [←Subgroup.map_inf _ _ _ S.subtype_injective,←Subgroup.map_inf _ _ _ S.subtype_injective,
      ←map_commutator]
    exact map_mono h.first_cross_le
  · rw [←Subgroup.map_inf _ _ _ S.subtype_injective,←Subgroup.map_inf _ _ _ S.subtype_injective,
      ←Subgroup.map_inf _ _ _ S.subtype_injective,←Subgroup.map_inf _ _ _ S.subtype_injective,
      ←map_commutator,←map_commutator]
    exact fun he => h.cross_ne (map_injective S.subtype_injective he)
end Stellmacher
