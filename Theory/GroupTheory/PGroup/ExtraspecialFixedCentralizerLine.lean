module

public import Theory.GroupTheory.PGroup.NormalExtraspecialDerivedCenter

/-!
# Characteristic central lines of extraspecial fixed cores

Let a normal subgroup have abelian quotient. If its fixed subgroup under an
inner automorphism is extraspecial, the full centralizer has derived-center
intersection equal to the extraspecial center. Any central involution in the
normal subgroup therefore generates this characteristic line.

The proof restricts the abelian quotient to the centralizer, applies the
normal extraspecial derived-center theorem, and identifies the resulting
order-two subgroup by its central involution.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, case (b)(i), printed p.391.
-/

namespace Subgroup

/-- An extraspecial fixed core determines the characteristic central line
in the full centralizer. -/
public theorem centralizer_derived_inf_center_line_of_extraspecial_fixed
    {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [H.Normal] [IsMulCommutative (P ⧸ H)]
    (z t : P) (hz : orderOf z = 2) (hzc : z ∈ center P) (hzH : z ∈ H)
    [IsExtraspecial 2 (H.subgroupOf (centralizer ({t} : Set P)))] :
    (_root_.commutator (centralizer ({t} : Set P)) ⊓
      center (centralizer ({t} : Set P))).map
      (centralizer ({t} : Set P)).subtype = zpowers z := by
  let E := centralizer ({t} : Set P)
  let D := H.subgroupOf E
  have hder : _root_.commutator E ≤ D := by
    apply map_le_iff_le_comap.mp
    rw [map_subtype_commutator]
    exact (commutator_mono le_top le_top).trans
      (Normal.quotient_commutative_iff_commutator_le.mp inferInstance)
  let : IsMulCommutative (E ⧸ D) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hder
  change (_root_.commutator E ⊓ center E).map E.subtype = zpowers z
  rw [derived_inf_center_eq_of_normal_extraspecial D]
  have hzE : z ∈ E := mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzc t).symm
  let zE : E := ⟨z, hzE⟩
  let zD : D := ⟨zE, hzH⟩
  have hzD : zD ∈ center D := by
    apply mem_center_iff.mpr
    intro d
    apply Subtype.ext
    apply Subtype.ext
    exact mem_center_iff.mp hzc d
  have hle : zpowers z ≤ ((center D).map D.subtype).map E.subtype :=
    zpowers_le.mpr (mem_map_of_mem E.subtype (mem_map_of_mem D.subtype hzD))
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective E.subtype_injective,
    card_map_of_injective D.subtype_injective, IsExtraspecial.center_order_p 2 D,
    Nat.card_zpowers, hz]

end Subgroup
