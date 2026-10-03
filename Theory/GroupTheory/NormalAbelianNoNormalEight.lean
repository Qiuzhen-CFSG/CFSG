module

public import Theory.GroupTheory.PGroup.AbelianOmega
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Normal abelian two-subgroups without normal elementary eights

A normal abelian two-subgroup is cyclic if the ambient group has neither
normal elementary fours nor normal elementary subgroups of order at least
eight. Only its characteristic first omega subgroup needs a cardinal bound.
This normal-only variant of `RankTwoNormalAbelian` supplies Hall's
symplectic-type criterion in Janko–Thompson (1970), §4, p.389.
-/

namespace Subgroup

/-- A normal abelian two-subgroup of normal elementary rank at most two is cyclic
when the ambient group has no normal elementary four-group. -/
public theorem isCyclic_of_normal_abelian_of_no_normal_four_or_eight
    {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) [B.Normal] [IsMulCommutative B] (hB : IsPGroup 2 B)
    (hrank : ∀ D : Subgroup G, D.Normal → IsElementaryAbelian 2 D → Nat.card D < 8)
    (hno : ∀ U : Subgroup G, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4) :
    IsCyclic B := by
  let O := omega₁ B (p := 2)
  let : O.Characteristic := omega₁_characteristic B
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative B
  let D := O.map B.subtype
  let : D.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map_subtype
  have hlt : Nat.card O < 8 := by
    have h := hrank D inferInstance inferInstance
    rwa [card_map_of_injective B.subtype_injective] at h
  have hne : Nat.card O ≠ 4 := by
    have h := hno D inferInstance inferInstance
    rwa [card_map_of_injective B.subtype_injective] at h
  apply hB.isCyclic_of_card_omega_one_le_two
  obtain ⟨n, hn⟩ := (hB.to_subgroup O).exists_card_eq
  have hnlt : n < 3 := by
    by_contra! h
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) h
    omega
  change Nat.card O ≤ 2
  interval_cases n <;> simp only [pow_zero, pow_one, Nat.reducePow] at hn <;> omega

/-- Every characteristic abelian subgroup of a normal two-subgroup is cyclic
under the normal rank-two bound and the absence of ambient normal four-groups. -/
public theorem isCyclic_characteristic_abelian_of_no_normal_four_or_eight
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hrank : ∀ D : Subgroup G, D.Normal → IsElementaryAbelian 2 D → Nat.card D < 8)
    (hno : ∀ U : Subgroup G, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (B : Subgroup Q) [B.Characteristic] [IsMulCommutative B] : IsCyclic B := by
  let K := B.map Q.subtype
  let : K.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsMulCommutative K := Subgroup.map_isMulCommutative (H := B) Q.subtype
  have hK : IsCyclic K := isCyclic_of_normal_abelian_of_no_normal_four_or_eight K
    ((hQ.to_subgroup B).map Q.subtype)
    hrank hno
  exact (B.equivMapOfInjective Q.subtype Q.subtype_injective).isCyclic.mpr hK

end Subgroup
