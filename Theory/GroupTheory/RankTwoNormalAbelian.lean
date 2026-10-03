module

public import Theory.GroupTheory.PGroup.AbelianOmega
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Normal abelian subgroups under a binary rank bound

Suppose a finite group has no normal elementary four-group. An abelian normal
two-subgroup of elementary rank at most two is cyclic: its characteristic
first omega subgroup is elementary and normal in the ambient group. The rank
bound gives its order at most four, and the absence of a normal four reduces
this to at most two. The abelian omega criterion then gives cyclicity.

Applied to characteristic abelian subgroups of a normal two-subgroup, this
supplies the hypothesis of Philip Hall's symplectic-type theorem, GLS2,
Theorem 10.3 (`refs/KGroup/GLS2/ChapterC.tex`). No structural classification
is used here.
-/

namespace Subgroup

/-- A normal abelian two-subgroup of elementary rank at most two is cyclic
when the ambient group has no normal elementary four-group. -/
public theorem isCyclic_of_normal_abelian_of_no_normal_four
    {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) [B.Normal] [IsMulCommutative B] (hB : IsPGroup 2 B)
    (hrank : ∀ D : Subgroup G, IsElementaryAbelian 2 D → D ≤ B → Nat.card D < 8)
    (hno : ∀ U : Subgroup G, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4) :
    IsCyclic B := by
  let O := omega₁ B (p := 2)
  let : O.Characteristic := omega₁_characteristic B
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative B
  let D := O.map B.subtype
  let : D.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map_subtype
  have hlt : Nat.card O < 8 := by
    have h := hrank D inferInstance (map_subtype_le O)
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
under the rank-two bound and the absence of ambient normal four-groups. -/
public theorem isCyclic_characteristic_abelian_of_no_normal_four
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hrank : ∀ D : Subgroup G, IsElementaryAbelian 2 D → D ≤ Q → Nat.card D < 8)
    (hno : ∀ U : Subgroup G, U.Normal → IsElementaryAbelian 2 U → Nat.card U ≠ 4)
    (B : Subgroup Q) [B.Characteristic] [IsMulCommutative B] : IsCyclic B := by
  let K := B.map Q.subtype
  let : K.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsMulCommutative K := Subgroup.map_isMulCommutative (H := B) Q.subtype
  have hK : IsCyclic K := isCyclic_of_normal_abelian_of_no_normal_four K
    ((hQ.to_subgroup B).map Q.subtype)
    (fun D hD hDK => hrank D hD (hDK.trans (map_subtype_le B))) hno
  exact (B.equivMapOfInjective Q.subtype Q.subtype_injective).isCyclic.mpr hK

end Subgroup
