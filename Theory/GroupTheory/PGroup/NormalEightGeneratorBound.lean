module

public import Theory.Frattini.SubgroupIndexBound
public import Theory.GroupTheory.PGroup.RelativeNormalAbelian
public import Theory.GroupTheory.PGroup.NormalEightAbelianReduction
public import Theory.GroupTheory.PGroup.OmegaImage
public import Theory.GroupTheory.PGroup.SymplecticNormalAbelianIndex

/-!
# The normal-subgroup four-generator bound for binary symplectic groups

Inside a normal subgroup `U` of a finite two-group `P`, choose an abelian
subgroup normal in `P` and self-centralizing in `U`. If `P` has no normal
elementary subgroup of order at least eight, this abelian subgroup has first
omega of order at most four. An intrinsic index bound of four then bounds
`|U/Φ(U)|` by sixteen using `SubgroupIndexBound`.

For `U` of binary symplectic type with cyclic center, the intrinsic index
bound follows from `SymplecticNormalAbelianIndex`, completing this specialization
of the four-generator theorem. No inheritance of the ambient normal-elementary
hypothesis by `U` is used.

Source: the four-generator theorem of MacWilliams and Sah, quoted in
Janko–Thompson, Math. Z. 113 (1970), result 1.1, printed p.385, and applied
on printed p.389. The source is
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup

namespace IsPGroup

/-- Choose the abelian subgroup inside `U` while retaining normality in `P`,
so that the ambient exclusion of elementary eights bounds its omega order. -/
public theorem exists_ambient_normal_abelian_omega_le_four_of_no_normal_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (U : Subgroup P) [U.Normal] :
    ∃ A : Subgroup U, (A.map U.subtype).Normal ∧ A.Normal ∧
      IsMulCommutative A ∧ centralizer (A : Set U) ≤ A ∧
      Nat.card (omega₁ A (p := 2)) ≤ 4 := by
  obtain ⟨D, hDU, hDn, hDa, hDc⟩ :=
    exists_ambient_normal_abelian_selfCentralizing hP U
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  let A := D.subgroupOf U
  let e : A ≃* D := subgroupOfEquivOfLe hDU
  let : IsMulCommutative A := IsMulCommutative.of_comm fun x y => by
    apply e.injective
    simp only [map_mul]
    exact IsMulCommutative.is_comm.comm (e x) (e y)
  have hmap : A.map U.subtype = D := map_subgroupOf_eq_of_le hDU
  refine ⟨A, hmap.symm ▸ hDn, inferInstance, inferInstance, ?_, ?_⟩
  · intro x hx
    apply hDc
    refine ⟨x.property, ?_⟩
    intro d hd
    exact congrArg Subtype.val (hx ⟨d, hDU hd⟩ hd)
  · have hcard := Nat.card_congr (e.omega 2 1).toEquiv
    change Nat.card (omega₁ A (p := 2)) = Nat.card (omega₁ D (p := 2)) at hcard
    rw [hcard]
    exact hP.card_omega_one_normal_abelian_le_four_of_no_normal_eight hno D

/-- An intrinsic index bound on normal abelian self-centralizers completes
the ambient-normal Frattini bound. -/
public theorem normal_subgroup_frattini_card_le_sixteen_of_abelian_index_bound
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (U : Subgroup P) [U.Normal]
    (hindex : ∀ A : Subgroup U, A.Normal → IsMulCommutative A →
      centralizer (A : Set U) ≤ A → Nat.card (omega₁ A (p := 2)) ≤ 4 →
      A.index ≤ 4) :
    Nat.card (U ⧸ frattini U) ≤ 16 := by
  obtain ⟨A, -, hAn, hAa, hAc, hAo⟩ :=
    hP.exists_ambient_normal_abelian_omega_le_four_of_no_normal_eight hno U
  let : IsMulCommutative A := hAa
  have hi := hindex A hAn hAa hAc hAo
  exact ((hP.to_subgroup U).card_frattini_quotient_le_index_mul_omega_one A).trans
    (by simpa using Nat.mul_le_mul hi hAo)

/-- A normal subgroup of binary symplectic type with cyclic center needs at
most four generators when the ambient two-group has no normal elementary
subgroup of order at least eight. -/
public theorem normal_subgroup_frattini_card_le_sixteen_of_symplectic_type
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (U : Subgroup P) [U.Normal] [IsCyclic (center U)]
    (hsymp : IsBinarySymplecticType U) :
    Nat.card (U ⧸ frattini U) ≤ 16 := by
  apply hP.normal_subgroup_frattini_card_le_sixteen_of_abelian_index_bound hno U
  intro A hAn hAa hAc hAo
  let : A.Normal := hAn
  let : IsMulCommutative A := hAa
  exact (hP.to_subgroup U).normal_abelian_index_le_four_of_symplectic_type
    hsymp A hAc hAo

end IsPGroup
