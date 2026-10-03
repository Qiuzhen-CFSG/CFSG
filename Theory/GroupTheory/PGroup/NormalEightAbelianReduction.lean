module

public import Theory.GroupTheory.PGroup.NormalEightCentralFour
public import Theory.GroupTheory.PGroup.AbelianRankTwoHomocyclic

/-!
# Normal abelian reduction of the elementary order bound

In a finite two-group without normal elementary eights, the first omega of
any normal abelian subgroup has order at most four. If the central omega has
order four, a self-centralizing normal abelian subgroup has that same omega,
and hence is a product of two nontrivial cyclic two-groups.

Conjugation embeds the kernel of an elementary subgroup's action into the
first omega of the normal abelian subgroup. The kernel order is thus at most
four; bounding the action image by four suffices to bound the elementary
subgroup by sixteen. This module establishes the reduction, leaving that
image bound to separate structural arguments.

Source: the normal-abelian approach to the MacWilliams–Sah four-generator
bound, quoted in Janko–Thompson, Math. Z. 113 (1970), 1.1, printed p.385,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup

namespace IsPGroup

/-- First omega of a normal abelian subgroup has order at most four when no normal elementary eight exists. -/
public theorem card_omega_one_normal_abelian_le_four_of_no_normal_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D] :
    Nat.card (omega₁ D (p := 2)) ≤ 4 := by
  let O := omega₁ D (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let B := O.map D.subtype
  have hBn : B.Normal := ConjAct.normal_of_characteristic_of_normal
  have hBe : IsElementaryAbelian 2 B := IsElementaryAbelian.map_subtype
  have hlt : Nat.card O < 8 := by
    by_contra! h
    exact hno ⟨B, hBn, hBe, by
      simpa only [B, card_map_of_injective D.subtype_injective] using h⟩
  obtain ⟨n, hn⟩ := ((hP.to_subgroup D).to_subgroup O).exists_card_eq
  have hnlt : n < 3 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    simpa [← hn] using hlt
  change Nat.card O ≤ 4
  rw [hn]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 2))

/-- The first omega of a self-centralizing normal abelian subgroup is the central omega four. -/
public theorem omega_one_normal_abelian_eq_center_of_no_normal_eight
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D) :
    (omega₁ D (p := 2)).map D.subtype =
      (omega₁ (center P) (p := 2)).map (center P).subtype := by
  let O := omega₁ D (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let B := O.map D.subtype
  let : B.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map_subtype
  apply le_antisymm
  · exact normal_elementary_le_omega_center_of_no_normal_eight hno hZ B
  · rintro x ⟨z, hz, rfl⟩
    have hzD : (z : P) ∈ D := hD (center_le_centralizer _ z.property)
    refine ⟨⟨z, hzD⟩, subset_closure ?_, rfl⟩
    let : IsElementaryAbelian 2 (omega₁ (center P) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative _
    change (⟨(z : P), hzD⟩ : D) ^ (2 ^ 1) = 1
    apply Subtype.ext
    exact congrArg (fun a : center P => (a : P))
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz)

/-- The central-four case supplies a self-centralizing normal abelian subgroup with two cyclic factors. -/
public theorem exists_normal_abelian_two_cyclic_factors_of_no_normal_eight_of_center_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4) :
    ∃ D : Subgroup P, D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set P) ≤ D ∧ Nat.card (omega₁ D (p := 2)) = 4 ∧
      ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nonempty
        (D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) := by
  obtain ⟨D, hDn, hDa, hDC⟩ := exists_normal_abelian_selfCentralizing hP
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  have hEq := omega_one_normal_abelian_eq_center_of_no_normal_eight hno hZ D hDC
  have hcard : Nat.card (omega₁ D (p := 2)) = 4 := by
    have hc := congrArg (fun H : Subgroup P => Nat.card H) hEq
    simpa only [card_map_of_injective D.subtype_injective,
      card_map_of_injective (center P).subtype_injective, hZ] using hc
  exact ⟨D, hDn, hDa, hDC, hcard,
    (hP.to_subgroup D).equiv_two_cyclic_factors_of_card_omega_one_eq_four hcard⟩

end IsPGroup

namespace Subgroup

/-- The elementary subgroup order is bounded by its conjugation image order times the normal subgroup’s omega order. -/
public theorem card_le_omega_one_mul_conj_image_of_elementary
    {P : Type*} [Group P] [Finite P]
    (D : Subgroup P) [D.Normal]
    (hD : centralizer (D : Set P) ≤ D)
    (E : Subgroup P) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ Nat.card (omega₁ D (p := 2)) *
      Nat.card ((MulAut.conjNormal : P →* MulAut D).comp E.subtype).range := by
  let f := (MulAut.conjNormal : P →* MulAut D).comp E.subtype
  have hmem (x : f.ker) : ((x : E) : P) ∈ D := by
    apply hD
    intro d hd
    have hh := congrArg (fun t : MulAut D => (t ⟨d, hd⟩ : P))
      (MonoidHom.mem_ker.mp x.property)
    change (x : P) * d * (x : P)⁻¹ = d at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let j : f.ker → omega₁ D (p := 2) := fun x =>
    ⟨⟨x, hmem x⟩, subset_closure (by
      change (⟨(x : P), hmem x⟩ : D) ^ (2 ^ 1) = 1
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (x : P) (x : E).property)⟩
  have hj : Function.Injective j := by
    intro x y h
    have he := congrArg (fun z : omega₁ D (p := 2) => ((z : D) : P)) h
    exact Subtype.ext (Subtype.ext he)
  have hk := Nat.card_le_card_of_injective j hj
  have hc := f.ker.card_mul_index
  rw [index_ker] at hc
  change Nat.card E ≤ Nat.card (omega₁ D (p := 2)) * Nat.card f.range
  rw [← hc]
  exact Nat.mul_le_mul_right _ hk

end Subgroup
