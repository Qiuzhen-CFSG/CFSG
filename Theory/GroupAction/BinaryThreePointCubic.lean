module
public import Theory.GroupAction.PerfectFixedCover
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Calculations

/-!
# Cubics fixing a point in a binary natural module

Every vector in the natural SL3(2) module has a cubic in its stabilizer.
A surjection with two-group kernel lifts a cubic into that stabilizer by
Cauchy's theorem, and the lift has nontrivial quotient image. If an external
coprime actor fixes the quotient, its actual fixed subgroup still surjects;
this yields the cubic inside that fixed subgroup without splitting the group.

The intended application is the original binary point centralizer in
Aschbacher–Smith 15.3.23, with the external actor of order three.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.GroupAction.BinaryThreePointCubic
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
local notation "W" => Fin 3 → ZMod 2

private theorem model_cubic (v : W) :
    ∃ c : SL, orderOf c = 3 ∧ c • v = v := by
  let c := Matrix.PSL3Two.MarkedAutomorphisms.cubic
  have hc : orderOf c = 3 := orderOf_eq_prime
    Matrix.PSL3Two.MarkedAutomorphisms.cubic_cube (by decide +kernel)
  by_cases hv : v = 0
  · exact ⟨c,hc,by rw [hv]; exact smul_zero _⟩
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    (![1,0,0] : W) v (by decide) hv
  change g • (![1,0,0] : W) = v at hg
  have hfix : c • (![1,0,0] : W) = (![1,0,0] : W) := by decide +kernel
  refine ⟨(MulAut.conj g) c,?_,?_⟩
  · exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c).trans hc
  · change (g * c * g⁻¹) • v = v
    rw [←hg,mul_smul,mul_smul,inv_smul_smul,hfix]

theorem exists_cubic_fixing_vector {J : Type*} [Group J] [Finite J]
    (π : J →* SL) (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (v : W) : ∃ c : J, orderOf c = 3 ∧ π c ≠ 1 ∧ (π c) • v = v := by
  obtain ⟨b,hb,hbv⟩ := model_cubic v
  let P := MulAction.stabilizer SL v
  have hD : zpowers b ≤ P := zpowers_le.mpr hbv
  have hdiv : 3 ∣ Nat.card P := by
    simpa only [Nat.card_zpowers,hb] using card_dvd_of_le hD
  let C := P.comap π
  have hdivC : 3 ∣ Nat.card C := hdiv.trans
    (card_dvd_of_surjective (π.subgroupComap P) (π.subgroupComap_surjective_of_surjective P hπ))
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hdivC
  have hcJ : orderOf (c : J) = 3 := (Subgroup.orderOf_coe c).trans hc
  refine ⟨c,hcJ,?_,c.property⟩
  intro he
  have hm : (c : J) ∈ π.ker := he
  have hcop := hker.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨c,hm⟩ : π.ker)
  have ho : orderOf (⟨c,hm⟩ : π.ker) = 3 := (Subgroup.orderOf_coe _).symm.trans hcJ
  rw [ho] at hcop
  norm_num at hcop

theorem fixedPoints_surjective {J A K : Type*}
    [Group J] [Finite J] [Group A] [Finite A] [Group K]
    [MulDistribMulAction A J]
    (π : J →* K) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card π.ker))
    (htriv : ∀ a : A, ∀ j : J, π (a • j) = π j) :
    Function.Surjective (π.comp (FixedPoints.subgroup A J).subtype) := by
  let : IsInvariant A J π.ker := ⟨fun a j => by
    change π j = 1 ↔ π (a • j) = 1
    rw [htriv]⟩
  have hsolv : Group.IsSolvable π.ker := by
    let := hker.isNilpotent
    infer_instance
  intro k
  obtain ⟨j,rfl⟩ := hπ k
  obtain ⟨n,hn⟩ := Theory.GroupAction.exists_fixed_mul_of_solvable_coprime_displacement
    π.ker hsolv hcop j (fun a => by
      change π (j⁻¹ * (a • j)) = 1
      rw [map_mul,map_inv,htriv,inv_mul_cancel])
  refine ⟨⟨j * n,hn⟩,?_⟩
  change π (j * n) = π j
  rw [map_mul,show π (n : J) = 1 from n.property,mul_one]

theorem exists_fixed_cubic_fixing_vector {J A : Type*}
    [Group J] [Finite J] [Group A] [Finite A]
    [MulDistribMulAction A J]
    (π : J →* SL) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card π.ker))
    (htriv : ∀ a : A, ∀ j : J, π (a • j) = π j)
    (v : W) : ∃ c : J, c ∈ FixedPoints.subgroup A J ∧
      orderOf c = 3 ∧ π c ≠ 1 ∧ (π c) • v = v := by
  let C := FixedPoints.subgroup A J
  let f := π.comp C.subtype
  have hf := fixedPoints_surjective π hπ hker hcop htriv
  have hk : IsPGroup 2 f.ker := hker.comap_of_injective C.subtype C.subtype_injective
  obtain ⟨c,hc,hcn,hcv⟩ := exists_cubic_fixing_vector f hf hk v
  exact ⟨c,c.property,(Subgroup.orderOf_coe c).trans hc,hcn,hcv⟩

end Theory.GroupAction.BinaryThreePointCubic
