module

public import Theory.GroupTheory.CharacteristicCyclicCentralizerAutomorphisms
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrder
public import Theory.GroupTheory.PGroup.ExtraspecialCyclicOmegaTwo
public import Theory.GroupTheory.PGroup.LargeHallRotationStructure

/-!
# Odd automorphisms of large Hall central products

A characteristic nonabelian subgroup of order sixteen with cyclic centralizer
detects every odd automorphism subgroup of a finite two-group faithfully.
The small nonabelian automorphism bound therefore makes its order divide three.
For a central product of an extraspecial group of order eight and a large
noncyclic binary Hall factor, the rotation product is characteristic. Its second
omega supplies this subgroup of order sixteen. Neither displayed factor needs
to be characteristic, and no rank or width exclusion is required.

This is the action reduction for large Hall central products in
Janko–Thompson, Math. Z. 113 (1970), §4, p.392. The final theorem combines the
structural construction of the characteristic subgroup with this reduction.
-/

namespace Subgroup

/-- A small characteristic nonabelian subgroup with cyclic centralizer bounds
the odd automorphism subgroups of its ambient two-group. -/
public theorem odd_automorphism_card_dvd_three_of_characteristic_sixteen
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (N : Subgroup P) [N.Characteristic]
    [IsCyclic (centralizer (N : Set P))]
    (hnoncomm : ¬ IsMulCommutative N) (hcard : Nat.card N = 16)
    (U : Subgroup (MulAut P)) (hodd : Odd (Nat.card U)) :
    Nat.card U ∣ 3 := by
  let f := (MulAut.characteristic N).comp U.subtype
  have hker : IsPGroup 2 f.ker :=
    (isPGroup_characteristic_restriction_kernel_of_cyclic_centralizer hP N).comap_of_injective
      U.subtype U.subtype_injective
  have hinj : Function.Injective f := by
    obtain ⟨n, hn⟩ := hker.exists_card_dvd_pow
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply Subgroup.card_eq_one.mp
    exact Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_right.pow_right n)
      f.ker.card_subgroup_dvd_card hn
  have hsize : Nat.card f.range = Nat.card U :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hbound := SmallNonabelianTwoGroup.small_nonabelian_two_group_odd_order_bound
    (hP.to_subgroup N) hnoncomm (by omega)
    (by omega) f.range (hsize.symm ▸ hodd)
  rw [hsize] at hbound
  simpa only [hcard, show (16 : ℕ) ≠ 32 by decide, if_false] using hbound

/-- Odd automorphism subgroups of a central product of an extraspecial group
of order eight and a noncyclic binary Hall factor of order at least sixteen
have order dividing three, provided the ambient two-group has cyclic center. -/
public theorem odd_automorphism_card_dvd_three_of_large_hall_central_product
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (A D : Subgroup P) [A.Normal] [D.Normal]
    [IsExtraspecial 2 A] (hA : Nat.card A = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (A : Set P)) (hg : A ⊔ D = ⊤)
    (hlarge : 16 ≤ Nat.card D)
    (U : Subgroup (MulAut P)) (hodd : Odd (Nat.card U)) :
    Nat.card U ∣ 3 := by
  obtain ⟨B, hBn, hBc, hB, hBD, hM, hcut⟩ :=
    exists_characteristic_rotation_product_of_large_hall hP A D hD hn hc hg hlarge
  let : B.Normal := hBn
  let : IsCyclic B := hBc
  obtain ⟨N, hN, hnoncomm, hcard, hcent⟩ :=
    exists_characteristic_sixteen_of_extraspecial_cyclic_product hP A B hA
      (by omega) (hBD.trans hc) hM hcut
  let : N.Characteristic := hN
  let : IsCyclic (centralizer (N : Set P)) := hcent
  exact odd_automorphism_card_dvd_three_of_characteristic_sixteen
    hP N hnoncomm hcard U hodd

end Subgroup
