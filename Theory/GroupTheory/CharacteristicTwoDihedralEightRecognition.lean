module

public import Theory.GroupTheory.IndexTwoIntersection
public import Theory.GroupTheory.SelfCentralizingTwoSubgroupSize
public import Theory.GroupTheory.SpecificGroups.DihedralAut
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual

/-!
# Characteristic-two recognition with a dihedral Sylow of order eight

Characteristic two passes to subnormal subgroups by monotonicity of the
intrinsic generalized Fitting subgroup. A characteristic-two group of order
24 with a dihedral Sylow is S4: its self-centralizing two-core has order four
or eight; the latter would make its automorphism group a two-group, contrary
to the faithful cubic action. This supplies the residual vertex restrictions
in Aschbacher--Smith F.6.18(9), printed p.310.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory

/-- Characteristic two passes to the actual subnormal subgroup. -/
theorem characteristic_two_of_subnormal {G : Type*} [Group G] [Finite G]
    (hgood : generalizedFitting G = pCore 2 G)
    (N : Subgroup G) (hN : N.IsSubnormal) :
    generalizedFitting N = pCore 2 N := by
  have hle : (generalizedFitting N).map N.subtype ≤ pCore 2 G :=
    (generalizedFitting_map_subtype_le_of_isSubnormal N hN).trans hgood.le
  have hp : IsPGroup 2 (generalizedFitting N) :=
    (pCore_isPGroup.to_le hle).of_equiv
      ((generalizedFitting N).equivMapOfInjective N.subtype N.subtype_injective).symm
  exact le_antisymm (le_sSup ⟨inferInstance, hp⟩)
    ((pCore_le_fitting N 2).trans (fitting_le_generalizedFitting N))

/-- A characteristic-two group of order 24 with dihedral Sylow is S4. -/
theorem symmetric_four_of_characteristic_two_card_twentyfour {G : Type*} [Group G] [Finite G]
    (hgood : generalizedFitting G = pCore 2 G)
    (hcard : Nat.card G = 24) (S : Sylow 2 G) (eS : S ≃* DihedralGroup 4) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  let Q := pCore 2 G
  have hself : centralizer (Q : Set G) ≤ Q := by
    simpa only [hgood] using centralizer_generalizedFitting_le G
  have hQ4 : 4 ≤ Nat.card Q := card_ge_four_of_selfCentralizing_normal_two_subgroup
    Q pCore_isPGroup hself (by rw [hcard]; decide)
  have hQS : Q ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have hS8 : Nat.card S = 8 := by
    rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
  have hQdvd : Nat.card Q ∣ 8 := hS8 ▸ card_dvd_of_le hQS
  have hQcard : Nat.card Q = 4 := by
    have hcases : Nat.card Q = 4 ∨ Nat.card Q = 8 := by
      have := Nat.le_of_dvd (by decide : 0 < 8) hQdvd
      interval_cases h : Nat.card Q <;> norm_num [h] at *
    rcases hcases with hc | hc
    · exact hc
    · have heq : Q = (S : Subgroup G) := eq_of_le_of_card_ge hQS (by omega)
      let e : Q ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr heq).trans eS
      have hAut : IsPGroup 2 (MulAut Q) :=
        (DihedralGroup.isPGroup_mulAut_of_two_lt (by decide : 2 < 4)
          (IsPGroup.of_card (n := 3) (by rw [DihedralGroup.nat_card]; norm_num))).of_equiv
            (MulAut.congr e).symm
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hcard]; decide)
      have ha : MulAut.conjNormal (H := Q) x = 1 := by
        have hd : orderOf (MulAut.conjNormal (H := Q) x) ∣ 3 :=
          hx ▸ orderOf_map_dvd MulAut.conjNormal x
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
          (hAut.orderOf_coprime (by decide : Nat.Coprime 2 3) _) dvd_rfl hd)
      have hxQ : x ∈ Q := hself (mem_centralizer_iff.mpr (fun q hq => by
        have hh := congrArg (fun a : MulAut Q => (a ⟨q, hq⟩ : G)) ha
        change x * q * x⁻¹ = q at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm))
      have hz := (pCore_isPGroup (p := 2) (G := G)).orderOf_coprime
        (by decide : Nat.Coprime 2 3) (⟨x, hxQ⟩ : Q)
      rw [← Subgroup.orderOf_coe, hx] at hz
      norm_num at hz
  exact mulEquiv_perm_four_of_selfCentralizing_normal_four Q
    pCore_isPGroup hQcard hself hcard

variable {G : Type*} [Group G] [Finite G]

/-- A characteristic-two subgroup of order 48 crossing a normal index-two
subgroup restricts to S4 when its common Sylow restriction is D8. -/
theorem symmetric_four_intersection_of_characteristic_two
    (K A : Subgroup G) [K.Normal] (hK : K.index = 2)
    (hgood : generalizedFitting A = pCore 2 A) (hA : Nat.card A = 48)
    (hcross : ¬ A ≤ K) (S : Sylow 2 K) (eS : S ≃* DihedralGroup 4)
    (hSA : (S : Subgroup K) ≤ A.subgroupOf K) :
    Nonempty (A.subgroupOf K ≃* Equiv.Perm (Fin 4)) := by
  let N := K.subgroupOf A
  let M := A.subgroupOf K
  let a : M ≃* N := {
    toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hN : generalizedFitting N = pCore 2 N :=
    characteristic_two_of_subnormal hgood N (inferInstance : N.Normal).isSubnormal
  have hc : Nat.card N = 24 := by
    have hi : N.index = 2 := K.subgroupOf_index_eq_two A hK hcross
    have hh := N.card_mul_index
    rw [hi, hA] at hh
    omega
  let U := S.subtype hSA
  let b : U ≃* S := subgroupOfEquivOfLe hSA
  let V := U.mapSurjective (f := a.toMonoidHom) a.surjective
  let c : U ≃* V := a.subgroupMap (U : Subgroup M)
  obtain ⟨e⟩ := symmetric_four_of_characteristic_two_card_twentyfour hN hc V
    ((c.symm.trans b).trans eS)
  exact ⟨a.trans e⟩


end Theory.GroupTheory
