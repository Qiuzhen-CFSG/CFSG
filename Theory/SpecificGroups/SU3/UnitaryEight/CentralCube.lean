module
public import Theory.SpecificGroups.SU3.UnitaryEight.BinarySeed
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.SU3.BorelTorus.Basic

/-!
# A torus cube generating the scalar center of SU₃(8)

The norm-one torus has order nine. Its generator has a nontrivial cube in
the scalar kernel, whose order divides three. Thus that cube generates the
full center, with the special-unitary carrier and its projective map retained.
Source: the SU₃(8) torus in Aschbacher–Smith 13.8.20, printed p.955.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEightSeed
variable {E : Type*} [Field E] [Finite E]

theorem torus_central_cube (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0])
    (hcard : Nat.card E = 64) (hfixed : Nat.card {x : E // J.conj x = x} = 8) :
    ∃ t : J.specialSubgroup, t ∈ (hermitianTorusSU J hJ).range ∧
      orderOf t = 9 ∧ zpowers (t^3) = center J.specialSubgroup := by
  have hconj := huppert_II_10_4_conj_eq_frobenius J 8 (by simpa using hcard) hfixed
  have hnorm : Nat.card (EvenInner.normOne J) = 9 :=
    EvenInner.normOne_card J (q := 8) (by simpa using hcard) hconj
  obtain ⟨k,hk⟩ := IsCyclic.exists_generator (α := EvenInner.normOne J)
  have hko : orderOf k = 9 := (orderOf_eq_card_of_forall_mem_zpowers hk).trans hnorm
  let t := hermitianTorusSU J hJ k.val
  have hto : orderOf t = 9 := by
    rw [show orderOf t = orderOf k.val from
      orderOf_injective (hermitianTorusSU J hJ) (BorelTorus.special_injective J hJ) k.val,
      ←Subgroup.orderOf_mk k.val k.property,hko]
  have hc : t^3 ∈ center J.specialSubgroup := by
    apply J.specialToProjective_ker_le_center
    change J.specialToProjective (t^3) = 1
    have he : EvenInner.normOneMap J hJ (k^3) = 1 :=
      (EvenInner.normOneMap_eq_one_iff J hJ (k^3)).mpr (by
        rw [←pow_mul]; simpa only [hko] using pow_orderOf_eq_one k)
    have hp : J.specialToProjective (hermitianTorusSU J hJ k.val) =
        hermitianTorusPSU J hJ k.val := by
      apply Subtype.ext
      rw [J.specialToProjective_apply_val,hermitianTorusPSU_val]
      rfl
    rw [map_pow,hp]
    simpa only [EvenInner.normOneMap, MonoidHom.comp_apply, Subgroup.subtype_apply, map_pow] using he
  have hcardZ : Nat.card (center J.specialSubgroup) ∣ 3 := by
    rw [←J.specialToProjective_ker_eq_center
      (EvenProjectiveComparison.center_eq_bot J (n := 3) (by decide) hcard hconj)]
    exact J.card_specialToProjective_ker_dvd_three
  have hzc : Nat.card (zpowers (t^3)) = 3 := by
    norm_num [Nat.card_zpowers,orderOf_pow,hto]
  exact ⟨t,⟨k.val,rfl⟩,hto,eq_of_le_of_card_ge (zpowers_le.mpr hc)
    ((Nat.le_of_dvd (by decide : 0 < 3) hcardZ).trans_eq hzc.symm)⟩
end BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEightSeed

