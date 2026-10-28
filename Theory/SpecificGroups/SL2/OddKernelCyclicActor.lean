module
public import Theory.GroupTheory.Hall.CyclicHallInvolution
public import Theory.SpecificGroups.SL2.SylowInnerFixer
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# A fixed involution in an odd-by-SL₂ normal subgroup

An odd kernel preserves the Sylow subgroup of SL₂. That Sylow is
nonabelian and has a unique involution. A cyclic odd actor permuting
with the full ambient Sylow fixes the involution, by the cyclic-Hall
two-core argument in the actual normal intersection. The full Sylow
also fixes it. Its image is the scalar minus identity.

Source application: the nonquasisimple containing component in
Aschbacher–Smith 5.1.13, printed p.636. No quintic or cubic restriction
on the original cyclic actor is imposed.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups IsMulCommutative
namespace Theory.SpecificGroups.SL2.OddKernel

private theorem sl2_involution_eq {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (x : SL(2,F)) (hx : orderOf x = 2) : x = -1 := by
  have hp : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hd : (Matrix.SpecialLinearGroup.toGL x).det = 1 := by apply Units.ext; exact x.property
  rcases Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one h2
      (Matrix.SpecialLinearGroup.toGL x) (by rw [←map_pow,hp,map_one]) hd with he | he
  · have he' : x = 1 := Matrix.SpecialLinearGroup.toGL_injective (by simpa using he)
    simp [he'] at hx
  · exact Subtype.ext (congrArg Units.val he)

private theorem odd_sl2_sylow
    {Y F : Type*} [Group Y] [Finite Y] [Field F] [Finite F]
    (f : Y →* SL(2,F)) (hf : Function.Surjective f)
    (hk : Nat.Coprime 2 (Nat.card f.ker)) (ho : Odd (Nat.card F))
    (S : Sylow 2 Y) :
    8 ∣ Nat.card S ∧
      (∀ x y : S, orderOf x = 2 → orderOf y = 2 → x = y) := by
  let P := S.mapSurjective hf
  let e : S ≃* P := Sylow.equivOfSurjectiveCoprime f hf hk S P
  have h8 : 8 ∣ Nat.card SL(2,F) := by
    rw [GorensteinWalter.sl2_card_formula]
    have hh : 8 ∣ Nat.card F ^ 2 - 1 := by
      have hmod : Nat.card F % 2 = 1 := Nat.odd_iff.mp ho
      have hsq : Nat.card F ^ 2 % 8 = 1 := by
        rcases (show Nat.card F % 8 = 1 ∨ Nat.card F % 8 = 3 ∨
            Nat.card F % 8 = 5 ∨ Nat.card F % 8 = 7 by omega) with hh | hh | hh | hh <;>
          simp [Nat.pow_mod,hh]
      exact Nat.dvd_of_mod_eq_zero (by omega)
    exact dvd_mul_of_dvd_right hh _
  constructor
  · rw [Nat.card_congr e.toEquiv]
    exact P.pow_dvd_card_of_pow_dvd_card (n := 3) h8
  · intro x y hx hy
    apply e.injective
    apply Subtype.ext
    have h2 := GorensteinWalter.two_ne_zero_of_odd_card F ho
    exact (sl2_involution_eq h2 (e x) ((orderOf_coe _).trans ((e.orderOf_eq _).trans hx))).trans
      (sl2_involution_eq h2 (e y) ((orderOf_coe _).trans ((e.orderOf_eq _).trans hy))).symm

/-- The original cyclic actor and full Sylow fix the same scalar-lifting
involution in the normal odd-by-SL₂ subgroup. -/
theorem exists_actor_fixed_involution
    {Y F : Type*} [Group Y] [Finite Y] [Field F] [Finite F]
    (C D : Subgroup Y) [C.Normal] [Group.IsPerfect C] [IsCyclic D]
    (P : Sylow 2 Y) (f : C →* SL(2,F)) (hf : Function.Surjective f)
    (hk : Nat.Coprime 2 (Nat.card f.ker)) (ho : Odd (Nat.card F))
    (hD : Odd (Nat.card D))
    (hp : (D : Set Y) * (P : Set Y) = (P : Set Y) * (D : Set Y))
    (hs : Group.IsSolvable (D ⊔ (P : Subgroup Y) : Subgroup Y)) :
    ∃ z : C, (z : Y) ∈ P ∧ orderOf z = 2 ∧ f z = -1 ∧
      D ⊔ (P : Subgroup Y) ≤ centralizer ({(z : Y)} : Set Y) := by
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal C
  obtain ⟨h8,hu⟩ := odd_sl2_sylow f hf hk ho S
  let Q := S.mapSurjective hf
  let e : S ≃* Q := Sylow.equivOfSurjectiveCoprime f hf hk S Q
  let : Group.IsPerfect SL(2,F) := Group.IsPerfect.ofSurjective hf
  have hna : ¬ IsMulCommutative S := by
    intro hc
    apply Matrix.SpecialLinearGroup.sylow_two_not_isMulCommutative ho Q
    exact IsMulCommutative.of_comm (fun a b => e.symm.injective (by
      rw [map_mul,map_mul,hc.is_comm.comm]))
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := S) 2
    ((by decide : 2 ∣ 8).trans h8)
  have hzC : orderOf z.val = 2 := (orderOf_coe z).trans hz
  have hzf : orderOf (f z.val) = 2 := by
    have hd : Disjoint (S : Subgroup C) f.ker := by
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hkS⟩ := S.isPGroup'.exists_card_eq
      rw [hkS]
      exact hk.pow_left k
    have hi : Function.Injective (f.comp (S : Subgroup C).subtype) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by
        apply le_bot_iff.mp
        intro x hx
        exact Subtype.ext (disjoint_def.mp hd x.property hx))
    exact (orderOf_injective _ hi z).trans hz
  have hzP : (z.val : Y) ∈ P := by
    have hh := z.property
    exact (congrArg (fun U : Subgroup C => z.val ∈ U) hS).mp hh
  refine ⟨z.val,hzP,hzC,sl2_involution_eq
    (GorensteinWalter.two_ne_zero_of_odd_card F ho) _ hzf,sup_le ?_ ?_⟩
  · exact Theory.GroupTheory.CyclicHallInvolution.actor_fixes_involution
      D C P hD hp hs S hS hna hu z hz
  · intro x hx
    have hc : x * (z.val : Y) * x⁻¹ ∈ C :=
      (inferInstance : C.Normal).conj_mem _ z.val.property x
    have hsp : (⟨x * (z.val : Y) * x⁻¹,hc⟩ : C) ∈ S := by
      apply (congrArg (fun U : Subgroup C => (⟨x * (z.val : Y) * x⁻¹,hc⟩ : C) ∈ U) hS).mpr
      exact (P : Subgroup Y).mul_mem ((P : Subgroup Y).mul_mem hx hzP)
        ((P : Subgroup Y).inv_mem hx)
    have hh := hu ⟨⟨_,hc⟩,hsp⟩ z
      ((orderOf_coe _).symm.trans ((orderOf_coe _).symm.trans
        (((MulAut.conj x).orderOf_eq (z.val : Y)).trans ((orderOf_coe z.val).trans hzC)))) hz
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp
      (congrArg (fun v : S => (v.val : Y)) hh))

end Theory.SpecificGroups.SL2.OddKernel
