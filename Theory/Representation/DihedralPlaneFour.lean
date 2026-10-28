module
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.RepresentationTheory.Basic
/-!
# Odd prime-power dihedral actions on a plane over four elements

Every reflection has determinant of order dividing both two and three,
so the whole dihedral image lies in SL₂(4). Its order divides sixty.
An odd prime-power rotation order must therefore be three or five.
The argument uses the given faithful representation and no replacement
action or general finite-subgroup classification.

Source application: Aschbacher–Smith 8.2.8(3), printed p.719,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
namespace Representation
open Matrix Subgroup
open scoped MatrixGroups

/-- A faithful dihedral action over F₄ has prime-power rotation order three or five. -/
theorem dihedral_prime_power_plane_four {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) {p a : ℕ} (hp : p.Prime) (ho : Odd p) (ha : 0 < a)
    (ρ : Representation F (DihedralGroup (p^a)) (Fin 2 → F))
    (hi : Function.Injective ρ.asGroupHom) : p^a = 3 ∨ p^a = 5 := by
  let f : DihedralGroup (p^a) →* GL (Fin 2) F :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp ρ.asGroupHom
  have hf : Function.Injective f := GeneralLinearGroup.toLin.symm.injective.comp hi
  let d := GeneralLinearGroup.det.comp f
  have hs (j : ZMod (p^a)) : d (DihedralGroup.sr j) = 1 := by
    have h2 : d (DihedralGroup.sr j)^2 = 1 := by
      rw [←map_pow,pow_two,DihedralGroup.sr_mul_self,map_one]
    have h3 : d (DihedralGroup.sr j)^3 = 1 := by
      have hh := pow_card_eq_one' (x := d (DihedralGroup.sr j))
      simpa only [Nat.card_units,hF] using hh
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp
      (show orderOf (d (DihedralGroup.sr j)) ∣ 1 from
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)))
  have hd (g : DihedralGroup (p^a)) : f g ∈ GeneralLinearGroup.det.ker := by
    change d g = 1
    cases g with
    | sr j => exact hs j
    | r j =>
      rw [show DihedralGroup.r j = DihedralGroup.sr 0 * DihedralGroup.sr j by
        rw [DihedralGroup.sr_mul_sr,sub_zero],map_mul,hs,hs,mul_one]
  let q : DihedralGroup (p^a) →* SL(2,F) :=
    (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm.toMonoidHom.comp
      (f.codRestrict GeneralLinearGroup.det.ker hd)
  have hq : Function.Injective q :=
    (SpecialLinearGroup.determinantKernelEquiv (Fin 2) F).symm.injective.comp
      (fun _ _ he => hf (congrArg Subtype.val he))
  let : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcard := card_dvd_of_injective q hq
  rw [DihedralGroup.nat_card,Atlas.card_sl_two,hF] at hcard
  norm_num at hcard
  have hpow : p^a ∣ 60 := (dvd_mul_left (p^a) 2).trans hcard
  have hp60 : p ∣ 60 := (dvd_pow_self p ha.ne').trans hpow
  have hps : p = 2 ∨ p = 3 ∨ p = 5 := by
    have hh : p ∣ 2*2*3*5 := hp60
    simp only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)] at hh
    tauto
  rcases hps with rfl | rfl | rfl
  · obtain ⟨j,hj⟩ := ho
    omega
  · have he : a = 1 := by
      by_contra he
      have h9 : 9 ∣ 60 := (pow_dvd_pow 3 (by omega : 2 ≤ a)).trans hpow
      norm_num at h9
    exact Or.inl (by rw [he,pow_one])
  · have he : a = 1 := by
      by_contra he
      have h25 : 25 ∣ 60 := (pow_dvd_pow 5 (by omega : 2 ≤ a)).trans hpow
      norm_num at h25
    exact Or.inr (by rw [he,pow_one])
end Representation
