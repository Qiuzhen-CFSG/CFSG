module

public import Theory.GroupTheory.SpecificGroups.DihedralEightFixedInvolution
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group
/-!
# Splitting a normal dihedral factor by a fixed involution

A complement acting on a normal D₈ and fixing a noncentral involution s
acts through conjugation by ⟨s⟩. Correcting the complement by this unique
homomorphism makes it commute with D₈. Disjointness is unchanged, and
the order formula supplies the full direct product.

This is the split-extension step used by Aschbacher--Smith F.5.4(3).
-/

public noncomputable section
open Subgroup
namespace ElementaryFourSymmetricFourExtension
variable {G H : Type*} [Group G] [Finite G] [Group H]

theorem exists_product_of_normal_dihedral (K : Subgroup G) [K.Normal]
    (eK : K ≃* DihedralGroup 4) (d : H →* G)
    (hdis : ∀ h, d h ∈ K → h=1)
    (s : K) (hs : s^2=1) (hn : s ∉ center K)
    (hfix : ∀ h, d h * (s : G) = (s : G) * d h)
    (hcard : Nat.card G = Nat.card K * Nat.card H) :
    Nonempty (G ≃* K × H) := by
  let a : H →* MulAut K := MulAut.conjNormal.comp d
  have hafix : ∀ h, a h s = s := by
    intro h
    apply Subtype.ext
    change d h * (s : G) * (d h)⁻¹ = s
    rw [hfix,mul_inv_cancel_right]
  obtain ⟨u,hu⟩ := DihedralGroup.exists_conj_lift_of_fixed_involution eK s hs hn a hafix
  let w : H →* K := (zpowers s).subtype.comp u
  let v : H →* G := K.subtype.comp w
  have hv2 (h : H) : v h ^ 2 = 1 := by
    have hmem := (u h).property
    have ho := orderOf_dvd_of_mem_zpowers hmem
    have hp : (w h)^2=1 := orderOf_dvd_iff_pow_eq_one.mp
      (ho.trans (orderOf_dvd_of_pow_eq_one hs))
    exact congrArg Subtype.val hp
  have hcomm (x y : H) : Commute (v x) (d y) := by
    obtain ⟨n,he⟩ := (u x).property
    have hc : Commute (s : G) (d y) := (hfix y).symm
    have hh := hc.zpow_left n
    have hev : (s : G)^n = v x := congrArg Subtype.val he
    rw [hev] at hh
    exact hh
  let t : H →* G := (v.noncommCoprod d hcomm).comp ((MonoidHom.id H).prod (MonoidHom.id H))
  have ht (h : H) : t h = v h * d h := rfl
  have hKt (k : K) (h : H) : Commute (k : G) (t h) := by
    have hh := DFunLike.congr_fun (hu h) k
    have hh' := congrArg Subtype.val hh
    change v h * (k : G) * (v h)⁻¹ = d h * (k : G) * (d h)⁻¹ at hh'
    have hvInv : (v h)⁻¹ = v h := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv2 h)
    have hd : d h * (k : G) = v h * (k : G) * v h * d h := by
      have hz := congrArg (fun z : G => z * d h) hh'.symm
      simpa only [hvInv,mul_assoc,inv_mul_cancel,mul_one] using hz
    change (k : G) * t h = t h * k
    rw [ht,mul_assoc (v h),hd]
    have hvsq := hv2 h
    simp only [pow_two] at hvsq
    simp only [←mul_assoc,hvsq,one_mul]
  let f : K × H →* G := K.subtype.noncommCoprod t hKt
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    rintro ⟨k,h⟩ hx
    change (k : G) * (v h * d h) = 1 at hx
    have hd : d h ∈ K := by
      have he : d h = ((k : G) * v h)⁻¹ := by
        symm
        apply inv_eq_of_mul_eq_one_right
        simpa only [mul_assoc] using hx
      rw [he]
      exact K.inv_mem (K.mul_mem k.property (w h).property)
    have hh := hdis h hd
    subst h
    have hk : k=1 := by
      apply Subtype.ext
      change (k : G)=1
      simpa only [map_one,mul_one] using hx
    exact Prod.ext hk rfl
  have hfc : Nat.card (K × H) = Nat.card G := by rw [Nat.card_prod,hcard]
  exact ⟨(MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi,hfc⟩)).symm⟩

end ElementaryFourSymmetricFourExtension
