module
public import Theory.GroupTheory.CubicNormalizerNine
public import Theory.GroupTheory.PPerfectHom

/-!
# Detecting a cubic pair in a quotient

A cubic generating a two-perfect group together with its two-core has
nontrivial image under every nontrivial quotient map on that group.
For a commuting cubic pair, suppose one factor lies in a subgroup C and
the other lies in Y with Y∩C a two-group. Any homomorphism whose kernel
lies in C and which detects the first cubic is injective on the pair.

Source application: the actual elementary nine-group and the literal
centralizer quotient I/C_I(V_I) in Aschbacher–Smith 14.7.32, p.1058.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {D Q : Type*} [Group D] [Group Q]

theorem injective_on_cubic_pair_of_twoGroup_intersection (f : D →* Q) (Y C : Subgroup D)
    (hk : f.ker ≤ C) (hYC : IsPGroup 2 (Y ⊓ C : Subgroup D))
    (x y : D) (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hxC : x ∈ C) (hyY : y ∈ Y) (hxy : Commute x y) (hfx : f x ≠ 1) :
    Function.Injective (f.comp (zpowers y ⊔ zpowers x).subtype) := by
  have hXC : zpowers x ≤ C := zpowers_le.mpr hxC
  have hYX : zpowers x ≤ centralizer (zpowers y : Set D) := by
    apply zpowers_le.mpr
    have hyC : zpowers y ≤ centralizer ({x} : Set D) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxy.symm)
    intro z hz
    exact mem_centralizer_singleton_iff.mp (hyC hz)
  have hdis := (f.ker.disjoint_zpowers_of_prime_order_not_mem x hx hfx).symm
  have hp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hy,pow_one])
  have hd := hp.disjoint_of_coprime hYC (by decide : Nat.Coprime 3 2)
  apply (injective_iff_map_eq_one _).mpr
  intro z hz
  have hzC : (z : D) ∈ C := hk hz
  have hzprod : (z : D) ∈ (zpowers y : Set D) * (zpowers x : Set D) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hYX.trans (centralizer_le_normalizer _))]
    exact z.property
  obtain ⟨a,ha,b,hb,hab⟩ := hzprod
  have haC : a ∈ C := by
    have hh := C.mul_mem hzC (C.inv_mem (hXC hb))
    rw [←hab,mul_inv_cancel_right] at hh
    exact hh
  have ha1 : a = 1 := hd.le_bot ⟨ha,⟨(zpowers_le.mpr hyY) ha,haC⟩⟩
  have hzb : (z : D) = b := by simpa only [ha1,one_mul] using hab.symm
  apply Subtype.ext
  exact hdis.le_bot ⟨hzb.symm ▸ hb,hz⟩

theorem cubic_image_ne_one_of_twoPerfect (f : D →* Q) (A : Subgroup D) (hp : IsPPerfect 2 A)
    (x : D) (hgen : zpowers x ⊔ A.pCoreIn 2 = A) (hne : A.map f ≠ ⊥) :
    f x ≠ 1 := by
  intro hx
  have he : A.map f = (A.pCoreIn 2).map f := by
    conv_lhs => rw [← hgen]
    simp only [map_sup,MonoidHom.map_zpowers,hx,Subgroup.zpowers_one_eq_bot,bot_sup_eq]
  have htwo : IsPGroup 2 (A.map f) := he ▸ (isPGroup_pCoreIn 2 A).map f
  have hz := hp.hom_eq_one_of_isPGroup htwo (f.subgroupMap A)
  apply hne
  apply bot_unique
  rintro z ⟨a,ha,rfl⟩
  exact congrArg Subtype.val (DFunLike.congr_fun hz ⟨a,ha⟩)
end Subgroup
