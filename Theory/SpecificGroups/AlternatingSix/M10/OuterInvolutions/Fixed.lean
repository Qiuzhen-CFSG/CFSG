module
public import Theory.SpecificGroups.AlternatingSix.M10.OuterInvolutions

/-!
# Involution conjugacy in a diagonal automorphism centralizer

Every involution of M10 is inner. If it commutes with a diagonal involution,
its unique preimage in A6 belongs to that diagonal involution's D10 fixed
subgroup. The involutions of D10 form one class, so the conjugator can be
chosen in the same fixed subgroup. The result retains its actual inner image
and its commutation with the original automorphism.

Source: Aschbacher–Smith J.2.7(8), printed pp.436–437 (PDF pp.447–448).
-/

open Subgroup
namespace AlternatingSix.M10.OuterInvolutions
open ShadowLocal GLS3.Chapter5

lemma commute_inner_iff (β : AutA6) (x : A6) :
    Commute β (MulAut.conj x) ↔ β x=x := by
  have he : β*MulAut.conj x*β⁻¹=MulAut.conj (β x) := by
    apply MulEquiv.ext
    intro y
    simp
  constructor
  · intro h
    exact inner_injective (he.symm.trans h.mul_inv_cancel)
  · intro h
    apply mul_inv_eq_iff_eq_mul.mp
    rw [he,h]

lemma dihedral_five_involutions_conjugate :
    ∀ x y : DihedralGroup 5, x^2=1 → x≠1 → y^2=1 → y≠1 →
      ∃g:DihedralGroup 5,g*x*g⁻¹=y := by decide +kernel

public theorem diagonal_fixed_involutions_conjugate (β : AutA6) (hβ : orderOf β=2)
    (hn : β∉natural) (x y : AutA6) (hx : orderOf x=2) (hy : orderOf y=2)
    (hxM : x∈extension) (hyM : y∈extension)
    (hβx : Commute β x) (hβy : Commute β y) :
    ∃ a∈ShadowLocal.inner, Commute β a ∧ a*x*a⁻¹=y := by
  obtain ⟨x,rfl⟩ := InvolutionAlignment.involution_mem_inner x hx hxM
  obtain ⟨y,rfl⟩ := InvolutionAlignment.involution_mem_inner y hy hyM
  have hfixx := (commute_inner_iff β x).mp hβx
  have hfixy := (commute_inner_iff β y).mp hβy
  let xF : automorphismFixedSubgroup β := ⟨x,hfixx⟩
  let yF : automorphismFixedSubgroup β := ⟨y,hfixy⟩
  have hxo : orderOf xF=2 := (Subgroup.orderOf_coe xF).symm.trans
    ((orderOf_injective MulAut.conj inner_injective x).symm.trans hx)
  have hyo : orderOf yF=2 := (Subgroup.orderOf_coe yF).symm.trans
    ((orderOf_injective MulAut.conj inner_injective y).symm.trans hy)
  obtain ⟨e⟩ := outside_natural_involution_fixed_equiv_dihedral β hβ hn
  have hxd : orderOf (e xF)=2 := (e.orderOf_eq xF).trans hxo
  have hyd : orderOf (e yF)=2 := (e.orderOf_eq yF).trans hyo
  obtain ⟨g,hg⟩ := dihedral_five_involutions_conjugate (e xF) (e yF)
    (hxd ▸ pow_orderOf_eq_one _) (by intro h;simp [h] at hxd)
    (hyd ▸ pow_orderOf_eq_one _) (by intro h;simp [h] at hyd)
  let a := e.symm g
  have he : a*xF*a⁻¹=yF := by
    apply e.injective
    simpa only [a,map_mul,map_inv,e.apply_symm_apply] using hg
  refine ⟨MulAut.conj (a:A6),⟨a,rfl⟩,(commute_inner_iff β a).mpr a.property,?_⟩
  rw [←map_inv,←map_mul,←map_mul]
  exact congrArg MulAut.conj (congrArg Subtype.val he)

end AlternatingSix.M10.OuterInvolutions
