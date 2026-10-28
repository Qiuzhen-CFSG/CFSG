module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairExchange
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree.ExceptionalFactor
public import Theory.Representation.BinaryOffender.ComponentSum
public import Mathlib.LinearAlgebra.Projection
/-!
# The original two-factor quotient action and conjugate coordinates

Displacement by the opposite factor lies in both complementary quotient
summands, hence vanishes. The original quotient action is consequently the
product of its two actual factor actions. Ambient conjugation carries a moved
summand to the conjugate factor's moved summand and intertwines the literal
quotient actions. Transporting a chosen model along this map preserves the
same field and coordinates, without splitting the original module.

Source: Aschbacher–Smith B.5.6(3), B.6.9(2), pp.105 and115–116.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}
theorem SourceFactorCase.moved_le_space {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) : moved ρ A ≤ U.toSubmodule := by
  cases h with
  | natural hm _ => exact hm.ge
  | doubleNatural _ _ hm _ => exact hm.ge
  | exceptional hm _ => exact hm

theorem SourceTwoFactorCase.second_fixes_first (d : SourceTwoFactorCase ρ)
    (b : d.second) (v : ((fixed ρ).quotientImage d.firstSpace).toSubmodule) :
    ((fixed ρ).quotientImage d.firstSpace).toRepresentation b v = v := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hfirst : (fixed ρ).quotientRepresentation b v - v ∈
      ((fixed ρ).quotientImage d.firstSpace).toSubmodule :=
    ((fixed ρ).quotientImage d.firstSpace).toSubmodule.sub_mem
      (((fixed ρ).quotientImage d.firstSpace).apply_mem_toSubmodule b v.property) v.property
  have hsecond : (fixed ρ).quotientRepresentation b v - v ∈
      ((fixed ρ).quotientImage d.secondSpace).toSubmodule := by
    obtain ⟨w,hw,he⟩ := v.property
    change (fixed ρ).toSubmodule.mkQ w = (v : V ⧸ (fixed ρ).toSubmodule) at he
    rw [← he]
    change (fixed ρ).toSubmodule.mkQ (ρ b w) - (fixed ρ).toSubmodule.mkQ w ∈
      d.secondSpace.toSubmodule.map (fixed ρ).toSubmodule.mkQ
    exact ⟨ρ b w-w, d.secondCase.moved_le_space
      (Submodule.subset_span ⟨b,b.property,w,Submodule.mem_top,rfl⟩), map_sub _ _ _⟩
  exact d.decomposition.disjoint.eq_bot.le ⟨hfirst,hsecond⟩

theorem SourceTwoFactorCase.first_fixes_second (d : SourceTwoFactorCase ρ)
    (a : d.first) (v : ((fixed ρ).quotientImage d.secondSpace).toSubmodule) :
    ((fixed ρ).quotientImage d.secondSpace).toRepresentation a v = v :=
  (show SourceTwoFactorCase ρ from {
    first := d.second
    second := d.first
    product := d.product.swap
    firstSpace := d.secondSpace
    secondSpace := d.firstSpace
    decomposition := d.decomposition.symm
    firstCase := d.secondCase
    secondCase := d.firstCase }).second_fixes_first a v

noncomputable def SourceTwoFactorCase.quotientProductEquiv (d : SourceTwoFactorCase ρ) :
    (V ⧸ (fixed ρ).toSubmodule) ≃ₗ[ZMod 2]
      (((fixed ρ).quotientImage d.firstSpace).toSubmodule × ((fixed ρ).quotientImage d.secondSpace).toSubmodule) :=
  (Submodule.prodEquivOfIsCompl _ _ d.decomposition).symm

theorem SourceTwoFactorCase.quotientProductEquiv_action (d : SourceTwoFactorCase ρ)
    (a : d.first) (b : d.second) (v : V ⧸ (fixed ρ).toSubmodule) :
    d.quotientProductEquiv ((fixed ρ).quotientRepresentation ((a:D)*b) v) =
      (((fixed ρ).quotientImage d.firstSpace).toRepresentation a
        (d.quotientProductEquiv v).1,
       ((fixed ρ).quotientImage d.secondSpace).toRepresentation b
        (d.quotientProductEquiv v).2) := by
  apply d.quotientProductEquiv.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  obtain ⟨⟨v₁,v₂⟩,rfl⟩ := d.quotientProductEquiv.symm.surjective v
  change (fixed ρ).quotientRepresentation ((a:D)*b)
    ((v₁ : V ⧸ (fixed ρ).toSubmodule)+v₂) = _
  rw [map_mul,Module.End.mul_apply,map_add,map_add]
  have h1 := congrArg Subtype.val (d.second_fixes_first b v₁)
  have h2 := congrArg Subtype.val (d.first_fixes_second a
    (((fixed ρ).quotientImage d.secondSpace).toRepresentation b v₂))
  change (fixed ρ).quotientRepresentation b v₁ = (v₁ : V ⧸ (fixed ρ).toSubmodule) at h1
  change (fixed ρ).quotientRepresentation a
    ((fixed ρ).quotientRepresentation b v₂) =
    (fixed ρ).quotientRepresentation b v₂ at h2
  rw [h1,h2]
  simp only [LinearEquiv.apply_symm_apply]
  rfl

variable {D₁ D₂ M₁ M₂ : Type*} [Group D₁] [Group D₂]
  [AddCommGroup M₁] [Module (ZMod 2) M₁] [AddCommGroup M₂] [Module (ZMod 2) M₂]
noncomputable def SourceTwoFactorCase.quotientModelEquiv (d : SourceTwoFactorCase ρ)
    (τ₁ : Representation (ZMod 2) D₁ M₁) (τ₂ : Representation (ZMod 2) D₂ M₂)
    (e₁ : ActionEquiv (((fixed ρ).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype) τ₁)
    (e₂ : ActionEquiv (((fixed ρ).quotientImage d.secondSpace).toRepresentation.comp d.second.subtype) τ₂) :
    ActionEquiv (fixed ρ).quotientRepresentation
      (Representation.prod (τ₁.comp (MonoidHom.fst D₁ D₂)) (τ₂.comp (MonoidHom.snd D₁ D₂))) where
  groupEquiv := d.product.equiv.symm.trans (e₁.groupEquiv.prodCongr e₂.groupEquiv)
  linearEquiv := d.quotientProductEquiv.trans (e₁.linearEquiv.prodCongr e₂.linearEquiv)
  intertwines g v := by
    obtain ⟨a,b,rfl⟩ := d.product.exists_mul g
    change (e₁.linearEquiv.prodCongr e₂.linearEquiv)
      (d.quotientProductEquiv ((fixed ρ).quotientRepresentation ((a:D)*b) v)) = _
    rw [d.quotientProductEquiv_action]
    change (e₁.linearEquiv (((fixed ρ).quotientImage d.firstSpace).toRepresentation a
        (d.quotientProductEquiv v).1),
      e₂.linearEquiv (((fixed ρ).quotientImage d.secondSpace).toRepresentation b
        (d.quotientProductEquiv v).2)) = _
    have h₁ := e₁.intertwines a (d.quotientProductEquiv v).1
    have h₂ := e₂.intertwines b (d.quotientProductEquiv v).2
    simp only [MonoidHom.comp_apply,Subgroup.coe_subtype] at h₁ h₂
    rw [h₁,h₂]
    have he : d.product.equiv.symm ((a:D)*b) = (a,b) := by
      rw [← d.product.apply_eq, d.product.equiv.symm_apply_apply]
    change _ = (τ₁ (e₁.groupEquiv (d.product.equiv.symm ((a:D)*b)).1)
        (e₁.linearEquiv (d.quotientProductEquiv v).1),
      τ₂ (e₂.groupEquiv (d.product.equiv.symm ((a:D)*b)).2)
        (e₂.linearEquiv (d.quotientProductEquiv v).2))
    rw [he]

theorem SourceTwoFactorCase.quotientModelEquiv_first (d : SourceTwoFactorCase ρ)
    (τ₁ : Representation (ZMod 2) D₁ M₁) (τ₂ : Representation (ZMod 2) D₂ M₂)
    (e₁ : ActionEquiv (((fixed ρ).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype) τ₁)
    (e₂ : ActionEquiv (((fixed ρ).quotientImage d.secondSpace).toRepresentation.comp d.second.subtype) τ₂) :
    ((⊤ : Subgroup D₁).prod (⊥ : Subgroup D₂)).map
      (d.quotientModelEquiv τ₁ τ₂ e₁ e₂).groupEquiv.symm.toMonoidHom = d.first := by
  ext x
  constructor
  · rintro ⟨⟨a,b⟩,⟨_,hb⟩,rfl⟩
    have hb : b = 1 := hb
    subst b
    change d.product.equiv (e₁.groupEquiv.symm a,e₂.groupEquiv.symm 1) ∈ d.first
    rw [map_one,d.product.apply_eq,OneMemClass.coe_one,mul_one]
    exact (e₁.groupEquiv.symm a).property
  · intro hx
    refine ⟨(e₁.groupEquiv ⟨x,hx⟩,1),⟨Subgroup.mem_top _,Subgroup.mem_bot.mpr rfl⟩,?_⟩
    change d.product.equiv (e₁.groupEquiv.symm (e₁.groupEquiv ⟨x,hx⟩),e₂.groupEquiv.symm 1) = x
    rw [e₁.groupEquiv.symm_apply_apply,map_one,d.product.apply_eq,OneMemClass.coe_one,mul_one]

theorem SourceTwoFactorCase.quotientModelEquiv_second (d : SourceTwoFactorCase ρ)
    (τ₁ : Representation (ZMod 2) D₁ M₁) (τ₂ : Representation (ZMod 2) D₂ M₂)
    (e₁ : ActionEquiv (((fixed ρ).quotientImage d.firstSpace).toRepresentation.comp d.first.subtype) τ₁)
    (e₂ : ActionEquiv (((fixed ρ).quotientImage d.secondSpace).toRepresentation.comp d.second.subtype) τ₂) :
    ((⊥ : Subgroup D₁).prod (⊤ : Subgroup D₂)).map
      (d.quotientModelEquiv τ₁ τ₂ e₁ e₂).groupEquiv.symm.toMonoidHom = d.second := by
  ext x
  constructor
  · rintro ⟨⟨a,b⟩,⟨ha,_⟩,rfl⟩
    have ha : a = 1 := ha
    subst a
    change d.product.equiv (e₁.groupEquiv.symm 1,e₂.groupEquiv.symm b) ∈ d.second
    rw [map_one,d.product.apply_eq,OneMemClass.coe_one,one_mul]
    exact (e₂.groupEquiv.symm b).property
  · intro hx
    refine ⟨(1,e₂.groupEquiv ⟨x,hx⟩),⟨Subgroup.mem_bot.mpr rfl,Subgroup.mem_top _⟩,?_⟩
    change d.product.equiv (e₁.groupEquiv.symm 1,e₂.groupEquiv.symm (e₂.groupEquiv ⟨x,hx⟩)) = x
    rw [e₂.groupEquiv.symm_apply_apply,map_one,d.product.apply_eq,OneMemClass.coe_one,one_mul]
end CFSG.Quasithin.ChapterB.SourceInduction

namespace CFSG.Quasithin.ChapterB
open QuasisimpleSource SourceInduction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (Y : Subgroup G) [Y.Normal]
  (A B : Subgroup Y) (U W : Subrepresentation (ρ.comp Y.subtype))
  (hU : U.toSubmodule = moved (ρ.comp Y.subtype) A)
  (hW : W.toSubmodule = moved (ρ.comp Y.subtype) B)
  (g : G) (hAB : A.map (MulAut.conjNormal g).toMonoidHom = B)

include hU hW hAB in
theorem source_factor_quotient_image_conjugate :
    (((fixed (ρ.comp Y.subtype)).quotientImage U).toSubmodule).map
      (fixedQuotient ρ Y g) = ((fixed (ρ.comp Y.subtype)).quotientImage W).toSubmodule := by
  rw [source_factor_image_eq_moved ρ Y A U hU,
    source_factor_image_eq_moved ρ Y B W hW,moved_map_conjugate]
  have he := congrArg (map Y.subtype) hAB
  rw [map_map] at he
  have hc : Y.subtype.comp (MulAut.conjNormal g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp Y.subtype := by ext; rfl
  rw [hc,← map_map] at he
  rw [he]

noncomputable def sourceFactorConjugateEquiv :
    ActionEquiv (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype)
      (((fixed (ρ.comp Y.subtype)).quotientImage W).toRepresentation.comp B.subtype) where
  groupEquiv := (A.equivMapOfInjective (MulAut.conjNormal g).toMonoidHom
    (MulAut.conjNormal g).injective).trans (MulEquiv.subgroupCongr hAB)
  linearEquiv := (Submodule.equivMapOfInjective (fixedQuotient ρ Y g)
    ((fixedQuotient ρ Y).apply_bijective g).injective _).trans
      (LinearEquiv.ofEq _ _ (source_factor_quotient_image_conjugate ρ Y A B U W hU hW g hAB))
  intertwines a v := by
    apply Subtype.ext
    change fixedQuotient ρ Y g (fixedQuotient ρ Y (a:Y) v.val) =
      fixedQuotient ρ Y (g*(a:Y)*g⁻¹) (fixedQuotient ρ Y g v.val)
    simp only [map_mul,Module.End.mul_apply,(fixedQuotient ρ Y).inv_self_apply]

variable {D M : Type*} [Group D] [AddCommGroup M] [Module (ZMod 2) M]
noncomputable def sourceFactorConjugateModelEquiv (τ : Representation (ZMod 2) D M)
    (e : ActionEquiv (((fixed (ρ.comp Y.subtype)).quotientImage U).toRepresentation.comp A.subtype) τ) :
    ActionEquiv (((fixed (ρ.comp Y.subtype)).quotientImage W).toRepresentation.comp B.subtype) τ := by
  let c := sourceFactorConjugateEquiv ρ Y A B U W hU hW g hAB
  refine ⟨c.groupEquiv.symm.trans e.groupEquiv,c.linearEquiv.symm.trans e.linearEquiv,?_⟩
  intro b v
  change e.linearEquiv (c.linearEquiv.symm
    ((((fixed (ρ.comp Y.subtype)).quotientImage W).toRepresentation.comp B.subtype) b v)) = _
  have hh := c.intertwines (c.groupEquiv.symm b) (c.linearEquiv.symm v)
  rw [c.groupEquiv.apply_symm_apply,c.linearEquiv.apply_symm_apply] at hh
  rw [← hh,c.linearEquiv.symm_apply_apply]
  exact e.intertwines _ _
end CFSG.Quasithin.ChapterB

