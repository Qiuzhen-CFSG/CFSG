module
public import Theory.Representation.SL2NaturalOffenders.PairPointwiseFixer
public import Mathlib.LinearAlgebra.Prod
/-!
# The coordinate equivalence induced by a factor exchanger

A natural SL₂ factor fixes exactly the opposite coordinate space. An
ambient element exchanging the two factors therefore exchanges those spaces.
Its first output coordinate induces a binary linear equivalence from the
second input coordinate, with no chosen field automorphism or splitting.
Source: Aschbacher–Smith B.6.9 and 10.2.3(4), pp.115–116 and 746.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Representation.SL2NaturalOffenders
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]
  {H : Type*} [Group H]
local notation "D" => SL(2,F)
local notation "V" => Fin 2 → F
set_option backward.isDefEq.respectTransparency false in
theorem exchanged_pair_coordinate_equiv
    (Y : Subgroup H) [Y.Normal] (e : Y ≃* D × D)
    (ρ : Representation (ZMod 2) H (V × V))
    (hnat : ∀ (g : Y) (v : V × V), ρ (g:H) v =
      ((e g).1.val.mulVec v.1,(e g).2.val.mulVec v.2))
    (t : H)
    (h₁ : (((⊤ : Subgroup D).prod ⊥).map e.symm.toMonoidHom).map
      (MulAut.conjNormal t).toMonoidHom = ((⊥ : Subgroup D).prod ⊤).map e.symm.toMonoidHom)
    (h₂ : (((⊥ : Subgroup D).prod ⊤).map e.symm.toMonoidHom).map
      (MulAut.conjNormal t).toMonoidHom = ((⊤ : Subgroup D).prod ⊥).map e.symm.toMonoidHom) :
    ∃ f : V ≃ₗ[ZMod 2] V, ∀ v : V × V, (ρ t v).1 = f v.2 := by
  have heq (a b : Y) (hab : MulAut.conjNormal t a = b) (v : V × V)
      (ha : ρ (a:H) v = v) : ρ (b:H) (ρ t v) = ρ t v := by
    have hh : (b:H) * t = t * (a:H) := by
      have h := congrArg Y.subtype hab
      change t*(a:H)*t⁻¹ = (b:H) at h
      rw [←h]
      simp only [mul_assoc,inv_mul_cancel,mul_one]
    calc
      ρ (b:H) (ρ t v) = ρ ((b:H)*t) v := by rw [map_mul]; rfl
      _ = ρ (t*(a:H)) v := by rw [hh]
      _ = ρ t v := by rw [map_mul]; change ρ t (ρ (a:H) v) = _; rw [ha]
  have hz₁ (v : V) : (ρ t (v,0)).1 = 0 := by
    apply natural_fixed_all_eq_zero
    intro g
    have hm : e.symm (g,1) ∈ (((⊥ : Subgroup D).prod ⊤).map e.symm.toMonoidHom).map
        (MulAut.conjNormal t).toMonoidHom := by
      rw [h₂]
      exact mem_map_of_mem _ ⟨mem_top _,one_mem _⟩
    obtain ⟨a,⟨b,hb,rfl⟩,ha⟩ := hm
    have hh := heq (e.symm b) (e.symm (g,1)) ha (v,0) (by
      rw [hnat,e.apply_symm_apply]
      apply Prod.ext
      · rw [show b.1 = 1 from hb.1]
        simp
      · simp)
    rw [hnat,e.apply_symm_apply] at hh
    exact congrArg Prod.fst hh
  have hz₂ (v : V) : (ρ t (0,v)).2 = 0 := by
    apply natural_fixed_all_eq_zero
    intro g
    have hm : e.symm (1,g) ∈ (((⊤ : Subgroup D).prod ⊥).map e.symm.toMonoidHom).map
        (MulAut.conjNormal t).toMonoidHom := by
      rw [h₁]
      exact mem_map_of_mem _ ⟨one_mem _,mem_top _⟩
    obtain ⟨a,⟨b,hb,rfl⟩,ha⟩ := hm
    have hh := heq (e.symm b) (e.symm (1,g)) ha (0,v) (by
      rw [hnat,e.apply_symm_apply]
      apply Prod.ext
      · simp
      · rw [show b.2 = 1 from hb.2]
        simp)
    rw [hnat,e.apply_symm_apply] at hh
    exact congrArg Prod.snd hh
  let f : V →ₗ[ZMod 2] V := (LinearMap.fst _ _ _).comp
    ((ρ t).comp (LinearMap.inr _ _ _))
  have hf (v : V × V) : (ρ t v).1 = f v.2 := by
    have hh := (ρ t).map_add (v.1,0) (0,v.2)
    have h := congrArg Prod.fst hh
    change (ρ t v).1 = (ρ t (0,v.2)).1
    simpa only [Prod.fst_add,Prod.mk_add_mk,add_zero,zero_add,hz₁] using h
  have hfi : Function.Injective f := by
    intro v w hvw
    have he : ρ t (0,v) = ρ t (0,w) := Prod.ext hvw ((hz₂ v).trans (hz₂ w).symm)
    have hh := congrArg (ρ t⁻¹) he
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] at hh
    exact congrArg Prod.snd hh
  have hfs : Function.Surjective f := by
    intro v
    refine ⟨(ρ t⁻¹ (v,0)).2,?_⟩
    rw [←hf]
    simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  exact ⟨LinearEquiv.ofBijective f ⟨hfi,hfs⟩,hf⟩
end Representation.SL2NaturalOffenders
