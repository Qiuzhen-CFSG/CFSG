module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.AffineNormal
public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# Centralizers of translations in an affine group

In an affine semidirect product with abelian translation group, an element
centralizes a specified translation exactly when its linear part fixes that
vector. Projection therefore gives an exact sequence with the entire
translation group as kernel and the vector stabilizer as quotient. If the
original action is faithful, the kernel is self-centralizing in this actual
centralizer.

This supplies the affine calculation for the M₂₄ class-2B centralizer in
Aschbacher–Smith 16.1.5(7), printed p.1171. The centralizer calculation uses
the existing ATLAS affine-centralizer lemma, attributed in its own module.
-/

@[expose] public section

open Subgroup SemidirectProduct

namespace Theory.GroupTheory.TranslationCentralizer
variable {U B : Type*} [CommGroup U] [Group B] (φ : B →* MulAut U) (v : U)

def actors : Subgroup B where
  carrier := {g | φ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change φ (g * h) v = v
    rw [map_mul, MulAut.mul_apply, show φ h v = v from hh]
    exact hg
  inv_mem' := by
    intro g hg
    apply (φ g).injective
    simpa only [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      MulAut.one_apply] using hg.symm

abbrev centralizer := Subgroup.centralizer ({(inl v : U ⋊[φ] B)} : Set (U ⋊[φ] B))

theorem mem_iff (x : U ⋊[φ] B) : x ∈ centralizer φ v ↔ φ x.right v = v := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hl := congrArg SemidirectProduct.left h
    simpa only [mul_left, left_inl, right_inl, map_one, MulAut.one_apply,
      mul_comm v, mul_left_cancel_iff] using hl
  · intro h
    apply SemidirectProduct.ext
    · simp only [mul_left, left_inl, right_inl, map_one, MulAut.one_apply, h, mul_comm]
    · simp only [mul_right, right_inl, mul_one, one_mul]

def projection : centralizer φ v →* actors φ v where
  toFun x := ⟨x.val.right, (mem_iff φ v x.val).mp x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def inclusion : U →* centralizer φ v :=
  (inl : U →* U ⋊[φ] B).codRestrict _ (fun u => (mem_iff φ v _).mpr (by simp))

theorem inclusion_injective : Function.Injective (inclusion φ v) := by
  intro u w h
  exact inl_injective (congrArg Subtype.val h)

theorem projection_surjective : Function.Surjective (projection φ v) := by
  intro g
  exact ⟨⟨inr g.val, (mem_iff φ v _).mpr g.property⟩, rfl⟩

def kernelEquiv : U ≃* (projection φ v).ker where
  toFun u := ⟨inclusion φ v u, rfl⟩
  invFun x := x.val.val.left
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact (congrArg Subtype.val x.property).symm
  map_mul' _ _ := by
    apply Subtype.ext
    exact map_mul (inclusion φ v) _ _

def extension : GroupExtension U (centralizer φ v) (actors φ v) where
  inl := inclusion φ v
  rightHom := projection φ v
  inl_injective := inclusion_injective φ v
  rightHom_surjective := projection_surjective φ v
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩; rfl
    · intro hx
      obtain ⟨u, hu⟩ := (kernelEquiv φ v).surjective ⟨x, hx⟩
      exact ⟨u, congrArg Subtype.val hu⟩

theorem kernel_selfCentralizing (faithful : Function.Injective φ) :
    Subgroup.centralizer ((projection φ v).ker : Set (centralizer φ v)) ≤
      (projection φ v).ker := by
  intro x hx
  have ha : x.val ∈ Subgroup.centralizer
      ((inl : U →* U ⋊[φ] B).range : Set (U ⋊[φ] B)) := by
    rintro _ ⟨u, rfl⟩
    exact congrArg Subtype.val (hx (inclusion φ v u) (show inclusion φ v u ∈
      (projection φ v).ker from rfl))
  rw [Atlas.GroupTheory.affine_centralizer φ faithful] at ha
  obtain ⟨u, hu⟩ := ha
  apply Subtype.ext
  exact (congrArg SemidirectProduct.right hu).symm

end Theory.GroupTheory.TranslationCentralizer
