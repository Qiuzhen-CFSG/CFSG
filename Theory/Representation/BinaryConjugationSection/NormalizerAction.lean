module
public import Theory.Representation.BinaryConjugationSection
public import Mathlib.Algebra.Module.ZMod

/-!
# Extending faithful section coordinates to the full normalizer

A bijective coordinate homomorphism transports conjugation by the entire
normalizer of the original subgroup to binary linear automorphisms. On the
original section actor it agrees with the given representation. This keeps
the same vectors when passing from the determinant group to its normalizer
in the source tensor case, Aschbacher–Smith 9.1 (printed p.729).
-/

public noncomputable section
namespace Representation.BinaryConjugationSection
open Subgroup
variable {G : Type*} [Group G] {A H : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private def linearOfAut (a : MulAut (Multiplicative W)) : W ≃ₗ[ZMod 2] W where
  toFun := fun w => (a (Multiplicative.ofAdd w)).toAdd
  invFun := fun w => (a.symm (Multiplicative.ofAdd w)).toAdd
  left_inv := a.left_inv
  right_inv := a.right_inv
  map_add' := a.map_mul
  map_smul' := ZMod.map_smul
    ({ toFun := fun w => (a (Multiplicative.ofAdd w)).toAdd
       map_zero' := a.map_one
       map_add' := a.map_mul } : W →+ W)

private def linearAutHom : MulAut (Multiplicative W) →* (W ≃ₗ[ZMod 2] W) where
  toFun := linearOfAut
  map_one' := by ext w; rfl
  map_mul' _ _ := by ext w; rfl

def normalizerAction (c : A →* Multiplicative W) (hc : Function.Bijective c) :
    normalizer (A : Set G) →* (W ≃ₗ[ZMod 2] W) :=
  linearAutHom.comp ((MulAut.congr (MulEquiv.ofBijective c hc)).toMonoidHom.comp
    A.normalizerMonoidHom)

theorem normalizerAction_coordinates (c : A →* Multiplicative W)
    (hc : Function.Bijective c) (h : normalizer (A : Set G)) (a : A) :
    normalizerAction c hc h (c a).toAdd =
      (c (A.normalizerMonoidHom h a)).toAdd := by
  let E := MulEquiv.ofBijective c hc
  change (E (A.normalizerMonoidHom h (E.symm (E a)))).toAdd = _
  rw [E.symm_apply_apply]
  rfl

theorem normalizerAction_restrict
    {ρ : Representation (ZMod 2) H W}
    (s : BinaryConjugationSection H A ⊥ ρ)
    (hi : Function.Injective s.coordinates) (h : H) :
    (normalizerAction s.coordinates ⟨hi,s.onto⟩
      ⟨(h : G),s.normalized h.property⟩).toLinearMap = ρ h := by
  ext w
  obtain ⟨a,ha⟩ := s.onto (Multiplicative.ofAdd w)
  have hw : (s.coordinates a).toAdd = w := congrArg Multiplicative.toAdd ha
  change normalizerAction s.coordinates ⟨hi,s.onto⟩
    ⟨(h : G),s.normalized h.property⟩ w = ρ h w
  rw [← hw]
  exact (normalizerAction_coordinates s.coordinates ⟨hi,s.onto⟩
    ⟨(h : G),s.normalized h.property⟩ a).trans (s.equivariant h a)

end Representation.BinaryConjugationSection
