module
public import Theory.SpecificGroups.AffineEight.TransferGeometry

/-!
# The characteristic involution class of the affine-eight group

The multiplier-five involution has exactly two automorphic images: itself
and its product with translation by four. These are the only elements of
square one with centralizer of order sixteen, as checked in the explicit
finite model. Translation by four is a commutator, so all homomorphisms to
commutative groups take the same value on these images.

This intrinsic calculation supplies the normalizer-invariance input to the
ordinary transfer obstruction of Andersen--Oliver--Ventura, *Fusion systems
and amalgams*, Proposition 2.3(b), for the holomorph of C8.
-/

namespace AffineEight
open scoped commutatorElement

/-- Automorphisms preserve the conjugacy class of the multiplier-five involution. -/
public theorem automorphism_five (f : MulAut Model) :
    f (SemidirectProduct.inr five) = SemidirectProduct.inr five ∨
    f (SemidirectProduct.inr five) =
      SemidirectProduct.inl (Multiplicative.ofAdd (4 : ZMod 8)) *
        SemidirectProduct.inr five := by
  let t : Model := SemidirectProduct.inr five
  have hsq : (f t) ^ 2 = 1 := by
    rw [← map_pow, show t ^ 2 = 1 by decide, map_one]
  have hcard : Fintype.card {y : Model // y * f t = f t * y} = 16 := by
    let e : {y : Model // y * t = t * y} ≃
        {y : Model // y * f t = f t * y} := {
      toFun := fun y => ⟨f y, by simpa only [map_mul] using congrArg f y.property⟩
      invFun := fun y => ⟨f.symm y, by
        apply f.injective
        simpa only [map_mul, f.apply_symm_apply] using y.property⟩
      left_inv := fun y => Subtype.ext (f.symm_apply_apply y)
      right_inv := fun y => Subtype.ext (f.apply_symm_apply y) }
    rw [← Fintype.card_congr e]
    decide
  have hfinite : ∀ x : Model, x ^ 2 = 1 →
      Fintype.card {y : Model // y * x = x * y} = 16 →
      x = SemidirectProduct.inr five ∨
      x = SemidirectProduct.inl (Multiplicative.ofAdd (4 : ZMod 8)) *
        SemidirectProduct.inr five := by decide
  exact hfinite (f t) hsq hcard

/-- Every commutative image of the multiplier-five involution is
invariant under all automorphisms. -/
public theorem map_automorphism_five {A : Type*} [CommGroup A]
    (φ : Model →* A) (f : MulAut Model) :
    φ (f (SemidirectProduct.inr five)) = φ (SemidirectProduct.inr five) := by
  rcases automorphism_five f with h | h
  · rw [h]
  · rw [h, map_mul]
    have hz : φ (SemidirectProduct.inl (Multiplicative.ofAdd (4 : ZMod 8))) = 1 := by
      have hc : ⁅(SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 8)) : Model),
          (SemidirectProduct.inr five : Model)⁆ =
          SemidirectProduct.inl (Multiplicative.ofAdd (4 : ZMod 8)) := by decide
      rw [← hc, map_commutatorElement]
      simp [commutatorElement_def]
    rw [hz, one_mul]

end AffineEight
