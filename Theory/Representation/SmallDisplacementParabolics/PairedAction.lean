module
public import Theory.Representation.SmallDisplacementParabolics.Models

/-!
# The literal paired natural representation

At an output coordinate i, a wreath element first shifts the input by the
inverse of its right coordinate, then applies its left linear map at i.
This defines the six-dimensional paired natural representation. The paired
clause of `ActionModel` supplies an actual equivalence to this representation.

This shared action is the input to the paired parabolic calculation in
Aschbacher--Smith, original15.2.27(2), printed p.1119 (PDF p.1136).
No parabolic existence, stabilizer classification or movement is assumed here.
-/

@[expose] public section
namespace Representation.SmallDisplacementParabolics

/-- The regular wreath action, with the inverse shift at the input coordinate. -/
def pairedRepresentation : Representation (ZMod 2) PairedActor (PairIndex → ThreeSpace) where
  toFun g := {
    toFun v := fun i => g.left i (v (g.right⁻¹ * i))
    map_add' v w := by funext i; exact map_add (g.left i) _ _
    map_smul' c v := by funext i; exact map_smul (g.left i) _ _ }
  map_one' := by ext v i; simp
  map_mul' g h := by
    ext v i
    simp [RegularWreathProduct.mul_left, RegularWreathProduct.mul_right, mul_assoc]

@[simp] theorem pairedRepresentation_apply (g : PairedActor) (v : PairIndex → ThreeSpace)
    (i : PairIndex) : pairedRepresentation g v i = g.left i (v (g.right⁻¹ * i)) := rfl

/-- The coordinate clause in `ActionModel` is an actual equivalence of representations. -/
def pairedEquiv {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (e : D ≃* PairedActor)
    (E : W ≃ₗ[ZMod 2] (PairIndex → ThreeSpace))
    (hE : ∀ g w i, E (ρ g w) i = (e g).left i (E w ((e g).right⁻¹ * i))) :
    ρ.Equiv (pairedRepresentation.comp e.toMonoidHom) :=
  Representation.Equiv.mk E (by intro g; apply LinearMap.ext; intro w; funext i; exact hE g w i)

end Representation.SmallDisplacementParabolics
