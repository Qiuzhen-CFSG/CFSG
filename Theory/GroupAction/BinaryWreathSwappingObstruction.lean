module
public import Theory.GroupAction.BinaryWreathPlaneGeometry

/-!
# A swapping involution and its point stabilizer

In the natural binary two-plane wreath module, a swapping involution fixes
only singular nonzero points. At each such point, some element of the point
stabilizer has commutator with the involution that moves its displacement
space. This is the finite action obstruction in Aschbacher--Smith 14.6.13,
printed p.1032. The certificate checks the 72-element actor on 16 vectors.
-/

public section
open Subgroup
open scoped commutatorElement
namespace BinaryWreathPointStabilizer
attribute [local instance] FourGroupMatrixCoordinates.naturalAction
attribute [local instance] RegularWreathProduct.functionModule
local instance : Fintype Actor := Fintype.ofEquiv ((Index → MatrixActor) × Index)
  (RegularWreathProduct.equivProd MatrixActor Index).symm
local instance (x : Actor) (z : Vector) : Decidable (∃ y : Actor, y • z = z ∧
    ∃ v : Vector, ⁅x,y⁆ • (x • v * v⁻¹) ≠ x • v * v⁻¹) :=
  Fintype.decidableExistsFintype
local instance (x : Actor) : Decidable (∀ z : Vector,
    x.right ≠ 1 → (∀ v : Vector, x • (x • v) = v) → z ≠ 1 → x • z = z →
    ∃ y : Actor, y • z = z ∧
      ∃ v : Vector, ⁅x,y⁆ • (x • v * v⁻¹) ≠ x • v * v⁻¹) := Fintype.decidableForallFintype
set_option maxRecDepth 4096 in
private theorem swapping_obstruction_check : ∀ (x : Actor) (z : Vector),
    x.right ≠ 1 → (∀ v : Vector, x • (x • v) = v) → z ≠ 1 → x • z = z →
    ∃ y : Actor, y • z = z ∧
      ∃ v : Vector, ⁅x,y⁆ • (x • v * v⁻¹) ≠ x • v * v⁻¹ := by
  decide +kernel
/-- A swapping involution cannot have all its point-stabilizer commutators
fix its displacement space pointwise. -/
theorem swapping_point_stabilizer_obstruction (x : Actor) (z : Vector)
    (hs : x.right ≠ 1) (hx : x ^ 2 = 1) (hz : z ≠ 1) (hf : x • z = z) :
    ∃ y : Actor, y • z = z ∧
      ∃ v : Vector, ⁅x,y⁆ • (x • v * v⁻¹) ≠ x • v * v⁻¹ := by
  apply swapping_obstruction_check x z hs _ hz hf
  intro v
  rw [←mul_smul,←pow_two,hx,one_smul]
end BinaryWreathPointStabilizer
