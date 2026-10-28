module

public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.TensorVanishing

/-!
# No fixed vectors in the binary Hermitian model

A fixed Hermitian vector gives a fixed vector in the ambient quadratic
Frobenius tensor. Its fixed space is zero, so the Hermitian vector vanishes.
This is the fixed-kernel calculation needed when passing from the crossed
module factors to their literal orthogonal coordinates in Chapter 10.

Source: Aschbacher--Smith, 10.1.1(4) and 10.1.2(5), printed pp.741--742;
the ambient tensor calculation is the existing I.1.6(3) model calculation.
-/

public noncomputable section
namespace Representation.SL2.BinarySmall
open OrthogonalFourMinus OrthogonalFourMinus.FiniteModel
local instance fixedVectorBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (fixedField n) := ZMod.algebra _ 2
local instance fixedVectorBinaryModule (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

theorem hermitian_fixed_eq_zero (n : ℕ) [NeZero n] (X : Space n)
    (hX : ∀ g, hermitian n g X = X) : X = 0 := by
  have hx : X.val ∈ OneCohomology.fixed (tensorAction (conjugation n)) := by
    intro g
    exact congrArg Subtype.val (hX g)
  have hz := tensorAction_frobenius_fixed_eq_bot n (Nat.pos_of_ne_zero (NeZero.ne n))
  change X.val ∈ OneCohomology.fixed (tensorAction (iterateFrobeniusEquiv (GaloisField 2 (2 * n)) 2 n)) at hx
  rw [hz] at hx
  exact Subtype.ext (show X.val = 0 from hx)
end Representation.SL2.BinarySmall
