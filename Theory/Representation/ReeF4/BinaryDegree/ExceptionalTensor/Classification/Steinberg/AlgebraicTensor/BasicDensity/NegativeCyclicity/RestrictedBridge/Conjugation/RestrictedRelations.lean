module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.Basic

/-!
# Restricted square relations on the actual simple differential quotient

The additive root-group law identifies composition with the first canonical
root operator with formal differentiation of each scalar orbit polynomial.
Extracting the next coefficient in characteristic two gives square zero.
The actual quotient algebra action transports this relation to every quotient
root operator, without assuming differential irreducibility of the factor.

These are the root-power relations in Steinberg's restricted-module convention
preceding Curtis 2.7. The other Chevalley and Cartan relations, highest-line
uniqueness, and conjugation invariance are not asserted here.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §2; DOI 10.1017/S0027763000011016.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

private theorem rootPolynomial_dual_operator (B : AlgebraicFactor F)
    (r : F4Chevalley.Root) (l : Module.Dual F B.Space) (v : B.Space) :
    EndNode.Multiplicity.rootPolynomial B r
        (l.comp (EndNode.Multiplicity.rootOperator B r)) v =
      (EndNode.Multiplicity.rootPolynomial B r l v).derivative := by
  have root_add (s t : F) :
      algebraicRootElement r (s + t) = algebraicRootElement r s * algebraicRootElement r t := by
    apply ZeroAndMiddle.carrierMatrix_injective
    simp only [map_mul, ZeroAndMiddle.carrierMatrix_root, F4Chevalley.rootCurve_add]
  apply Polynomial.funext
  intro t
  have hp : EndNode.Multiplicity.rootPolynomial B r l
      ((B.action.action (algebraicRootElement r t) : Module.End F B.Space) v) =
      Polynomial.taylor t (EndNode.Multiplicity.rootPolynomial B r l v) := by
    apply Polynomial.funext
    intro s
    simp only [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, EndNode.Multiplicity.rootPolynomial_eval,
      root_add, map_mul, Units.val_mul, Module.End.mul_apply]
  rw [EndNode.Multiplicity.rootPolynomial_eval, LinearMap.comp_apply,
    EndNode.Multiplicity.dual_rootOperator, hp, Polynomial.taylor_coeff_one]

/-- Every canonical root operator on the original rational factor has square zero. -/
theorem rootOperator_square [CharP F 2] (B : AlgebraicFactor F) (r : F4Chevalley.Root) :
    EndNode.Multiplicity.rootOperator B r ^ 2 = 0 := by
  ext v
  apply (Module.finBasis F B.Space).repr.injective
  ext i
  let l := (Module.finBasis F B.Space).coord i
  change l (EndNode.Multiplicity.rootOperator B r
    (EndNode.Multiplicity.rootOperator B r v)) = l 0
  change (l.comp (EndNode.Multiplicity.rootOperator B r))
    (EndNode.Multiplicity.rootOperator B r v) = l 0
  rw [EndNode.Multiplicity.dual_rootOperator, rootPolynomial_dual_operator,
    Polynomial.coeff_derivative]
  have htwo : (1 : F) + 1 = 0 := by
    simpa only [Nat.cast_ofNat, one_add_one_eq_two] using CharP.cast_eq_zero F 2
  simp only [Nat.cast_one, htwo, mul_zero, map_zero]

namespace SimpleCyclicQuotient
variable {B : AlgebraicFactor F} {v : B.Space} (Q : SimpleCyclicQuotient B v)

/-- The same restricted relation holds on the actual simple quotient. -/
theorem operator_square [CharP F 2] (r : F4Chevalley.Root) : Q.operator r ^ 2 = 0 := by
  have h : rootGenerator B r ^ 2 = 0 := Subtype.ext (rootOperator_square B r)
  change Q.rootAction (rootGenerator B r) ^ 2 = 0
  rw [← map_pow, h, map_zero]

end SimpleCyclicQuotient

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
