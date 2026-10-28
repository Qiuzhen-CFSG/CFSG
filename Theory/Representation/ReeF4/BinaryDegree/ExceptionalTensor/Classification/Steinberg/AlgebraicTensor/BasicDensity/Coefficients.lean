module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.RootOperators
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Multiplicity.RootOperators


/-!
# Comparison with the canonical rational root operator

Polynomial uniqueness identifies the degree-one coefficient of any published
`RootExpansion` with the canonical `EndNode.Multiplicity.rootOperator` of the
same actual action. Thus previously proved root identities apply to these
coefficients without choosing arbitrary differential witnesses.

Source: coefficient extraction for rational root actions, as used in
Steinberg, *Representations of Algebraic Groups* (1963), §§4–5 and 11.
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
variable {F : Type*} [Field F] [IsAlgClosed F]

/-- Every root expansion has the canonical first-degree operator. -/
theorem RootExpansion.coeff_one_eq_rootOperator {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (r : F4Chevalley.Root) :
    p.coeff r 1 = EndNode.Multiplicity.rootOperator B r := by
  classical
  ext v
  apply (Module.finBasis F B.Space).repr.injective
  ext i
  let l := (Module.finBasis F B.Space).coord i
  let q : Polynomial F := (p.coeff r).sum (fun n A => Polynomial.monomial n (l (A v)))
  have hq : q = EndNode.Multiplicity.rootPolynomial B r l v := by
    apply Polynomial.funext
    intro t
    rw [EndNode.Multiplicity.rootPolynomial_eval, ← p.eval_eq]
    simp only [q, Finsupp.sum, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro n hn
    exact mul_comm _ _
  have hc := congrArg (fun q : Polynomial F => q.coeff 1) hq
  change l (p.coeff r 1 v) = l (EndNode.Multiplicity.rootOperator B r v)
  rw [EndNode.Multiplicity.dual_rootOperator]
  by_cases h : 1 ∈ (p.coeff r).support
  · simpa [q, Finsupp.sum, Polynomial.coeff_monomial, eq_comm, h] using hc
  · simpa [q, Finsupp.sum, Polynomial.coeff_monomial, eq_comm, h,
      Finsupp.notMem_support_iff.mp h] using hc

/-- A vector fixed by the root group is killed by its first coefficient. -/
theorem RootExpansion.coeff_one_eq_zero_of_fixed {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (r : F4Chevalley.Root) (v : B.Space)
    (hv : ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v) :
    p.coeff r 1 v = 0 := by
  rw [p.coeff_one_eq_rootOperator]
  exact EndNode.Multiplicity.rootOperator_eq_zero_of_fixed B r v hv
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
