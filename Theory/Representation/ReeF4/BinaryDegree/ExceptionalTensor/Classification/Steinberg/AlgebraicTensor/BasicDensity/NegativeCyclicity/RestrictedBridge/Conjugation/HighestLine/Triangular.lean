module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.HighestLine.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.HighestLine.Triangular.RootRelations

/-!
# Triangular spanning on the actual simple F₄ quotient

The canonical root operators and simple Cartan commutators satisfy the needed
structure relations, by differentiation of the concrete adjoint action and
transport through the original rational factor and its quotient algebra action.
Reordering words into negative, Cartan and positive blocks spans the generated
algebra. Simplicity and Jacobson density identify this with the full quotient
endomorphism algebra. The imported Cartan/root relation also proves that the
sum of all negative-root images is stable under every simple Cartan operator.

Neither conclusion needs a highest-weight hypothesis, a rational lift of the
quotient, or a choice of conjugation implementers. These are the two inputs to
the highest-line argument retained in `HighestLine.lean`.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §2, structure equations 2.1–2.6, Curtis 2.7 and monomials 2.8;
DOI 10.1017/S0027763000011016.
-/

public section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
namespace SimpleCyclicQuotient
variable {B : AlgebraicFactor F} {v : B.Space} (Q : SimpleCyclicQuotient B v)

/-- Negative, simple Cartan, and positive words span the full endomorphism
algebra of the actual simple quotient. No ordering inside a block is required. -/
theorem triangularSpan_eq_top [CharP F 2] : Q.triangularSpan = ⊤ :=
  Q.triangularSpan_eq_top_of_mixed_commutators fun p n =>
    Q.operator_commutator_mem_rootCartanSpan p.val n.val

end SimpleCyclicQuotient
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
