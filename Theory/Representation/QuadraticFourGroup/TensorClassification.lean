module

public import Theory.Representation.QuadraticFourGroup.Models
public import Theory.Representation.QuadraticFourGroup.TensorClassification.AlgebraicInputs
public import Theory.Representation.QuadraticFourGroup.TensorClassification.CubicNatural
public import Theory.Representation.QuadraticFourGroup.TensorClassification.Descent
public import Theory.Representation.QuadraticFourGroup.TensorClassification.ProductFactors

/-!
# Binary natural-tensor classification

For an irreducible binary representation of the genuine product of two PSL₂
factors, the cubic fixed-point conditions survive passage to the Schur field
and its algebraic closure. An irreducible external-tensor decomposition and
the cubic natural-module classification over that closure then give two
explicit Frobenius factors. Trace-field identification and Noether--Deuring
descent produce the exact binary tensor model in `Models`.

`isNaturalTensorAlong_of_cubicFreeOnFactors` assembles the proved product
decomposition, single-factor classification and scalar descent. Its only
additional hypotheses are `1 < n` and the fixed-point conditions on the two
factors. The resulting factors are faithful two-dimensional representations
over the same defining field, and the equivalence is binary linear.

This proves the representation prerequisite in GLS2 Theorem 25.14 Step 5.
Source: `refs/KGroup/GLS2/ChapterG.tex`, the remarks at lines 786--788 and
Step 5 at lines 906--928. The tensor field is F_(2^n), as specified by the
remarks, rather than the misprinted Step 5 heading. Component recognition
and the derivation of the cubic fixed-point hypotheses belong to the full
quadratic four-group theorem.
-/

public section

namespace Representation.QuadraticFourGroup.TensorClassification

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) (Factor n × Factor n) V) [σ.IsIrreducible]

/-- Assemble the two algebraically closed inputs, including all scalar descent.
The product and single-factor classifications remain explicit premises. -/
theorem isNaturalTensorAlong_of_algebraic_inputs
    (h : CubicFreeOnFactors σ)
    (hprod : HasIrreducibleProductFactors (schurClosureRep σ))
    (hnat : CubicNaturalClassification (schurClosureEmbedding σ)) :
    IsNaturalTensorAlong (MonoidHom.id (Factor n × Factor n)) σ := by
  obtain ⟨i, j, _, _, ⟨φ⟩⟩ := exists_naturalTensor_equiv_of_factors
    (schurClosureRep σ) (schurClosureEmbedding σ) h.schurClosureRep hprod hnat
  exact isNaturalTensorAlong_of_schurClosure_equiv σ (schurClosureEmbedding σ) i j φ

/-- An irreducible binary representation of `PSL₂(2ⁿ) × PSL₂(2ⁿ)` whose
order-three elements in each factor act fixed-point freely is an actual
tensor over `GaloisField 2 n` of two faithful two-dimensional representations,
restricted to the binary field. This is the representation prerequisite of
GLS2 Theorem 25.14, Step 5 and its remarks. -/
theorem isNaturalTensorAlong_of_cubicFreeOnFactors (hn : 1 < n)
    (h : CubicFreeOnFactors σ) :
    IsNaturalTensorAlong (MonoidHom.id (Factor n × Factor n)) σ :=
  isNaturalTensorAlong_of_algebraic_inputs σ h
    (schurClosureRep_hasIrreducibleProductFactors σ)
    (cubicNaturalClassification_schurClosure hn σ)

end Representation.QuadraticFourGroup.TensorClassification

end
