module

public import Theory.Representation.Triality.BinaryDegree
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport

/-!
# Binary triality degree from classification on the concrete Spin carrier

The unconditional Geck-to-Spin carrier equivalence transports tensor data on
faithful irreducibles without changing the scalar field or vector space.
Applying it over each Schur-field algebraic closure discharges the model
comparison in the binary degree theorem and yields its exact `24 * n` bound,
including at n = 1.

The restricted-weight classification remains an explicit input, owned by its
source theorem. This corollary does not assert that classification.

Sources: GLS3 §2.8 (`refs/KGroup/GLS3/chapter2.tex`) and Aschbacher–Smith,
*The Classification of Quasithin Groups*, printed p.356 (PDF p.367).
-/

public section
namespace Triality.BinaryDegree
universe v

/-- A proved tensor classification on the actual Clifford Spin elementary
central quotient implies the exact binary bound on `Standard.BinaryCarrier`.
No root-comparison, field-embedding or fixed-point-coverage premise remains. -/
theorem triality_binary_degree_ge_of_spin_tensor_classification
    {n : ℕ} (hn : 0 < n)
    (hclassification : ∀
      (E : Type v) [Field E] [Finite E] [CharP E 2]
      (W : Type v) [AddCommGroup W] [Module (AlgebraicClosure E) W]
      [FiniteDimensional (AlgebraicClosure E) W]
      (σ : Representation (AlgebraicClosure E)
        (Triality.SimplyConnected.GraphField.Carrier (AlgebraicClosure E) n) W),
      σ.IsIrreducible → Function.Injective σ → Nonempty (TensorData n σ))
    {V : Type v} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Triality.Standard.BinaryCarrier n hn) V)
    [ρ.IsIrreducible] (hρ : Function.Injective ρ) :
    24 * n ≤ Module.finrank (ZMod 2) V := by
  apply triality_binary_degree_ge_of_tensor_classification hn ?_ ρ hρ
  intro E _ _ _ W _ _ _ σ hi hf
  exact tensorClassification_of_spin (AlgebraicClosure E) hn (hclassification E W) σ hi hf

end Triality.BinaryDegree
