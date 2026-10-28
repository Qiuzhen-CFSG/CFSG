module
public import Theory.Representation.ReeF4.BinaryDegree
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceHighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Exhaustion
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.Source
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Source
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.Source

/-!
# Faithful irreducible binary degree of the Ree groups

The proved finite exceptional tensor classification supplies actual algebraic
factors for the representation over its Schur-field closure. The basic F4
minimum is 26. Coefficient Frobenius and uniqueness of the tensor parameters
supply periodic factor dimensions, and Schur descent multiplies the resulting
lower bound by the genuine odd field exponent. No classification, geometric,
class-count, or representation-theoretic input remains explicit.

This is the model estimate used in G.9.3 to exclude the large Ree family.
Source: GLS3, 2.8.2, 2.8.5, 2.8.6(b) and 2.8.8; Aschbacher--Smith,
*The Classification of Quasithin Groups*, printed p.356.
-/

public section

open Theory.AlgebraicGroup Representation.FrobeniusTensor
namespace ReeF4.BinaryDegree
open ExceptionalTensor ExceptionalTensor.Classification
universe v

/-- Every faithful irreducible binary representation of the genuine Ree
carrier has degree at least 26 times its field exponent. -/
theorem ree_binary_degree_ge {k : ℕ} (hk : 1 ≤ k) {V : Type v} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Model k) V)
    [ρ.IsIrreducible] (hρ : Function.Injective ρ) :
    26 * (2 * k + 1) ≤ Module.finrank (ZMod 2) V := by
  apply ree_binary_degree_ge_of_tensor_classification ?_ hk ρ hρ
  intro m _hm E _ _ _ W _ _ _ σ hi hf
  let := hi
  have hU := Steinberg.Geometry.carrier_isUniversalVersion_of_semisimple_centers
    (F := AlgebraicClosure E)
    (fun _ _ hH _ hT =>
      SemisimpleCenterContainment.center_le_maximalTorus_of_semisimple hH hT)
  obtain ⟨B, hB, ⟨e⟩⟩ := Steinberg.FiniteRootAction.exists_tensor_of_class_bound m hU
    (coefficientHom (AlgebraicClosure E) m)
    (Steinberg.FiniteRootAction.exceptionalTensor_distinction m hU)
    (Steinberg.Geometry.OddClasses.model_odd_class_bound m) σ
  obtain ⟨hl, hp, hs⟩ := factorization_consequences σ hf
    (splitEmbedding (coefficientHom (AlgebraicClosure E) m))
    (fun B hB => Steinberg.FiniteRootAction.exceptionalTensor_irreducible m B hU hB
      (coefficientHom (AlgebraicClosure E) m))
    (Steinberg.FiniteRootAction.exceptionalTensor_distinction m hU) B hB e
    (Steinberg.SourceHighestWeight.character_shift
      (coefficientHom (AlgebraicClosure E) m) B hB)
  exact ⟨traceTensorData_of_algebraic_factors σ
    (splitEmbedding (coefficientHom (AlgebraicClosure E) m)) B e hB
    basicFactorMinimum_charTwo hl hp hs⟩
end ReeF4.BinaryDegree
