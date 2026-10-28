module

public import Theory.Representation.QuadraticFourGroup.TensorClassification.FixedPoints
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The absolutely irreducible Schur-field reduction

An irreducible binary representation becomes absolutely irreducible when
regarded over its actual Schur endomorphism field. We extend that action to
its algebraic closure, retaining finite dimension and the cubic fixed-point
conditions, and embed the matrix field in the same closure.

This is the scalar setup for GLS2 Theorem 25.14, Step 5. It does not identify
the binary scalar extension with a single constituent.
-/

@[expose] public section

open scoped MonoidAlgebra TensorProduct
namespace Representation.QuadraticFourGroup.TensorClassification

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) (Factor n × Factor n) V) [σ.IsIrreducible]

abbrev SchurField := Module.End (ZMod 2)[Factor n × Factor n] σ.asModule
abbrev SchurClosure := AlgebraicClosure (SchurField σ)
abbrev SchurSpace := SchurClosure σ ⊗[SchurField σ] σ.asModule

noncomputable def schurClosureRep : Representation (SchurClosure σ) (Factor n × Factor n)
    (SchurSpace σ) := extendScalars (SchurClosure σ) σ.endFieldRep

instance schurField_moduleFinite : Module.Finite (SchurField σ) σ.asModule := by
  let : Finite σ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) σ.asModule)
  exact Module.Finite.of_finite

instance schurClosureRep_finiteDimensional : FiniteDimensional (SchurClosure σ) (SchurSpace σ) :=
  inferInstanceAs (Module.Finite (SchurClosure σ) (SchurClosure σ ⊗[SchurField σ] σ.asModule))

instance schurClosureRep_isIrreducible : (schurClosureRep σ).IsIrreducible := by
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  exact IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep (SchurClosure σ)

theorem CubicFreeOnFactors.schurClosureRep
    (h : CubicFreeOnFactors σ) : CubicFreeOnFactors (schurClosureRep σ) :=
  h.endFieldRep.extendScalars (SchurClosure σ)

instance schurField_charTwo : CharP (SchurField σ) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField σ)).injective 2

instance schurClosure_charTwo : CharP (SchurClosure σ) 2 :=
  charP_of_injective_algebraMap (algebraMap (SchurField σ) (SchurClosure σ)).injective 2

noncomputable def schurClosureEmbedding : GaloisField 2 n →+* SchurClosure σ := by
  let : Algebra (ZMod 2) (SchurClosure σ) := ZMod.algebra _ 2
  exact (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 n)
    (M := SchurClosure σ)).toRingHom

end Representation.QuadraticFourGroup.TensorClassification

end
