module

public import Theory.Character.GLTwoUnipotentWeightDimension
public import Theory.Character.GLTwoWhittakerMultiplicity
public import Mathlib.NumberTheory.LegendreSymbol.Complex
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Degree of a GL₂ representation without unipotent fixed vectors

An irreducible complex representation of `GL₂(F)` with no nonzero vector fixed
by the upper unipotent subgroup has degree `|F| - 1`. The dimension formula for
nontrivial upper-unipotent weights supplies divisibility and positivity, while
the GL₂ Whittaker multiplicity-one theorem makes the selected weight one
dimensional. The proof uses the actual `upperRightHom` matrices and the
primitive complex additive character supplied by Mathlib, so it includes the
field with two elements.

This is the cuspidal branch of the ordinary GL₂ character-degree analysis
underlying Brauer, *Desarguesian planes II*, printed p. 128.
-/

open scoped MatrixGroups

private theorem irreducible_dimension_pos
    {F : Type*} [Field F] (size : ℕ)
    (rho : Representation ℂ (GL (Fin 2) F) (Fin size → ℂ))
    (hirred : Representation.IsIrreducible rho) : 0 < size := by
  let := hirred
  have : Nontrivial rho.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GL (Fin 2) F)) rho.asModule
  have : Nontrivial (Fin size → ℂ) := ‹Nontrivial rho.asModule›
  simpa using (Module.finrank_pos_iff (R := ℂ) (M := Fin size → ℂ)).2 inferInstance

public theorem gl2_irreducible_dimension_of_no_unipotent_fixed
    {F : Type*} [Field F] [Finite F] (size : ℕ)
    (rho : Representation ℂ (GL (Fin 2) F) (Fin size → ℂ))
    (hirred : Representation.IsIrreducible rho)
    (hnofixed : ¬ ∃ vector, vector ≠ 0 ∧ ∀ parameter : F,
      rho (Matrix.GeneralLinearGroup.upperRightHom parameter) vector = vector) :
    size = Nat.card F - 1 := by
  let psi := AddChar.FiniteField.primitiveChar_to_Complex F
  have hpsi : psi ≠ 1 := by
    simpa only [AddChar.mulShift_one] using
      AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F (a := 1) one_ne_zero
  have hdim := gl2_dimension_eq_nontrivial_unipotent_weight_mul
    size rho hnofixed psi hpsi
  have hbound := gl2_nontrivial_unipotent_weight_finrank_le_one
    size rho hirred psi hpsi
  have hpos := irreducible_dimension_pos size rho hirred
  have hweight : Module.finrank ℂ
      (⨅ parameter : F,
        Module.End.eigenspace
          (rho (Matrix.GeneralLinearGroup.upperRightHom parameter)) (psi parameter) :
        Submodule ℂ (Fin size → ℂ)) = 1 := by
    have hnonzero : Module.finrank ℂ
        (⨅ parameter : F,
          Module.End.eigenspace
            (rho (Matrix.GeneralLinearGroup.upperRightHom parameter)) (psi parameter) :
          Submodule ℂ (Fin size → ℂ)) ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hdim
      omega
    omega
  simpa only [hweight, mul_one] using hdim

#print axioms gl2_irreducible_dimension_of_no_unipotent_fixed
