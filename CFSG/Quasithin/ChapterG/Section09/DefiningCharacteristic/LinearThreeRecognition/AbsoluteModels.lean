module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.Models
public import Theory.Representation.EndFieldRep
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Shared absolute-model statements for SL₃ recognition

These predicates specify actual equivalences of the scalar extension of the
Schur-field representation. They separate two independent obligations:
classification over a splitting field, and descent of those equivalences to
the natural binary module or the half-field tensor module. They assert no
classification theorem and supply no witnesses.

An arbitrary embedding of the matrix-entry field permits field twists.
The tensor predicate permits duality but requires the second factor to use
the precise 2ʳ-power automorphism, not an unrelated automorphism.

Source: GLS III 2.8.6, 2.8.8 and 2.8.10(c); Aschbacher--Smith G.9.3(8),(17).
-/

@[expose] public section

open Representation
open scoped MatrixGroups MonoidAlgebra

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(3,F) V) [IsIrreducible ρ]

/-- The actual commuting endomorphism field of the binary action. -/
abbrev SchurField := Module.End (ZMod 2)[SL(3,F)] ρ.asModule

/-- An algebraic closure of the actual Schur field. -/
abbrev SplittingField := AlgebraicClosure (SchurField ρ)

/-- The degree of the actual Schur field over the binary field. -/
noncomputable def schurDegree : ℕ := Module.finrank (ZMod 2) (SchurField ρ)

/-- Absolute natural recognition, with both duality and coefficient twists. -/
def HasAbsoluteNaturalModel : Prop :=
  ∃ ι : F →+* SplittingField ρ,
    Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv (naturalOver F ι)) ∨
    Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv (naturalOver F ι).dual)

/-- Absolute half-field tensor recognition, including its permitted dual. -/
def HasAbsoluteTwistedModel (r : ℕ) : Prop :=
  ∃ σ : F ≃+* F, (∀ a, σ a = a ^ (2 ^ r)) ∧
    ∃ ι : F →+* SplittingField ρ,
      Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
        (twistedTensorOver F ι σ)) ∨
      Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
        (twistedTensorOver F ι σ).dual)

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
