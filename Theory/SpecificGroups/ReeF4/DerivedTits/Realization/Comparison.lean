module

public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.Words
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.BinaryRelations
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Reduction of the binary Ree realization to a concrete matrix comparison

The root words are already exceptional fixed points, and the literal binary
matrices satisfy all 37 Parrott relations. An identification of their entries
under a basis enumeration therefore completes the realization. The matrix
comparison is retained as an explicit premise until it has been proved for
the actual root curves; no isomorphism or recognition certificate is assumed.

Source: Parrott (1972), printed p.683; GLS3 §§2.3–2.4.
-/

public section
noncomputable section
namespace ReeF4.DerivedTits.Realization

open Theory.AlgebraicGroup

/-- The canonical inclusion of binary scalars into the actual coefficient field. -/
@[expose] def binaryScalar : ZMod 2 →+* CoefficientField 0 :=
  ZMod.castHom (dvd_refl 2) (CoefficientField 0)

/-- The literal matrices in the actual coefficient field. -/
def specializedBinary : Tits.ParrottGenerator →
    (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
  fun i => Units.map binaryScalar.mapMatrix.toMonoidHom (Binary.assignment i)

/-- The actual split matrices, with their rows and columns numbered by `e`. -/
def numberedSplit (e : F4Chevalley.BasisIndex ≃ Fin 52) :
    SplitGroup 0 →* (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
  (Units.map (Matrix.reindexRingEquiv (CoefficientField 0) e).toMonoidHom).comp
    (SplitGroup 0).subtype

private theorem numberedSplit_injective (e : F4Chevalley.BasisIndex ≃ Fin 52) :
    Function.Injective (numberedSplit e) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  apply (Matrix.reindexRingEquiv (CoefficientField 0) e).injective
  exact congrArg Units.val h

/-- The remaining obligation is equality of actual matrix entries in one
explicit basis enumeration. -/
@[expose] def MatrixComparison (e : F4Chevalley.BasisIndex ≃ Fin 52) : Prop :=
  ∀ i, Matrix.reindex e e ((assignment i).val.val) =
    (Binary.generatorMatrix i).map binaryScalar

private theorem comparison_units (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : MatrixComparison e) (i : Tits.ParrottGenerator) :
    numberedSplit e (assignment i) = specializedBinary i :=
  Units.ext (h i)

private theorem specializedBinary_relations :
    Tits.SatisfiesParrottRelations specializedBinary := by
  let f : (Matrix (Fin 52) (Fin 52) (ZMod 2))ˣ →*
      (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
    Units.map binaryScalar.mapMatrix.toMonoidHom
  have he : FreeGroup.lift specializedBinary = f.comp (FreeGroup.lift Binary.assignment) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    rfl
  intro i
  rw [he, MonoidHom.comp_apply, Binary.assignment_relations i, map_one]

private theorem specializedBinary_nontrivial : ∃ i, specializedBinary i ≠ 1 := by
  refine ⟨.s8, ?_⟩
  intro h
  have he := congrArg (fun a : (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ =>
    a.val 0 28) h
  change binaryScalar (Binary.generatorMatrix .s8 0 28) =
    (1 : Matrix (Fin 52) (Fin 52) (CoefficientField 0)) 0 28 at he
  rw [Binary.s8_entry, map_one] at he
  exact one_ne_zero (he.trans (Matrix.one_apply_ne (by decide)))

/-- Matrix comparison transfers the checked presentation to the fixed root words. -/
theorem assignment_relations_of_matrixComparison
    (e : F4Chevalley.BasisIndex ≃ Fin 52) (h : MatrixComparison e) :
    Tits.SatisfiesParrottRelations assignment := by
  have he : (numberedSplit e).comp (FreeGroup.lift assignment) =
      FreeGroup.lift specializedBinary := by
    apply FreeGroup.ext_hom
    intro i
    simpa only [MonoidHom.comp_apply, FreeGroup.lift_apply_of] using comparison_units e h i
  intro i
  apply numberedSplit_injective e
  change ((numberedSplit e).comp (FreeGroup.lift assignment)) (Tits.parrottRelator i) = _
  rw [he, specializedBinary_relations i, map_one]

/-- The same entry comparison gives a nonidentity actual split matrix. -/
theorem assignment_nontrivial_of_matrixComparison
    (e : F4Chevalley.BasisIndex ≃ Fin 52) (h : MatrixComparison e) :
    ∃ i, assignment i ≠ 1 := by
  obtain ⟨i, hi⟩ := specializedBinary_nontrivial
  refine ⟨i, fun he => hi ?_⟩
  rw [← comparison_units e h i, he, map_one]

end ReeF4.DerivedTits.Realization

namespace ReeF4.DerivedTits

/-- Conditional assembly; the explicit root-matrix comparison remains to be
proved before asserting the unconditional `parrott_realization`. -/
theorem parrott_realization_of_matrixComparison
    (e : Theory.AlgebraicGroup.F4Chevalley.BasisIndex ≃ Fin 52)
    (h : Realization.MatrixComparison e) :
    ∃ g : Tits.ParrottGenerator → SplitGroup 0,
      (∀ i, reeTwist 0 (g i) = g i) ∧
      Tits.SatisfiesParrottRelations g ∧ (∃ i, g i ≠ 1) :=
  ⟨Realization.assignment, Realization.assignment_fixed,
    Realization.assignment_relations_of_matrixComparison e h,
    Realization.assignment_nontrivial_of_matrixComparison e h⟩

end ReeF4.DerivedTits
