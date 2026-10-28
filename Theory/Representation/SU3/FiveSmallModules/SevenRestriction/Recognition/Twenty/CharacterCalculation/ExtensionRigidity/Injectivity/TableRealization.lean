module
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.TableRealization.Model
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.TableRealization.Products
/-!
# Realization of the marked degree-twenty Bruhat tables

The actual 126-coset augmentation quotient gives a representation of the
standard table-field SU group on twenty coordinates. The checked product
program identifies both literal coefficient families in its standard basis.
Its irreducibility supplies the SU-center kernel and root-center fixed-space
conditions. This constructs the requested reference model over every finite
characteristic-two field, without a recognition or injectivity assumption.

Source: Huppert II.10.12 for the equations; Guralnick–Malle Proposition 4.3
for the degree-twenty application. See TableRealization/source/README.md for
the retained coset and coefficient provenance.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.TableRealization
open Degrees.TrivialCalculation.MiddleFactors.Realization
open ProductCertificate
universe v
variable (K : Type v) [Field K] [Finite K] [CharP K 2]
attribute [local irreducible] representation quotientCoordinates

omit [Finite K] [CharP K 2] in
theorem left_zero : Certificate.matrix (K := K) (Certificate.Data.leftRows 0 0) = 0 := by
  have h : Certificate.Data.leftRows 0 0 = fun _ => 0 := by decide +kernel
  rw [h]
  ext i j
  simp [Certificate.matrix, Certificate.entry]
omit [Finite K] [CharP K 2] in
theorem right_zero : Certificate.matrix (K := K) (Certificate.Data.rightRows 0 0) = 0 := by
  have h : Certificate.Data.rightRows 0 0 = fun _ => 0 := by decide +kernel
  rw [h]
  ext i j
  simp [Certificate.matrix, Certificate.entry]

theorem left_marked (s : Fin 2) (c : Fin 5) :
    LinearMap.toMatrixAlgEquiv (Pi.basisFun K (Fin 20))
      (leftCoefficient form rfl (representation K) (marked s c)) =
      Certificate.matrix (Certificate.Data.leftRows s c) := by
  by_cases hz : (marked s c).val.2 = 0
  · unfold leftCoefficient
    rw [dif_pos hz, map_zero]
    obtain ⟨rfl, rfl⟩ := (marked_second_zero s c).mp hz
    exact (left_zero K).symm
  · unfold leftCoefficient
    rw [dif_neg hz]
    change matrixRepresentation K _ = _
    have h := element_image K (matrixRepresentation K) (matrixRepresentation_actor K)
      (leftIndex s c) (leftIndex_lt s c)
    rw [left_element s c hz, left_binary_matrix s c hz, cast_certificate] at h
    exact h

theorem right_marked (s : Fin 2) (c : Fin 5) :
    LinearMap.toMatrixAlgEquiv (Pi.basisFun K (Fin 20))
      (rightCoefficient form rfl (representation K) (marked s c)) =
      Certificate.matrix (Certificate.Data.rightRows s c) := by
  by_cases hz : (marked s c).val.2 = 0
  · unfold rightCoefficient
    rw [dif_pos hz, map_zero]
    obtain ⟨rfl, rfl⟩ := (marked_second_zero s c).mp hz
    exact (right_zero K).symm
  · unfold rightCoefficient
    rw [dif_neg hz]
    change matrixRepresentation K _ = _
    have h := element_image K (matrixRepresentation K) (matrixRepresentation_actor K)
      (rightIndex s c) (rightIndex_lt s c)
    rw [right_element s c hz, right_binary_matrix s c hz, cast_certificate] at h
    exact h

/-- The genuine basis and both literal coefficient families. -/
noncomputable def coordinates : Coordinates form rfl (representation K) where
  basis := Pi.basisFun K (Fin 20)
  point := point
  centerEquiv := centerEquiv
  left_eq s c := by
    obtain ⟨i, rfl⟩ := centerPoint_bijective.surjective c
    rw [centerEquiv_centerPoint]
    simpa only [marked, centerPoint] using left_marked K s i
  right_eq s c := by
    obtain ⟨i, rfl⟩ := centerPoint_bijective.surjective c
    rw [centerEquiv_centerPoint]
    simpa only [marked, centerPoint] using right_marked K s i

/-- A reference model with every structural and marked-matrix premise discharged. -/
noncomputable def referenceModel : ReferenceModel tableForm K where
  representation := representation K
  center_le_ker := (representation_centers K).1.ge
  rootCenter_invariants := (representation_centers K).2
  coordinates := coordinates K
end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.TableRealization

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
universe v
/-- The actual degree-twenty coset quotient realizes both marked Bruhat tables
uniformly over every finite coefficient field of characteristic two. -/
theorem twenty_table_bruhat_models : TableBruhatModels.{v} := by
  intro K _ _ _
  exact ⟨ExtensionRigidity.Injectivity.TableRealization.referenceModel K⟩
end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
