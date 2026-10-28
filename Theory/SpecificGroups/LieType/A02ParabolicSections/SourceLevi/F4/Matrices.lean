module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4.Matrices.DividedPowers

/-!
# All simple F4 root matrices at parameter one

The integral middle-root divided powers and the established end-root tables
identify all eight literal simple curves with their integer matrices over
any coefficient ring. These identities connect the finite binary word
certificates to the exceptional source carrier.

Source: Geck's integral root curves; GLS3 §1.12 and §2.6, used in
Aschbacher–Smith A.2.18, printed p.40.
-/

@[expose] public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4.Cartan.FieldSeparation.TraceValues
namespace Theory.SpecificGroups.LieType.SourceLevi.F4.Matrices
open Operators DividedPowers
noncomputable section
open scoped Classical Matrix
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
def positiveInteger : Fin 4 → Matrix (Fin 52) (Fin 52) ℤ :=
  ![matrix (identityEntries ++ positive0Linear ++ positive0Quadratic),
    matrix (identityEntries ++ positive1Linear ++ positive1Quadratic),
    matrix (identityEntries ++ positive2Linear ++ positive2Quadratic),
    matrix (identityEntries ++ positive3Linear ++ positive3Quadratic)]

def negativeInteger : Fin 4 → Matrix (Fin 52) (Fin 52) ℤ :=
  ![matrix (identityEntries ++ negative0Linear ++ negative0Quadratic),
    matrix (identityEntries ++ negative1Linear ++ negative1Quadratic),
    matrix (identityEntries ++ negative2Linear ++ negative2Quadratic),
    matrix (identityEntries ++ negative3Linear ++ negative3Quadratic)]

variable {S : Type*} [CommRing S]

/-- The four positive simple root matrices, before any characteristic assumption. -/
theorem positive_one (i : Fin 4) :
    reindex (positiveMatrix (typeF4RootPairing_baseEquiv i) (1 : S)) =
      (positiveInteger i).map (Int.castRingHom S) := by
  fin_cases i
  · rw [positiveMatrix_formula]
    simp only [map_add, map_one, reindex_smul, reindex_map, eDividedPower_one]
    simp [positiveInteger, matrix_append, matrix_identity, Matrix.map_add, Matrix.map_one,
      add_assoc]
    rw [eMatrix_0, eDividedPower_0_two, eDividedPower_0_three]
    simp
  · rw [positiveMatrix_formula]
    simp only [map_add, map_one, reindex_smul, reindex_map, eDividedPower_one]
    simp [positiveInteger, matrix_append, matrix_identity, Matrix.map_add, Matrix.map_one,
      add_assoc]
    rw [eMatrix_1, eDividedPower_1_two, eDividedPower_1_three]
    simp
  · rw [positiveMatrix_formula]
    simp only [map_add, map_one, reindex_smul, reindex_map, eDividedPower_one]
    simp [positiveInteger, matrix_append, matrix_identity, Matrix.map_add, Matrix.map_one,
      add_assoc]
    rw [eMatrix_2, eDividedPower_2_two, eDividedPower_2_three]
    simp
  · rw [positiveMatrix_formula]
    simp only [map_add, map_one, reindex_smul, reindex_map, eDividedPower_one]
    simp [positiveInteger, matrix_append, matrix_identity, Matrix.map_add, Matrix.map_one,
      add_assoc]
    rw [eMatrix_3, eDividedPower_3_two, eDividedPower_3_three]
    simp

/-- The four negative simple root matrices in the same coordinates. -/
theorem negative_one (i : Fin 4) :
    reindex (negativeMatrix (typeF4RootPairing_baseEquiv i) (1 : S)) =
      (negativeInteger i).map (Int.castRingHom S) := by
  fin_cases i
  · rw [negativeMatrix_formula]
    simp only [map_add, map_one, reindex_smul, reindex_map, fDividedPower_one]
    simp [negativeInteger, matrix_append, matrix_identity, Matrix.map_add, Matrix.map_one,
      add_assoc]
    rw [fMatrix_0, fDividedPower_0_two, fDividedPower_0_three]
    simp
  · rw [negativeMatrix_formula]
    simp only [map_add, map_one, reindex_smul, reindex_map, fDividedPower_one]
    simp [negativeInteger, matrix_append, matrix_identity, Matrix.map_add, Matrix.map_one,
      add_assoc]
    rw [fMatrix_1, fDividedPower_1_two, fDividedPower_1_three]
    simp
  · rw [negativeMatrix_formula]
    simp only [map_add, map_one, reindex_smul, reindex_map, fDividedPower_one]
    simp [negativeInteger, matrix_append, matrix_identity, Matrix.map_add, Matrix.map_one,
      add_assoc]
    rw [fMatrix_2, fDividedPower_2_two, fDividedPower_2_three]
    simp
  · rw [negativeMatrix_formula]
    simp only [map_add, map_one, reindex_smul, reindex_map, fDividedPower_one]
    simp [negativeInteger, matrix_append, matrix_identity, Matrix.map_add, Matrix.map_one,
      add_assoc]
    rw [fMatrix_3, fDividedPower_3_two, fDividedPower_3_three]
    simp

/-- Ordering: positive then negative at nodes zero through three. -/
def integerGenerator : Fin 8 → Matrix (Fin 52) (Fin 52) ℤ :=
  ![positiveInteger 0, negativeInteger 0, positiveInteger 1, negativeInteger 1,
    positiveInteger 2, negativeInteger 2, positiveInteger 3, negativeInteger 3]

end
end Theory.SpecificGroups.LieType.SourceLevi.F4.Matrices
