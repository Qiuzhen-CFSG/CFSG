module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.Seed
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Permutations for the marked dihedral subgroup

These lookup tables are certificates for the two fixed words in `Seed`.
`Dihedral.lean` checks the comparisons, multiplication, injectivity and
containment in the literal edge fixer. The tables themselves assert no
recognition or group order. Source: retained ATLAS J2G1-p100B0 data.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.DihedralData
open Theory.GroupTheory

def rotationTable : Equiv.Perm (Fin 100) :=
  tablePerm ![95, 4, 51, 41, 89, 35, 0, 3, 87, 8, 46, 91, 62, 93, 74, 84, 71, 27, 1, 21, 56, 28, 99, 82, 73, 22, 13, 37, 77, 86, 68, 11, 50, 78, 6, 53, 85, 2, 18, 34, 55, 40, 23, 14, 69, 49, 97, 61, 12, 54, 45, 17, 83, 36, 32, 7, 76, 92, 64, 72, 58, 43, 59, 75, 16, 79, 96, 63, 25, 94, 98, 60, 48, 26, 47, 65, 29, 88, 9, 67, 90, 80, 70, 44, 31, 5, 20, 33, 19, 38, 57, 15, 81, 24, 52, 39, 10, 66, 42, 30] ![6, 18, 37, 7, 1, 85, 34, 55, 9, 78, 96, 31, 48, 26, 43, 91, 64, 51, 38, 88, 86, 19, 25, 42, 93, 68, 73, 17, 21, 76, 99, 84, 54, 87, 39, 5, 53, 27, 89, 95, 41, 3, 98, 61, 83, 50, 10, 74, 72, 45, 32, 2, 94, 35, 49, 40, 20, 90, 60, 62, 71, 47, 12, 67, 58, 75, 97, 79, 30, 44, 82, 16, 59, 24, 14, 63, 56, 28, 33, 65, 81, 92, 23, 52, 15, 36, 29, 8, 77, 4, 80, 11, 57, 13, 69, 0, 66, 46, 70, 22]
    (by decide +kernel) (by decide +kernel)

def reflectionTable : Equiv.Perm (Fin 100) :=
  tablePerm ![0, 89, 17, 40, 4, 5, 95, 55, 9, 8, 46, 91, 62, 73, 74, 31, 60, 2, 38, 28, 20, 21, 99, 70, 93, 30, 26, 37, 19, 76, 25, 15, 32, 33, 39, 85, 53, 27, 18, 34, 3, 41, 98, 47, 52, 49, 10, 43, 59, 45, 54, 51, 44, 36, 50, 7, 86, 90, 64, 48, 16, 61, 12, 63, 58, 79, 66, 75, 68, 94, 23, 71, 72, 13, 14, 67, 29, 88, 87, 65, 92, 81, 82, 83, 84, 35, 56, 78, 77, 1, 57, 11, 80, 24, 69, 6, 97, 96, 42, 22] ![0, 89, 17, 40, 4, 5, 95, 55, 9, 8, 46, 91, 62, 73, 74, 31, 60, 2, 38, 28, 20, 21, 99, 70, 93, 30, 26, 37, 19, 76, 25, 15, 32, 33, 39, 85, 53, 27, 18, 34, 3, 41, 98, 47, 52, 49, 10, 43, 59, 45, 54, 51, 44, 36, 50, 7, 86, 90, 64, 48, 16, 61, 12, 63, 58, 79, 66, 75, 68, 94, 23, 71, 72, 13, 14, 67, 29, 88, 87, 65, 92, 81, 82, 83, 84, 35, 56, 78, 77, 1, 57, 11, 80, 24, 69, 6, 97, 96, 42, 22]
    (by decide +kernel) (by decide +kernel)

def permutation : DihedralGroup 5 → Equiv.Perm (Fin 100)
  | .r i => rotationTable ^ i.val
  | .sr i => reflectionTable * rotationTable ^ i.val

end Sporadic.LeechRelated.J2.RecognitionGeometry.DihedralData
