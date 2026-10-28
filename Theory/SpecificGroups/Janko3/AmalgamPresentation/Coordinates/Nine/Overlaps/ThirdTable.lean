module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.FiniteTables
import Mathlib.Tactic.FinCases

/-! Checked normalized matrices and generator transitions for the literal projective overlap. -/
@[expose] public section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates.OverlapTables.Third
open Subgroup

def rowMatrix : Fin 60 → Matrix (Fin 2) (Fin 2) F
  | 0 => !![(⟨1,0⟩:F),(⟨0,0⟩:F);(⟨0,0⟩:F),(⟨1,0⟩:F)]
  | 1 => !![(⟨1,0⟩:F),(⟨2,0⟩:F);(⟨1,2⟩:F),(⟨2,0⟩:F)]
  | 2 => !![(⟨1,0⟩:F),(⟨1,2⟩:F);(⟨2,1⟩:F),(⟨1,2⟩:F)]
  | 3 => !![(⟨1,0⟩:F),(⟨0,0⟩:F);(⟨0,2⟩:F),(⟨1,0⟩:F)]
  | 4 => !![(⟨1,0⟩:F),(⟨1,0⟩:F);(⟨2,0⟩:F),(⟨0,0⟩:F)]
  | 5 => !![(⟨1,0⟩:F),(⟨2,2⟩:F);(⟨1,1⟩:F),(⟨0,0⟩:F)]
  | 6 => !![(⟨1,0⟩:F),(⟨2,0⟩:F);(⟨1,1⟩:F),(⟨2,1⟩:F)]
  | 7 => !![(⟨1,0⟩:F),(⟨1,2⟩:F);(⟨2,0⟩:F),(⟨0,1⟩:F)]
  | 8 => !![(⟨1,0⟩:F),(⟨1,1⟩:F);(⟨0,1⟩:F),(⟨1,1⟩:F)]
  | 9 => !![(⟨1,0⟩:F),(⟨0,2⟩:F);(⟨2,2⟩:F),(⟨1,1⟩:F)]
  | 10 => !![(⟨0,0⟩:F),(⟨1,0⟩:F);(⟨2,0⟩:F),(⟨2,1⟩:F)]
  | 11 => !![(⟨1,0⟩:F),(⟨0,0⟩:F);(⟨0,1⟩:F),(⟨1,0⟩:F)]
  | 12 => !![(⟨1,0⟩:F),(⟨1,0⟩:F);(⟨2,2⟩:F),(⟨0,2⟩:F)]
  | 13 => !![(⟨1,0⟩:F),(⟨2,2⟩:F);(⟨1,0⟩:F),(⟨2,1⟩:F)]
  | 14 => !![(⟨0,0⟩:F),(⟨1,0⟩:F);(⟨2,0⟩:F),(⟨2,0⟩:F)]
  | 15 => !![(⟨1,0⟩:F),(⟨0,1⟩:F);(⟨2,2⟩:F),(⟨0,2⟩:F)]
  | 16 => !![(⟨1,0⟩:F),(⟨2,1⟩:F);(⟨1,2⟩:F),(⟨0,0⟩:F)]
  | 17 => !![(⟨1,0⟩:F),(⟨1,1⟩:F);(⟨0,2⟩:F),(⟨0,2⟩:F)]
  | 18 => !![(⟨1,0⟩:F),(⟨2,0⟩:F);(⟨1,0⟩:F),(⟨2,2⟩:F)]
  | 19 => !![(⟨1,0⟩:F),(⟨1,2⟩:F);(⟨2,2⟩:F),(⟨2,0⟩:F)]
  | 20 => !![(⟨1,0⟩:F),(⟨1,1⟩:F);(⟨0,0⟩:F),(⟨2,0⟩:F)]
  | 21 => !![(⟨1,0⟩:F),(⟨0,2⟩:F);(⟨2,1⟩:F),(⟨0,1⟩:F)]
  | 22 => !![(⟨1,0⟩:F),(⟨0,1⟩:F);(⟨0,2⟩:F),(⟨2,0⟩:F)]
  | 23 => !![(⟨1,0⟩:F),(⟨0,2⟩:F);(⟨0,0⟩:F),(⟨1,0⟩:F)]
  | 24 => !![(⟨1,0⟩:F),(⟨2,1⟩:F);(⟨1,0⟩:F),(⟨2,0⟩:F)]
  | 25 => !![(⟨1,0⟩:F),(⟨1,0⟩:F);(⟨0,2⟩:F),(⟨2,2⟩:F)]
  | 26 => !![(⟨1,0⟩:F),(⟨0,1⟩:F);(⟨2,0⟩:F),(⟨2,2⟩:F)]
  | 27 => !![(⟨1,0⟩:F),(⟨1,0⟩:F);(⟨2,1⟩:F),(⟨0,1⟩:F)]
  | 28 => !![(⟨1,0⟩:F),(⟨2,2⟩:F);(⟨1,2⟩:F),(⟨1,2⟩:F)]
  | 29 => !![(⟨0,0⟩:F),(⟨1,0⟩:F);(⟨2,0⟩:F),(⟨2,2⟩:F)]
  | 30 => !![(⟨1,0⟩:F),(⟨0,1⟩:F);(⟨2,1⟩:F),(⟨1,2⟩:F)]
  | 31 => !![(⟨1,0⟩:F),(⟨2,1⟩:F);(⟨1,1⟩:F),(⟨1,1⟩:F)]
  | 32 => !![(⟨1,0⟩:F),(⟨2,2⟩:F);(⟨1,1⟩:F),(⟨0,2⟩:F)]
  | 33 => !![(⟨1,0⟩:F),(⟨1,2⟩:F);(⟨0,1⟩:F),(⟨0,1⟩:F)]
  | 34 => !![(⟨1,0⟩:F),(⟨1,1⟩:F);(⟨2,1⟩:F),(⟨2,0⟩:F)]
  | 35 => !![(⟨1,0⟩:F),(⟨0,1⟩:F);(⟨0,0⟩:F),(⟨1,0⟩:F)]
  | 36 => !![(⟨1,0⟩:F),(⟨0,2⟩:F);(⟨0,1⟩:F),(⟨2,0⟩:F)]
  | 37 => !![(⟨1,0⟩:F),(⟨0,2⟩:F);(⟨2,0⟩:F),(⟨2,1⟩:F)]
  | 38 => !![(⟨1,0⟩:F),(⟨0,1⟩:F);(⟨0,1⟩:F),(⟨0,0⟩:F)]
  | 39 => !![(⟨1,0⟩:F),(⟨0,2⟩:F);(⟨0,2⟩:F),(⟨0,0⟩:F)]
  | 40 => !![(⟨1,0⟩:F),(⟨2,1⟩:F);(⟨1,2⟩:F),(⟨0,1⟩:F)]
  | 41 => !![(⟨1,0⟩:F),(⟨1,0⟩:F);(⟨0,1⟩:F),(⟨2,1⟩:F)]
  | 42 => !![(⟨0,0⟩:F),(⟨1,0⟩:F);(⟨1,0⟩:F),(⟨0,1⟩:F)]
  | 43 => !![(⟨0,0⟩:F),(⟨1,0⟩:F);(⟨1,0⟩:F),(⟨0,2⟩:F)]
  | 44 => !![(⟨1,0⟩:F),(⟨2,2⟩:F);(⟨1,2⟩:F),(⟨1,1⟩:F)]
  | 45 => !![(⟨1,0⟩:F),(⟨2,1⟩:F);(⟨1,1⟩:F),(⟨1,2⟩:F)]
  | 46 => !![(⟨1,0⟩:F),(⟨2,1⟩:F);(⟨1,0⟩:F),(⟨2,2⟩:F)]
  | 47 => !![(⟨1,0⟩:F),(⟨2,2⟩:F);(⟨1,0⟩:F),(⟨2,0⟩:F)]
  | 48 => !![(⟨1,0⟩:F),(⟨1,2⟩:F);(⟨0,0⟩:F),(⟨2,0⟩:F)]
  | 49 => !![(⟨1,0⟩:F),(⟨1,1⟩:F);(⟨2,0⟩:F),(⟨0,2⟩:F)]
  | 50 => !![(⟨1,0⟩:F),(⟨2,0⟩:F);(⟨1,2⟩:F),(⟨2,2⟩:F)]
  | 51 => !![(⟨1,0⟩:F),(⟨2,0⟩:F);(⟨1,0⟩:F),(⟨2,1⟩:F)]
  | 52 => !![(⟨1,0⟩:F),(⟨1,0⟩:F);(⟨0,0⟩:F),(⟨2,0⟩:F)]
  | 53 => !![(⟨0,0⟩:F),(⟨1,0⟩:F);(⟨1,0⟩:F),(⟨0,0⟩:F)]
  | 54 => !![(⟨1,0⟩:F),(⟨0,0⟩:F);(⟨2,1⟩:F),(⟨2,0⟩:F)]
  | 55 => !![(⟨1,0⟩:F),(⟨0,0⟩:F);(⟨2,2⟩:F),(⟨2,0⟩:F)]
  | 56 => !![(⟨1,0⟩:F),(⟨0,0⟩:F);(⟨2,0⟩:F),(⟨2,0⟩:F)]
  | 57 => !![(⟨1,0⟩:F),(⟨1,2⟩:F);(⟨0,2⟩:F),(⟨1,2⟩:F)]
  | 58 => !![(⟨1,0⟩:F),(⟨1,1⟩:F);(⟨2,2⟩:F),(⟨1,1⟩:F)]
  | _ => !![(⟨1,0⟩:F),(⟨2,0⟩:F);(⟨1,1⟩:F),(⟨2,0⟩:F)]

theorem rowMatrix_det (i : Fin 60) : (rowMatrix i).det ≠ 0 := by
  have h : ∀ i, (rowMatrix i).det ≠ 0 := by decide +kernel
  exact h i

def row (i : Fin 60) : GL9 := Matrix.GeneralLinearGroup.mkOfDetNeZero (rowMatrix i) (rowMatrix_det i)
noncomputable def repr (i : Fin 60) : P := Matrix.ProjGenLinGroup.mk (row i)
noncomputable def generator (b : Bool) : P := Matrix.ProjGenLinGroup.mk (overlapMatrix (if b then 3 else 2))
noncomputable def subgroup : Subgroup P := closure (Set.range generator)

def parent : Fin 60 → Fin 60
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 3
  | 8 => 4
  | 9 => 5
  | 10 => 5
  | 11 => 6
  | 12 => 7
  | 13 => 7
  | 14 => 8
  | 15 => 8
  | 16 => 9
  | 17 => 10
  | 18 => 10
  | 19 => 11
  | 20 => 12
  | 21 => 13
  | 22 => 15
  | 23 => 15
  | 24 => 16
  | 25 => 16
  | 26 => 17
  | 27 => 19
  | 28 => 19
  | 29 => 20
  | 30 => 20
  | 31 => 21
  | 32 => 23
  | 33 => 25
  | 34 => 25
  | 35 => 26
  | 36 => 26
  | 37 => 28
  | 38 => 30
  | 39 => 30
  | 40 => 31
  | 41 => 31
  | 42 => 32
  | 43 => 34
  | 44 => 36
  | 45 => 36
  | 46 => 37
  | 47 => 39
  | 48 => 41
  | 49 => 41
  | 50 => 42
  | 51 => 43
  | 52 => 46
  | 53 => 47
  | 54 => 50
  | 55 => 50
  | 56 => 51
  | 57 => 52
  | 58 => 52
  | _ => 53

def letter : Fin 60 → Bool
  | 0 => false
  | 1 => false
  | 2 => true
  | 3 => true
  | 4 => false
  | 5 => true
  | 6 => false
  | 7 => true
  | 8 => true
  | 9 => false
  | 10 => true
  | 11 => true
  | 12 => false
  | 13 => true
  | 14 => false
  | 15 => true
  | 16 => true
  | 17 => false
  | 18 => true
  | 19 => true
  | 20 => true
  | 21 => false
  | 22 => false
  | 23 => true
  | 24 => false
  | 25 => true
  | 26 => true
  | 27 => false
  | 28 => true
  | 29 => false
  | 30 => true
  | 31 => true
  | 32 => false
  | 33 => false
  | 34 => true
  | 35 => false
  | 36 => true
  | 37 => false
  | 38 => false
  | 39 => true
  | 40 => false
  | 41 => true
  | 42 => true
  | 43 => false
  | 44 => false
  | 45 => true
  | 46 => true
  | 47 => false
  | 48 => false
  | 49 => true
  | 50 => true
  | 51 => true
  | 52 => true
  | 53 => true
  | 54 => false
  | 55 => true
  | 56 => true
  | 57 => false
  | 58 => true
  | _ => true

def parentScalar : Fin 60 → F
  | 0 => (⟨1,0⟩:F)
  | 1 => (⟨1,0⟩:F)
  | 2 => (⟨1,0⟩:F)
  | 3 => (⟨2,2⟩:F)
  | 4 => (⟨1,1⟩:F)
  | 5 => (⟨1,2⟩:F)
  | 6 => (⟨1,0⟩:F)
  | 7 => (⟨1,0⟩:F)
  | 8 => (⟨0,1⟩:F)
  | 9 => (⟨2,0⟩:F)
  | 10 => (⟨2,2⟩:F)
  | 11 => (⟨2,2⟩:F)
  | 12 => (⟨1,1⟩:F)
  | 13 => (⟨1,2⟩:F)
  | 14 => (⟨1,2⟩:F)
  | 15 => (⟨2,0⟩:F)
  | 16 => (⟨2,1⟩:F)
  | 17 => (⟨1,2⟩:F)
  | 18 => (⟨2,1⟩:F)
  | 19 => (⟨1,0⟩:F)
  | 20 => (⟨0,1⟩:F)
  | 21 => (⟨2,0⟩:F)
  | 22 => (⟨2,1⟩:F)
  | 23 => (⟨0,2⟩:F)
  | 24 => (⟨1,2⟩:F)
  | 25 => (⟨1,1⟩:F)
  | 26 => (⟨2,0⟩:F)
  | 27 => (⟨1,1⟩:F)
  | 28 => (⟨1,2⟩:F)
  | 29 => (⟨1,2⟩:F)
  | 30 => (⟨2,0⟩:F)
  | 31 => (⟨2,1⟩:F)
  | 32 => (⟨0,2⟩:F)
  | 33 => (⟨2,2⟩:F)
  | 34 => (⟨0,1⟩:F)
  | 35 => (⟨2,1⟩:F)
  | 36 => (⟨0,2⟩:F)
  | 37 => (⟨2,0⟩:F)
  | 38 => (⟨2,1⟩:F)
  | 39 => (⟨0,2⟩:F)
  | 40 => (⟨1,2⟩:F)
  | 41 => (⟨1,1⟩:F)
  | 42 => (⟨2,2⟩:F)
  | 43 => (⟨1,2⟩:F)
  | 44 => (⟨0,2⟩:F)
  | 45 => (⟨2,1⟩:F)
  | 46 => (⟨2,1⟩:F)
  | 47 => (⟨0,2⟩:F)
  | 48 => (⟨2,2⟩:F)
  | 49 => (⟨0,1⟩:F)
  | 50 => (⟨2,1⟩:F)
  | 51 => (⟨2,1⟩:F)
  | 52 => (⟨1,1⟩:F)
  | 53 => (⟨2,2⟩:F)
  | 54 => (⟨0,1⟩:F)
  | 55 => (⟨2,2⟩:F)
  | 56 => (⟨2,2⟩:F)
  | 57 => (⟨2,2⟩:F)
  | 58 => (⟨0,1⟩:F)
  | _ => (⟨2,1⟩:F)

private def parentUnit (i : Fin 60) : Fˣ := Units.mk0 (parentScalar i) (by
  have h : ∀ i, parentScalar i ≠ 0 := by decide +kernel
  exact h i)

private theorem parent_lt : ∀ i : Fin 60, i ≠ 0 → (parent i).val < i.val := by decide +kernel
private theorem parent_matrix (i : Fin 60) : i ≠ 0 →
    row (parent i) * overlapMatrix (if letter i then 3 else 2) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (parentUnit i) * row i := by
  intro hi
  apply Matrix.GeneralLinearGroup.ext
  intro j k
  fin_cases j <;> fin_cases k <;> revert i <;> decide +kernel

private theorem repr_zero : repr 0 = 1 := by
  change Matrix.ProjGenLinGroup.mk (row 0) = 1
  rw [show row 0 = 1 from by apply Matrix.GeneralLinearGroup.ext; intro j k; fin_cases j <;> fin_cases k <;> decide +kernel,map_one]

private theorem parent_repr (i : Fin 60) (hi : i ≠ 0) :
    repr i = repr (parent i) * generator (letter i) := by
  change _ = Matrix.ProjGenLinGroup.mk _ * Matrix.ProjGenLinGroup.mk _
  rw [←map_mul,parent_matrix i hi,map_mul,Matrix.ProjGenLinGroup.mk_scalar,one_mul]
  rfl

def next : Fin 60 → Fin 4 → Fin 60
  | 0 => ![1,1,2,18]
  | 1 => ![0,0,3,14]
  | 2 => ![4,4,5,0]
  | 3 => ![6,6,7,1]
  | 4 => ![2,2,8,24]
  | 5 => ![9,9,10,2]
  | 6 => ![3,3,11,29]
  | 7 => ![12,12,13,3]
  | 8 => ![14,14,15,4]
  | 9 => ![5,5,16,35]
  | 10 => ![17,17,18,5]
  | 11 => ![18,18,19,6]
  | 12 => ![7,7,20,40]
  | 13 => ![21,21,14,7]
  | 14 => ![8,8,1,13]
  | 15 => ![22,22,23,8]
  | 16 => ![24,24,25,9]
  | 17 => ![10,10,26,27]
  | 18 => ![11,11,0,10]
  | 19 => ![27,27,28,11]
  | 20 => ![29,29,30,12]
  | 21 => ![13,13,31,22]
  | 22 => ![15,15,21,49]
  | 23 => ![32,32,24,15]
  | 24 => ![16,16,4,23]
  | 25 => ![33,33,34,16]
  | 26 => ![35,35,36,17]
  | 27 => ![19,19,17,45]
  | 28 => ![37,37,29,19]
  | 29 => ![20,20,6,28]
  | 30 => ![38,38,39,20]
  | 31 => ![40,40,41,21]
  | 32 => ![23,23,42,33]
  | 33 => ![25,25,32,55]
  | 34 => ![43,43,35,25]
  | 35 => ![26,26,9,34]
  | 36 => ![44,44,45,26]
  | 37 => ![28,28,46,38]
  | 38 => ![30,30,37,58]
  | 39 => ![47,47,40,30]
  | 40 => ![31,31,12,39]
  | 41 => ![48,48,49,31]
  | 42 => ![49,49,50,32]
  | 43 => ![34,34,51,44]
  | 44 => ![36,36,43,57]
  | 45 => ![46,46,27,36]
  | 46 => ![45,45,52,37]
  | 47 => ![39,39,53,48]
  | 48 => ![41,41,47,54]
  | 49 => ![42,42,22,41]
  | 50 => ![54,54,55,42]
  | 51 => ![55,55,56,43]
  | 52 => ![57,57,58,46]
  | 53 => ![58,58,59,47]
  | 54 => ![50,50,48,59]
  | 55 => ![51,51,33,50]
  | 56 => ![59,59,57,51]
  | 57 => ![52,52,44,56]
  | 58 => ![53,53,38,52]
  | _ => ![56,56,54,53]

def stepScalar : Fin 60 → Fin 4 → F
  | 0 => ![(⟨1,0⟩:F),(⟨0,2⟩:F),(⟨1,0⟩:F),(⟨1,2⟩:F)]
  | 1 => ![(⟨0,1⟩:F),(⟨1,0⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F)]
  | 2 => ![(⟨1,1⟩:F),(⟨1,2⟩:F),(⟨1,2⟩:F),(⟨1,0⟩:F)]
  | 3 => ![(⟨1,0⟩:F),(⟨0,2⟩:F),(⟨1,0⟩:F),(⟨1,2⟩:F)]
  | 4 => ![(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F),(⟨2,1⟩:F)]
  | 5 => ![(⟨2,0⟩:F),(⟨0,1⟩:F),(⟨2,2⟩:F),(⟨2,2⟩:F)]
  | 6 => ![(⟨0,1⟩:F),(⟨1,0⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F)]
  | 7 => ![(⟨1,1⟩:F),(⟨1,2⟩:F),(⟨1,2⟩:F),(⟨1,0⟩:F)]
  | 8 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,0⟩:F),(⟨0,2⟩:F)]
  | 9 => ![(⟨0,2⟩:F),(⟨2,0⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F)]
  | 10 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨1,2⟩:F)]
  | 11 => ![(⟨1,0⟩:F),(⟨0,2⟩:F),(⟨1,0⟩:F),(⟨1,2⟩:F)]
  | 12 => ![(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F),(⟨2,1⟩:F)]
  | 13 => ![(⟨2,0⟩:F),(⟨0,1⟩:F),(⟨2,2⟩:F),(⟨2,2⟩:F)]
  | 14 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨1,2⟩:F)]
  | 15 => ![(⟨2,1⟩:F),(⟨1,1⟩:F),(⟨0,2⟩:F),(⟨2,0⟩:F)]
  | 16 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F),(⟨1,1⟩:F)]
  | 17 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,0⟩:F),(⟨0,2⟩:F)]
  | 18 => ![(⟨0,1⟩:F),(⟨1,0⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F)]
  | 19 => ![(⟨1,1⟩:F),(⟨1,2⟩:F),(⟨1,2⟩:F),(⟨1,0⟩:F)]
  | 20 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,0⟩:F),(⟨0,2⟩:F)]
  | 21 => ![(⟨0,2⟩:F),(⟨2,0⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F)]
  | 22 => ![(⟨2,1⟩:F),(⟨1,1⟩:F),(⟨0,2⟩:F),(⟨2,0⟩:F)]
  | 23 => ![(⟨0,2⟩:F),(⟨2,0⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F)]
  | 24 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F),(⟨1,1⟩:F)]
  | 25 => ![(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F),(⟨2,1⟩:F)]
  | 26 => ![(⟨2,1⟩:F),(⟨1,1⟩:F),(⟨0,2⟩:F),(⟨2,0⟩:F)]
  | 27 => ![(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F),(⟨2,1⟩:F)]
  | 28 => ![(⟨2,0⟩:F),(⟨0,1⟩:F),(⟨2,2⟩:F),(⟨2,2⟩:F)]
  | 29 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨1,2⟩:F)]
  | 30 => ![(⟨2,1⟩:F),(⟨1,1⟩:F),(⟨0,2⟩:F),(⟨2,0⟩:F)]
  | 31 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F),(⟨1,1⟩:F)]
  | 32 => ![(⟨2,0⟩:F),(⟨0,1⟩:F),(⟨2,2⟩:F),(⟨2,2⟩:F)]
  | 33 => ![(⟨1,1⟩:F),(⟨1,2⟩:F),(⟨1,2⟩:F),(⟨1,0⟩:F)]
  | 34 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,0⟩:F),(⟨0,2⟩:F)]
  | 35 => ![(⟨2,1⟩:F),(⟨1,1⟩:F),(⟨0,2⟩:F),(⟨2,0⟩:F)]
  | 36 => ![(⟨0,2⟩:F),(⟨2,0⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F)]
  | 37 => ![(⟨0,2⟩:F),(⟨2,0⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F)]
  | 38 => ![(⟨2,1⟩:F),(⟨1,1⟩:F),(⟨0,2⟩:F),(⟨2,0⟩:F)]
  | 39 => ![(⟨0,2⟩:F),(⟨2,0⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F)]
  | 40 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F),(⟨1,1⟩:F)]
  | 41 => ![(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F),(⟨2,1⟩:F)]
  | 42 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨1,2⟩:F)]
  | 43 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨1,2⟩:F)]
  | 44 => ![(⟨2,0⟩:F),(⟨0,1⟩:F),(⟨2,2⟩:F),(⟨2,2⟩:F)]
  | 45 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F),(⟨1,1⟩:F)]
  | 46 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F),(⟨1,1⟩:F)]
  | 47 => ![(⟨2,0⟩:F),(⟨0,1⟩:F),(⟨2,2⟩:F),(⟨2,2⟩:F)]
  | 48 => ![(⟨1,1⟩:F),(⟨1,2⟩:F),(⟨1,2⟩:F),(⟨1,0⟩:F)]
  | 49 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,0⟩:F),(⟨0,2⟩:F)]
  | 50 => ![(⟨0,1⟩:F),(⟨1,0⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F)]
  | 51 => ![(⟨0,1⟩:F),(⟨1,0⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F)]
  | 52 => ![(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨0,1⟩:F),(⟨2,1⟩:F)]
  | 53 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,1⟩:F),(⟨1,2⟩:F)]
  | 54 => ![(⟨1,0⟩:F),(⟨0,2⟩:F),(⟨1,0⟩:F),(⟨1,2⟩:F)]
  | 55 => ![(⟨1,0⟩:F),(⟨0,2⟩:F),(⟨1,0⟩:F),(⟨1,2⟩:F)]
  | 56 => ![(⟨1,0⟩:F),(⟨0,2⟩:F),(⟨1,0⟩:F),(⟨1,2⟩:F)]
  | 57 => ![(⟨1,1⟩:F),(⟨1,2⟩:F),(⟨1,2⟩:F),(⟨1,0⟩:F)]
  | 58 => ![(⟨1,2⟩:F),(⟨2,2⟩:F),(⟨2,0⟩:F),(⟨0,2⟩:F)]
  | _ => ![(⟨0,1⟩:F),(⟨1,0⟩:F),(⟨2,2⟩:F),(⟨1,1⟩:F)]

private def stepUnit (i : Fin 60) (j : Fin 4) : Fˣ := Units.mk0 (stepScalar i j) (by
  have h : ∀ i j, stepScalar i j ≠ 0 := by decide +kernel
  exact h i j)
private def signedMatrix (j : Fin 4) : GL9 :=
  if j.val % 2 = 0 then overlapMatrix (if j.val < 2 then 2 else 3)
  else (overlapMatrix (if j.val < 2 then 2 else 3))⁻¹
private theorem step_matrix (i : Fin 60) (j : Fin 4) :
    row i * signedMatrix j = Matrix.GeneralLinearGroup.scalar (Fin 2) (stepUnit i j) * row (next i j) := by
  apply Matrix.GeneralLinearGroup.ext
  intro k l
  fin_cases k <;> fin_cases l <;> fin_cases j <;> revert i <;> decide +kernel
private theorem step_repr (i : Fin 60) (j : Fin 4) :
    repr i * Matrix.ProjGenLinGroup.mk (signedMatrix j) = repr (next i j) := by
  change Matrix.ProjGenLinGroup.mk _ * Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  rw [←map_mul,step_matrix,map_mul,Matrix.ProjGenLinGroup.mk_scalar,one_mul]

/-- The table is exactly the actual projective word subgroup. -/
theorem carrier_eq : (subgroup : Set P) = Set.range repr := by
  apply closure_eq_range generator repr 0 repr_zero
    (row_mem_of_parent generator repr repr_zero parent letter parent_lt parent_repr)
  · intro i b
    cases b
    · exact ⟨next i 0,step_repr i 0⟩
    · exact ⟨next i 2,step_repr i 2⟩
  · intro i b
    cases b
    · exact ⟨next i 1,by simpa [signedMatrix,generator] using step_repr i 1⟩
    · exact ⟨next i 3,by simpa [signedMatrix,generator] using step_repr i 3⟩

private theorem row_pivot : ∀ i : Fin 60, pivot (row i) = 1 := by decide +kernel
private theorem rowMatrix_injective : Function.Injective rowMatrix := by decide +kernel

theorem repr_injective : Function.Injective repr := by
  intro i j hij
  have he := normalized_injective (row_pivot i) (row_pivot j) hij
  apply rowMatrix_injective
  exact congrArg (fun m : GL9 => (m : Matrix (Fin 2) (Fin 2) F)) he

theorem subgroup_card : Nat.card subgroup = 60 := card_of_range subgroup repr repr_injective carrier_eq

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates.OverlapTables.Third
