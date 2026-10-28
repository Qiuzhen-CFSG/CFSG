module

public import Theory.Character.ClassFunction
public import Theory.Character.ScalarProductMultiplicity
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Separate ordinary-character constructions for A6

The four nonprincipal rational rows and the pair of degree-eight rows are
independent representation-theoretic obligations on the actual alternating
group. The rational rows are marked by an element of order three; the
degree-eight rows are marked by an element of order five. These interfaces
require actual irreducible representation characters, not numerical
orthogonality alone. Their inhabitants remain to be constructed.

Combining the two blocks with the trivial representation gives the row order
used by Janko, *A characterization of the Mathieu simple groups, I*, §6,
pp.10–11: `1,9,10,8,8,5,5`.
-/

noncomputable section
namespace Theory.Character.AlternatingSix

/-- The rational rows of degrees `9,10,5,5`, on columns
`1,2A,3A,3B,4A,5A/B`. The marking of `3A` is supplied separately. -/
@[expose] public def rationalValues : Fin 4 → Fin 6 → ℤ :=
  ![![9, 1, 0, 0, 1, -1], ![10, -2, 1, 1, 0, 0],
    ![5, 1, 2, -1, -1, 0], ![5, 1, -1, 2, -1, 0]]

/-- Four genuine irreducibles, with their two degree-five rows marked by `c`.
The existence theorem must assume and use `orderOf c = 3`. -/
public structure RationalBlock (c : alternatingGroup (Fin 6)) where
  character : Fin 4 → ClassFunction (alternatingGroup (Fin 6))
  irreducible : ∀ j, IsIrreducibleCharacter (character j)
  one : ∀ j, character j 1 = (rationalValues j 0 : ℂ)
  two : ∀ j x, orderOf x = 2 → character j x = (rationalValues j 1 : ℂ)
  three : ∀ j, character j c = (rationalValues j 2 : ℂ)
  otherThree : ∀ j x, orderOf x = 3 → ¬ IsConj x c →
    character j x = (rationalValues j 3 : ℂ)
  four : ∀ j x, orderOf x = 4 → character j x = (rationalValues j 4 : ℂ)
  five : ∀ j x, orderOf x = 5 → character j x = (rationalValues j 5 : ℂ)

/-- The two actual degree-eight irreducibles, ordered by their value at `μ`.
The existence theorem must assume and use `orderOf μ = 5`. -/
public structure GoldenBlock (μ : alternatingGroup (Fin 6)) where
  parameter : ℂ
  parameter_equation : parameter ^ 2 = parameter + 1
  character : Fin 2 → ClassFunction (alternatingGroup (Fin 6))
  irreducible : ∀ j, IsIrreducibleCharacter (character j)
  one : ∀ j, character j 1 = 8
  two : ∀ j x, orderOf x = 2 → character j x = 0
  three : ∀ j x, orderOf x = 3 → character j x = -1
  four : ∀ j x, orderOf x = 4 → character j x = 0
  five : ∀ j, character j μ = ![parameter, 1 - parameter] j
  five_sq : ∀ j, character j (μ ^ 2) = ![1 - parameter, parameter] j

variable {c μ : alternatingGroup (Fin 6)}

/-- The principal representation and the two independently constructed blocks. -/
@[expose] public def combinedCharacter (R : RationalBlock c) (B : GoldenBlock μ) :
    Fin 7 → ClassFunction (alternatingGroup (Fin 6)) :=
  ![1, R.character 0, R.character 1, B.character 0, B.character 1,
    R.character 2, R.character 3]

public theorem combinedCharacter_irreducible (R : RationalBlock c) (B : GoldenBlock μ)
    (j : Fin 7) : IsIrreducibleCharacter (combinedCharacter R B j) := by
  fin_cases j
  · exact isIrreducibleCharacter_one
  · exact R.irreducible 0
  · exact R.irreducible 1
  · exact B.irreducible 0
  · exact B.irreducible 1
  · exact R.irreducible 2
  · exact R.irreducible 3

public theorem combinedCharacter_principal (R : RationalBlock c) (B : GoldenBlock μ) :
    combinedCharacter R B 0 = 1 := rfl

end Theory.Character.AlternatingSix
