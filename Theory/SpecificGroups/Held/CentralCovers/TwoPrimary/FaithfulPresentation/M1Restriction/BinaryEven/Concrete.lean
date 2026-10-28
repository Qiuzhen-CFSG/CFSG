module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven.Core
public import Theory.SpecificGroups.Held.Model.FourPointBase
import Mathlib.Tactic.FinCases

/-!
# Concrete involution conjugacies for the four marked even relations

Every equality here is checked on the proved four-point base of Held's
literal ATLAS carrier. The witnesses retain the original right-conjugation
and generator conventions. The second seed is the square of the source
word centralizing a; multiplication by a brings that square to the first
class. Nine further words are conjugated to one of these two seeds.
No class coverage or presentation faithfulness is assumed.

Source: John Bray's `Held/Model/Source/HeG1-P1.M` and the retained
`HeG1-p2058B0` permutation tables. The seven segment words replay the
literal entry 11 from `M1Restriction/Data.lean`.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven

def marked {G : Type*} [Group G] (a b : G) : Fin 3 → G
  | 0 => a
  | 1 => (b ^ 2)⁻¹ * a * b ^ 2
  | 2 => b ^ 2 * a * (b ^ 2)⁻¹

theorem marked_lifted (i : Fin 3) : marked x y i = liftedGenerator i := by
  fin_cases i <;> rfl

theorem marked_concrete (i : Fin 3) : marked a b i = concreteGenerator i := by
  fin_cases i <;> simp only [marked, concreteGenerator_eq]

def testLetters : Fin 9 → List (Fin 3)
  | 0 => [1, 0, 1, 0, 1, 0]
  | 1 => [1, 0, 1, 2, 0, 2, 0, 2, 1, 0]
  | 2 => [2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0]
  | 3 => [1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1]
  | 4 => [2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2]
  | 5 => [1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2]
  | 6 => [1, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0]
  | 7 => [1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2]
  | 8 => [0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2]

def testElement : Fin 10 → He
  | 0 => a * sourceV a b ^ 2
  | 1 => positive (marked a b) (testLetters 0)
  | 2 => positive (marked a b) (testLetters 1)
  | 3 => positive (marked a b) (testLetters 2)
  | 4 => positive (marked a b) (testLetters 3)
  | 5 => positive (marked a b) (testLetters 4)
  | 6 => positive (marked a b) (testLetters 5)
  | 7 => positive (marked a b) (testLetters 6)
  | 8 => positive (marked a b) (testLetters 7)
  | 9 => positive (marked a b) (testLetters 8)

def secondClass : Fin 10 → Bool
  | 0 => false
  | 1 => false
  | 2 => false
  | 3 => true
  | 4 => true
  | 5 => false
  | 6 => true
  | 7 => true
  | 8 => false
  | 9 => true

def testSeed (i : Fin 10) : He := if secondClass i then sourceV a b ^ 2 else a

def initialConjugator : Fin 10 → He
  | 0 => b * b * a * b * b * b
  | 1 => b
  | 2 => b * b * b * a
  | 3 => b * b * b * a * b * a * b
  | 4 => b * b * a * b * b * a * b
  | 5 => 1
  | 6 => b * b * b * a * b
  | 7 => b * b * b
  | 8 => b * b * b
  | 9 => b * b * b * a * b * b * a * b

def testConjugator (i : Fin 10) : He :=
  initialConjugator i * (testElement i *
    (initialConjugator i)⁻¹ * testSeed i * initialConjugator i)

private theorem conjugacy_0 : testElement 0 =
    (testConjugator 0)⁻¹ * testSeed 0 * testConjugator 0 := by
  apply Held.eq_of_four_point_images
  decide +kernel

private theorem conjugacy_1 : testElement 1 =
    (testConjugator 1)⁻¹ * testSeed 1 * testConjugator 1 := by
  apply Held.eq_of_four_point_images
  decide +kernel

private theorem conjugacy_2 : testElement 2 =
    (testConjugator 2)⁻¹ * testSeed 2 * testConjugator 2 := by
  apply Held.eq_of_four_point_images
  decide +kernel

private theorem conjugacy_3 : testElement 3 =
    (testConjugator 3)⁻¹ * testSeed 3 * testConjugator 3 := by
  apply Held.eq_of_four_point_images
  decide +kernel

private theorem conjugacy_4 : testElement 4 =
    (testConjugator 4)⁻¹ * testSeed 4 * testConjugator 4 := by
  apply Held.eq_of_four_point_images
  decide +kernel

private theorem conjugacy_5 : testElement 5 =
    (testConjugator 5)⁻¹ * testSeed 5 * testConjugator 5 := by
  apply Held.eq_of_four_point_images
  decide +kernel

private theorem conjugacy_6 : testElement 6 =
    (testConjugator 6)⁻¹ * testSeed 6 * testConjugator 6 := by
  apply Held.eq_of_four_point_images
  decide +kernel

private theorem conjugacy_7 : testElement 7 =
    (testConjugator 7)⁻¹ * testSeed 7 * testConjugator 7 := by
  apply Held.eq_of_four_point_images
  decide +kernel

private theorem conjugacy_8 : testElement 8 =
    (testConjugator 8)⁻¹ * testSeed 8 * testConjugator 8 := by
  apply Held.eq_of_four_point_images
  decide +kernel

private theorem conjugacy_9 : testElement 9 =
    (testConjugator 9)⁻¹ * testSeed 9 * testConjugator 9 := by
  apply Held.eq_of_four_point_images
  decide +kernel

theorem test_conjugacy (i : Fin 10) : testElement i =
    (testConjugator i)⁻¹ * testSeed i * testConjugator i := by
  fin_cases i
  · exact conjugacy_0
  · exact conjugacy_1
  · exact conjugacy_2
  · exact conjugacy_3
  · exact conjugacy_4
  · exact conjugacy_5
  · exact conjugacy_6
  · exact conjugacy_7
  · exact conjugacy_8
  · exact conjugacy_9

def tenthLeft : List (Fin 3) := [2,1,0,2]
def tenthRight : List (Fin 3) := [1,2,1,0,2,0,2,1,0,2,0,1,0]

theorem tenth_right_cube : positive (marked a b) tenthRight ^ 3 = 1 := by
  apply Held.eq_of_four_point_images
  decide +kernel

theorem tenth_commute : Commute (positive (marked a b) tenthRight)
    (positive (marked a b) tenthLeft) := by
  change _ * _ = _ * _
  apply Held.eq_of_four_point_images
  decide +kernel

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven
