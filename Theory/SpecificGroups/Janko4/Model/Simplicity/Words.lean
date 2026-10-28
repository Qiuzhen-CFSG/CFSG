module

public import Theory.SpecificGroups.Janko4.Model
public import Mathlib.Data.Fin.VecNotation

/-!
# Words for the prime-order cyclic classes of the binary J₄ model

The words below are transcribed from the conjugacy-class table at
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ (retrieved 2026-10-03),
by R. A. Wilson, S. J. Nickerson and J. N. Bray. Taking powers of the listed
10B, 66A–B, 42A–B and 22B representatives gives the proposed representatives
of orders 2, 3, 5, 7 and 11. The remaining words are listed there directly.

These are definitions, not assertions about orders or conjugacy coverage.
Coverage by powers and conjugates and normal generation are separate
certification obligations. In particular, class names in this documentation
are source labels, not a recognition theorem for the matrix group.
-/

@[expose] public section

namespace Janko4.Simplicity

/-- Evaluate a positive word in two elements; other characters denote the identity. -/
def word {G : Type*} [Group G] (a b : G) (s : String) : G :=
  (s.toList.map fun c => if c = 'a' then a else if c = 'b' then b else 1).prod

/-- Twelve proposed representatives of prime-order cyclic classes, in order:
2A, 2B, 3A, 5A, 7A–B, 11A, 11B, 23A, 29A, 31A–C, 37A–C, 43A–C.
Only one generator is needed for each conjugacy class of cyclic subgroups. -/
def primeRepresentative {G : Type*} [Group G] (a b : G) : Fin 12 → G :=
  ![a,
    word a b "ababb" ^ 5,
    word a b "abbabababb" ^ 22,
    word a b "ababb" ^ 2,
    word a b "babbabababbbabababb" ^ 6,
    word a b "abbabababb" ^ 6,
    word a b "abbabababbabababbabbabababb" ^ 2,
    word a b "aababbabbabababb",
    word a b "abbaababbabbabababb",
    word a b "ababbbabababb",
    a * b,
    word a b "ababbabbabababb"]

/-- The first matrix, as a unit, once its involution identity is certified. -/
def unitA (hA : matrixA * matrixA = 1) : BinaryMatrixˣ :=
  ⟨matrixA, matrixA, hA, hA⟩

/-- The second matrix, as a unit, once its fourth-power identity is certified. -/
def unitB (hB : matrixB ^ 4 = 1) : BinaryMatrixˣ :=
  ⟨matrixB, matrixB ^ 3, by simpa only [← pow_succ'] using hB,
    by simpa only [← pow_succ] using hB⟩

/-- The first certified generator in the actual matrix carrier. -/
def a (hA : matrixA * matrixA = 1) : Model :=
  generator (unitA hA) (Or.inl rfl)

/-- The second certified generator in the actual matrix carrier. -/
def b (hB : matrixB ^ 4 = 1) : Model :=
  generator (unitB hB) (Or.inr rfl)

@[simp] theorem toMatrix_a (hA : matrixA * matrixA = 1) :
    toMatrix (a hA) = matrixA := rfl

@[simp] theorem toMatrix_b (hB : matrixB ^ 4 = 1) :
    toMatrix (b hB) = matrixB := rfl

/-- The certified second generator satisfies its matrix fourth-power relation. -/
theorem b_pow_four (hB : matrixB ^ 4 = 1) : b hB ^ 4 = 1 := by
  apply toMatrix_injective
  simpa using hB

end Janko4.Simplicity
