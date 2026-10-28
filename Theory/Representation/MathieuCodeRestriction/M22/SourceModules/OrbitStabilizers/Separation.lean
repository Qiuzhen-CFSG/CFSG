module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.PairVectors
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Pairing

/-!
# Separating the 22 native M22 pair classes

Subtracting the marked-pair evaluation times Golay row zero puts every
Golay generator in the code hyperplane. Their coordinate pairings distinguish
the 22 moving coordinates and separate each class from zero. The finite
separation certificates are checked by the kernel; the passage to the literal
quotient uses the already proved coordinate duality.

Source: Aschbacher--Smith, H.15.1(1), printed p.398.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu
open scoped BigOperators
namespace MathieuCode
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The native moving-coordinate parametrization of the source family. -/
def m22WeightTwoVector (i : Fin 22) : M22Cocode :=
  m22CocodePair 0 (m22Coordinates i)

private def separatingRow (r : Fin 12) : Full :=
  row r - (row r 0 + row r 9) • row 0

private theorem separatingRow_mem (r : Fin 12) : separatingRow r ∈ golay :=
  golay.sub_mem (row_mem r) (golay.smul_mem _ (row_mem 0))

private theorem separatingRow_pair (r : Fin 12) :
    separatingRow r 0 + separatingRow r 9 = 0 := by
  have h : row 0 0 + row 0 9 = 1 := by decide +kernel
  dsimp [separatingRow]
  calc
    _ = row r 0 + row r 9 - (row r 0 + row r 9) * (row 0 0 + row 0 9) := by ring
    _ = 0 := by rw [h]; ring

private theorem separates : ∀ i j : Fin 22, i ≠ j → ∃ r : Fin 12,
    separatingRow r (m22Coordinates i) ≠ separatingRow r (m22Coordinates j) := by
  decide +kernel

private theorem nonzero : ∀ i : Fin 22, ∃ r : Fin 12,
    separatingRow r 0 + separatingRow r (m22Coordinates i) ≠ 0 := by
  decide +kernel

private def testCode (r : Fin 12) : M22Code :=
  ⟨codeLine.mkQ ⟨separatingRow r, separatingRow_mem r⟩, separatingRow_pair r⟩

private theorem testCode_apply (r : Fin 12) (i j : Fin 24) :
    m22CodeCocodeDuality (testCode r) (m22CocodePair i j) =
      separatingRow r i + separatingRow r j := by
  rw [m22CocodePair, testCode, m22CodeCocodeDuality_apply_mk]
  simp [m22EvenPair, dotForm, dotProductBilin, dotProduct_single]

theorem m22WeightTwoVector_injective : Function.Injective (m22WeightTwoVector) := by
  intro i j hij
  change m22CocodePair 0 (m22Coordinates i) = m22CocodePair 0 (m22Coordinates j) at hij
  by_contra hne
  obtain ⟨r, hr⟩ := separates i j hne
  have h := congrArg (m22CodeCocodeDuality (testCode r)) hij
  rw [testCode_apply, testCode_apply] at h
  exact hr (add_left_cancel h)

theorem m22WeightTwoVector_ne_zero (i : Fin 22) : m22WeightTwoVector i ≠ 0 := by
  intro hz
  change m22CocodePair 0 (m22Coordinates i) = 0 at hz
  obtain ⟨r, hr⟩ := nonzero i
  have h := congrArg (m22CodeCocodeDuality (testCode r)) hz
  rw [testCode_apply, map_zero] at h
  exact hr h

end MathieuCode
