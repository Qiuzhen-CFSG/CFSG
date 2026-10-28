module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Data

/-!
# Reachability and separation of the linear enumeration

The checked tree reaches every index from zero, and each generator transition
has a checked inverse permutation. The nine entries in rows and columns 28–30
recover the enumeration index. This proves distinctness only; the separate
full-matrix product certificates supply closure.

Source: the untrusted ATLAS enumeration in DiagonalImage/source; see the
attribution and certificate explanation in LinearOrder/source/README.md.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.LinearEnumeration
open GeneratorCertificates

def generatorRows (j : Fin 2) : Vector ℕ 112 :=
  if j = 0 then linearFirstRows else linearSecondRows

theorem zero_matrix : decodeRows (rows 0) = 1 := by
  rw [← decode_packedOne]
  apply congrArg decodeRows
  apply Vector.ext
  intro i hi
  have h : ∀ k : Fin 112, (rows 0).get k = packedOne.get k := by
    simp only [packedOne, get_ofFn]
    decide +kernel
  exact h ⟨i, hi⟩

theorem next_prev : ∀ (i : Fin 168) (j : Fin 2), next (prev i j) j = i := by
  decide +kernel

theorem tree : ∀ i : Fin 168, i ≠ 0 →
    (parent i).val < i.val ∧ next (parent i) (edge i) = i := by
  decide +kernel

/-- An observable of actual matrices, using all nine entries of the marked block. -/
def matrixKey (m : BinaryMatrix) : ℕ :=
  (m 28 28).val + 2 * (m 28 29).val + 4 * (m 28 30).val +
  8 * (m 29 28).val + 16 * (m 29 29).val + 32 * (m 29 30).val +
  64 * (m 30 28).val + 128 * (m 30 29).val + 256 * (m 30 30).val

def recoverIndex (m : BinaryMatrix) : ℕ := keyLookup[matrixKey m]?.getD 0

theorem recover_rows (i : Fin 168) : recoverIndex (decodeRows (rows i)) = i.val := by
  fin_cases i <;> decide +kernel

theorem matrices_injective : Function.Injective (fun i => decodeRows (rows i)) := by
  intro i j h
  change decodeRows (rows i) = decodeRows (rows j) at h
  apply Fin.ext
  rw [← recover_rows i, ← recover_rows j, h]

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.LinearEnumeration
