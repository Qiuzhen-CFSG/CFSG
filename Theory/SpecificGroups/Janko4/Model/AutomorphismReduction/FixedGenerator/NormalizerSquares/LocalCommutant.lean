module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalReduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Words
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Numerics

/-!
# The commutant of the actual J₄ involution centralizer

Eight explicitly certified words in the two ATLAS generators commute with the
first generator. Their word orbit contains a cyclic basis of 112 rows. A sum
of these words annihilates the seed row and has a checked right multiple whose
left kernel is spanned by that row and its image under the involution. Every
matrix commuting with the actual local subgroup therefore lies in the span
of the identity and the first generator.

The calculation uses the literal ATLAS representation `J4G1-f2r112B0`, with
source attribution in `Janko4/Model/Data.lean`. The witnesses and reproduction
script are retained in `LocalCommutant/source/`. No group order, simplicity,
normalizer or automorphism hypothesis is used.
-/

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open CommutantCertificate Matrix

/-- The full binary matrix commutant of the actual involution centralizer. -/
public theorem localMatrixCommutant : LocalMatrixCommutant := by
  apply commutant_of_certificates wordElements.get qMatrix qiMatrix rMatrix
    polynomialElements
  · intro i
    change qMatrix i = (((wordElements.get i : BinaryMatrixˣ) : BinaryMatrix)) 0
    rw [word_images]
    exact cyclic_rows i
  · exact cyclic_left_inverse
  · change rMatrix = (polynomialElements.map
        (fun c => ((c : BinaryMatrixˣ) : BinaryMatrix))).sum
    rw [polynomial_images]
    exact annihilator_polynomial.symm
  · exact annihilator_zero_row
  · intro x hx
    refine ⟨x 0, x 1, rowProjection_kernel x ?_⟩
    rw [← projection_matrix, ← annihilator_projection,
      ← vecMul_vecMul, hx, zero_vecMul]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares
