module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.NormalForms.Transitions
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.NormalForms.Separation

/-!
# Normal-form certificates for the local J4 three-subgroup

The packed normal forms have the two asserted right-generator transitions and
are distinct, as certified in `Transitions` and `Separation`. Faithfulness of
the matrix inclusion transfers these facts to the concrete group words using
the packed matrix evaluations certified in `Matrices`. No subgroup enumeration
or order assertion is assumed.

The words and source attribution (ATLAS `J4G1-max10W1`, R. A. Wilson,
S. J. Nickerson and J. N. Bray) are in `Threes.LocalModel`.
-/

public section
namespace Janko4.Simplicity
open Janko4.GeneratorCertificates ThreeLocalCertificates

/-- Transfer the first certified transition through the faithful representation. -/
theorem threeLocalNormalForm_mul_u_of_matrix_evaluations
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hu : toMatrix (threeLocalU hA hB) = decodeRows uRows)
    (hn : ∀ t, toMatrix (threeLocalNormalForm hA hB t) = decodeRows (normalRows t))
    (t : Fin 3 × Fin 3 × Fin 3) :
    threeLocalNormalForm hA hB t * threeLocalU hA hB =
      threeLocalNormalForm hA hB (t.1 + 1, t.2.1, t.2.2 - t.2.1) := by
  apply toMatrix_injective
  rw [map_mul, hn, hu, hn, ← decode_packedMul, normalRows_mul_u]

/-- Transfer the second certified transition through the faithful representation. -/
theorem threeLocalNormalForm_mul_v_of_matrix_evaluations
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hv : toMatrix (threeLocalV hA hB) = decodeRows vRows)
    (hn : ∀ t, toMatrix (threeLocalNormalForm hA hB t) = decodeRows (normalRows t))
    (t : Fin 3 × Fin 3 × Fin 3) :
    threeLocalNormalForm hA hB t * threeLocalV hA hB =
      threeLocalNormalForm hA hB (t.1, t.2.1 + 1, t.2.2) := by
  apply toMatrix_injective
  rw [map_mul, hn, hv, hn, ← decode_packedMul, normalRows_mul_v]

/-- Six matrix entries distinguish the concrete words once evaluated. -/
theorem threeLocalNormalForm_injective_of_matrix_evaluations
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hn : ∀ t, toMatrix (threeLocalNormalForm hA hB t) = decodeRows (normalRows t)) :
    Function.Injective (threeLocalNormalForm hA hB) := by
  intro s t h
  apply normalRows_decode_injective
  change decodeRows (normalRows s) = decodeRows (normalRows t)
  rw [← hn s, ← hn t, h]

theorem threeLocalNormalForm_mul_u
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (t : Fin 3 × Fin 3 × Fin 3) :
    threeLocalNormalForm hA hB t * threeLocalU hA hB =
      threeLocalNormalForm hA hB (t.1 + 1, t.2.1, t.2.2 - t.2.1) :=
  threeLocalNormalForm_mul_u_of_matrix_evaluations hA hB
    (u_matrix hA hB) (normalForm_matrix hA hB) t

theorem threeLocalNormalForm_mul_v
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (t : Fin 3 × Fin 3 × Fin 3) :
    threeLocalNormalForm hA hB t * threeLocalV hA hB =
      threeLocalNormalForm hA hB (t.1, t.2.1 + 1, t.2.2) :=
  threeLocalNormalForm_mul_v_of_matrix_evaluations hA hB
    (v_matrix hA hB) (normalForm_matrix hA hB) t

theorem threeLocalNormalForm_injective
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Function.Injective (threeLocalNormalForm hA hB) :=
  threeLocalNormalForm_injective_of_matrix_evaluations hA hB
    (normalForm_matrix hA hB)

end Janko4.Simplicity
