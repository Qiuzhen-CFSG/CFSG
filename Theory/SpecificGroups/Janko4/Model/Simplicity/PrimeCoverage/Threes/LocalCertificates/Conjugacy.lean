module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Conjugacy.Assembly

/-!
# Conjugacy of the local order-three normal forms

The 26 explicit ATLAS-word witnesses are certified by packed multiplication.
`Matrices` identifies the program outputs and normal forms; `Conjugacy.Assembly`
transfers the product certificates through the faithful matrix map.
See `Threes.LocalModel`, `Model.Data`, and `Conjugacy.Rows` for attribution.
-/

public section
namespace Janko4.Simplicity
open ThreeLocalCertificates

theorem threeLocalNormalForm_conjugacy
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ∀ t : Fin 3 × Fin 3 × Fin 3, t ≠ (0,0,0) →
      ∃ (i : Fin 2) (g : Model),
        threeLocalRepresentative hA hB i = g * threeLocalNormalForm hA hB t * g⁻¹ :=
  threeLocalNormalForm_conjugacy_of_matrices hA hB
    (program_fst_matrix hA hB) (program_snd_matrix hA hB)
    (u_matrix hA hB) (z_matrix hA hB) (normalForm_matrix hA hB)

end Janko4.Simplicity
