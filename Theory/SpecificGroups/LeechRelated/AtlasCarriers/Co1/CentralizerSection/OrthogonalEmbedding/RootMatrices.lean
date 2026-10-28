module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.Roots
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.Words
/-!
# Coordinate matrices of the six Siegel generators

Entrywise evaluation identifies each actual Siegel isometry with its elementary
binary matrix in the fixed hyperbolic coordinates. These equalities connect the
matrix-word certificates to the elementary orthogonal carrier, independently
of any group order or recognition assertion.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
def rootRows : Fin 6 → Rows := ![![33, 18, 4, 8, 16, 32, 64, 128],
![65, 2, 20, 8, 16, 32, 64, 128],
![129, 2, 4, 24, 16, 32, 64, 128],
![3, 2, 4, 8, 16, 48, 64, 128],
![5, 2, 4, 8, 16, 32, 80, 128],
![9, 2, 4, 8, 16, 32, 64, 144]]
theorem root_entry : ∀ (i : Fin 6) (j k : Fin 8),
    coordinates ((rootGenerator i).val (coordinates.symm (Pi.single k 1))) j =
      Packed.decode (rootRows i) j k := by
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

theorem rootGenerator_val (i : Fin 6) :
    (matrixHom (rootGenerator i)).val = Packed.decode (rootRows i) := by
  ext j k
  rw [matrixHom_entry]
  exact root_entry i j k
end Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
