module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords

/-! The alternating certificate discharges the corresponding premise of the
actual first-seven-source-word consumer. The independent generator and
commutator families remain with their existing producers. -/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts

/-- Apply the unconditional alternating family to the original word assembly. -/
theorem smallWords_of_other_products (g : GeneratorProducts) (c : CommutatorProducts) :
    ∀ i : Fin 7, matrixWord ⟨i.val, by omega⟩ = 1 :=
  smallWords_of_products g alternatingProducts c

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts
