module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five.Products
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.Shared.Gate00

/-!
# Reuse the checked square of the literal second generator

The long-word circuit already checks every row of B times B. The equality
below checks that its numerical output is precisely this circuit's candidate.
No generator-order or word-interpretation premise is needed.

Source: the unchanged HSG1-f4r896aB0 matrices, with provenance retained in
`TracePair/source/README.md`, and the shared gate-zero certificate.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five
open Certificates

theorem bTwoRows_eq_longRows : bTwoRows = LongWords.rows02 := by
  decide +kernel

/-- The first gate reuses the fully checked literal B² product. -/
theorem value_gate_zero : ProductCheck 0 := by
  change Certificates.Packed.eval 896 generatorRowsB *
    Certificates.Packed.eval 896 generatorRowsB = Certificates.Packed.eval 896 bTwoRows
  rw [bTwoRows_eq_longRows]
  exact LongWords.Shared.Gate00.product_checked

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.Commutators.Five
