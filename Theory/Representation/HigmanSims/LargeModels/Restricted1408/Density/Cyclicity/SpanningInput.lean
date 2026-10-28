module

public import Theory.LinearAlgebra.PackedBinaryRows
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.RowData
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity.ColumnData

/-!
# The two remaining packed spanning contracts

Every coordinate unit vector must be a checked binary linear combination of
the proposed orbit rows. This is an arithmetic certificate contract, not an
assertion that the orbit spans. It needs no action or kernel hypotheses and
can be proved independently of all generator recurrences.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity

/-- Each standard basis vector has an explicit packed linear combination. -/
def PackedSpanning (rows : Array Nat) : Prop :=
  ∀ i : Fin 1408, ∃ c : Nat, PackedBinaryRows.listProduct c 0 rows.toList = 2 ^ i.val

end Representation.HigmanSims.LargeModels.Restricted1408.Density.Cyclicity
