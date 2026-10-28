module

public import Theory.AlgebraicGroup.Borel.RootBorelDecomposition
public import Theory.AlgebraicGroup.RootData.Realization

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-!
The actual-root-generation assembly needs a positive system on the *same*
root labels as the realized root subgroups.  `RootGroupData.IsRealization`
identifies the canonical positive set as the roots of positive height, but its
contract does not exclude height-zero labels.  The realization-layer theorem
therefore takes nonzero height as an explicit premise.  This module wires that
certificate into `RealizedRootBorelOppositeData` while leaving the independent
positive and opposite Borel witnesses explicit.  No numbered Borel or root-
generation theorem is used.
-/

omit [IsAlgClosed k] in
/-- Package the canonical positive set with compatible Borel witnesses.

The Borel witnesses are intentionally hypotheses: this theorem supplies only
the positive-system part of the actual-root-generation input and does not hide
the unresolved geometric Borel-existence step.
-/
public theorem exists_realizedRootBorelOppositeData_of_height_ne_zero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization)
    (hheight : ∀ α : D.Root, D.height α ≠ 0)
    (hB : ∃ B : ClosedSubgroup K,
      Nonempty (IsBorelOfPositiveSystem D D.positive B))
    (hBopp : ∃ Bopp : ClosedSubgroup K,
      Nonempty (IsBorelOfPositiveSystem D (D.neg ⁻¹' D.positive) Bopp)) :
    Nonempty (RealizedRootBorelOppositeData T D D.positive) := by
  exact RealizedRootBorelOppositeData.exists_of_witnesses
    (hD.positive_isPositiveSystem_of_height_ne_zero hheight) hB hBopp

end Theory.AlgebraicGroup

