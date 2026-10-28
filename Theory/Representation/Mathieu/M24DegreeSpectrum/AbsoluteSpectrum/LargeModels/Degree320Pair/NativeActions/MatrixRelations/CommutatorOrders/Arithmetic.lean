module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.Blocks

/-!
# Literal row checks for the degree-320 commutator words

A single row uses the existing proved skipRow checker with literal input and
output numbers. Joining these certificates does not evaluate list slicing
inside the arithmetic reduction. The Products modules are the consumers.
Source: John Bray, ATLAS M24G1-P1.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.CommutatorOrders

/-- Attach one literal row to the remaining checked rows. -/
theorem cons {a c : Nat} {as b cs : List Nat}
    (h : MatrixCertificates.skipRow a b = c) (ht : Checked as b cs) :
    Checked (a :: as) b (c :: cs) := by
  refine ⟨?_⟩
  simp only [checkRows, ← MatrixCertificates.skipRow_eq, h, beq_self_eq_true,
    Bool.true_and]
  exact ht.eq_true

/-- The empty tail of a row certificate. -/
theorem nil (b : List Nat) : Checked [] b [] := ⟨rfl⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate.CommutatorOrders
