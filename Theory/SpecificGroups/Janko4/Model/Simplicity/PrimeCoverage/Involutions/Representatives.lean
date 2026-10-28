module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.MatrixResults

/-!
# The two proposed involution representatives have order two

The kernel-checked matrix products in `GeneratorCertificates.MatrixResults`
prove that the ATLAS words `a` and `ababb` have orders 2 and 10. Faithfulness
of the matrix representation and the order formula for powers give order 2
for entries 0 and 1 of `primeRepresentative`. No class-table information is
used. The source words are documented in `Simplicity.Words`.
-/

public section

namespace Janko4.Simplicity

/-- The first proposed involution is certified directly by its matrix. -/
theorem involutionRepresentative_zero_orderOf
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    orderOf (primeRepresentative (a hA) (b hB) 0) = 2 := by
  change orderOf (a hA) = 2
  rw [← orderOf_injective toMatrix toMatrix_injective, toMatrix_a]
  exact orderOf_matrixA

/-- The fifth power of the certified order-ten word is an involution. -/
theorem involutionRepresentative_one_orderOf
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    orderOf (primeRepresentative (a hA) (b hB) 1) = 2 := by
  change orderOf (word (a hA) (b hB) "ababb" ^ 5) = 2
  have hw : orderOf (word (a hA) (b hB) "ababb") = 10 := by
    rw [← orderOf_injective toMatrix toMatrix_injective]
    simpa [word, mul_assoc] using orderOf_matrixABABB
  rw [orderOf_pow, hw]
  norm_num

end Janko4.Simplicity
