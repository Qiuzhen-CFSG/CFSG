module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Injectivity.FirstRow
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Injectivity.Certificates

/-!
# Distinctness of the 2048 binary matrix products

The first row determines the eleven selected factors. The row recurrence and a
binary-search retraction are checked by kernel reduction in `Certificates`;
`FirstRow` transfers them to the increasing-index products in `matrixProduct`.
The proof uses no group relations or identification of the matrices with words.

Source for the matrices: ATLAS `J4G1-max1W1`, as recorded in `KernelCount.Tables`.
-/

public section
namespace Janko4.Cardinality.KernelCount

/-- The eleven choices give 2048 distinct matrices, already distinguished by
    their first rows. -/
theorem matrixProduct_injective : Function.Injective matrixProduct :=
  Injectivity.matrixProduct_injective_of_certificate
    Injectivity.row Injectivity.row_zero Injectivity.row_step
    Injectivity.recover Injectivity.recover_row Injectivity.row_lt

end Janko4.Cardinality.KernelCount
