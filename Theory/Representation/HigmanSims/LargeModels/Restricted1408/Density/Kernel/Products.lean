module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Contracts
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Density.Kernel.Products21

/-!
# Certified rows of the degree-1408 singular matrix

Each of the 1408 proposed rows is checked by kernel reduction against the
literal expression `1 + B + A*B + B*A`. The 64-row certificates are combined
using `checkRange_append`, and the existing decoder bridge identifies the
result with ordinary matrix multiplication in the published coordinates.

The proposals and numerical source are described in `source/README.md`.
This discharges the row-table premise of the exact-kernel assembly; the
independent row-reduction certificate remains with its own producer.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData

/-- All rows of the proposed table agree with the two literal packed products. -/
theorem rowTableCertificate : RowTableCertificate := productsThrough1408

/-- The certified table decodes to the actual singular matrix used by density. -/
theorem separatingMatrix_eq_decode_certified :
    separatingMatrix = Thompson.BinaryMatrix.decode 1408 sRows :=
  separatingMatrix_eq_decode rowTableCertificate

end Representation.HigmanSims.LargeModels.Restricted1408.Density.KernelData
