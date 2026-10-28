module

public import Theory.SpecificGroups.Thompson.Model.Order.LocalOrder.PackedData
public import Theory.SpecificGroups.Thompson.Model.Order.LocalOrder.RowCheck

/-!
# Kernel-checked local matrix products

Checked packed lookups and Boolean row products certify the usual matrix
multiplication. All computations reduce in Lean's kernel. The independent
products are split into independent compilation units. Source: `Order/source/`.
-/

namespace Thompson.OrderCertificate.LocalMatrices
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
public theorem mul_r3_r3 :
    (BinaryMatrix.decode 248 r3Rows) * (BinaryMatrix.decode 248 r3Rows) = BinaryMatrix.decode 248 p2Rows := by
  apply checked_mul_packed 248 r3Rows r3Rows p2Rows r3Packed r3Packed
  · decide +kernel
  · decide +kernel
  · decide +kernel

end Thompson.OrderCertificate.LocalMatrices
