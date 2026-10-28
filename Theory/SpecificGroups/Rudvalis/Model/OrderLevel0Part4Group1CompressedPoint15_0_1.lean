module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Fast

namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
set_option maxRecDepth 30000
set_option Elab.async false

private def point15_0_1Word : List (Fin 71) := [64, 61, 37, 42, 68, 38]
private theorem point15_0_1Expanded :
    point15_0_1Word.flatMap Part4Group1Fast.word = L0Factor 0 2181 := by
  decide +kernel
set_option maxHeartbeats 1600000 in
private theorem point15_0_1Check : Part4Group1Fast.check 0 2181 point15_0_1Word = true := by
  decide +kernel
public theorem compressedPoint15_0_1 : stepCheck 0 2181 :=
  Part4Group1Fast.ofCheck 0 2181 point15_0_1Word point15_0_1Expanded point15_0_1Check

end Rudvalis.OrderCertificate.ForwardReduction.Part4Certificates
