module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterReps
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Factors

/-!
# Transitions 40–79 for the 266-coset cover

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

public theorem outerEdge40_0 : outer40 * a = (factor0_0 : Model) * outer46 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer40, image_a, image_outer46]
  change outerMatrix40 * matrixA = hMatrixValue factor0_0 * outerMatrix46
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge40_1 : outer40 * b = (factor0_0 : Model) * outer47 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer40, image_b, image_outer47]
  change outerMatrix40 * matrixB = hMatrixValue factor0_0 * outerMatrix47
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge41_0 : outer41 * a = (factor0_0 : Model) * outer48 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer41, image_a, image_outer48]
  change outerMatrix41 * matrixA = hMatrixValue factor0_0 * outerMatrix48
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge41_1 : outer41 * b = (factor3_42 : Model) * outer34 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer41, image_b, image_outer34]
  change outerMatrix41 * matrixB = hMatrixValue factor3_42 * outerMatrix34
  rw [image_factor3_42]
  decide +kernel

public theorem outerEdge42_0 : outer42 * a = (factor0_0 : Model) * outer35 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer42, image_a, image_outer35]
  change outerMatrix42 * matrixA = hMatrixValue factor0_0 * outerMatrix35
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge42_1 : outer42 * b = (factor0_0 : Model) * outer49 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer42, image_b, image_outer49]
  change outerMatrix42 * matrixB = hMatrixValue factor0_0 * outerMatrix49
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge43_0 : outer43 * a = (factor0_0 : Model) * outer36 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer43, image_a, image_outer36]
  change outerMatrix43 * matrixA = hMatrixValue factor0_0 * outerMatrix36
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge43_1 : outer43 * b = (factor5_43 : Model) * outer42 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer43, image_b, image_outer42]
  change outerMatrix43 * matrixB = hMatrixValue factor5_43 * outerMatrix42
  rw [image_factor5_43]
  decide +kernel

public theorem outerEdge44_0 : outer44 * a = (factor0_0 : Model) * outer37 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer44, image_a, image_outer37]
  change outerMatrix44 * matrixA = hMatrixValue factor0_0 * outerMatrix37
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge44_1 : outer44 * b = (factor0_0 : Model) * outer50 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer44, image_b, image_outer50]
  change outerMatrix44 * matrixB = hMatrixValue factor0_0 * outerMatrix50
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge45_0 : outer45 * a = (factor0_0 : Model) * outer39 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer45, image_a, image_outer39]
  change outerMatrix45 * matrixA = hMatrixValue factor0_0 * outerMatrix39
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge45_1 : outer45 * b = (factor0_0 : Model) * outer51 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer45, image_b, image_outer51]
  change outerMatrix45 * matrixB = hMatrixValue factor0_0 * outerMatrix51
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge46_0 : outer46 * a = (factor0_0 : Model) * outer40 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer46, image_a, image_outer40]
  change outerMatrix46 * matrixA = hMatrixValue factor0_0 * outerMatrix40
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge46_1 : outer46 * b = (factor0_0 : Model) * outer52 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer46, image_b, image_outer52]
  change outerMatrix46 * matrixB = hMatrixValue factor0_0 * outerMatrix52
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge47_0 : outer47 * a = (factor2_46 : Model) * outer47 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer47, image_a, image_outer47]
  change outerMatrix47 * matrixA = hMatrixValue factor2_46 * outerMatrix47
  rw [image_factor2_46]
  decide +kernel

public theorem outerEdge47_1 : outer47 * b = (factor0_0 : Model) * outer31 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer47, image_b, image_outer31]
  change outerMatrix47 * matrixB = hMatrixValue factor0_0 * outerMatrix31
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge48_0 : outer48 * a = (factor0_0 : Model) * outer41 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer48, image_a, image_outer41]
  change outerMatrix48 * matrixA = hMatrixValue factor0_0 * outerMatrix41
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge48_1 : outer48 * b = (factor2_46 : Model) * outer46 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer48, image_b, image_outer46]
  change outerMatrix48 * matrixB = hMatrixValue factor2_46 * outerMatrix46
  rw [image_factor2_46]
  decide +kernel

public theorem outerEdge49_0 : outer49 * a = (factor0_0 : Model) * outer53 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer49, image_a, image_outer53]
  change outerMatrix49 * matrixA = hMatrixValue factor0_0 * outerMatrix53
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge49_1 : outer49 * b = (factor5_43 : Model) * outer43 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer49, image_b, image_outer43]
  change outerMatrix49 * matrixB = hMatrixValue factor5_43 * outerMatrix43
  rw [image_factor5_43]
  decide +kernel

public theorem outerEdge50_0 : outer50 * a = (factor0_0 : Model) * outer54 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer50, image_a, image_outer54]
  change outerMatrix50 * matrixA = hMatrixValue factor0_0 * outerMatrix54
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge50_1 : outer50 * b = (factor0_0 : Model) * outer55 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer50, image_b, image_outer55]
  change outerMatrix50 * matrixB = hMatrixValue factor0_0 * outerMatrix55
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge51_0 : outer51 * a = (factor0_0 : Model) * outer56 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer51, image_a, image_outer56]
  change outerMatrix51 * matrixA = hMatrixValue factor0_0 * outerMatrix56
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge51_1 : outer51 * b = (factor0_0 : Model) * outer57 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer51, image_b, image_outer57]
  change outerMatrix51 * matrixB = hMatrixValue factor0_0 * outerMatrix57
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge52_0 : outer52 * a = (factor0_0 : Model) * outer58 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer52, image_a, image_outer58]
  change outerMatrix52 * matrixA = hMatrixValue factor0_0 * outerMatrix58
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge52_1 : outer52 * b = (factor2_46 : Model) * outer48 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer52, image_b, image_outer48]
  change outerMatrix52 * matrixB = hMatrixValue factor2_46 * outerMatrix48
  rw [image_factor2_46]
  decide +kernel

public theorem outerEdge53_0 : outer53 * a = (factor0_0 : Model) * outer49 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer53, image_a, image_outer49]
  change outerMatrix53 * matrixA = hMatrixValue factor0_0 * outerMatrix49
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge53_1 : outer53 * b = (factor0_0 : Model) * outer59 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer53, image_b, image_outer59]
  change outerMatrix53 * matrixB = hMatrixValue factor0_0 * outerMatrix59
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge54_0 : outer54 * a = (factor0_0 : Model) * outer50 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer54, image_a, image_outer50]
  change outerMatrix54 * matrixA = hMatrixValue factor0_0 * outerMatrix50
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge54_1 : outer54 * b = (factor0_0 : Model) * outer60 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer54, image_b, image_outer60]
  change outerMatrix54 * matrixB = hMatrixValue factor0_0 * outerMatrix60
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge55_0 : outer55 * a = (factor0_0 : Model) * outer61 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer55, image_a, image_outer61]
  change outerMatrix55 * matrixA = hMatrixValue factor0_0 * outerMatrix61
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge55_1 : outer55 * b = (factor0_0 : Model) * outer44 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer55, image_b, image_outer44]
  change outerMatrix55 * matrixB = hMatrixValue factor0_0 * outerMatrix44
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge56_0 : outer56 * a = (factor0_0 : Model) * outer51 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer56, image_a, image_outer51]
  change outerMatrix56 * matrixA = hMatrixValue factor0_0 * outerMatrix51
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge56_1 : outer56 * b = (factor0_0 : Model) * outer62 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer56, image_b, image_outer62]
  change outerMatrix56 * matrixB = hMatrixValue factor0_0 * outerMatrix62
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge57_0 : outer57 * a = (factor0_0 : Model) * outer63 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer57, image_a, image_outer63]
  change outerMatrix57 * matrixA = hMatrixValue factor0_0 * outerMatrix63
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge57_1 : outer57 * b = (factor0_0 : Model) * outer45 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer57, image_b, image_outer45]
  change outerMatrix57 * matrixB = hMatrixValue factor0_0 * outerMatrix45
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge58_0 : outer58 * a = (factor0_0 : Model) * outer52 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer58, image_a, image_outer52]
  change outerMatrix58 * matrixA = hMatrixValue factor0_0 * outerMatrix52
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge58_1 : outer58 * b = (factor0_0 : Model) * outer64 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer58, image_b, image_outer64]
  change outerMatrix58 * matrixB = hMatrixValue factor0_0 * outerMatrix64
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge59_0 : outer59 * a = (factor0_0 : Model) * outer65 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer59, image_a, image_outer65]
  change outerMatrix59 * matrixA = hMatrixValue factor0_0 * outerMatrix65
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge59_1 : outer59 * b = (factor0_0 : Model) * outer66 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer59, image_b, image_outer66]
  change outerMatrix59 * matrixB = hMatrixValue factor0_0 * outerMatrix66
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge60_0 : outer60 * a = (factor5_43 : Model) * outer66 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer60, image_a, image_outer66]
  change outerMatrix60 * matrixA = hMatrixValue factor5_43 * outerMatrix66
  rw [image_factor5_43]
  decide +kernel

public theorem outerEdge60_1 : outer60 * b = (factor0_0 : Model) * outer67 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer60, image_b, image_outer67]
  change outerMatrix60 * matrixB = hMatrixValue factor0_0 * outerMatrix67
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge61_0 : outer61 * a = (factor0_0 : Model) * outer55 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer61, image_a, image_outer55]
  change outerMatrix61 * matrixA = hMatrixValue factor0_0 * outerMatrix55
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge61_1 : outer61 * b = (factor0_0 : Model) * outer68 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer61, image_b, image_outer68]
  change outerMatrix61 * matrixB = hMatrixValue factor0_0 * outerMatrix68
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge62_0 : outer62 * a = (factor0_0 : Model) * outer69 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer62, image_a, image_outer69]
  change outerMatrix62 * matrixA = hMatrixValue factor0_0 * outerMatrix69
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge62_1 : outer62 * b = (factor0_0 : Model) * outer70 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer62, image_b, image_outer70]
  change outerMatrix62 * matrixB = hMatrixValue factor0_0 * outerMatrix70
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge63_0 : outer63 * a = (factor0_0 : Model) * outer57 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer63, image_a, image_outer57]
  change outerMatrix63 * matrixA = hMatrixValue factor0_0 * outerMatrix57
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge63_1 : outer63 * b = (factor0_0 : Model) * outer71 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer63, image_b, image_outer71]
  change outerMatrix63 * matrixB = hMatrixValue factor0_0 * outerMatrix71
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge64_0 : outer64 * a = (factor0_0 : Model) * outer72 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer64, image_a, image_outer72]
  change outerMatrix64 * matrixA = hMatrixValue factor0_0 * outerMatrix72
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge64_1 : outer64 * b = (factor0_0 : Model) * outer73 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer64, image_b, image_outer73]
  change outerMatrix64 * matrixB = hMatrixValue factor0_0 * outerMatrix73
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge65_0 : outer65 * a = (factor0_0 : Model) * outer59 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer65, image_a, image_outer59]
  change outerMatrix65 * matrixA = hMatrixValue factor0_0 * outerMatrix59
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge65_1 : outer65 * b = (factor0_0 : Model) * outer74 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer65, image_b, image_outer74]
  change outerMatrix65 * matrixB = hMatrixValue factor0_0 * outerMatrix74
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge66_0 : outer66 * a = (factor5_43 : Model) * outer60 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer66, image_a, image_outer60]
  change outerMatrix66 * matrixA = hMatrixValue factor5_43 * outerMatrix60
  rw [image_factor5_43]
  decide +kernel

public theorem outerEdge66_1 : outer66 * b = (factor0_0 : Model) * outer53 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer66, image_b, image_outer53]
  change outerMatrix66 * matrixB = hMatrixValue factor0_0 * outerMatrix53
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge67_0 : outer67 * a = (factor0_0 : Model) * outer75 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer67, image_a, image_outer75]
  change outerMatrix67 * matrixA = hMatrixValue factor0_0 * outerMatrix75
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge67_1 : outer67 * b = (factor0_0 : Model) * outer54 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer67, image_b, image_outer54]
  change outerMatrix67 * matrixB = hMatrixValue factor0_0 * outerMatrix54
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge68_0 : outer68 * a = (factor0_0 : Model) * outer76 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer68, image_a, image_outer76]
  change outerMatrix68 * matrixA = hMatrixValue factor0_0 * outerMatrix76
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge68_1 : outer68 * b = (factor0_0 : Model) * outer77 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer68, image_b, image_outer77]
  change outerMatrix68 * matrixB = hMatrixValue factor0_0 * outerMatrix77
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge69_0 : outer69 * a = (factor0_0 : Model) * outer62 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer69, image_a, image_outer62]
  change outerMatrix69 * matrixA = hMatrixValue factor0_0 * outerMatrix62
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge69_1 : outer69 * b = (factor0_0 : Model) * outer78 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer69, image_b, image_outer78]
  change outerMatrix69 * matrixB = hMatrixValue factor0_0 * outerMatrix78
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge70_0 : outer70 * a = (factor0_0 : Model) * outer79 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer70, image_a, image_outer79]
  change outerMatrix70 * matrixA = hMatrixValue factor0_0 * outerMatrix79
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge70_1 : outer70 * b = (factor0_0 : Model) * outer56 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer70, image_b, image_outer56]
  change outerMatrix70 * matrixB = hMatrixValue factor0_0 * outerMatrix56
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge71_0 : outer71 * a = (factor0_0 : Model) * outer80 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer71, image_a, image_outer80]
  change outerMatrix71 * matrixA = hMatrixValue factor0_0 * outerMatrix80
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge71_1 : outer71 * b = (factor0_0 : Model) * outer72 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer71, image_b, image_outer72]
  change outerMatrix71 * matrixB = hMatrixValue factor0_0 * outerMatrix72
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge72_0 : outer72 * a = (factor0_0 : Model) * outer64 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer72, image_a, image_outer64]
  change outerMatrix72 * matrixA = hMatrixValue factor0_0 * outerMatrix64
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge72_1 : outer72 * b = (factor0_0 : Model) * outer63 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer72, image_b, image_outer63]
  change outerMatrix72 * matrixB = hMatrixValue factor0_0 * outerMatrix63
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge73_0 : outer73 * a = (factor8_0 : Model) * outer74 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer73, image_a, image_outer74]
  change outerMatrix73 * matrixA = hMatrixValue factor8_0 * outerMatrix74
  rw [image_factor8_0]
  decide +kernel

public theorem outerEdge73_1 : outer73 * b = (factor0_0 : Model) * outer58 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer73, image_b, image_outer58]
  change outerMatrix73 * matrixB = hMatrixValue factor0_0 * outerMatrix58
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge74_0 : outer74 * a = (factor3_0 : Model) * outer73 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer74, image_a, image_outer73]
  change outerMatrix74 * matrixA = hMatrixValue factor3_0 * outerMatrix73
  rw [image_factor3_0]
  decide +kernel

public theorem outerEdge74_1 : outer74 * b = (factor0_0 : Model) * outer81 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer74, image_b, image_outer81]
  change outerMatrix74 * matrixB = hMatrixValue factor0_0 * outerMatrix81
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge75_0 : outer75 * a = (factor0_0 : Model) * outer67 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer75, image_a, image_outer67]
  change outerMatrix75 * matrixA = hMatrixValue factor0_0 * outerMatrix67
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge75_1 : outer75 * b = (factor0_0 : Model) * outer82 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer75, image_b, image_outer82]
  change outerMatrix75 * matrixB = hMatrixValue factor0_0 * outerMatrix82
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge76_0 : outer76 * a = (factor0_0 : Model) * outer68 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer76, image_a, image_outer68]
  change outerMatrix76 * matrixA = hMatrixValue factor0_0 * outerMatrix68
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge76_1 : outer76 * b = (factor0_0 : Model) * outer83 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer76, image_b, image_outer83]
  change outerMatrix76 * matrixB = hMatrixValue factor0_0 * outerMatrix83
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge77_0 : outer77 * a = (factor0_0 : Model) * outer78 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer77, image_a, image_outer78]
  change outerMatrix77 * matrixA = hMatrixValue factor0_0 * outerMatrix78
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge77_1 : outer77 * b = (factor0_0 : Model) * outer61 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer77, image_b, image_outer61]
  change outerMatrix77 * matrixB = hMatrixValue factor0_0 * outerMatrix61
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge78_0 : outer78 * a = (factor0_0 : Model) * outer77 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer78, image_a, image_outer77]
  change outerMatrix78 * matrixA = hMatrixValue factor0_0 * outerMatrix77
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge78_1 : outer78 * b = (factor0_0 : Model) * outer84 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer78, image_b, image_outer84]
  change outerMatrix78 * matrixB = hMatrixValue factor0_0 * outerMatrix84
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge79_0 : outer79 * a = (factor0_0 : Model) * outer70 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer79, image_a, image_outer70]
  change outerMatrix79 * matrixA = hMatrixValue factor0_0 * outerMatrix70
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge79_1 : outer79 * b = (factor0_0 : Model) * outer85 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer79, image_b, image_outer85]
  change outerMatrix79 * matrixB = hMatrixValue factor0_0 * outerMatrix85
  rw [image_factor0_0]
  decide +kernel


end Janko1.OrderCertificate
