module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterReps
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Factors

/-!
# Transitions 80–119 for the 266-coset cover

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

public theorem outerEdge80_0 : outer80 * a = (factor0_0 : Model) * outer71 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer80, image_a, image_outer71]
  change outerMatrix80 * matrixA = hMatrixValue factor0_0 * outerMatrix71
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge80_1 : outer80 * b = (factor0_0 : Model) * outer86 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer80, image_b, image_outer86]
  change outerMatrix80 * matrixB = hMatrixValue factor0_0 * outerMatrix86
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge81_0 : outer81 * a = (factor0_0 : Model) * outer87 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer81, image_a, image_outer87]
  change outerMatrix81 * matrixA = hMatrixValue factor0_0 * outerMatrix87
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge81_1 : outer81 * b = (factor0_0 : Model) * outer65 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer81, image_b, image_outer65]
  change outerMatrix81 * matrixB = hMatrixValue factor0_0 * outerMatrix65
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge82_0 : outer82 * a = (factor0_0 : Model) * outer88 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer82, image_a, image_outer88]
  change outerMatrix82 * matrixA = hMatrixValue factor0_0 * outerMatrix88
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge82_1 : outer82 * b = (factor0_0 : Model) * outer89 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer82, image_b, image_outer89]
  change outerMatrix82 * matrixB = hMatrixValue factor0_0 * outerMatrix89
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge83_0 : outer83 * a = (factor0_0 : Model) * outer90 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer83, image_a, image_outer90]
  change outerMatrix83 * matrixA = hMatrixValue factor0_0 * outerMatrix90
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge83_1 : outer83 * b = (factor0_0 : Model) * outer91 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer83, image_b, image_outer91]
  change outerMatrix83 * matrixB = hMatrixValue factor0_0 * outerMatrix91
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge84_0 : outer84 * a = (factor0_0 : Model) * outer92 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer84, image_a, image_outer92]
  change outerMatrix84 * matrixA = hMatrixValue factor0_0 * outerMatrix92
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge84_1 : outer84 * b = (factor0_0 : Model) * outer69 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer84, image_b, image_outer69]
  change outerMatrix84 * matrixB = hMatrixValue factor0_0 * outerMatrix69
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge85_0 : outer85 * a = (factor0_0 : Model) * outer93 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer85, image_a, image_outer93]
  change outerMatrix85 * matrixA = hMatrixValue factor0_0 * outerMatrix93
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge85_1 : outer85 * b = (factor0_0 : Model) * outer94 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer85, image_b, image_outer94]
  change outerMatrix85 * matrixB = hMatrixValue factor0_0 * outerMatrix94
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge86_0 : outer86 * a = (factor0_0 : Model) * outer95 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer86, image_a, image_outer95]
  change outerMatrix86 * matrixA = hMatrixValue factor0_0 * outerMatrix95
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge86_1 : outer86 * b = (factor0_0 : Model) * outer96 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer86, image_b, image_outer96]
  change outerMatrix86 * matrixB = hMatrixValue factor0_0 * outerMatrix96
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge87_0 : outer87 * a = (factor0_0 : Model) * outer81 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer87, image_a, image_outer81]
  change outerMatrix87 * matrixA = hMatrixValue factor0_0 * outerMatrix81
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge87_1 : outer87 * b = (factor0_0 : Model) * outer97 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer87, image_b, image_outer97]
  change outerMatrix87 * matrixB = hMatrixValue factor0_0 * outerMatrix97
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge88_0 : outer88 * a = (factor0_0 : Model) * outer82 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer88, image_a, image_outer82]
  change outerMatrix88 * matrixA = hMatrixValue factor0_0 * outerMatrix82
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge88_1 : outer88 * b = (factor0_0 : Model) * outer98 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer88, image_b, image_outer98]
  change outerMatrix88 * matrixB = hMatrixValue factor0_0 * outerMatrix98
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge89_0 : outer89 * a = (factor0_0 : Model) * outer99 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer89, image_a, image_outer99]
  change outerMatrix89 * matrixA = hMatrixValue factor0_0 * outerMatrix99
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge89_1 : outer89 * b = (factor0_0 : Model) * outer75 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer89, image_b, image_outer75]
  change outerMatrix89 * matrixB = hMatrixValue factor0_0 * outerMatrix75
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge90_0 : outer90 * a = (factor0_0 : Model) * outer83 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer90, image_a, image_outer83]
  change outerMatrix90 * matrixA = hMatrixValue factor0_0 * outerMatrix83
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge90_1 : outer90 * b = (factor0_0 : Model) * outer100 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer90, image_b, image_outer100]
  change outerMatrix90 * matrixB = hMatrixValue factor0_0 * outerMatrix100
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge91_0 : outer91 * a = (factor0_0 : Model) * outer101 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer91, image_a, image_outer101]
  change outerMatrix91 * matrixA = hMatrixValue factor0_0 * outerMatrix101
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge91_1 : outer91 * b = (factor0_0 : Model) * outer76 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer91, image_b, image_outer76]
  change outerMatrix91 * matrixB = hMatrixValue factor0_0 * outerMatrix76
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge92_0 : outer92 * a = (factor0_0 : Model) * outer84 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer92, image_a, image_outer84]
  change outerMatrix92 * matrixA = hMatrixValue factor0_0 * outerMatrix84
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge92_1 : outer92 * b = (factor0_0 : Model) * outer102 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer92, image_b, image_outer102]
  change outerMatrix92 * matrixB = hMatrixValue factor0_0 * outerMatrix102
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge93_0 : outer93 * a = (factor0_0 : Model) * outer85 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer93, image_a, image_outer85]
  change outerMatrix93 * matrixA = hMatrixValue factor0_0 * outerMatrix85
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge93_1 : outer93 * b = (factor0_0 : Model) * outer103 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer93, image_b, image_outer103]
  change outerMatrix93 * matrixB = hMatrixValue factor0_0 * outerMatrix103
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge94_0 : outer94 * a = (factor0_0 : Model) * outer104 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer94, image_a, image_outer104]
  change outerMatrix94 * matrixA = hMatrixValue factor0_0 * outerMatrix104
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge94_1 : outer94 * b = (factor0_0 : Model) * outer79 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer94, image_b, image_outer79]
  change outerMatrix94 * matrixB = hMatrixValue factor0_0 * outerMatrix79
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge95_0 : outer95 * a = (factor0_0 : Model) * outer86 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer95, image_a, image_outer86]
  change outerMatrix95 * matrixA = hMatrixValue factor0_0 * outerMatrix86
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge95_1 : outer95 * b = (factor0_0 : Model) * outer105 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer95, image_b, image_outer105]
  change outerMatrix95 * matrixB = hMatrixValue factor0_0 * outerMatrix105
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge96_0 : outer96 * a = (factor0_0 : Model) * outer106 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer96, image_a, image_outer106]
  change outerMatrix96 * matrixA = hMatrixValue factor0_0 * outerMatrix106
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge96_1 : outer96 * b = (factor0_0 : Model) * outer80 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer96, image_b, image_outer80]
  change outerMatrix96 * matrixB = hMatrixValue factor0_0 * outerMatrix80
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge97_0 : outer97 * a = (factor0_0 : Model) * outer107 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer97, image_a, image_outer107]
  change outerMatrix97 * matrixA = hMatrixValue factor0_0 * outerMatrix107
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge97_1 : outer97 * b = (factor0_0 : Model) * outer108 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer97, image_b, image_outer108]
  change outerMatrix97 * matrixB = hMatrixValue factor0_0 * outerMatrix108
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge98_0 : outer98 * a = (factor0_0 : Model) * outer109 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer98, image_a, image_outer109]
  change outerMatrix98 * matrixA = hMatrixValue factor0_0 * outerMatrix109
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge98_1 : outer98 * b = (factor0_0 : Model) * outer110 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer98, image_b, image_outer110]
  change outerMatrix98 * matrixB = hMatrixValue factor0_0 * outerMatrix110
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge99_0 : outer99 * a = (factor0_0 : Model) * outer89 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer99, image_a, image_outer89]
  change outerMatrix99 * matrixA = hMatrixValue factor0_0 * outerMatrix89
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge99_1 : outer99 * b = (factor0_0 : Model) * outer111 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer99, image_b, image_outer111]
  change outerMatrix99 * matrixB = hMatrixValue factor0_0 * outerMatrix111
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge100_0 : outer100 * a = (factor0_0 : Model) * outer112 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer100, image_a, image_outer112]
  change outerMatrix100 * matrixA = hMatrixValue factor0_0 * outerMatrix112
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge100_1 : outer100 * b = (factor0_0 : Model) * outer113 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer100, image_b, image_outer113]
  change outerMatrix100 * matrixB = hMatrixValue factor0_0 * outerMatrix113
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge101_0 : outer101 * a = (factor0_0 : Model) * outer91 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer101, image_a, image_outer91]
  change outerMatrix101 * matrixA = hMatrixValue factor0_0 * outerMatrix91
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge101_1 : outer101 * b = (factor0_0 : Model) * outer114 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer101, image_b, image_outer114]
  change outerMatrix101 * matrixB = hMatrixValue factor0_0 * outerMatrix114
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge102_0 : outer102 * a = (factor0_0 : Model) * outer115 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer102, image_a, image_outer115]
  change outerMatrix102 * matrixA = hMatrixValue factor0_0 * outerMatrix115
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge102_1 : outer102 * b = (factor0_0 : Model) * outer116 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer102, image_b, image_outer116]
  change outerMatrix102 * matrixB = hMatrixValue factor0_0 * outerMatrix116
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge103_0 : outer103 * a = (factor0_0 : Model) * outer117 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer103, image_a, image_outer117]
  change outerMatrix103 * matrixA = hMatrixValue factor0_0 * outerMatrix117
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge103_1 : outer103 * b = (factor0_0 : Model) * outer118 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer103, image_b, image_outer118]
  change outerMatrix103 * matrixB = hMatrixValue factor0_0 * outerMatrix118
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge104_0 : outer104 * a = (factor0_0 : Model) * outer94 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer104, image_a, image_outer94]
  change outerMatrix104 * matrixA = hMatrixValue factor0_0 * outerMatrix94
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge104_1 : outer104 * b = (factor0_0 : Model) * outer119 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer104, image_b, image_outer119]
  change outerMatrix104 * matrixB = hMatrixValue factor0_0 * outerMatrix119
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge105_0 : outer105 * a = (factor0_0 : Model) * outer120 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer105, image_a, image_outer120]
  change outerMatrix105 * matrixA = hMatrixValue factor0_0 * outerMatrix120
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge105_1 : outer105 * b = (factor0_0 : Model) * outer121 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer105, image_b, image_outer121]
  change outerMatrix105 * matrixB = hMatrixValue factor0_0 * outerMatrix121
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge106_0 : outer106 * a = (factor0_0 : Model) * outer96 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer106, image_a, image_outer96]
  change outerMatrix106 * matrixA = hMatrixValue factor0_0 * outerMatrix96
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge106_1 : outer106 * b = (factor0_0 : Model) * outer122 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer106, image_b, image_outer122]
  change outerMatrix106 * matrixB = hMatrixValue factor0_0 * outerMatrix122
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge107_0 : outer107 * a = (factor0_0 : Model) * outer97 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer107, image_a, image_outer97]
  change outerMatrix107 * matrixA = hMatrixValue factor0_0 * outerMatrix97
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge107_1 : outer107 * b = (factor0_0 : Model) * outer123 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer107, image_b, image_outer123]
  change outerMatrix107 * matrixB = hMatrixValue factor0_0 * outerMatrix123
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge108_0 : outer108 * a = (factor0_0 : Model) * outer124 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer108, image_a, image_outer124]
  change outerMatrix108 * matrixA = hMatrixValue factor0_0 * outerMatrix124
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge108_1 : outer108 * b = (factor0_0 : Model) * outer87 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer108, image_b, image_outer87]
  change outerMatrix108 * matrixB = hMatrixValue factor0_0 * outerMatrix87
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge109_0 : outer109 * a = (factor0_0 : Model) * outer98 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer109, image_a, image_outer98]
  change outerMatrix109 * matrixA = hMatrixValue factor0_0 * outerMatrix98
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge109_1 : outer109 * b = (factor5_43 : Model) * outer124 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer109, image_b, image_outer124]
  change outerMatrix109 * matrixB = hMatrixValue factor5_43 * outerMatrix124
  rw [image_factor5_43]
  decide +kernel

public theorem outerEdge110_0 : outer110 * a = (factor0_0 : Model) * outer125 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer110, image_a, image_outer125]
  change outerMatrix110 * matrixA = hMatrixValue factor0_0 * outerMatrix125
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge110_1 : outer110 * b = (factor0_0 : Model) * outer88 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer110, image_b, image_outer88]
  change outerMatrix110 * matrixB = hMatrixValue factor0_0 * outerMatrix88
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge111_0 : outer111 * a = (factor0_0 : Model) * outer126 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer111, image_a, image_outer126]
  change outerMatrix111 * matrixA = hMatrixValue factor0_0 * outerMatrix126
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge111_1 : outer111 * b = (factor0_0 : Model) * outer112 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer111, image_b, image_outer112]
  change outerMatrix111 * matrixB = hMatrixValue factor0_0 * outerMatrix112
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge112_0 : outer112 * a = (factor0_0 : Model) * outer100 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer112, image_a, image_outer100]
  change outerMatrix112 * matrixA = hMatrixValue factor0_0 * outerMatrix100
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge112_1 : outer112 * b = (factor0_0 : Model) * outer99 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer112, image_b, image_outer99]
  change outerMatrix112 * matrixB = hMatrixValue factor0_0 * outerMatrix99
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge113_0 : outer113 * a = (factor0_0 : Model) * outer127 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer113, image_a, image_outer127]
  change outerMatrix113 * matrixA = hMatrixValue factor0_0 * outerMatrix127
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge113_1 : outer113 * b = (factor0_0 : Model) * outer90 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer113, image_b, image_outer90]
  change outerMatrix113 * matrixB = hMatrixValue factor0_0 * outerMatrix90
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge114_0 : outer114 * a = (factor4_36 : Model) * outer114 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer114, image_a, image_outer114]
  change outerMatrix114 * matrixA = hMatrixValue factor4_36 * outerMatrix114
  rw [image_factor4_36]
  decide +kernel

public theorem outerEdge114_1 : outer114 * b = (factor0_0 : Model) * outer128 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer114, image_b, image_outer128]
  change outerMatrix114 * matrixB = hMatrixValue factor0_0 * outerMatrix128
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge115_0 : outer115 * a = (factor0_0 : Model) * outer102 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer115, image_a, image_outer102]
  change outerMatrix115 * matrixA = hMatrixValue factor0_0 * outerMatrix102
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge115_1 : outer115 * b = (factor0_0 : Model) * outer129 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer115, image_b, image_outer129]
  change outerMatrix115 * matrixB = hMatrixValue factor0_0 * outerMatrix129
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge116_0 : outer116 * a = (factor0_0 : Model) * outer130 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer116, image_a, image_outer130]
  change outerMatrix116 * matrixA = hMatrixValue factor0_0 * outerMatrix130
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge116_1 : outer116 * b = (factor0_0 : Model) * outer92 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer116, image_b, image_outer92]
  change outerMatrix116 * matrixB = hMatrixValue factor0_0 * outerMatrix92
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge117_0 : outer117 * a = (factor0_0 : Model) * outer103 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer117, image_a, image_outer103]
  change outerMatrix117 * matrixA = hMatrixValue factor0_0 * outerMatrix103
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge117_1 : outer117 * b = (factor0_0 : Model) * outer131 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer117, image_b, image_outer131]
  change outerMatrix117 * matrixB = hMatrixValue factor0_0 * outerMatrix131
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge118_0 : outer118 * a = (factor7_19 : Model) * outer118 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer118, image_a, image_outer118]
  change outerMatrix118 * matrixA = hMatrixValue factor7_19 * outerMatrix118
  rw [image_factor7_19]
  decide +kernel

public theorem outerEdge118_1 : outer118 * b = (factor0_0 : Model) * outer93 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer118, image_b, image_outer93]
  change outerMatrix118 * matrixB = hMatrixValue factor0_0 * outerMatrix93
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge119_0 : outer119 * a = (factor0_0 : Model) * outer132 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer119, image_a, image_outer132]
  change outerMatrix119 * matrixA = hMatrixValue factor0_0 * outerMatrix132
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge119_1 : outer119 * b = (factor0_0 : Model) * outer120 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer119, image_b, image_outer120]
  change outerMatrix119 * matrixB = hMatrixValue factor0_0 * outerMatrix120
  rw [image_factor0_0]
  decide +kernel


end Janko1.OrderCertificate
