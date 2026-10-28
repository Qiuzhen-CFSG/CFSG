module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterReps
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Factors

/-!
# Transitions 120–159 for the 266-coset cover

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

public theorem outerEdge120_0 : outer120 * a = (factor0_0 : Model) * outer105 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer120, image_a, image_outer105]
  change outerMatrix120 * matrixA = hMatrixValue factor0_0 * outerMatrix105
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge120_1 : outer120 * b = (factor0_0 : Model) * outer104 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer120, image_b, image_outer104]
  change outerMatrix120 * matrixB = hMatrixValue factor0_0 * outerMatrix104
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge121_0 : outer121 * a = (factor0_0 : Model) * outer133 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer121, image_a, image_outer133]
  change outerMatrix121 * matrixA = hMatrixValue factor0_0 * outerMatrix133
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge121_1 : outer121 * b = (factor0_0 : Model) * outer95 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer121, image_b, image_outer95]
  change outerMatrix121 * matrixB = hMatrixValue factor0_0 * outerMatrix95
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge122_0 : outer122 * a = (factor0_0 : Model) * outer134 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer122, image_a, image_outer134]
  change outerMatrix122 * matrixA = hMatrixValue factor0_0 * outerMatrix134
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge122_1 : outer122 * b = (factor0_0 : Model) * outer135 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer122, image_b, image_outer135]
  change outerMatrix122 * matrixB = hMatrixValue factor0_0 * outerMatrix135
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge123_0 : outer123 * a = (factor3_0 : Model) * outer135 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer123, image_a, image_outer135]
  change outerMatrix123 * matrixA = hMatrixValue factor3_0 * outerMatrix135
  rw [image_factor3_0]
  decide +kernel

public theorem outerEdge123_1 : outer123 * b = (factor0_0 : Model) * outer136 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer123, image_b, image_outer136]
  change outerMatrix123 * matrixB = hMatrixValue factor0_0 * outerMatrix136
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge124_0 : outer124 * a = (factor0_0 : Model) * outer108 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer124, image_a, image_outer108]
  change outerMatrix124 * matrixA = hMatrixValue factor0_0 * outerMatrix108
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge124_1 : outer124 * b = (factor0_0 : Model) * outer137 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer124, image_b, image_outer137]
  change outerMatrix124 * matrixB = hMatrixValue factor0_0 * outerMatrix137
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge125_0 : outer125 * a = (factor0_0 : Model) * outer110 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer125, image_a, image_outer110]
  change outerMatrix125 * matrixA = hMatrixValue factor0_0 * outerMatrix110
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge125_1 : outer125 * b = (factor0_0 : Model) * outer138 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer125, image_b, image_outer138]
  change outerMatrix125 * matrixB = hMatrixValue factor0_0 * outerMatrix138
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge126_0 : outer126 * a = (factor0_0 : Model) * outer111 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer126, image_a, image_outer111]
  change outerMatrix126 * matrixA = hMatrixValue factor0_0 * outerMatrix111
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge126_1 : outer126 * b = (factor0_0 : Model) * outer139 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer126, image_b, image_outer139]
  change outerMatrix126 * matrixB = hMatrixValue factor0_0 * outerMatrix139
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge127_0 : outer127 * a = (factor0_0 : Model) * outer113 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer127, image_a, image_outer113]
  change outerMatrix127 * matrixA = hMatrixValue factor0_0 * outerMatrix113
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge127_1 : outer127 * b = (factor0_0 : Model) * outer140 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer127, image_b, image_outer140]
  change outerMatrix127 * matrixB = hMatrixValue factor0_0 * outerMatrix140
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge128_0 : outer128 * a = (factor0_0 : Model) * outer141 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer128, image_a, image_outer141]
  change outerMatrix128 * matrixA = hMatrixValue factor0_0 * outerMatrix141
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge128_1 : outer128 * b = (factor0_0 : Model) * outer101 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer128, image_b, image_outer101]
  change outerMatrix128 * matrixB = hMatrixValue factor0_0 * outerMatrix101
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge129_0 : outer129 * a = (factor0_0 : Model) * outer142 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer129, image_a, image_outer142]
  change outerMatrix129 * matrixA = hMatrixValue factor0_0 * outerMatrix142
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge129_1 : outer129 * b = (factor0_0 : Model) * outer143 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer129, image_b, image_outer143]
  change outerMatrix129 * matrixB = hMatrixValue factor0_0 * outerMatrix143
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge130_0 : outer130 * a = (factor0_0 : Model) * outer116 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer130, image_a, image_outer116]
  change outerMatrix130 * matrixA = hMatrixValue factor0_0 * outerMatrix116
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge130_1 : outer130 * b = (factor0_0 : Model) * outer144 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer130, image_b, image_outer144]
  change outerMatrix130 * matrixB = hMatrixValue factor0_0 * outerMatrix144
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge131_0 : outer131 * a = (factor0_0 : Model) * outer145 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer131, image_a, image_outer145]
  change outerMatrix131 * matrixA = hMatrixValue factor0_0 * outerMatrix145
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge131_1 : outer131 * b = (factor0_0 : Model) * outer146 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer131, image_b, image_outer146]
  change outerMatrix131 * matrixB = hMatrixValue factor0_0 * outerMatrix146
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge132_0 : outer132 * a = (factor0_0 : Model) * outer119 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer132, image_a, image_outer119]
  change outerMatrix132 * matrixA = hMatrixValue factor0_0 * outerMatrix119
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge132_1 : outer132 * b = (factor0_0 : Model) * outer147 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer132, image_b, image_outer147]
  change outerMatrix132 * matrixB = hMatrixValue factor0_0 * outerMatrix147
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge133_0 : outer133 * a = (factor0_0 : Model) * outer121 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer133, image_a, image_outer121]
  change outerMatrix133 * matrixA = hMatrixValue factor0_0 * outerMatrix121
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge133_1 : outer133 * b = (factor0_0 : Model) * outer148 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer133, image_b, image_outer148]
  change outerMatrix133 * matrixB = hMatrixValue factor0_0 * outerMatrix148
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge134_0 : outer134 * a = (factor0_0 : Model) * outer122 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer134, image_a, image_outer122]
  change outerMatrix134 * matrixA = hMatrixValue factor0_0 * outerMatrix122
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge134_1 : outer134 * b = (factor0_0 : Model) * outer149 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer134, image_b, image_outer149]
  change outerMatrix134 * matrixB = hMatrixValue factor0_0 * outerMatrix149
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge135_0 : outer135 * a = (factor8_0 : Model) * outer123 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer135, image_a, image_outer123]
  change outerMatrix135 * matrixA = hMatrixValue factor8_0 * outerMatrix123
  rw [image_factor8_0]
  decide +kernel

public theorem outerEdge135_1 : outer135 * b = (factor0_0 : Model) * outer106 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer135, image_b, image_outer106]
  change outerMatrix135 * matrixB = hMatrixValue factor0_0 * outerMatrix106
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge136_0 : outer136 * a = (factor0_0 : Model) * outer150 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer136, image_a, image_outer150]
  change outerMatrix136 * matrixA = hMatrixValue factor0_0 * outerMatrix150
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge136_1 : outer136 * b = (factor0_0 : Model) * outer107 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer136, image_b, image_outer107]
  change outerMatrix136 * matrixB = hMatrixValue factor0_0 * outerMatrix107
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge137_0 : outer137 * a = (factor0_0 : Model) * outer151 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer137, image_a, image_outer151]
  change outerMatrix137 * matrixA = hMatrixValue factor0_0 * outerMatrix151
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge137_1 : outer137 * b = (factor5_43 : Model) * outer109 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer137, image_b, image_outer109]
  change outerMatrix137 * matrixB = hMatrixValue factor5_43 * outerMatrix109
  rw [image_factor5_43]
  decide +kernel

public theorem outerEdge138_0 : outer138 * a = (factor0_0 : Model) * outer152 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer138, image_a, image_outer152]
  change outerMatrix138 * matrixA = hMatrixValue factor0_0 * outerMatrix152
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge138_1 : outer138 * b = (factor0_0 : Model) * outer153 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer138, image_b, image_outer153]
  change outerMatrix138 * matrixB = hMatrixValue factor0_0 * outerMatrix153
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge139_0 : outer139 * a = (factor0_0 : Model) * outer154 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer139, image_a, image_outer154]
  change outerMatrix139 * matrixA = hMatrixValue factor0_0 * outerMatrix154
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge139_1 : outer139 * b = (factor0_0 : Model) * outer155 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer139, image_b, image_outer155]
  change outerMatrix139 * matrixB = hMatrixValue factor0_0 * outerMatrix155
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge140_0 : outer140 * a = (factor0_0 : Model) * outer156 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer140, image_a, image_outer156]
  change outerMatrix140 * matrixA = hMatrixValue factor0_0 * outerMatrix156
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge140_1 : outer140 * b = (factor0_0 : Model) * outer157 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer140, image_b, image_outer157]
  change outerMatrix140 * matrixB = hMatrixValue factor0_0 * outerMatrix157
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge141_0 : outer141 * a = (factor0_0 : Model) * outer128 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer141, image_a, image_outer128]
  change outerMatrix141 * matrixA = hMatrixValue factor0_0 * outerMatrix128
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge141_1 : outer141 * b = (factor0_0 : Model) * outer158 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer141, image_b, image_outer158]
  change outerMatrix141 * matrixB = hMatrixValue factor0_0 * outerMatrix158
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge142_0 : outer142 * a = (factor0_0 : Model) * outer129 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer142, image_a, image_outer129]
  change outerMatrix142 * matrixA = hMatrixValue factor0_0 * outerMatrix129
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge142_1 : outer142 * b = (factor0_0 : Model) * outer141 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer142, image_b, image_outer141]
  change outerMatrix142 * matrixB = hMatrixValue factor0_0 * outerMatrix141
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge143_0 : outer143 * a = (factor0_0 : Model) * outer159 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer143, image_a, image_outer159]
  change outerMatrix143 * matrixA = hMatrixValue factor0_0 * outerMatrix159
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge143_1 : outer143 * b = (factor0_0 : Model) * outer115 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer143, image_b, image_outer115]
  change outerMatrix143 * matrixB = hMatrixValue factor0_0 * outerMatrix115
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge144_0 : outer144 * a = (factor0_0 : Model) * outer160 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer144, image_a, image_outer160]
  change outerMatrix144 * matrixA = hMatrixValue factor0_0 * outerMatrix160
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge144_1 : outer144 * b = (factor0_0 : Model) * outer145 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer144, image_b, image_outer145]
  change outerMatrix144 * matrixB = hMatrixValue factor0_0 * outerMatrix145
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge145_0 : outer145 * a = (factor0_0 : Model) * outer131 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer145, image_a, image_outer131]
  change outerMatrix145 * matrixA = hMatrixValue factor0_0 * outerMatrix131
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge145_1 : outer145 * b = (factor0_0 : Model) * outer130 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer145, image_b, image_outer130]
  change outerMatrix145 * matrixB = hMatrixValue factor0_0 * outerMatrix130
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge146_0 : outer146 * a = (factor0_0 : Model) * outer161 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer146, image_a, image_outer161]
  change outerMatrix146 * matrixA = hMatrixValue factor0_0 * outerMatrix161
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge146_1 : outer146 * b = (factor0_0 : Model) * outer117 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer146, image_b, image_outer117]
  change outerMatrix146 * matrixB = hMatrixValue factor0_0 * outerMatrix117
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge147_0 : outer147 * a = (factor0_0 : Model) * outer162 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer147, image_a, image_outer162]
  change outerMatrix147 * matrixA = hMatrixValue factor0_0 * outerMatrix162
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge147_1 : outer147 * b = (factor0_0 : Model) * outer163 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer147, image_b, image_outer163]
  change outerMatrix147 * matrixB = hMatrixValue factor0_0 * outerMatrix163
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge148_0 : outer148 * a = (factor0_0 : Model) * outer164 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer148, image_a, image_outer164]
  change outerMatrix148 * matrixA = hMatrixValue factor0_0 * outerMatrix164
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge148_1 : outer148 * b = (factor0_0 : Model) * outer165 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer148, image_b, image_outer165]
  change outerMatrix148 * matrixB = hMatrixValue factor0_0 * outerMatrix165
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge149_0 : outer149 * a = (factor0_0 : Model) * outer166 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer149, image_a, image_outer166]
  change outerMatrix149 * matrixA = hMatrixValue factor0_0 * outerMatrix166
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge149_1 : outer149 * b = (factor0_0 : Model) * outer167 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer149, image_b, image_outer167]
  change outerMatrix149 * matrixB = hMatrixValue factor0_0 * outerMatrix167
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge150_0 : outer150 * a = (factor0_0 : Model) * outer136 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer150, image_a, image_outer136]
  change outerMatrix150 * matrixA = hMatrixValue factor0_0 * outerMatrix136
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge150_1 : outer150 * b = (factor0_0 : Model) * outer168 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer150, image_b, image_outer168]
  change outerMatrix150 * matrixB = hMatrixValue factor0_0 * outerMatrix168
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge151_0 : outer151 * a = (factor0_0 : Model) * outer137 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer151, image_a, image_outer137]
  change outerMatrix151 * matrixA = hMatrixValue factor0_0 * outerMatrix137
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge151_1 : outer151 * b = (factor0_0 : Model) * outer169 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer151, image_b, image_outer169]
  change outerMatrix151 * matrixB = hMatrixValue factor0_0 * outerMatrix169
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge152_0 : outer152 * a = (factor0_0 : Model) * outer138 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer152, image_a, image_outer138]
  change outerMatrix152 * matrixA = hMatrixValue factor0_0 * outerMatrix138
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge152_1 : outer152 * b = (factor0_0 : Model) * outer170 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer152, image_b, image_outer170]
  change outerMatrix152 * matrixB = hMatrixValue factor0_0 * outerMatrix170
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge153_0 : outer153 * a = (factor0_0 : Model) * outer171 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer153, image_a, image_outer171]
  change outerMatrix153 * matrixA = hMatrixValue factor0_0 * outerMatrix171
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge153_1 : outer153 * b = (factor0_0 : Model) * outer125 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer153, image_b, image_outer125]
  change outerMatrix153 * matrixB = hMatrixValue factor0_0 * outerMatrix125
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge154_0 : outer154 * a = (factor0_0 : Model) * outer139 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer154, image_a, image_outer139]
  change outerMatrix154 * matrixA = hMatrixValue factor0_0 * outerMatrix139
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge154_1 : outer154 * b = (factor0_0 : Model) * outer172 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer154, image_b, image_outer172]
  change outerMatrix154 * matrixB = hMatrixValue factor0_0 * outerMatrix172
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge155_0 : outer155 * a = (factor0_0 : Model) * outer173 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer155, image_a, image_outer173]
  change outerMatrix155 * matrixA = hMatrixValue factor0_0 * outerMatrix173
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge155_1 : outer155 * b = (factor0_0 : Model) * outer126 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer155, image_b, image_outer126]
  change outerMatrix155 * matrixB = hMatrixValue factor0_0 * outerMatrix126
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge156_0 : outer156 * a = (factor0_0 : Model) * outer140 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer156, image_a, image_outer140]
  change outerMatrix156 * matrixA = hMatrixValue factor0_0 * outerMatrix140
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge156_1 : outer156 * b = (factor0_0 : Model) * outer174 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer156, image_b, image_outer174]
  change outerMatrix156 * matrixB = hMatrixValue factor0_0 * outerMatrix174
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge157_0 : outer157 * a = (factor0_0 : Model) * outer175 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer157, image_a, image_outer175]
  change outerMatrix157 * matrixA = hMatrixValue factor0_0 * outerMatrix175
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge157_1 : outer157 * b = (factor0_0 : Model) * outer127 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer157, image_b, image_outer127]
  change outerMatrix157 * matrixB = hMatrixValue factor0_0 * outerMatrix127
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge158_0 : outer158 * a = (factor0_0 : Model) * outer176 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer158, image_a, image_outer176]
  change outerMatrix158 * matrixA = hMatrixValue factor0_0 * outerMatrix176
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge158_1 : outer158 * b = (factor0_0 : Model) * outer142 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer158, image_b, image_outer142]
  change outerMatrix158 * matrixB = hMatrixValue factor0_0 * outerMatrix142
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge159_0 : outer159 * a = (factor0_0 : Model) * outer143 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer159, image_a, image_outer143]
  change outerMatrix159 * matrixA = hMatrixValue factor0_0 * outerMatrix143
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge159_1 : outer159 * b = (factor0_0 : Model) * outer177 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer159, image_b, image_outer177]
  change outerMatrix159 * matrixB = hMatrixValue factor0_0 * outerMatrix177
  rw [image_factor0_0]
  decide +kernel


end Janko1.OrderCertificate
