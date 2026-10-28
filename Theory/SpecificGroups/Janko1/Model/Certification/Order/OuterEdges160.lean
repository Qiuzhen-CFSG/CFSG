module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterReps
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Factors

/-!
# Transitions 160–199 for the 266-coset cover

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

public theorem outerEdge160_0 : outer160 * a = (factor0_0 : Model) * outer144 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer160, image_a, image_outer144]
  change outerMatrix160 * matrixA = hMatrixValue factor0_0 * outerMatrix144
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge160_1 : outer160 * b = (factor0_0 : Model) * outer178 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer160, image_b, image_outer178]
  change outerMatrix160 * matrixB = hMatrixValue factor0_0 * outerMatrix178
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge161_0 : outer161 * a = (factor0_0 : Model) * outer146 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer161, image_a, image_outer146]
  change outerMatrix161 * matrixA = hMatrixValue factor0_0 * outerMatrix146
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge161_1 : outer161 * b = (factor0_0 : Model) * outer179 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer161, image_b, image_outer179]
  change outerMatrix161 * matrixB = hMatrixValue factor0_0 * outerMatrix179
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge162_0 : outer162 * a = (factor0_0 : Model) * outer147 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer162, image_a, image_outer147]
  change outerMatrix162 * matrixA = hMatrixValue factor0_0 * outerMatrix147
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge162_1 : outer162 * b = (factor7_19 : Model) * outer161 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer162, image_b, image_outer161]
  change outerMatrix162 * matrixB = hMatrixValue factor7_19 * outerMatrix161
  rw [image_factor7_19]
  decide +kernel

public theorem outerEdge163_0 : outer163 * a = (factor0_0 : Model) * outer180 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer163, image_a, image_outer180]
  change outerMatrix163 * matrixA = hMatrixValue factor0_0 * outerMatrix180
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge163_1 : outer163 * b = (factor0_0 : Model) * outer132 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer163, image_b, image_outer132]
  change outerMatrix163 * matrixB = hMatrixValue factor0_0 * outerMatrix132
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge164_0 : outer164 * a = (factor0_0 : Model) * outer148 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer164, image_a, image_outer148]
  change outerMatrix164 * matrixA = hMatrixValue factor0_0 * outerMatrix148
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge164_1 : outer164 * b = (factor0_0 : Model) * outer181 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer164, image_b, image_outer181]
  change outerMatrix164 * matrixB = hMatrixValue factor0_0 * outerMatrix181
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge165_0 : outer165 * a = (factor0_0 : Model) * outer182 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer165, image_a, image_outer182]
  change outerMatrix165 * matrixA = hMatrixValue factor0_0 * outerMatrix182
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge165_1 : outer165 * b = (factor0_0 : Model) * outer133 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer165, image_b, image_outer133]
  change outerMatrix165 * matrixB = hMatrixValue factor0_0 * outerMatrix133
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge166_0 : outer166 * a = (factor0_0 : Model) * outer149 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer166, image_a, image_outer149]
  change outerMatrix166 * matrixA = hMatrixValue factor0_0 * outerMatrix149
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge166_1 : outer166 * b = (factor0_0 : Model) * outer183 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer166, image_b, image_outer183]
  change outerMatrix166 * matrixB = hMatrixValue factor0_0 * outerMatrix183
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge167_0 : outer167 * a = (factor0_0 : Model) * outer184 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer167, image_a, image_outer184]
  change outerMatrix167 * matrixA = hMatrixValue factor0_0 * outerMatrix184
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge167_1 : outer167 * b = (factor0_0 : Model) * outer134 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer167, image_b, image_outer134]
  change outerMatrix167 * matrixB = hMatrixValue factor0_0 * outerMatrix134
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge168_0 : outer168 * a = (factor0_0 : Model) * outer185 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer168, image_a, image_outer185]
  change outerMatrix168 * matrixA = hMatrixValue factor0_0 * outerMatrix185
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge168_1 : outer168 * b = (factor0_0 : Model) * outer186 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer168, image_b, image_outer186]
  change outerMatrix168 * matrixB = hMatrixValue factor0_0 * outerMatrix186
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge169_0 : outer169 * a = (factor0_0 : Model) * outer187 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer169, image_a, image_outer187]
  change outerMatrix169 * matrixA = hMatrixValue factor0_0 * outerMatrix187
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge169_1 : outer169 * b = (factor0_0 : Model) * outer188 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer169, image_b, image_outer188]
  change outerMatrix169 * matrixB = hMatrixValue factor0_0 * outerMatrix188
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge170_0 : outer170 * a = (factor0_0 : Model) * outer189 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer170, image_a, image_outer189]
  change outerMatrix170 * matrixA = hMatrixValue factor0_0 * outerMatrix189
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge170_1 : outer170 * b = (factor7_11 : Model) * outer184 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer170, image_b, image_outer184]
  change outerMatrix170 * matrixB = hMatrixValue factor7_11 * outerMatrix184
  rw [image_factor7_11]
  decide +kernel

public theorem outerEdge171_0 : outer171 * a = (factor0_0 : Model) * outer153 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer171, image_a, image_outer153]
  change outerMatrix171 * matrixA = hMatrixValue factor0_0 * outerMatrix153
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge171_1 : outer171 * b = (factor0_0 : Model) * outer190 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer171, image_b, image_outer190]
  change outerMatrix171 * matrixB = hMatrixValue factor0_0 * outerMatrix190
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge172_0 : outer172 * a = (factor0_0 : Model) * outer191 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer172, image_a, image_outer191]
  change outerMatrix172 * matrixA = hMatrixValue factor0_0 * outerMatrix191
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge172_1 : outer172 * b = (factor0_0 : Model) * outer192 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer172, image_b, image_outer192]
  change outerMatrix172 * matrixB = hMatrixValue factor0_0 * outerMatrix192
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge173_0 : outer173 * a = (factor0_0 : Model) * outer155 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer173, image_a, image_outer155]
  change outerMatrix173 * matrixA = hMatrixValue factor0_0 * outerMatrix155
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge173_1 : outer173 * b = (factor0_0 : Model) * outer193 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer173, image_b, image_outer193]
  change outerMatrix173 * matrixB = hMatrixValue factor0_0 * outerMatrix193
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge174_0 : outer174 * a = (factor0_0 : Model) * outer194 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer174, image_a, image_outer194]
  change outerMatrix174 * matrixA = hMatrixValue factor0_0 * outerMatrix194
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge174_1 : outer174 * b = (factor0_0 : Model) * outer195 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer174, image_b, image_outer195]
  change outerMatrix174 * matrixB = hMatrixValue factor0_0 * outerMatrix195
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge175_0 : outer175 * a = (factor0_0 : Model) * outer157 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer175, image_a, image_outer157]
  change outerMatrix175 * matrixA = hMatrixValue factor0_0 * outerMatrix157
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge175_1 : outer175 * b = (factor0_0 : Model) * outer196 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer175, image_b, image_outer196]
  change outerMatrix175 * matrixB = hMatrixValue factor0_0 * outerMatrix196
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge176_0 : outer176 * a = (factor0_0 : Model) * outer158 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer176, image_a, image_outer158]
  change outerMatrix176 * matrixA = hMatrixValue factor0_0 * outerMatrix158
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge176_1 : outer176 * b = (factor4_36 : Model) * outer175 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer176, image_b, image_outer175]
  change outerMatrix176 * matrixB = hMatrixValue factor4_36 * outerMatrix175
  rw [image_factor4_36]
  decide +kernel

public theorem outerEdge177_0 : outer177 * a = (factor0_0 : Model) * outer197 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer177, image_a, image_outer197]
  change outerMatrix177 * matrixA = hMatrixValue factor0_0 * outerMatrix197
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge177_1 : outer177 * b = (factor0_0 : Model) * outer198 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer177, image_b, image_outer198]
  change outerMatrix177 * matrixB = hMatrixValue factor0_0 * outerMatrix198
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge178_0 : outer178 * a = (factor0_0 : Model) * outer199 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer178, image_a, image_outer199]
  change outerMatrix178 * matrixA = hMatrixValue factor0_0 * outerMatrix199
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge178_1 : outer178 * b = (factor0_0 : Model) * outer200 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer178, image_b, image_outer200]
  change outerMatrix178 * matrixB = hMatrixValue factor0_0 * outerMatrix200
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge179_0 : outer179 * a = (factor0_0 : Model) * outer201 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer179, image_a, image_outer201]
  change outerMatrix179 * matrixA = hMatrixValue factor0_0 * outerMatrix201
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge179_1 : outer179 * b = (factor7_19 : Model) * outer162 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer179, image_b, image_outer162]
  change outerMatrix179 * matrixB = hMatrixValue factor7_19 * outerMatrix162
  rw [image_factor7_19]
  decide +kernel

public theorem outerEdge180_0 : outer180 * a = (factor0_0 : Model) * outer163 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer180, image_a, image_outer163]
  change outerMatrix180 * matrixA = hMatrixValue factor0_0 * outerMatrix163
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge180_1 : outer180 * b = (factor0_0 : Model) * outer202 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer180, image_b, image_outer202]
  change outerMatrix180 * matrixB = hMatrixValue factor0_0 * outerMatrix202
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge181_0 : outer181 * a = (factor0_0 : Model) * outer203 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer181, image_a, image_outer203]
  change outerMatrix181 * matrixA = hMatrixValue factor0_0 * outerMatrix203
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge181_1 : outer181 * b = (factor0_0 : Model) * outer204 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer181, image_b, image_outer204]
  change outerMatrix181 * matrixB = hMatrixValue factor0_0 * outerMatrix204
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge182_0 : outer182 * a = (factor0_0 : Model) * outer165 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer182, image_a, image_outer165]
  change outerMatrix182 * matrixA = hMatrixValue factor0_0 * outerMatrix165
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge182_1 : outer182 * b = (factor0_0 : Model) * outer205 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer182, image_b, image_outer205]
  change outerMatrix182 * matrixB = hMatrixValue factor0_0 * outerMatrix205
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge183_0 : outer183 * a = (factor0_0 : Model) * outer206 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer183, image_a, image_outer206]
  change outerMatrix183 * matrixA = hMatrixValue factor0_0 * outerMatrix206
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge183_1 : outer183 * b = (factor0_0 : Model) * outer207 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer183, image_b, image_outer207]
  change outerMatrix183 * matrixB = hMatrixValue factor0_0 * outerMatrix207
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge184_0 : outer184 * a = (factor0_0 : Model) * outer167 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer184, image_a, image_outer167]
  change outerMatrix184 * matrixA = hMatrixValue factor0_0 * outerMatrix167
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge184_1 : outer184 * b = (factor1_49 : Model) * outer152 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer184, image_b, image_outer152]
  change outerMatrix184 * matrixB = hMatrixValue factor1_49 * outerMatrix152
  rw [image_factor1_49]
  decide +kernel

public theorem outerEdge185_0 : outer185 * a = (factor0_0 : Model) * outer168 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer185, image_a, image_outer168]
  change outerMatrix185 * matrixA = hMatrixValue factor0_0 * outerMatrix168
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge185_1 : outer185 * b = (factor0_0 : Model) * outer208 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer185, image_b, image_outer208]
  change outerMatrix185 * matrixB = hMatrixValue factor0_0 * outerMatrix208
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge186_0 : outer186 * a = (factor0_0 : Model) * outer209 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer186, image_a, image_outer209]
  change outerMatrix186 * matrixA = hMatrixValue factor0_0 * outerMatrix209
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge186_1 : outer186 * b = (factor0_0 : Model) * outer150 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer186, image_b, image_outer150]
  change outerMatrix186 * matrixB = hMatrixValue factor0_0 * outerMatrix150
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge187_0 : outer187 * a = (factor0_0 : Model) * outer169 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer187, image_a, image_outer169]
  change outerMatrix187 * matrixA = hMatrixValue factor0_0 * outerMatrix169
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge187_1 : outer187 * b = (factor0_0 : Model) * outer210 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer187, image_b, image_outer210]
  change outerMatrix187 * matrixB = hMatrixValue factor0_0 * outerMatrix210
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge188_0 : outer188 * a = (factor0_0 : Model) * outer211 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer188, image_a, image_outer211]
  change outerMatrix188 * matrixA = hMatrixValue factor0_0 * outerMatrix211
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge188_1 : outer188 * b = (factor0_0 : Model) * outer151 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer188, image_b, image_outer151]
  change outerMatrix188 * matrixB = hMatrixValue factor0_0 * outerMatrix151
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge189_0 : outer189 * a = (factor0_0 : Model) * outer170 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer189, image_a, image_outer170]
  change outerMatrix189 * matrixA = hMatrixValue factor0_0 * outerMatrix170
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge189_1 : outer189 * b = (factor0_0 : Model) * outer212 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer189, image_b, image_outer212]
  change outerMatrix189 * matrixB = hMatrixValue factor0_0 * outerMatrix212
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge190_0 : outer190 * a = (factor0_0 : Model) * outer213 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer190, image_a, image_outer213]
  change outerMatrix190 * matrixA = hMatrixValue factor0_0 * outerMatrix213
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge190_1 : outer190 * b = (factor0_0 : Model) * outer191 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer190, image_b, image_outer191]
  change outerMatrix190 * matrixB = hMatrixValue factor0_0 * outerMatrix191
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge191_0 : outer191 * a = (factor0_0 : Model) * outer172 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer191, image_a, image_outer172]
  change outerMatrix191 * matrixA = hMatrixValue factor0_0 * outerMatrix172
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge191_1 : outer191 * b = (factor0_0 : Model) * outer171 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer191, image_b, image_outer171]
  change outerMatrix191 * matrixB = hMatrixValue factor0_0 * outerMatrix171
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge192_0 : outer192 * a = (factor0_0 : Model) * outer214 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer192, image_a, image_outer214]
  change outerMatrix192 * matrixA = hMatrixValue factor0_0 * outerMatrix214
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge192_1 : outer192 * b = (factor0_0 : Model) * outer154 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer192, image_b, image_outer154]
  change outerMatrix192 * matrixB = hMatrixValue factor0_0 * outerMatrix154
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge193_0 : outer193 * a = (factor7_55 : Model) * outer193 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer193, image_a, image_outer193]
  change outerMatrix193 * matrixA = hMatrixValue factor7_55 * outerMatrix193
  rw [image_factor7_55]
  decide +kernel

public theorem outerEdge193_1 : outer193 * b = (factor0_0 : Model) * outer215 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer193, image_b, image_outer215]
  change outerMatrix193 * matrixB = hMatrixValue factor0_0 * outerMatrix215
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge194_0 : outer194 * a = (factor0_0 : Model) * outer174 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer194, image_a, image_outer174]
  change outerMatrix194 * matrixA = hMatrixValue factor0_0 * outerMatrix174
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge194_1 : outer194 * b = (factor0_0 : Model) * outer216 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer194, image_b, image_outer216]
  change outerMatrix194 * matrixB = hMatrixValue factor0_0 * outerMatrix216
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge195_0 : outer195 * a = (factor0_0 : Model) * outer217 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer195, image_a, image_outer217]
  change outerMatrix195 * matrixA = hMatrixValue factor0_0 * outerMatrix217
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge195_1 : outer195 * b = (factor0_0 : Model) * outer156 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer195, image_b, image_outer156]
  change outerMatrix195 * matrixB = hMatrixValue factor0_0 * outerMatrix156
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge196_0 : outer196 * a = (factor0_0 : Model) * outer218 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer196, image_a, image_outer218]
  change outerMatrix196 * matrixA = hMatrixValue factor0_0 * outerMatrix218
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge196_1 : outer196 * b = (factor4_36 : Model) * outer176 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer196, image_b, image_outer176]
  change outerMatrix196 * matrixB = hMatrixValue factor4_36 * outerMatrix176
  rw [image_factor4_36]
  decide +kernel

public theorem outerEdge197_0 : outer197 * a = (factor0_0 : Model) * outer177 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer197, image_a, image_outer177]
  change outerMatrix197 * matrixA = hMatrixValue factor0_0 * outerMatrix177
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge197_1 : outer197 * b = (factor0_0 : Model) * outer219 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer197, image_b, image_outer219]
  change outerMatrix197 * matrixB = hMatrixValue factor0_0 * outerMatrix219
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge198_0 : outer198 * a = (factor0_0 : Model) * outer220 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer198, image_a, image_outer220]
  change outerMatrix198 * matrixA = hMatrixValue factor0_0 * outerMatrix220
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge198_1 : outer198 * b = (factor0_0 : Model) * outer159 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer198, image_b, image_outer159]
  change outerMatrix198 * matrixB = hMatrixValue factor0_0 * outerMatrix159
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge199_0 : outer199 * a = (factor0_0 : Model) * outer178 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer199, image_a, image_outer178]
  change outerMatrix199 * matrixA = hMatrixValue factor0_0 * outerMatrix178
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge199_1 : outer199 * b = (factor0_0 : Model) * outer221 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer199, image_b, image_outer221]
  change outerMatrix199 * matrixB = hMatrixValue factor0_0 * outerMatrix221
  rw [image_factor0_0]
  decide +kernel


end Janko1.OrderCertificate
