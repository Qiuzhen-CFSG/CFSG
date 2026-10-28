module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.WordValues.DataChecks

/-!
# Certified products for the last three basis endpoints

Every displayed product is proved from a natural-number Boolean certificate
by `mul_sound`; `decide +kernel` checks the certificate. Witnesses come from
the original ATLAS matrices and the words documented in `Two/source/README.md`.
-/

@[expose] public section

namespace ONan.Simplicity.TwoCertificate.Enumeration.WordValues

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w0_mul_w4 : decode w0 * decode w4 = decode w22 := by
  apply mul_sound w0 w4 w4T w22 transpose_w4
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w22_mul_w7 : decode w22 * decode w7 = decode w23 := by
  apply mul_sound w22 w7 w7T w23 transpose_w7
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w23_mul_u : decode w23 * decode u = decode w24 := by
  apply mul_sound w23 u uT w24 transpose_u
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w1_mul_w4 : decode w1 * decode w4 = decode w25 := by
  apply mul_sound w1 w4 w4T w25 transpose_w4
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w25_mul_w5 : decode w25 * decode w5 = decode w26 := by
  apply mul_sound w25 w5 w5T w26 transpose_w5
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w26_mul_w6 : decode w26 * decode w6 = decode w27 := by
  apply mul_sound w26 w6 w6T w27 transpose_w6
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w4_mul_v : decode w4 * decode v = decode w28 := by
  apply mul_sound w4 v vT w28 transpose_v
  apply allRows_sound
  decide +kernel


end ONan.Simplicity.TwoCertificate.Enumeration.WordValues
