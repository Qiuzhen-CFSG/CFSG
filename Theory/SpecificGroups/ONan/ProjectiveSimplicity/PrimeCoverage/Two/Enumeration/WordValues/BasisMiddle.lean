module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.WordValues.DataChecks

/-!
# Certified products for the middle two basis endpoints

Every displayed product is proved from a natural-number Boolean certificate
by `mul_sound`; `decide +kernel` checks the certificate. Witnesses come from
the original ATLAS matrices and the words documented in `Two/source/README.md`.
-/

@[expose] public section

namespace ONan.Simplicity.TwoCertificate.Enumeration.WordValues

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem v_mul_w2 : decode v * decode w2 = decode w15 := by
  apply mul_sound v w2 w2T w15 transpose_w2
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w15_mul_w4 : decode w15 * decode w4 = decode w16 := by
  apply mul_sound w15 w4 w4T w16 transpose_w4
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w16_mul_w0 : decode w16 * decode w0 = decode w17 := by
  apply mul_sound w16 w0 w0T w17 transpose_w0
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w17_mul_v : decode w17 * decode v = decode w18 := by
  apply mul_sound w17 v vT w18 transpose_v
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w18_mul_w0 : decode w18 * decode w0 = decode w19 := by
  apply mul_sound w18 w0 w0T w19 transpose_w0
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w1_mul_w3 : decode w1 * decode w3 = decode w20 := by
  apply mul_sound w1 w3 w3T w20 transpose_w3
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w20_mul_w0 : decode w20 * decode w0 = decode w21 := by
  apply mul_sound w20 w0 w0T w21 transpose_w0
  apply allRows_sound
  decide +kernel


end ONan.Simplicity.TwoCertificate.Enumeration.WordValues
