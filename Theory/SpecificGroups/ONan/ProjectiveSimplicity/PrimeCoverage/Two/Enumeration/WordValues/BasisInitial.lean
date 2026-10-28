module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.WordValues.DataChecks

/-!
# Certified products for the common short subwords

Every displayed product is proved from a natural-number Boolean certificate
by `mul_sound`; `decide +kernel` checks the certificate. Witnesses come from
the original ATLAS matrices and the words documented in `Two/source/README.md`.
-/

@[expose] public section

namespace ONan.Simplicity.TwoCertificate.Enumeration.WordValues

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem u_mul_v : decode u * decode v = decode w0 := by
  apply mul_sound u v vT w0 transpose_v
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w0_mul_w0 : decode w0 * decode w0 = decode w1 := by
  apply mul_sound w0 w0 w0T w1 transpose_w0
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem v_mul_w1 : decode v * decode w1 = decode w2 := by
  apply mul_sound v w1 w1T w2 transpose_w1
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w0_mul_w2 : decode w0 * decode w2 = decode w3 := by
  apply mul_sound w0 w2 w2T w3 transpose_w2
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem v_mul_w3 : decode v * decode w3 = decode w4 := by
  apply mul_sound v w3 w3T w4 transpose_w3
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w2_mul_w0 : decode w2 * decode w0 = decode w5 := by
  apply mul_sound w2 w0 w0T w5 transpose_w0
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem v_mul_u : decode v * decode u = decode w6 := by
  apply mul_sound v u uT w6 transpose_u
  apply allRows_sound
  decide +kernel


end ONan.Simplicity.TwoCertificate.Enumeration.WordValues
