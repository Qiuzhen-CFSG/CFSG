module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.WordValues.DataChecks

/-!
# Certified products for the first three noninitial basis endpoints

Every displayed product is proved from a natural-number Boolean certificate
by `mul_sound`; `decide +kernel` checks the certificate. Witnesses come from
the original ATLAS matrices and the words documented in `Two/source/README.md`.
-/

@[expose] public section

namespace ONan.Simplicity.TwoCertificate.Enumeration.WordValues

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w3_mul_w4 : decode w3 * decode w4 = decode w7 := by
  apply mul_sound w3 w4 w4T w7 transpose_w4
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w2_mul_w5 : decode w2 * decode w5 = decode w8 := by
  apply mul_sound w2 w5 w5T w8 transpose_w5
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w8_mul_u : decode w8 * decode u = decode w9 := by
  apply mul_sound w8 u uT w9 transpose_u
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w1_mul_w2 : decode w1 * decode w2 = decode w10 := by
  apply mul_sound w1 w2 w2T w10 transpose_w2
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w10_mul_w6 : decode w10 * decode w6 = decode w11 := by
  apply mul_sound w10 w6 w6T w11 transpose_w6
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w2_mul_w7 : decode w2 * decode w7 = decode w12 := by
  apply mul_sound w2 w7 w7T w12 transpose_w7
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w12_mul_w0 : decode w12 * decode w0 = decode w13 := by
  apply mul_sound w12 w0 w0T w13 transpose_w0
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem w13_mul_u : decode w13 * decode u = decode w14 := by
  apply mul_sound w13 u uT w14 transpose_u
  apply allRows_sound
  decide +kernel


end ONan.Simplicity.TwoCertificate.Enumeration.WordValues
