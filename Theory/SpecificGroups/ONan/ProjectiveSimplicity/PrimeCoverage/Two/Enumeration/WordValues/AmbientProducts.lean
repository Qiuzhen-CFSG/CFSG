module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.WordValues.DataChecks

/-!
# Certified products for the ambient word powers and their inverses

Every displayed product is proved from a natural-number Boolean certificate
by `mul_sound`; `decide +kernel` checks the certificate. Witnesses come from
the original ATLAS matrices and the words documented in `Two/source/README.md`.
-/

@[expose] public section

namespace ONan.Simplicity.TwoCertificate.Enumeration.WordValues

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem a_mul_b : decode a * decode b = decode c := by
  apply mul_sound a b bT c transpose_b
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem c_mul_b : decode c * decode b = decode d := by
  apply mul_sound c b bT d transpose_b
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem c_mul_d : decode c * decode d = decode e := by
  apply mul_sound c d dT e transpose_d
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem c_mul_e : decode c * decode e = decode f := by
  apply mul_sound c e eT f transpose_e
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem f_mul_e : decode f * decode e = decode fe := by
  apply mul_sound f e eT fe transpose_e
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem c_mul_fe : decode c * decode fe = decode h := by
  apply mul_sound c fe feT h transpose_fe
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem c_mul_c : decode c * decode c = decode c2 := by
  apply mul_sound c c cT c2 transpose_c
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem c2_mul_c2 : decode c2 * decode c2 = decode c4 := by
  apply mul_sound c2 c2 c2T c4 transpose_c2
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem d_mul_d : decode d * decode d = decode d2 := by
  apply mul_sound d d dT d2 transpose_d
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem d2_mul_d2 : decode d2 * decode d2 = decode d4 := by
  apply mul_sound d2 d2 d2T d4 transpose_d2
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem h_mul_h : decode h * decode h = decode h2 := by
  apply mul_sound h h hT h2 transpose_h
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem h2_mul_h2 : decode h2 * decode h2 = decode h4 := by
  apply mul_sound h2 h2 h2T h4 transpose_h2
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem c4inv_mul_c4 : decode c4inv * decode c4 = decode one := by
  apply mul_sound c4inv c4 c4T one transpose_c4
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem d4inv_mul_d4 : decode d4inv * decode d4 = decode one := by
  apply mul_sound d4inv d4 d4T one transpose_d4
  apply allRows_sound
  decide +kernel


end ONan.Simplicity.TwoCertificate.Enumeration.WordValues
