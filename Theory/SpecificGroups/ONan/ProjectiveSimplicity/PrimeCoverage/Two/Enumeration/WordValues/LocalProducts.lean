module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Two.Enumeration.WordValues.DataChecks

/-!
# Certified products for the two conjugated local generators

Every displayed product is proved from a natural-number Boolean certificate
by `mul_sound`; `decide +kernel` checks the certificate. Witnesses come from
the original ATLAS matrices and the words documented in `Two/source/README.md`.
-/

@[expose] public section

namespace ONan.Simplicity.TwoCertificate.Enumeration.WordValues

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem c4inv_mul_a : decode c4inv * decode a = decode ua := by
  apply mul_sound c4inv a aT ua transpose_a
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem ua_mul_c4 : decode ua * decode c4 = decode u := by
  apply mul_sound ua c4 c4T u transpose_c4
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem d4inv_mul_h4 : decode d4inv * decode h4 = decode vh := by
  apply mul_sound d4inv h4 h4T vh transpose_h4
  apply allRows_sound
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem vh_mul_d4 : decode vh * decode d4 = decode v := by
  apply mul_sound vh d4 d4T v transpose_d4
  apply allRows_sound
  decide +kernel


end ONan.Simplicity.TwoCertificate.Enumeration.WordValues
