module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.Data
public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.Words
public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport24

/-!
# Lyons plane transport through wordC, step 1

Kernel-checked elementary transports through the literal word `ABABABBAB`.
The accumulated identity records power number 1 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c1_valid : valid c0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c1_check : check atlasBRows c0 c1 = true := by
  decide +kernel

private theorem c1_step :
    matrixRepresentation generatorB * decode c0 = decode c1 :=
  sound atlasBRows c0 c1 c1_valid c1_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c2_valid : valid c1 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c2_check : check atlasARows c1 c2 = true := by
  decide +kernel

private theorem c2_step :
    matrixRepresentation generatorA * decode c1 = decode c2 :=
  sound atlasARows c1 c2 c2_valid c2_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c3_valid : valid c2 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c3_check : check atlasBRows c2 c3 = true := by
  decide +kernel

private theorem c3_step :
    matrixRepresentation generatorB * decode c2 = decode c3 :=
  sound atlasBRows c2 c3 c3_valid c3_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c4_valid : valid c3 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c4_check : check atlasBRows c3 c4 = true := by
  decide +kernel

private theorem c4_step :
    matrixRepresentation generatorB * decode c3 = decode c4 :=
  sound atlasBRows c3 c4 c4_valid c4_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c5_valid : valid c4 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c5_check : check atlasARows c4 c5 = true := by
  decide +kernel

private theorem c5_step :
    matrixRepresentation generatorA * decode c4 = decode c5 :=
  sound atlasARows c4 c5 c5_valid c5_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c6_valid : valid c5 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c6_check : check atlasBRows c5 c6 = true := by
  decide +kernel

private theorem c6_step :
    matrixRepresentation generatorB * decode c5 = decode c6 :=
  sound atlasBRows c5 c6 c6_valid c6_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c7_valid : valid c6 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c7_check : check atlasARows c6 c7 = true := by
  decide +kernel

private theorem c7_step :
    matrixRepresentation generatorA * decode c6 = decode c7 :=
  sound atlasARows c6 c7 c7_valid c7_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c8_valid : valid c7 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c8_check : check atlasBRows c7 c8 = true := by
  decide +kernel

private theorem c8_step :
    matrixRepresentation generatorB * decode c7 = decode c8 :=
  sound atlasBRows c7 c8 c8_valid c8_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c9_valid : valid c8 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem c9_check : check atlasARows c8 c9 = true := by
  decide +kernel

private theorem c9_step :
    matrixRepresentation generatorA * decode c8 = decode c9 :=
  sound atlasARows c8 c9 c9_valid c9_check

private theorem c_word0 :
    matrixRepresentation wordC * decode c0 = decode c9 := by
  simp only [wordC, wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [c1_step, c2_step, c3_step, c4_step, c5_step, c6_step, c7_step, c8_step, c9_step]

public theorem c_power1 :
    matrixRepresentation (wordC ^ 1) * decode c0 = decode c9 := by
  simpa only [pow_one] using c_word0

end Lyons.OrderCertificate.PlaneTransport
