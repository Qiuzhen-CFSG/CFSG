module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlaneInvariance.BTransport14

/-!
# Lyons plane transport through wordB, step 16

Kernel-checked elementary transports through the literal word `ABABABB`.
The accumulated identity records power number 16 acting on the starting plane.
Candidate generation and source attribution: `Atlas111SeparationSource/GenerateInvariance.py`.
-/

namespace Lyons.OrderCertificate.PlaneTransport

set_option Elab.async false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b106_valid : valid b105 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b106_check : check atlasBRows b105 b106 = true := by
  decide +kernel

private theorem b106_step :
    matrixRepresentation generatorB * decode b105 = decode b106 :=
  sound atlasBRows b105 b106 b106_valid b106_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b107_valid : valid b106 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b107_check : check atlasBRows b106 b107 = true := by
  decide +kernel

private theorem b107_step :
    matrixRepresentation generatorB * decode b106 = decode b107 :=
  sound atlasBRows b106 b107 b107_valid b107_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b108_valid : valid b107 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b108_check : check atlasARows b107 b108 = true := by
  decide +kernel

private theorem b108_step :
    matrixRepresentation generatorA * decode b107 = decode b108 :=
  sound atlasARows b107 b108 b108_valid b108_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b109_valid : valid b108 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b109_check : check atlasBRows b108 b109 = true := by
  decide +kernel

private theorem b109_step :
    matrixRepresentation generatorB * decode b108 = decode b109 :=
  sound atlasBRows b108 b109 b109_valid b109_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b110_valid : valid b109 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b110_check : check atlasARows b109 b110 = true := by
  decide +kernel

private theorem b110_step :
    matrixRepresentation generatorA * decode b109 = decode b110 :=
  sound atlasARows b109 b110 b110_valid b110_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b111_valid : valid b110 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b111_check : check atlasBRows b110 b111 = true := by
  decide +kernel

private theorem b111_step :
    matrixRepresentation generatorB * decode b110 = decode b111 :=
  sound atlasBRows b110 b111 b111_valid b111_check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b112_valid : valid b111 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem b112_check : check atlasARows b111 b112 = true := by
  decide +kernel

private theorem b112_step :
    matrixRepresentation generatorA * decode b111 = decode b112 :=
  sound atlasARows b111 b112 b112_valid b112_check

private theorem b_word15 :
    matrixRepresentation wordB * decode b105 = decode b112 := by
  simp only [wordB, pow_succ, pow_zero, map_mul, map_one,
    Matrix.one_mul, Matrix.mul_assoc]
  rw [b106_step, b107_step, b108_step, b109_step, b110_step, b111_step, b112_step]

public theorem b_power16 :
    matrixRepresentation (wordB ^ 16) * decode b0 = decode b112 := by
  exact power_step wordB 15 _ _ _ b_power15 b_word15

end Lyons.OrderCertificate.PlaneTransport
